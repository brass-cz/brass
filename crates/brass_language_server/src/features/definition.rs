//! Go-to-definition.
//!
//! Resolution order at the cursor: a member access (`recv.name`) resolves
//! through the receiver's type to a method (or the owning type for a field);
//! otherwise the identifier resolves as a local binding in the enclosing
//! function, then a free function, then a type. Local resolution beats the
//! symbol tables so a local shadowing a function jumps to the local.

use brass_hir::Type;
use tower_lsp_server::ls_types::{Location, Position};

use crate::analysis::FullAnalysis;
use crate::document::Document;
use crate::features::nav;

/// Resolve the definition of the symbol at `pos`, as an LSP `Location` in the
/// file that defines it (or `None` for a prelude symbol with no file).
pub fn definition(doc: &Document, full: &FullAnalysis, pos: Position) -> Option<Location> {
    let local = doc.offset_at(pos);
    let global = local + full.main_base;
    let module = vec!["main".to_string()];

    // Member access `recv.name` -- a field access or a method call. Resolved from
    // the name under the cursor and the receiver type ending at the preceding `.`,
    // so it works for a method call (whose `recv.name` callee is not recorded as a
    // standalone typed expression) as well as a bare field access.
    if let Some(loc) = member_definition(doc, full, local) {
        return Some(loc);
    }

    let (name, _) = nav::ident_at(&doc.text, local)?;

    // A local binding in the enclosing function shadows everything else.
    if let Some(binding) = nav::local_binding(&full.main_ast, global, &name) {
        return nav::locate(full, binding.span);
    }
    if let Some(f) = full.program.resolve_function(&module, &name) {
        return nav::locate(full, f.signature.span);
    }
    if let Some(t) = full.program.resolve_type(&module, &name) {
        return nav::locate(full, t.span);
    }
    if let Some(alias) = full.program.resolve_type_alias(&module, &name) {
        return nav::locate(full, alias.span);
    }
    None
}

/// Resolve a member access `recv.name` at the cursor: the name under the cursor
/// must be immediately preceded by `.`, and the receiver's type ends at that `.`.
fn member_definition(doc: &Document, full: &FullAnalysis, local: usize) -> Option<Location> {
    let (name, span) = nav::ident_at(&doc.text, local)?;
    let bytes = doc.text.as_bytes();
    if span.lo == 0 || bytes.get(span.lo - 1) != Some(&b'.') {
        return None;
    }
    let recv_hi = full.main_base + (span.lo - 1);
    // The widest receiver expression ending at the `.` (so `foo.bar.method` uses
    // `foo.bar`), mirroring hover/completion.
    let recv_ty = full
        .typed
        .expressions
        .iter()
        .filter(|e| e.span.hi == recv_hi)
        .min_by_key(|e| e.span.lo)
        .map(|e| e.ty.clone())?;
    resolve_member(full, &recv_ty, &name)
}

/// Look up `name` on receiver type `recv_ty`: its method (precise span) or field
/// (the owning type's span) for a record, then -- for a primitive/array receiver
/// -- the stdlib method `fun T.name` implemented on that class.
fn resolve_member(full: &FullAnalysis, recv_ty: &Type, name: &str) -> Option<Location> {
    if let Some(id) = nominal_id(recv_ty)
        && let Some(info) = full.program.type_by_id(id)
    {
        if let brass_hir::TypeKind::Record { methods, .. } = &info.kind
            && let Some(m) = methods.get(name)
        {
            return nav::locate(full, m.signature.span);
        }
        if has_field(info, name) {
            return nav::locate(full, info.span);
        }
    }
    // A stdlib method on a primitive/array receiver (`fun string.split`),
    // dispatched by the receiver's class.
    let mut t = recv_ty;
    while let Type::Nullable(i) | Type::ConstOf(i) | Type::Mut(i) | Type::Ref(i) = t {
        t = i;
    }
    let class = t.primitive_class()?;
    let symbol = full
        .program
        .primitive_methods
        .get(&(class.to_string(), name.to_string()))?;
    let f = full.program.functions.get(symbol)?;
    nav::locate(full, f.signature.span)
}

fn nominal_id(ty: &Type) -> Option<i32> {
    match ty {
        Type::Record(n) | Type::Sum(n) => Some(n.id),
        Type::Nullable(inner) | Type::ConstOf(inner) | Type::Mut(inner) | Type::Ref(inner) => {
            nominal_id(inner)
        }
        _ => None,
    }
}

fn has_field(info: &brass_hir::TypeInfo, name: &str) -> bool {
    match &info.kind {
        brass_hir::TypeKind::Record { fields, .. } => fields.iter().any(|f| f.name == name),
        brass_hir::TypeKind::Sum { variants } => variants
            .iter()
            .any(|v| v.fields.iter().any(|f| f.name == name)),
    }
}
