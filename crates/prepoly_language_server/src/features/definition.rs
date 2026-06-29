//! Go-to-definition.
//!
//! Resolution order at the cursor: a member access (`recv.name`) resolves
//! through the receiver's type to a method (or the owning type for a field);
//! otherwise the identifier resolves as a local binding in the enclosing
//! function, then a free function, then a type. Local resolution beats the
//! symbol tables so a local shadowing a function jumps to the local.

use prepoly_hir::{Type, TypedExprKind};
use prepoly_lexer::Span;
use prepoly_parser::ast::{Block, Expr, FieldPat, Pattern, Stmt, StrSeg};
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

    // Member access through a receiver type.
    if let Some(expr) = nav::smallest_typed_at(full, global)
        && let TypedExprKind::Field(name) = &expr.kind
        && let Some(loc) = resolve_member(full, &module, expr.span, name)
    {
        return Some(loc);
    }

    let (name, _) = nav::ident_at(&doc.text, local)?;

    // A local binding in the enclosing function shadows everything else.
    if let Some(span) = local_binding(full, global, &name) {
        return nav::locate(full, span);
    }
    if let Some(f) = full.program.resolve_function(&module, &name) {
        return nav::locate(full, f.signature.span);
    }
    if let Some(t) = full.program.resolve_type(&module, &name) {
        return nav::locate(full, t.span);
    }
    None
}

/// Resolve `recv.name` given the global span of the whole field expression:
/// look up the receiver's type, then its method (precise span) or field (the
/// owning type's span), falling back to a UFCS free function of the same name.
fn resolve_member(
    full: &FullAnalysis,
    module: &[String],
    field_span: Span,
    name: &str,
) -> Option<Location> {
    let recv_span = receiver_of_field(&full.main_ast, field_span)?;
    let recv_ty = full
        .typed
        .expressions
        .iter()
        .find(|e| e.span == recv_span)
        .map(|e| &e.ty)?;
    if let Some(id) = nominal_id(recv_ty)
        && let Some(info) = full.program.type_by_id(id)
    {
        if let prepoly_hir::TypeKind::Record { methods, .. } = &info.kind
            && let Some(m) = methods.get(name)
        {
            return nav::locate(full, m.signature.span);
        }
        if has_field(info, name) {
            return nav::locate(full, info.span);
        }
    }
    // UFCS: `arr.map(f)` calls the free function `map`.
    let f = full.program.resolve_function(module, name)?;
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

fn has_field(info: &prepoly_hir::TypeInfo, name: &str) -> bool {
    match &info.kind {
        prepoly_hir::TypeKind::Record { fields, .. } => fields.iter().any(|f| f.name == name),
        prepoly_hir::TypeKind::Sum { variants } => variants
            .iter()
            .any(|v| v.fields.iter().any(|f| f.name == name)),
    }
}

/// Find the nearest binding of `name` visible at `global_off` within the
/// enclosing function. Approximates lexical scope by the nearest preceding
/// binding in the function, which is correct in the absence of inner-block
/// shadowing after the use.
fn local_binding(full: &FullAnalysis, global_off: usize, name: &str) -> Option<Span> {
    let (params, body) = nav::enclosing(&full.main_ast, global_off)?;
    let mut found: Option<Span> = None;
    let mut consider = |bname: &str, span: Span| {
        if bname == name && span.lo <= global_off && found.map(|f| span.lo > f.lo).unwrap_or(true) {
            found = Some(span);
        }
    };
    for p in params {
        consider(&p.name, p.span);
    }
    collect_block_bindings(body, &mut consider);
    found
}

/// Walk a block collecting every binding it introduces (let patterns, for-loop
/// variables, closure parameters), invoking `f(name, span)` for each.
fn collect_block_bindings(block: &Block, f: &mut impl FnMut(&str, Span)) {
    for s in &block.stmts {
        collect_stmt_bindings(s, f);
    }
}

fn collect_stmt_bindings(s: &Stmt, f: &mut impl FnMut(&str, Span)) {
    match s {
        Stmt::Let { pat, value, .. } => {
            collect_pattern_bindings(pat, f);
            collect_expr_bindings(value, f);
        }
        Stmt::Assign { value, .. } => collect_expr_bindings(value, f),
        Stmt::Expr(e) => collect_expr_bindings(e, f),
        Stmt::While { body, .. } => collect_block_bindings(body, f),
        Stmt::For {
            var,
            iter,
            body,
            span,
        } => {
            // The loop variable has no standalone span; attribute it to the loop
            // header so it precedes uses inside the body.
            f(var, Span::new(span.lo, span.lo));
            collect_expr_bindings(iter, f);
            collect_block_bindings(body, f);
        }
        Stmt::Return(Some(e), _) => collect_expr_bindings(e, f),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

fn collect_pattern_bindings(p: &Pattern, f: &mut impl FnMut(&str, Span)) {
    match p {
        Pattern::Binding(name, span) => f(name, *span),
        Pattern::Record(_, fields, _) => {
            for FieldPat { name, pat, span } in fields {
                match pat {
                    Some(p) => collect_pattern_bindings(p, f),
                    None => f(name, *span),
                }
            }
        }
        Pattern::Array(pats, _) => {
            for p in pats {
                collect_pattern_bindings(p, f);
            }
        }
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
    }
}

/// Closures introduce bindings too; recurse into expressions to reach them.
fn collect_expr_bindings(e: &Expr, f: &mut impl FnMut(&str, Span)) {
    match e {
        Expr::Closure(params, body, _) => {
            for p in params {
                f(&p.name, p.span);
            }
            collect_expr_bindings(body, f);
        }
        Expr::Block(b, _) => collect_block_bindings(b, f),
        Expr::Unary(_, e, _) | Expr::ErrorProp(e, _) => collect_expr_bindings(e, f),
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) => {
            collect_expr_bindings(a, f);
            collect_expr_bindings(b, f);
        }
        Expr::Call(callee, args, _) => {
            collect_expr_bindings(callee, f);
            for arg in args {
                collect_expr_bindings(&arg.expr, f);
            }
        }
        Expr::Field(recv, _, _) => collect_expr_bindings(recv, f),
        Expr::Array(elems, _) => {
            for e in elems {
                collect_expr_bindings(e, f);
            }
        }
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(e) = seg {
                    collect_expr_bindings(e, f);
                }
            }
        }
        Expr::If(cond, then, els, _) => {
            collect_expr_bindings(cond, f);
            collect_block_bindings(then, f);
            if let Some(e) = els {
                collect_expr_bindings(e, f);
            }
        }
        Expr::IfLet(pat, scrut, then, els, _) => {
            collect_pattern_bindings(pat, f);
            collect_expr_bindings(scrut, f);
            collect_block_bindings(then, f);
            if let Some(e) = els {
                collect_expr_bindings(e, f);
            }
        }
        Expr::Match(scrut, arms, _) => {
            collect_expr_bindings(scrut, f);
            for arm in arms {
                collect_pattern_bindings(&arm.pattern, f);
                collect_expr_bindings(&arm.body, f);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, v) in fields {
                collect_expr_bindings(v, f);
            }
        }
        _ => {}
    }
}

/// Find the receiver span of the `Expr::Field` whose whole span is `field_span`.
fn receiver_of_field(main_ast: &prepoly_parser::ast::Module, field_span: Span) -> Option<Span> {
    let mut result = None;
    let mut visit = |e: &Expr| {
        if let Expr::Field(recv, _, span) = e
            && *span == field_span
        {
            result = Some(recv.span());
        }
    };
    nav::walk_exprs(main_ast, &mut visit);
    result
}
