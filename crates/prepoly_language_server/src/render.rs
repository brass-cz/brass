//! Type and signature rendering for hover.
//!
//! The compiler's `Type::display` prints every inference variable as a bare
//! `?`, which is ambiguous when several appear. For hover output we instead
//! number them `unknown_N` by order of first appearance, as the language
//! server's contract requires: a function whose parameters carry no annotation
//! has each unannotated slot shown as a distinct `unknown_N`, numbered in the
//! order the parameters (then the return) occur.

use std::collections::HashMap;

use prepoly_hir::{CallableSignature, FieldInfo, Type, TypeInfo, TypeKind, VariantInfo};

/// Assigns stable `unknown_N` names to inference variables, numbered by order
/// of first appearance. Share one namer across everything that should agree on
/// numbering -- e.g. all parameters and the return type of one signature.
#[derive(Default)]
pub struct UnknownNamer {
    /// Names already assigned to a concrete `Type::Unknown(id)`, so the same
    /// variable renders identically wherever it recurs.
    by_id: HashMap<u32, usize>,
    next: usize,
}

impl UnknownNamer {
    /// The name for inference variable `id`, allocating a fresh number the first
    /// time the id is seen.
    fn named(&mut self, id: u32) -> String {
        let next = self.next;
        let n = *self.by_id.entry(id).or_insert_with(|| {
            // `next` was captured before the borrow; only commit it on insert.
            next
        });
        if n == next {
            self.next += 1;
        }
        format!("unknown_{n}")
    }

    /// A fresh `unknown_N` with no backing inference variable, for an
    /// unannotated parameter or return type that the front end never assigned an
    /// id (the signature tables only retain explicit annotations).
    fn fresh(&mut self) -> String {
        let n = self.next;
        self.next += 1;
        format!("unknown_{n}")
    }
}

/// Render a resolved type, mapping inference variables to `unknown_N`.
pub fn render_type(ty: &Type, namer: &mut UnknownNamer) -> String {
    match ty {
        Type::Bool => "bool".into(),
        Type::Int(k) => k.name().into(),
        Type::Float(k) => k.name().into(),
        Type::Str => "string".into(),
        Type::Void => "void".into(),
        Type::Never => "never".into(),
        Type::Record(n) | Type::Sum(n) => render_nominal(n, namer),
        Type::Array(t, len) => format!("{}[{}]", render_type(t, namer), len),
        Type::Slice(t) => format!("{}[]", render_type(t, namer)),
        Type::Fun(params, ret) => format!(
            "({}) -> {}",
            params
                .iter()
                .map(|p| render_type(p, namer))
                .collect::<Vec<_>>()
                .join(", "),
            render_type(ret, namer)
        ),
        Type::Nullable(t) => format!("{}?", render_type(t, namer)),
        Type::ConstOf(t) => format!("const {}", render_type(t, namer)),
        Type::Unknown(id) => namer.named(*id),
        Type::SelfType => "Self".into(),
    }
}

/// Render a nominal type reference, recursing into a `Result` payload (or any
/// substitution) so inference variables there are also numbered.
fn render_nominal(n: &prepoly_hir::NominalType, namer: &mut UnknownNamer) -> String {
    if let Some((ok, err)) = n.result_payloads() {
        return format!(
            "Result<{}, {}>",
            render_type(ok, namer),
            render_type(err, namer)
        );
    }
    let mut subst: Vec<_> = n.substitution.iter().collect();
    if subst.is_empty() {
        return n.name().to_string();
    }
    subst.sort_by(|a, b| a.0.cmp(b.0));
    let entries = subst
        .into_iter()
        .map(|(key, ty)| format!("{key}={}", render_type(ty, namer)))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}<{entries}>", n.name())
}

/// Render a function or method signature as `fun name(p: T, ...) -> R`.
///
/// A parameter or return type with no annotation has no resolved type in the
/// signature tables, so it is rendered as a fresh `unknown_N` numbered by
/// position. An explicitly annotated slot is rendered from its resolved type.
pub fn render_signature(sig: &CallableSignature) -> String {
    render_signature_with(sig, None)
}

/// Like [`render_signature`], but an unannotated return type is rendered from
/// `inferred_ret` when given -- the type inference recovered for the function
/// (see `nav::inferred_return`) -- instead of a fresh `unknown_N`. The signature
/// tables hold only annotations, so this is how an inferred-but-unannotated
/// return such as a fallible `string` reaches hover output.
pub fn render_signature_with(sig: &CallableSignature, inferred_ret: Option<&Type>) -> String {
    let mut namer = UnknownNamer::default();
    let params = sig
        .params
        .iter()
        .map(|p| {
            // The method receiver is written bare in source and its type is the
            // enclosing type, so it is shown as `self` without consuming an
            // `unknown_N` slot -- the first real unannotated parameter is then
            // `unknown_0`.
            if p.name == "self" && p.resolved_ty.is_none() {
                return "self".to_string();
            }
            let ty = match &p.resolved_ty {
                Some(t) => render_type(t, &mut namer),
                None => namer.fresh(),
            };
            format!("{}: {ty}", p.name)
        })
        .collect::<Vec<_>>()
        .join(", ");
    let ret = match (&sig.ret_ty, inferred_ret) {
        (Some(t), _) => render_type(t, &mut namer),
        (None, Some(t)) => render_type(t, &mut namer),
        (None, None) => namer.fresh(),
    };
    format!("fun {}({params}) -> {ret}", sig.name)
}

/// Render a type definition for hover over a type name: a record's fields or a
/// sum type's variants, each on its own line.
pub fn render_type_def(info: &TypeInfo) -> String {
    let mut namer = UnknownNamer::default();
    match &info.kind {
        TypeKind::Record { fields, methods } => {
            let mut body = String::new();
            for f in fields {
                body.push_str(&format!("    {}\n", render_field(f, &mut namer)));
            }
            let mut names: Vec<&String> = methods.keys().collect();
            names.sort();
            for name in names {
                let sig = render_signature(&methods[name].signature);
                body.push_str(&format!("    {sig}\n"));
            }
            format!("type {} = {{\n{body}}}", info.name)
        }
        TypeKind::Sum { variants } => {
            let body = variants
                .iter()
                .map(|v| format!("    {}", render_variant(v, &mut namer)))
                .collect::<Vec<_>>()
                .join("\n");
            format!("type {} =\n{body}", info.name)
        }
    }
}

fn render_field(f: &FieldInfo, namer: &mut UnknownNamer) -> String {
    match &f.resolved_ty {
        Some(t) => format!("{}: {}", f.name, render_type(t, namer)),
        None => f.name.clone(),
    }
}

fn render_variant(v: &VariantInfo, namer: &mut UnknownNamer) -> String {
    if v.fields.is_empty() {
        return v.name.clone();
    }
    let fields = v
        .fields
        .iter()
        .map(|f| render_field(f, namer))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{} {{ {fields} }}", v.name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use prepoly_hir::{IntKind, Type};

    /// Distinct inference variables number by order of appearance and repeat
    /// consistently; a concrete type in between does not consume a number.
    #[test]
    fn unknowns_numbered_by_appearance() {
        let mut namer = UnknownNamer::default();
        let ty = Type::Fun(
            vec![Type::Unknown(7), Type::Int(IntKind::I32), Type::Unknown(3)],
            Box::new(Type::Unknown(7)),
        );
        assert_eq!(
            render_type(&ty, &mut namer),
            "(unknown_0, int32, unknown_1) -> unknown_0"
        );
    }
}
