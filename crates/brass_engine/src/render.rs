//! Render-order field resolution for nominal types.
//!
//! Both back ends render a record as `T {\n    field: <value>,\n}` and a sum
//! variant as `T.Variant { ... }`, and they must show the same fields, in the
//! same order, at the same resolved types: the LLVM JIT emits its renderer as
//! IR while the REPL interpreter walks runtime values, so any drift in the
//! field decision surfaces as output-parity breakage. The functions here are
//! the one authority both back ends' renderers resolve fields through; the
//! medium-specific emission (IR construction vs Rust string building) stays in
//! each back end.

use brass_hir::{NominalType, Program, Type, TypeKind};

/// The `(field name, concrete type)` list a record value of type `n` renders,
/// in declaration order, or `None` when no layout is available (the value then
/// renders as the bare `T {}`).
///
/// For a constructed value the substitution is authoritative: fields are taken
/// in declaration order with their substituted types (correct even when two
/// modules share a type name), and a declared field absent from the
/// substitution makes the whole layout unavailable. For a bare nominal
/// reference (empty substitution -- a sum variant binding or a nested declared
/// field type) the HIR declaration's field names and declared types are used,
/// so the nominal still renders. A nominal unknown to the program (a
/// structural record built at a deserialize boundary) renders its substitution
/// in its sorted field-name order.
///
/// The LLVM back end also derives a record's byte layout by walking this list,
/// so a record is constructed, accessed, and rendered through one field order.
pub fn render_record_fields(program: &Program, n: &NominalType) -> Option<Vec<(String, Type)>> {
    if n.substitution.is_empty() {
        let info = program.type_by_id(n.id)?;
        let TypeKind::Record { fields, .. } = &info.kind else {
            return None;
        };
        return fields
            .iter()
            .map(|f| f.resolved_ty.clone().map(|t| (f.name.clone(), t)))
            .collect();
    }
    let names: Vec<String> = match program.type_by_id(n.id) {
        Some(info) => match &info.kind {
            TypeKind::Record { fields, .. } => fields.iter().map(|f| f.name.clone()).collect(),
            _ => return None,
        },
        None => n
            .substitution
            .iter()
            .map(|(name, _)| name.to_string())
            .collect(),
    };
    names
        .into_iter()
        .map(|name| n.substitution.get(&name).cloned().map(|t| (name, t)))
        .collect()
}

/// The `(tag, [(field name, concrete type)])` of the named variant of the sum
/// type `n`, fields in declaration order, or `None` when the variant cannot be
/// resolved: an unknown nominal or variant name, or any field whose type is
/// neither in the substitution nor declared. An unresolvable variant renders
/// as the bare type name (the JIT reaches it through its unknown-tag default);
/// a resolvable field-less variant renders as bare `T.Variant`.
///
/// A field's concrete type is carried in the substitution keyed
/// `Variant.field` when it was inferred at construction -- the built-in
/// `Result` carries its payloads this way, under `Ok.value` / `Err.error` --
/// and the declared type is otherwise concrete enough to render.
///
/// Like [`render_record_fields`], this list also orders the LLVM back end's
/// variant payload layout, keeping construction and rendering consistent.
pub fn render_variant_fields(
    program: &Program,
    n: &NominalType,
    variant: &str,
) -> Option<(i32, Vec<(String, Type)>)> {
    let info = program.type_by_id(n.id)?;
    let TypeKind::Sum { variants } = &info.kind else {
        return None;
    };
    let v = variants.iter().find(|v| v.name == variant)?;
    let fields = v
        .fields
        .iter()
        .map(|fld| {
            n.substitution
                .get(&format!("{variant}.{}", fld.name))
                .cloned()
                .or_else(|| fld.resolved_ty.clone())
                .map(|t| (fld.name.clone(), t))
        })
        .collect::<Option<Vec<_>>>()?;
    Some((v.tag, fields))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bare_record_with_unresolved_field_has_no_partial_layout() {
        // The renderer's Option describes the entire layout. One unresolved
        // declaration invalidates it instead of silently dropping that field.
        let ast = brass_parser::parse("type Open = { known: int32, missing }\n").expect("parse");
        let (mut program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty(), "{errors:?}");
        let symbol = program
            .resolve_type(&["main".into()], "Open")
            .expect("Open")
            .symbol
            .clone();
        let TypeKind::Record { fields, .. } = &mut program.types.get_mut(&symbol).unwrap().kind
        else {
            panic!("Open is a record");
        };
        fields
            .iter_mut()
            .find(|field| field.name == "missing")
            .expect("missing field")
            .resolved_ty = None;
        let Type::Record(nominal) = program
            .resolve_type(&["main".into()], "Open")
            .expect("Open")
            .type_ref()
        else {
            panic!("Open is a record");
        };
        assert!(render_record_fields(&program, &nominal).is_none());
    }
}
