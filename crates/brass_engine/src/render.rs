//! Shared rendering policy, concrete user renderers, and nominal field layout.
//!
//! In the builtin structural form, both back ends render a record as `T {\n    field: <value>,\n}` and a sum
//! variant as `T.Variant { ... }`, and they must show the same fields, in the
//! same order, at the same resolved types: the LLVM JIT emits its renderer as
//! IR while the REPL interpreter walks runtime values, so any drift in the
//! field decision surfaces as output-parity breakage. The functions here are
//! the one authority both back ends' renderers resolve fields through; the
//! medium-specific emission (IR construction vs Rust string building) stays in
//! each back end.

use brass_hir::{NominalType, Program, Type, TypeKind};

/// The requested text form, shared with the checker declaration hook.
pub use brass_hir::rendering::RenderForm;

/// Resolve the user renderer's exact instance symbol, or the builtin fallback.
/// Both back ends use this authority. For a nullable, the symbol accepts the
/// inner value; the caller must retain its null branch and unwrap when present.
pub fn resolve_renderer(program: &Program, ty: &Type, form: RenderForm) -> Option<String> {
    let method = brass_hir::rendering::render_method(program, ty, form)?;
    let mut receiver = brass_hir::peel_modes(ty);
    while let Type::Nullable(inner) = receiver {
        receiver = brass_hir::peel_modes(inner);
    }
    Some(crate::method_symbol(method, std::slice::from_ref(receiver)))
}

/// Concrete nominal user-method calls made by a renderer, in layout order.
/// A custom method owns the remaining traversal. Builtin recursive layouts
/// are visited once per concrete type; callable fields stay opaque.
pub fn renderer_dependencies(
    program: &Program,
    ty: &Type,
    form: RenderForm,
) -> Vec<(Type, &'static str)> {
    fn visit(
        program: &Program,
        ty: &Type,
        form: RenderForm,
        seen: &mut fxhash::FxHashSet<Type>,
        out: &mut Vec<(Type, &'static str)>,
    ) {
        let ty = brass_hir::peel_modes(ty);
        if let Type::Nullable(inner) = ty {
            visit(program, inner, form, seen, out);
            return;
        }
        if let Some(method) = brass_hir::rendering::render_method(program, ty, form) {
            if seen.insert(ty.clone()) {
                out.push((ty.clone(), method));
            }
            return;
        }
        match ty {
            Type::Slice(t) | Type::Array(t, _) => visit(program, t, RenderForm::Debug, seen, out),
            Type::Tuple(ts) => {
                for t in ts {
                    visit(program, t, RenderForm::Debug, seen, out);
                }
            }
            Type::Record(n) if seen.insert(ty.clone()) => {
                for (_, t) in render_record_fields(program, n).unwrap_or_default() {
                    visit(program, &t, RenderForm::Debug, seen, out);
                }
            }
            Type::Sum(n) if seen.insert(ty.clone()) => {
                if let Some(TypeKind::Sum { variants }) = program.type_by_id(n.id).map(|i| &i.kind)
                {
                    for v in variants {
                        if let Some((_, fields)) = render_variant_fields(program, n, &v.name) {
                            for (_, t) in fields {
                                visit(program, &t, RenderForm::Debug, seen, out);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    visit(
        program,
        ty,
        form,
        &mut fxhash::FxHashSet::default(),
        &mut out,
    );
    out
}

/// The `(field name, concrete type)` list a record value of type `n` renders,
/// in declaration order, or `None` when no layout is available (the value then
/// renders as the bare `T {}`).
///
/// A substitution overrides the corresponding declared field type. Inferred
/// instances may carry only their generic fields, so an absent entry uses the
/// declaration, exactly as field-access typing does. A field with neither an
/// instance type nor a declared type makes the whole layout unavailable. Bare
/// nominal references use the same declaration fallback. A nominal unknown to
/// the program (a structural record or a view of one) renders its substitution
/// in sorted field-name order.
///
/// The LLVM back end also derives a record's byte layout by walking this list,
/// so a record is constructed, accessed, and rendered through one field order.
pub fn render_record_fields(program: &Program, n: &NominalType) -> Option<Vec<(String, Type)>> {
    if n.substitution.is_empty() {
        // A structural record without fields -- the view of an anonymous
        // argument whose callee only renders the parameter whole -- has the
        // empty layout, not an unavailable one.
        if n.id == brass_hir::STRUCTURAL_RECORD_ID {
            return Some(Vec::new());
        }
        let info = program.type_by_id(n.id)?;
        let TypeKind::Record { fields, .. } = &info.kind else {
            return None;
        };
        return fields
            .iter()
            .map(|f| f.resolved_ty.clone().map(|t| (f.name.clone(), t)))
            .collect();
    }
    match program.type_by_id(n.id) {
        Some(info) => match &info.kind {
            TypeKind::Record { fields, .. } => fields
                .iter()
                .map(|field| {
                    n.substitution
                        .get(&field.name)
                        .cloned()
                        .or_else(|| field.resolved_ty.clone())
                        .map(|ty| (field.name.clone(), ty))
                })
                .collect(),
            _ => None,
        },
        None => Some(
            n.substitution
                .iter()
                .map(|(name, ty)| (name.to_string(), ty.clone()))
                .collect(),
        ),
    }
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
            source: None,
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

    #[test]
    fn partial_instance_keeps_declared_fields_and_requires_open_fields() {
        let ast = brass_parser::parse("type Cell = { count: int64, value }\n").expect("parse");
        let (mut program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty(), "{errors:?}");
        let symbol = program
            .resolve_type(&["main".into()], "Cell")
            .unwrap()
            .symbol
            .clone();
        let TypeKind::Record { fields, .. } = &mut program.types.get_mut(&symbol).unwrap().kind
        else {
            panic!("Cell is a record");
        };
        fields[0].resolved_ty = Some(Type::Int(brass_hir::IntKind::I64));
        fields[1].resolved_ty = None;
        let Type::Record(mut nominal) = program
            .resolve_type(&["main".into()], "Cell")
            .unwrap()
            .type_ref()
        else {
            panic!("Cell is a record");
        };
        nominal.substitution.insert("value", Type::Str);
        assert_eq!(
            render_record_fields(&program, &nominal),
            Some(vec![
                ("count".into(), Type::Int(brass_hir::IntKind::I64)),
                ("value".into(), Type::Str),
            ])
        );
        // A supplied fixed field cannot stand in for an untyped generic field.
        nominal.substitution = brass_hir::Substitution::empty();
        nominal
            .substitution
            .insert("count", Type::Int(brass_hir::IntKind::I64));
        assert!(render_record_fields(&program, &nominal).is_none());
    }
}
