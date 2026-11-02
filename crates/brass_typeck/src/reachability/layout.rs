//! Read instantiated declaration layouts without solving expressions or bodies.

use brass_hir::{FieldInfo, NominalInfo, Program, Substitution, Type, TypeInfo, TypeKind};
use brass_parser::ast::TypeExpr;
use std::collections::BTreeMap;

/// Read the field's HIR type, or resolve its retained annotation for sum fields.
/// Failed catalog resolution stays unknown; it cannot certify an absent effect.
pub(super) fn field(program: &Program, owner: &TypeInfo, field: &FieldInfo) -> Option<Type> {
    field
        .resolved_ty
        .clone()
        .or_else(|| annotation(program, &owner.module, field.ty.as_ref()?))
}

/// Resolve declaration syntax using HIR's qualified alias/nominal authorities.
/// Refinements instantiate the declaration's slot variables into real fields,
/// matching HIR's field-keyed substitution representation (not slot-name keys).
pub(super) fn annotation(program: &Program, module: &[String], expr: &TypeExpr) -> Option<Type> {
    if let TypeExpr::Refine(base, pins, _) = expr {
        let TypeExpr::Named(name, _) = base.as_ref() else {
            return None;
        };
        let owner = program.resolve_type(module, name)?;
        let TypeKind::Record { fields, .. } = &owner.kind else {
            return None;
        };
        let pins: BTreeMap<_, _> = pins
            .iter()
            .map(|(name, ty, _)| Some((name.as_str(), annotation(program, module, ty)?)))
            .collect::<Option<_>>()?;
        let slots = owner
            .slots
            .iter()
            .map(|(name, var)| {
                (
                    *var,
                    pins.get(name.as_str())
                        .cloned()
                        .unwrap_or(Type::Unknown(brass_hir::INFER_VAR)),
                )
            })
            .collect();
        let mut substitution = Substitution::empty();
        for item in fields {
            let ty = pins.get(item.name.as_str()).cloned().or_else(|| {
                item.resolved_ty
                    .as_ref()
                    .map(|ty| brass_hir::substitute_vars(ty, &slots))
            })?;
            substitution.insert(item.name.clone(), ty);
        }
        let Type::Record(mut nominal) = owner.type_ref() else {
            return None;
        };
        nominal.substitution = substitution;
        return Some(Type::Record(nominal));
    }
    brass_hir::types::resolve_with_aliases(
        expr,
        |name| {
            program.resolve_type(module, name).map(|info| {
                if info.is_sum() {
                    NominalInfo::sum(info.id)
                } else {
                    NominalInfo::record(info.id)
                }
            })
        },
        |name| {
            program
                .resolve_type_alias(module, name)
                .map(|alias| alias.ty.clone())
        },
    )
    .ok()
}
