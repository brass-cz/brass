//! The declared record type a `T.from(v)` conversion builds: a nominal whose
//! substitution carries every field's declared type, resolved through a type
//! alias's pins when `T` names an alias.

use super::*;

/// The concrete `Type` of the record `T.from(v)` builds, `T` being `name` as
/// written in `module`: a nominal carrying every field's declared type in its
/// substitution, exactly as a constructed record does -- so it satisfies the
/// typed back end's support check and field reads resolve. Returns `None` if
/// `name` is neither a record type nor a record alias visible in `module`, or
/// a field has no declared type.
pub(super) fn record_from_target(program: &Program, module: &[String], name: &str) -> Option<Type> {
    if let Some(info) = program.resolve_type(module, name) {
        return declared_record_type(info);
    }
    // A `type A = R { .. }` alias names `R` at its instance: the fields it
    // pins take the pinned types.
    let alias = program.resolve_type_alias(module, name)?;
    let Type::Record(pins) = &alias.ty else {
        return None;
    };
    let Type::Record(mut record) = declared_record_type(program.type_by_id(pins.id)?)? else {
        return None;
    };
    for (field, pinned) in pins.substitution.iter() {
        if record.substitution.get(field).is_some() {
            record
                .substitution
                .insert(field.to_string(), pinned.clone());
        }
    }
    Some(Type::Record(record))
}

/// A record declaration as a nominal whose substitution holds every field's
/// declared type; `None` for a sum or a field without a declared type.
fn declared_record_type(info: &brass_hir::TypeInfo) -> Option<Type> {
    let TypeKind::Record { fields, .. } = &info.kind else {
        return None;
    };
    let mut subst = Substitution::empty();
    for f in fields {
        subst.insert(f.name.clone(), f.resolved_ty.clone()?);
    }
    Some(Type::Record(NominalType::with_substitution(
        info.id,
        info.name.clone(),
        subst,
    )))
}
