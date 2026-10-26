//! A callable's declared parameters at an instance: the parameter types an
//! instance starts from (a parameter declared nullable stays nullable), and
//! the backstop that every argument for a record-annotated parameter carries
//! the record's data fields.

use super::*;

/// Verify that every argument passed for a parameter annotated with a
/// declared record carries the record's data fields.
///
/// A record-annotated parameter is instantiated at the argument's own type
/// (structural subtyping: a record with more fields is accepted), so the
/// instance reads each field the annotation declares out of the argument's
/// layout. The checker admits only arguments that have all of them; an
/// argument lacking one would make the instance read a field that does not
/// exist, so it is reported as an internal error here rather than compiled.
/// Function-typed (protocol) members are provided by methods, not stored,
/// and are not required of the argument's layout.
pub(super) fn check_record_params(
    program: &Program,
    callee: &str,
    params: &[brass_hir::ParamInfo],
    arg_types: &[Type],
) -> Result<(), String> {
    for (param, arg) in params.iter().zip(arg_types) {
        let Some(Type::Record(want)) = param.resolved_ty.as_ref().map(record_position) else {
            continue;
        };
        let Type::Record(have) = record_position(arg) else {
            continue;
        };
        if have.id == want.id {
            continue;
        }
        let Some(TypeKind::Record { fields, .. }) =
            program.type_by_id(want.id).map(|info| &info.kind)
        else {
            continue;
        };
        let missing = fields.iter().find(|field| {
            !matches!(field.resolved_ty, Some(Type::Fun(..)))
                && !record_has_field(program, have, &field.name)
        });
        if let Some(field) = missing {
            return Err(format!(
                "internal error: `{callee}` was instantiated with a `{}` argument for parameter \
                 `{}: {}`, which lacks its field `{}`",
                arg.display(),
                param.name,
                want.name(),
                field.name
            ));
        }
    }
    Ok(())
}

/// The record a parameter or argument type holds, seen through passing modes
/// and a nullable.
fn record_position(ty: &Type) -> &Type {
    match brass_hir::peel_modes(ty) {
        Type::Nullable(inner) => brass_hir::peel_modes(inner),
        other => other,
    }
}

/// Whether record instance `record` stores a field named `name`: its
/// substitution for a structural record, its declaration otherwise.
fn record_has_field(program: &Program, record: &NominalType, name: &str) -> bool {
    if record.id == brass_hir::STRUCTURAL_RECORD_ID {
        return record.substitution.get(name).is_some();
    }
    match program.type_by_id(record.id).map(|info| &info.kind) {
        Some(TypeKind::Record { fields, .. }) => fields.iter().any(|f| f.name == name),
        _ => false,
    }
}

/// The declared parameters of method `name` of the type `info` (a sum's
/// method is declared on every variant with one signature).
pub(super) fn method_params<'p>(
    info: &'p brass_hir::TypeInfo,
    name: &str,
) -> Option<&'p [brass_hir::ParamInfo]> {
    match &info.kind {
        TypeKind::Record { methods, .. } => Some(&methods.get(name)?.signature.params),
        TypeKind::Sum { variants } => variants
            .iter()
            .find_map(|v| v.methods.get(name))
            .map(|m| m.signature.params.as_slice()),
    }
}

impl Monomorphizer<'_, '_> {
    /// The parameter types an instance created for a call with `arg_types`
    /// starts from: each argument's own type (an instance is specialized per
    /// caller type -- a record argument with more fields than a declared
    /// record parameter included), except that a parameter declared nullable
    /// (`T?`) stays nullable in every instance. A non-null argument flows in
    /// by nullable promotion -- the instance takes `X?` for an `X` argument,
    /// keeping the caller's refinement of `T` -- so the body's null tests stay
    /// live; a `null` argument takes the declared `T?` when the declaration
    /// fully describes it, so the body can read the value it tests for.
    /// (A simple annotation's declared type is seeded onto the parameter
    /// local by lowering and overrides this.)
    pub(super) fn instance_param_types(
        &self,
        params: &[brass_hir::ParamInfo],
        arg_types: &[Type],
    ) -> Vec<Type> {
        arg_types
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let declared = params
                    .get(i)
                    .and_then(|p| p.resolved_ty.as_ref())
                    .map(brass_hir::peel_modes);
                match declared {
                    Some(Type::Nullable(inner)) => self.nullable_param_type(inner, arg),
                    _ => arg.clone(),
                }
            })
            .collect()
    }

    /// The instance type of a parameter declared `declared?` receiving an
    /// argument of type `arg` (see [`Self::instance_param_types`]).
    fn nullable_param_type(&self, declared: &Type, arg: &Type) -> Type {
        match arg {
            Type::Nullable(inner) if matches!(**inner, Type::Never) => {
                let declared = Type::Nullable(Box::new(resolve_nominal(self.program, declared)));
                if brass_hir::is_fully_known(&declared)
                    && self.self_describing(&declared)
                    && is_supported(&declared)
                {
                    declared
                } else {
                    arg.clone()
                }
            }
            Type::Nullable(_) => arg.clone(),
            other => Type::Nullable(Box::new(other.clone())),
        }
    }
}
