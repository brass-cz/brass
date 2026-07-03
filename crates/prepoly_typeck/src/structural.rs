//! Structural subtyping: a record type S is usable where T is
//! required when S has every field and method of T with compatible types.
//! Sum types are nominal and excluded.

use std::collections::HashMap;

use prepoly_hir::{
    CallableSignature, MethodInfo, NominalType, ParamInfo, Program, STRUCTURAL_RECORD_ID, Type,
    TypeKind,
};

/// Whether `a` and `b` are mutually compatible, i.e. invariant. Mutable record
/// fields and method parameters use this instead of one-directional
/// assignability: a value stored in a field can be both read and overwritten,
/// and a parameter is consumed by the body, so widening either direction is
/// unsound. Unknowns stay flexible because
/// `types_compatible` accepts them in both directions, which preserves
/// interface constraint propagation.
pub fn types_invariant(program: &Program, a: &Type, b: &Type) -> bool {
    types_compatible(program, a, b) && types_compatible(program, b, a)
}

/// Whether a value of `have` can be used where `want` is required.
pub fn types_compatible(program: &Program, have: &Type, want: &Type) -> bool {
    if let (Some((h_ok, h_err)), Some((w_ok, w_err))) =
        (have.result_payloads(), want.result_payloads())
    {
        return types_compatible(program, h_ok, w_ok) && types_compatible(program, h_err, w_err);
    }
    if have.is_result_type() && want.is_result_type() {
        return true;
    }
    match (have, want) {
        (Type::Unknown(_), _) | (_, Type::Unknown(_)) => true,
        (Type::ConstOf(h), Type::ConstOf(w)) => types_compatible(program, h, w),
        (Type::ConstOf(h), other) => types_compatible(program, h, other),
        (other, Type::ConstOf(w)) => types_compatible(program, other, w),
        (Type::Mut(h), Type::Mut(w)) => types_compatible(program, h, w),
        (Type::Mut(h), other) => types_compatible(program, h, other),
        (other, Type::Mut(w)) => types_compatible(program, other, w),
        (Type::Ref(h), Type::Ref(w)) => types_compatible(program, h, w),
        (Type::Ref(h), other) => types_compatible(program, h, other),
        (other, Type::Ref(w)) => types_compatible(program, other, w),
        (Type::Never, Type::Nullable(_)) => true,
        (Type::Nullable(h), Type::Nullable(w))
            if matches!(h.as_ref(), Type::Never) || matches!(w.as_ref(), Type::Never) =>
        {
            true
        }
        (Type::Nullable(h), Type::Nullable(w)) => types_compatible(program, h, w),
        // Arrays and slices are mutable shared storage (`[T]` aliases the same
        // backing buffer), so their element type is invariant: reading wants
        // covariance and overwriting wants contravariance, and only invariance is
        // sound for both. Treating them as covariant would let a `Dog[]` alias as
        // `Animal[]`, store a bare `Animal`, and then read it back as a `Dog`.
        (Type::Array(h, hn), Type::Array(w, wn)) if hn == wn => types_invariant(program, h, w),
        (Type::Slice(h), Type::Slice(w)) => types_invariant(program, h, w),
        // A fixed-length array is usable where a slice is required: both share
        // the same runtime storage and the length is extra static information
        // the slice position simply drops. Not the reverse -- a slice's length
        // is dynamic, so it cannot satisfy a fixed-length position.
        (Type::Array(h, _), Type::Slice(w)) => types_invariant(program, h, w),
        // Function parameters are contravariant and the return type covariant: a
        // value usable where `(W) -> R` is required must accept every `W` the
        // caller may pass, so each required parameter `w` must be usable where the
        // value's parameter `h` is required (the reversed direction).
        (Type::Fun(hp, hr), Type::Fun(wp, wr)) if hp.len() == wp.len() => {
            hp.iter()
                .zip(wp)
                .all(|(h, w)| types_compatible(program, w, h))
                && types_compatible(program, hr, wr)
        }
        // Same *declared* record type instantiated two ways: compatible only when
        // each field the required instance fixes matches the value's. This mirrors
        // `sum_assignable` and is what the structural path below cannot see -- it
        // compares against the declaration's (unannotated, so anything-matching)
        // fields, ignoring the instantiation, which would let `_Entry<string,
        // int32>` pass as `_Entry<string, string>` and corrupt the unboxed layout.
        (Type::Record(sub), Type::Record(sup)) if sub.id >= 0 && sub.id == sup.id => {
            record_refinement_compatible(program, sub, sup)
        }
        (Type::Record(sub), Type::Record(sup)) if !sub.same_nominal(sup) => {
            record_satisfies(program, sub, sup).is_empty()
        }
        (Type::Sum(a), Type::Sum(b)) => sum_assignable(program, a, b),
        _ => have == want,
    }
}

/// Whether a value of record instance `sub` is usable where the same declared
/// record `sup` (a possibly-differently-instantiated version) is required: every
/// field the required instance fixes in its substitution must be present in the
/// value's and *invariant* with it (record fields are mutable). A field the
/// required instance leaves open (absent from its substitution) imposes no
/// constraint. Mirrors [`sum_assignable`] for records.
fn record_refinement_compatible(program: &Program, sub: &NominalType, sup: &NominalType) -> bool {
    sup.substitution
        .iter()
        .all(|(key, wt)| match sub.substitution.get(key) {
            Some(ht) => types_invariant(program, ht, wt),
            None => true,
        })
}

/// Whether a value of sum `have` is usable where sum `want` is required. A sum is
/// nominal, but a value's substitution may *refine* it with the concrete types of
/// unannotated variant fields (recorded at construction, e.g. `S<B.value=string>`).
/// A more refined value is usable where a less refined -- in particular the bare --
/// nominal is required: dropping refinement is sound because a sum is read by
/// matching a variant, and bare common-field access on an unannotated variant field
/// is rejected. The required type may not demand a refinement the value lacks.
fn sum_assignable(program: &Program, have: &NominalType, want: &NominalType) -> bool {
    have.id == want.id
        && (have.id >= 0 || have.name() == want.name())
        && want.substitution.iter().all(|(key, wt)| {
            have.substitution
                .get(key)
                .is_some_and(|ht| types_compatible(program, ht, wt))
        })
}

/// Whether callable signature `have` can stand in for signature `want`.
pub fn signature_satisfies(
    program: &Program,
    have: &CallableSignature,
    want: &CallableSignature,
) -> bool {
    same_self_kind(&have.params, &want.params)
        && have.params.len() == want.params.len()
        && have
            .params
            .iter()
            .zip(&want.params)
            .all(|(h, w)| param_satisfies(program, h, w))
        && annotated_type_satisfies(
            program,
            have.ret.is_some(),
            have.ret_ty.as_ref(),
            want.ret.is_some(),
            want.ret_ty.as_ref(),
        )
}

fn same_self_kind(have: &[ParamInfo], want: &[ParamInfo]) -> bool {
    have.first().is_some_and(|p| p.name == "self") == want.first().is_some_and(|p| p.name == "self")
}

fn param_satisfies(program: &Program, have: &ParamInfo, want: &ParamInfo) -> bool {
    // Method parameters are invariant: accepting a narrower parameter than the
    // interface declares would let a caller pass a value the implementation
    // cannot handle.
    annotated_type_invariant(
        program,
        have.ty.is_some(),
        have.resolved_ty.as_ref(),
        want.ty.is_some(),
        want.resolved_ty.as_ref(),
    )
}

fn annotated_type_satisfies(
    program: &Program,
    have_annotation: bool,
    have: Option<&Type>,
    want_annotation: bool,
    want: Option<&Type>,
) -> bool {
    annotated_type_relates(
        have_annotation,
        have,
        want_annotation,
        want,
        |have, want| types_compatible(program, have, want),
    )
}

fn annotated_type_invariant(
    program: &Program,
    have_annotation: bool,
    have: Option<&Type>,
    want_annotation: bool,
    want: Option<&Type>,
) -> bool {
    annotated_type_relates(
        have_annotation,
        have,
        want_annotation,
        want,
        |have, want| types_invariant(program, have, want),
    )
}

/// Shared annotation-presence handling for member compatibility. An absent
/// annotation behaves as a fresh unknown and stays flexible; two present
/// annotations are compared with `relate` (assignable or invariant).
fn annotated_type_relates(
    have_annotation: bool,
    have: Option<&Type>,
    want_annotation: bool,
    want: Option<&Type>,
    relate: impl Fn(&Type, &Type) -> bool,
) -> bool {
    if !want_annotation && want.is_none() {
        return true;
    }
    if !have_annotation && have.is_none() {
        return true;
    }
    match (have, want) {
        (Some(have), Some(want)) => relate(have, want),
        (_, None) => true,
        (None, Some(want)) => want.is_unknown(),
    }
}

/// Check that record `sub` structurally satisfies record `sup`: `sub` has every
/// field and method `sup` requires, with invariant member types. Members come
/// from the type declaration for a named record and from the substitution for a
/// structural/anonymous record (`anonymous { .. }`, record literals). The
/// substitution -- not a `program.types` lookup by the shared placeholder name
/// `<structural>` -- is the source of truth for an anonymous structure's fields,
/// so it is checked field by field instead of slipping through as compatible with
/// everything. Returns the list of incompatible members.
pub fn record_satisfies(program: &Program, sub: &NominalType, sup: &NominalType) -> Vec<String> {
    let mut issues = record_satisfies_fields(program, sub, sup);
    // Only a named record declares methods; a structural record requires and
    // provides none.
    if let Some(want_methods) = declared_methods(program, sup) {
        let have_methods = declared_methods(program, sub);
        for (name, want) in want_methods {
            match have_methods.and_then(|m| m.get(name)) {
                None => issues.push(format!("method `{name}`")),
                Some(have) => {
                    if !signature_satisfies(program, &have.signature, &want.signature) {
                        issues.push(format!("method `{name}`"));
                    }
                }
            }
        }
    }
    if !issues.is_empty() {
        tracing::debug!(
            sub = sub.name(),
            sup = sup.name(),
            ?issues,
            "record does not structurally satisfy"
        );
    }
    issues
}

/// The FIELD half of [`record_satisfies`]: every field `sup` declares must be
/// present on `sub` with an invariant type. Structural method resolution on an
/// anonymous value uses this alone -- the value cannot carry methods, it is
/// borrowing the candidate type's.
pub fn record_satisfies_fields(
    program: &Program,
    sub: &NominalType,
    sup: &NominalType,
) -> Vec<String> {
    let mut issues = Vec::new();
    let have_fields = record_fields(program, sub);
    for want in record_fields(program, sup) {
        match have_fields.iter().find(|h| h.name == want.name) {
            None => issues.push(format!("field `{}`", want.name)),
            Some(have) => {
                // Fields are mutable, so they are invariant: a covariant field
                // would let writes through one alias install a value the other
                // alias's type forbids.
                if !annotated_type_invariant(
                    program,
                    have.annotated,
                    have.ty.as_ref(),
                    want.annotated,
                    want.ty.as_ref(),
                ) {
                    issues.push(format!("field `{}`", want.name));
                }
            }
        }
    }
    issues
}

/// A record field normalized for structural comparison: whether it carries a type
/// annotation and its resolved type when known. A declared-record field may be
/// unannotated (flexible); a structural-record field always carries a concrete
/// type taken from the substitution.
struct NormField {
    name: String,
    annotated: bool,
    ty: Option<Type>,
}

/// The fields of record nominal `nt`: from its substitution for a structural
/// record, otherwise from its declaration. Empty when `nt` is neither a declared
/// record nor structural (an unresolvable name), so no field is required of it.
fn record_fields(program: &Program, nt: &NominalType) -> Vec<NormField> {
    if nt.id == STRUCTURAL_RECORD_ID {
        return nt
            .substitution
            .iter()
            .map(|(name, ty)| NormField {
                name: name.to_string(),
                annotated: true,
                ty: Some(ty.clone()),
            })
            .collect();
    }
    match program.types.get(nt.name()).map(|info| &info.kind) {
        Some(TypeKind::Record { fields, .. }) => fields
            .iter()
            .map(|f| {
                // An unannotated declared field is flexible only until the
                // value's instantiation pins it: constructing `A { x: "s" }`
                // records `x=string` in the instance substitution (the
                // declaration's `resolved_ty` is only a shared inference
                // variable), and that concrete type -- not the missing
                // annotation -- is what a structural position must compare
                // against. Treating the field as annotation-free here would let
                // `A { x: "s" }` satisfy a required `{ x: int32 }` and corrupt
                // the unboxed layout.
                let instance = nt.substitution.get(&f.name).cloned();
                let annotated = f.ty.is_some() || instance.is_some();
                NormField {
                    name: f.name.clone(),
                    annotated,
                    ty: instance.or_else(|| f.resolved_ty.clone()),
                }
            })
            .collect(),
        _ => Vec::new(),
    }
}

/// The method table of a named record; `None` for a structural record or an
/// unresolvable name (neither declares methods).
fn declared_methods<'a>(
    program: &'a Program,
    nt: &NominalType,
) -> Option<&'a HashMap<String, MethodInfo>> {
    if nt.id == STRUCTURAL_RECORD_ID {
        return None;
    }
    match program.types.get(nt.name()).map(|info| &info.kind) {
        Some(TypeKind::Record { methods, .. }) => Some(methods),
        _ => None,
    }
}
