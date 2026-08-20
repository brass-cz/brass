//! Structural subtyping: a record type S is usable where T is
//! required when S has every field and method of T with compatible types.
//! Sum types are nominal and excluded.

use fxhash::FxHashMap as HashMap;

use brass_hir::{
    CallableSignature, MethodInfo, NominalType, ParamInfo, PassingMode, Program,
    STRUCTURAL_RECORD_ID, Type, TypeKind, passing_modes_match, split_passing_mode,
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

/// Whether a value of type `subject` satisfies the type test `if v: pattern`.
///
/// The exact/wildcard core decides first (`brass_hir::type_test_matches`:
/// `infer` holes match anything, everything else representation-exact); what
/// the core refuses is then accepted when the value is USABLE where the
/// tested type is required per the language's subtyping
/// ([`types_compatible`]) -- a record that structurally satisfies the
/// pattern's fields and methods, a declared sum subtype flowing to its
/// parent, function subtyping. Conversions stay excluded: no numeric
/// widening and no `T` -> `T?` promotion, so `if v: int64` does not select
/// an `int32` value.
///
/// Subtype acceptance is sound here where blind structural flow would not
/// be, because a type test never reinterprets the value: the selected arm
/// keeps reading the subject at its OWN monomorphized type, and any flow of
/// the subject inside the arm goes through the ordinary checked flow sites
/// (which insert their views/rebuilds as usual).
///
/// This is THE deciding predicate for type tests: the checker's arm
/// selection and the back ends' branch folding both call it, so the checked
/// arm and the compiled arm always agree.
pub fn type_test_accepts(program: &Program, pattern: &Type, subject: &Type) -> bool {
    brass_hir::type_test_matches(pattern, subject) || types_compatible(program, subject, pattern)
}

/// Whether a value of `have` can be used where `want` is required.
pub fn types_compatible(program: &Program, have: &Type, want: &Type) -> bool {
    // Two instances of the SAME `Result` declaration compare by payloads; an
    // instance without payload entries constrains nothing. Different
    // declarations (a module's shadow vs the prelude's, or a declared
    // subtype) fall through to the sum rules below.
    if let (Type::Sum(h), Type::Sum(w)) = (have, want)
        && h.is_result_type()
        && w.is_result_type()
        && h.id == w.id
    {
        if let (Some((h_ok, h_err)), Some((w_ok, w_err))) =
            (h.result_payloads(), w.result_payloads())
        {
            return types_compatible(program, h_ok, w_ok)
                && types_compatible(program, h_err, w_err);
        }
        return true;
    }
    if drops_fixed_length_through_mutable_reference(have, want) {
        return false;
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
                .all(|(h, w)| function_part_compatible(program, w, h))
                && function_part_compatible(program, hr, wr)
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
        // A NON-record value can still satisfy a PROTOCOL record -- one whose
        // every member is function-typed -- when each member is provided by a
        // method: the built-in `debug` (every type renders itself, so any
        // value satisfies `Debug`) or a core primitive method (`1` and `"a"`
        // satisfy `Display` through `int32.display`/`string.display`).
        (have, Type::Record(sup)) if !matches!(have, Type::Record(_)) => {
            protocol_satisfied_by_methods(program, have, sup)
        }
        _ => have == want,
    }
}

/// Whether every member the protocol record `sup` requires is function-typed
/// and provided on `have` by a method ([`member_provided_by_method`]). A
/// record with any stored data field is not a protocol a non-record value can
/// satisfy, and an empty record constrains nothing but is not satisfied
/// either (a memberless annotation should not accept every scalar).
fn protocol_satisfied_by_methods(program: &Program, have: &Type, sup: &NominalType) -> bool {
    let fields = record_fields(program, sup);
    let methods = declared_methods(program, sup);
    let member_count = fields.len() + methods.map_or(0, |m| m.len());
    if member_count == 0 {
        return false;
    }
    fields.iter().all(|f| {
        f.ty.as_ref()
            .is_some_and(|w| member_provided_by_method(program, have, &f.name, w))
    }) && methods.is_none_or(|methods| {
        methods.iter().all(|(name, m)| {
            let params: Vec<Type> = m
                .signature
                .params
                .iter()
                .map(|p| p.resolved_ty.clone().unwrap_or(Type::Void))
                .collect();
            let ret = m
                .signature
                .ret_ty
                .clone()
                .unwrap_or(Type::Unknown(u32::MAX));
            member_provided_by_method(program, have, name, &Type::Fun(params, Box::new(ret)))
        })
    })
}

/// Whether a FUNCTION-typed interface member (`debug: (Self) -> string` on a
/// protocol record, its first parameter the receiver) is provided on `have`
/// by a METHOD rather than a stored field:
/// - the built-in `debug` -- every type renders itself, so a one-parameter
///   `debug` returning `string` is always satisfied;
/// - a method the nominal declares, with contravariantly compatible parameters
///   (including matching passing modes) and a compatible return;
/// - a core primitive/array method on `have`'s class (`fun string.display`).
pub fn member_provided_by_method(program: &Program, have: &Type, name: &str, want: &Type) -> bool {
    let Type::Fun(params, ret) = want else {
        return false;
    };
    // A nullable narrows before any method call, and a closure has no
    // rendering; neither carries the built-in `debug`.
    let debuggable = !matches!(
        have,
        Type::Nullable(_) | Type::Void | Type::Never | Type::Fun(..)
    );
    if name == "debug"
        && debuggable
        && params.len() == 1
        && matches!(**ret, Type::Str | Type::Unknown(_))
    {
        return true;
    }
    let params: Vec<Type> = params
        .iter()
        .map(|param| substitute_member_self(param, have))
        .collect();
    let ret = substitute_member_self(ret, have);
    let ret_compatible = |have_annotated: bool, have_ret: Option<&Type>| {
        let have_ret = have_ret.map(|ty| substitute_member_self(ty, have));
        annotated_type_satisfies(program, have_annotated, have_ret.as_ref(), true, Some(&ret))
    };
    let params_compatible = |have_params: &[ParamInfo]| {
        have_params.len() == params.len()
            && have_params
                .iter()
                .zip(&params)
                .all(|(have_param, want_param)| {
                    have_param.resolved_ty.as_ref().is_none_or(|have_param| {
                        let have_param = substitute_member_self(have_param, have);
                        // A provider must accept every value admitted by the
                        // protocol member, so parameter assignability is reversed.
                        // `function_part_compatible` also keeps the caller-visible
                        // passing convention invariant.
                        function_part_compatible(program, want_param, &have_param)
                    })
                })
    };
    if let Type::Record(n) | Type::Sum(n) = have
        && let Some(info) = program.type_by_id(n.id)
    {
        let found = match &info.kind {
            TypeKind::Record { methods, .. } => methods.get(name),
            TypeKind::Sum { variants } => variants.iter().find_map(|v| v.methods.get(name)),
        };
        if let Some(m) = found {
            return params_compatible(&m.signature.params)
                && ret_compatible(m.signature.ret.is_some(), m.signature.ret_ty.as_ref());
        }
    }
    if let Some(class) = have.primitive_class()
        && let Some(sym) = program
            .primitive_methods
            .get(&(class.to_string(), name.to_string()))
        && let Some(f) = program.functions.get(sym)
    {
        return params_compatible(&f.signature.params)
            && ret_compatible(f.signature.ret.is_some(), f.signature.ret_ty.as_ref());
    }
    false
}

/// Replace the protocol declaration's abstract `Self` with the concrete type
/// whose method is being considered. The replacement applies recursively so a
/// receiver nested in another function or container has the same meaning as a
/// top-level receiver parameter.
fn substitute_member_self(ty: &Type, replacement: &Type) -> Type {
    let substitute = |ty| substitute_member_self(ty, replacement);
    match ty {
        Type::SelfType => replacement.clone(),
        Type::Array(element, len) => Type::Array(Box::new(substitute(element)), *len),
        Type::Slice(element) => Type::Slice(Box::new(substitute(element))),
        Type::Tuple(elements) => Type::Tuple(elements.iter().map(substitute).collect()),
        Type::Fun(params, ret) => Type::Fun(
            params.iter().map(substitute).collect(),
            Box::new(substitute(ret)),
        ),
        Type::Nullable(inner) => Type::Nullable(Box::new(substitute(inner))),
        Type::ConstOf(inner) => Type::ConstOf(Box::new(substitute(inner))),
        Type::Mut(inner) => Type::Mut(Box::new(substitute(inner))),
        Type::Ref(inner) => Type::Ref(Box::new(substitute(inner))),
        other => other.clone(),
    }
}

/// Function subtyping may reverse the value-type direction of a parameter, but
/// it never changes how that parameter or result aliases caller-owned state.
pub fn function_part_compatible(program: &Program, have: &Type, want: &Type) -> bool {
    if !passing_modes_match(have, want) {
        return false;
    }
    let (_, have) = split_passing_mode(have);
    let (_, want) = split_passing_mode(want);
    types_compatible(program, have, want)
}

fn drops_fixed_length_through_mutable_reference(have: &Type, want: &Type) -> bool {
    let (want_mode, want_value) = split_passing_mode(want);
    if want_mode != PassingMode::MutableReference {
        return false;
    }
    let (_, have_value) = split_passing_mode(have);
    matches!(have_value, Type::Array(..)) && matches!(want_value, Type::Slice(_))
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
            None => false,
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
    if have.id == want.id {
        // A pinned payload slot is storage read back at the required side's
        // type with no coercion site (same-id flow inserts no rebuild), so it
        // is invariant like a record field: accepting `S<A.v=Child>` where
        // `S<A.v=Parent>` is required would read the child's layout as the
        // parent's. Unknowns stay flexible through `types_invariant`.
        return (have.id >= 0 || have.name() == want.name())
            && want.substitution.iter().all(|(key, wt)| {
                have.substitution
                    .get(key)
                    .is_some_and(|ht| types_invariant(program, ht, wt))
            });
    }
    declared_sum_subtype(program, have, want)
}

/// Whether sum `have` declares (transitively) `want`'s sum as a parent
/// (`type Child: Parent = | ..`) with a compatible instantiation. The
/// variant-set/field conformance itself is enforced once at the declaration
/// (interface checking); here the instances must agree on every payload slot
/// the required side fixes -- pinned in `want`'s substitution or annotated on
/// the parent declaration itself. The rebuild the back ends insert (SumView)
/// copies the value's payload into a slot read at the required side's type
/// with no nested coercion, so a slot fixed on both sides is invariant; a
/// slot the required side leaves open takes the value's refinement instead.
/// The declaration is the gate: undeclared same-shaped sums stay unrelated.
fn declared_sum_subtype(program: &Program, have: &NominalType, want: &NominalType) -> bool {
    if !declares_sum_parent(program, have.id, want.id, 0) {
        return false;
    }
    let Some(TypeKind::Sum { variants }) = program.type_by_id(want.id).map(|info| &info.kind)
    else {
        return false;
    };
    // Slots the parent declaration annotates constrain the value even when the
    // required instance does not pin them (an annotated field never enters the
    // substitution), so walk the declared fields alongside the substitution.
    let declared_slots = variants.iter().flat_map(|v| {
        v.fields.iter().filter_map(|f| {
            let ty = f.resolved_ty.clone().filter(|t| !t.is_unknown())?;
            Some((format!("{}.{}", v.name, f.name), ty))
        })
    });
    let pinned_slots = want
        .substitution
        .iter()
        .map(|(key, ty)| (key.to_string(), ty.clone()));
    pinned_slots.chain(declared_slots).all(|(key, wt)| {
        match sum_field_payload(program, have, &key) {
            Some(ht) => types_invariant(program, &ht, &wt),
            None => wt.is_unknown(),
        }
    })
}

/// The value-side type a sum instance carries for a `"Variant.field"` slot:
/// its substitution entry (an unannotated field recorded at construction) or
/// the declaration's annotated field type. `None` when neither is known.
pub fn sum_field_payload(program: &Program, n: &NominalType, key: &str) -> Option<Type> {
    if let Some(t) = n.substitution.get(key)
        && !t.is_unknown()
    {
        return Some(t.clone());
    }
    let (vname, fname) = key.split_once('.')?;
    let info = program.type_by_id(n.id)?;
    let TypeKind::Sum { variants } = &info.kind else {
        return None;
    };
    variants
        .iter()
        .find(|v| v.name == vname)?
        .fields
        .iter()
        .find(|f| f.name == fname)?
        .resolved_ty
        .clone()
        .filter(|t| !t.is_unknown())
}

/// Whether the sum with id `child` names (transitively) the sum with id
/// `parent` in its declared interface list. Parents resolve by their bare
/// table symbol, like interface checking does; the depth cap only guards a
/// (rejected elsewhere) declaration cycle.
pub fn declares_sum_parent(program: &Program, child: i32, parent: i32, depth: u8) -> bool {
    if depth > 8 || child == parent {
        return false;
    }
    let Some(info) = program.type_by_id(child) else {
        return false;
    };
    info.interfaces.iter().any(|name| {
        program.types.get(name).is_some_and(|p| {
            matches!(p.kind, TypeKind::Sum { .. })
                && (p.id == parent || declares_sum_parent(program, p.id, parent, depth + 1))
        })
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
    let mut issues = satisfies_fields(program, sub, sup, true);
    // Only a named record declares methods; a structural record requires and
    // provides none. A required method named `debug` with a receiver-only
    // signature is the built-in renderer, satisfied by every type.
    if let Some(want_methods) = declared_methods(program, sup) {
        let have_methods = declared_methods(program, sub);
        for (name, want) in want_methods {
            match have_methods.and_then(|m| m.get(name)) {
                None if name == "debug" && want.signature.params.len() == 1 => {}
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
    satisfies_fields(program, sub, sup, false)
}

/// [`record_satisfies_fields`] with the protocol-member fallback: when
/// `method_fallback` is set, a field `sub` lacks is still satisfied if it is
/// function-typed and provided by a METHOD ([`member_provided_by_method`]) --
/// the built-in `debug`, a declared method, or a primitive method. The
/// anonymous-value method-resolution path keeps the strict field-only check
/// (a structural value borrows the candidate's methods, so a candidate's
/// protocol field must not select it).
fn satisfies_fields(
    program: &Program,
    sub: &NominalType,
    sup: &NominalType,
    method_fallback: bool,
) -> Vec<String> {
    let mut issues = Vec::new();
    let have_ty = Type::Record(sub.clone());
    let have_fields = record_fields(program, sub);
    for want in record_fields(program, sup) {
        match have_fields.iter().find(|h| h.name == want.name) {
            None => {
                let provided = method_fallback
                    && want.ty.as_ref().is_some_and(|w| {
                        member_provided_by_method(program, &have_ty, &want.name, w)
                    });
                if !provided {
                    issues.push(format!("field `{}`", want.name));
                }
            }
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
    match program.type_by_id(nt.id).map(|info| &info.kind) {
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
    match program.type_by_id(nt.id).map(|info| &info.kind) {
        Some(TypeKind::Record { methods, .. }) => Some(methods),
        _ => None,
    }
}
