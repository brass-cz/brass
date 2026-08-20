//! Value-flow unification leniency, shared by every unification-based pass
//! (the HM checker and the JIT-time MIR checker) so a flow the front end
//! accepted is never re-rejected later in the pipeline.

use brass_hir::{Type, index_element};
use brass_solver::solver::Solver;

/// A nullable's element type (one level), else the type unchanged. Value flow
/// treats `T` and `T?` as compatible: a `T` flows into a `T?` by promotion and
/// a guarded `T?` into a `T` by narrowing. Deeper null-safety is the flow
/// checker's concern, not unification's.
pub fn strip_nullable(ty: Type) -> Type {
    match ty {
        Type::Nullable(inner) => *inner,
        other => other,
    }
}

/// The two sides of a value flow, resolved and with a top-level nullable
/// stripped from each: the normalization every flow entry point applies
/// before unifying, factored so the committing ([`flow_unify`]) and probing
/// ([`flow_probe`]) forms cannot drift.
fn flow_sides(solver: &Solver, a: &Type, b: &Type) -> (Type, Type) {
    (
        strip_nullable(solver.resolve(a)),
        strip_nullable(solver.resolve(b)),
    )
}

/// Whether indexing reaches a growable slice through the same passing-mode
/// wrappers that [`index_element`] sees through.
fn is_slice_indexable(ty: &Type) -> bool {
    match ty {
        Type::Slice(_) => true,
        Type::Ref(inner) | Type::Mut(inner) | Type::ConstOf(inner) => is_slice_indexable(inner),
        _ => false,
    }
}

/// Unify with Brass's value-flow leniency, returning whether it succeeded.
/// A top-level nullable is stripped from each side (see [`strip_nullable`]),
/// and a slice reconciles with another indexable type by element type -- a
/// `[1,2,3]` literal inferred as a slice matches an `int32[3]` annotation,
/// seen through `ref`/`mut`/`const` wrappers the same way indexing is. Two
/// fixed arrays retain their lengths as part of unification.
///
/// Succeeding commits the unification's bindings; failing commits nothing (the
/// attempt is rolled back), so a caller can try further fallbacks -- numeric
/// conversion, structural subtyping -- against unpolluted state.
pub fn flow_unify(solver: &mut Solver, a: &Type, b: &Type) -> bool {
    let (a, b) = flow_sides(solver, a, b);
    if (is_slice_indexable(&a) || is_slice_indexable(&b))
        && let (Some(x), Some(y)) = (index_element(&a), index_element(&b))
    {
        return flow_unify(solver, &x, &y);
    }
    let snapshot = solver.snapshot();
    if solver.unify(&a, &b).is_ok() {
        return true;
    }
    solver.rollback(snapshot);
    false
}

/// Non-committing probe of the nullable-stripping unification at the core of
/// [`flow_unify`]: whether the two sides unify once a top-level nullable is
/// stripped from each, with every binding rolled back even on success. This
/// is the acceptance core of the infer pass's assignability checks, which
/// probe one polymorphic value against many positions and must not pin it (a
/// store that should constrain the value commits separately).
///
/// Unlike [`flow_unify`] this does NOT reconcile array-like types by element:
/// assignability guards storage whose element layout is exact -- a `T?[]` is
/// cell storage that a `T[]` requirement must not accept -- so elements have
/// to unify as written.
pub fn flow_probe(solver: &mut Solver, a: &Type, b: &Type) -> bool {
    let (a, b) = flow_sides(solver, a, b);
    let snapshot = solver.snapshot();
    let ok = solver.unify(&a, &b).is_ok();
    solver.rollback(snapshot);
    ok
}

#[cfg(test)]
mod tests {
    use super::*;
    use brass_hir::IntKind;
    use brass_solver::solver::InferenceVarKind;

    /// A nullable reconciles with its element, and array-likes reconcile by
    /// element type even under a reference wrapper (the indexing rule).
    #[test]
    fn nullable_and_wrapped_arrays_reconcile() {
        let mut solver = Solver::new();
        let int = Type::Int(IntKind::I32);
        assert!(flow_unify(
            &mut solver,
            &Type::Nullable(Box::new(int.clone())),
            &int
        ));
        let arr = Type::Slice(Box::new(int.clone()));
        let fixed = Type::Array(Box::new(int.clone()), 3);
        assert!(flow_unify(
            &mut solver,
            &Type::Ref(Box::new(arr)),
            &Type::Ref(Box::new(fixed))
        ));
    }

    /// Fixed-array lengths are part of their storage type; element-only
    /// reconciliation is reserved for flows where one side is a slice.
    #[test]
    fn fixed_arrays_require_equal_lengths() {
        let mut solver = Solver::new();
        let int = Type::Int(IntKind::I32);
        assert!(!flow_unify(
            &mut solver,
            &Type::Array(Box::new(int.clone()), 3),
            &Type::Array(Box::new(int.clone()), 4),
        ));
        assert!(flow_unify(
            &mut solver,
            &Type::Slice(Box::new(int.clone())),
            &Type::Array(Box::new(int), 4),
        ));
    }

    /// The probe shares the nullable-stripping core but never commits: it
    /// accepts a `T` against a `T?` requirement, and a success against an
    /// open variable leaves that variable unbound afterwards.
    #[test]
    fn probe_strips_nullable_and_commits_nothing() {
        let mut solver = Solver::new();
        let int = Type::Int(IntKind::I32);
        assert!(flow_probe(
            &mut solver,
            &int,
            &Type::Nullable(Box::new(int.clone()))
        ));
        let v = solver.fresh(InferenceVarKind::Source);
        assert!(flow_probe(&mut solver, &int, &v));
        assert!(
            solver.resolve(&v).is_unknown(),
            "a successful probe leaked a binding: {:?}",
            solver.resolve(&v)
        );
    }

    /// The probe keeps array elements exact: a nullable-element slice must not
    /// pass where a plain-element slice is required (the two have different
    /// storage layouts), even though the committing form's element
    /// reconciliation would strip the nullable per level.
    #[test]
    fn probe_does_not_reconcile_array_elements() {
        let mut solver = Solver::new();
        let int = Type::Int(IntKind::I32);
        let nullable_elems = Type::Slice(Box::new(Type::Nullable(Box::new(int.clone()))));
        let plain_elems = Type::Slice(Box::new(int));
        assert!(!flow_probe(&mut solver, &nullable_elems, &plain_elems));
    }

    /// A failed flow unification must commit nothing: the variable bound while
    /// the attempt was in flight is unbound again afterwards, so a caller's
    /// fallback (numeric conversion, structural subtyping) sees clean state.
    #[test]
    fn failed_unification_commits_no_bindings() {
        let mut solver = Solver::new();
        let v = solver.fresh(InferenceVarKind::Source);
        // [v, string] vs [int32, bool]: v binds to int32 first, then the
        // string/bool element fails the whole unification.
        let a = Type::Tuple(vec![v.clone(), Type::Str]);
        let b = Type::Tuple(vec![Type::Int(IntKind::I32), Type::Bool]);
        assert!(!flow_unify(&mut solver, &a, &b));
        assert!(
            solver.resolve(&v).is_unknown(),
            "failed flow_unify leaked a partial binding: {:?}",
            solver.resolve(&v)
        );
    }
}
