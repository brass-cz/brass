//! Value-flow leniency for the unification-based checks: the nullable
//! stripping a flow applies before unifying, the non-committing flow probe
//! the infer pass's assignability checks rest on, and which requirements
//! shape a construction flowing into them.

use brass_hir::Type;
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

/// Whether a requirement of type `want` shapes a construction flowing into it
/// -- an anonymous record literal built as a declared record, a bracket
/// literal taking an array or tuple shape, a closure taking a function type's
/// parameters -- so a branching expression (`if`/`match`) in that position
/// passes it on to its branch values. Numeric and other scalar requirements
/// do not: branch values join by their own rule and the join then flows.
pub fn shapes_constructions(want: &Type) -> bool {
    match brass_hir::peel_modes(want) {
        Type::Nullable(inner) => shapes_constructions(inner),
        Type::Record(_)
        | Type::Sum(_)
        | Type::Tuple(_)
        | Type::Slice(_)
        | Type::Array(..)
        | Type::Fun(..) => true,
        _ => false,
    }
}

/// Non-committing probe of a value flow: whether the two sides unify once
/// both are resolved and a top-level nullable is stripped from each (see
/// [`strip_nullable`]), with every binding rolled back even on success. This
/// is the acceptance core of the infer pass's assignability checks, which
/// probe one polymorphic value against many positions and must not pin it (a
/// store that should constrain the value commits separately).
///
/// Array-like types are NOT reconciled by element: assignability guards
/// storage whose element layout is exact -- a `T?[]` is cell storage that a
/// `T[]` requirement must not accept -- so elements have to unify as written.
pub fn flow_probe(solver: &mut Solver, a: &Type, b: &Type) -> bool {
    let a = strip_nullable(solver.resolve(a));
    let b = strip_nullable(solver.resolve(b));
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

    /// The probe strips a top-level nullable but never commits: it accepts a
    /// `T` against a `T?` requirement, and a success against an open variable
    /// leaves that variable unbound afterwards.
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
    /// storage layouts).
    #[test]
    fn probe_does_not_reconcile_array_elements() {
        let mut solver = Solver::new();
        let int = Type::Int(IntKind::I32);
        let nullable_elems = Type::Slice(Box::new(Type::Nullable(Box::new(int.clone()))));
        let plain_elems = Type::Slice(Box::new(int));
        assert!(!flow_probe(&mut solver, &nullable_elems, &plain_elems));
    }
}
