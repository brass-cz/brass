//! The inference solver facade.
//!
//! This wraps the persistent `Subst` with inference-variable classification
//! and snapshot/rollback for speculative unification. It is the single owner
//! of the checker's substitution so that resolving, unifying, probing
//! (non-committing assignability), and pinning a variable across uses all go
//! through one path. Variable *allocation* stays with the checker's counter
//! (kept above the ids HIR already assigned), so `record_var` registers a kind
//! for an externally minted id.

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use brass_hir::Type;

use crate::unify::{Snapshot, Subst};

/// Why an inference variable exists. The kind decides whether an unresolved
/// variable may stay open (a `Source` unknown, decided per instantiation) or
/// is a diagnostic when it reaches a required position. A variable minted
/// without a recorded kind counts as `Source`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum InferenceVarKind {
    /// A genuine source-level unknown (unannotated binding/parameter).
    Source,
    /// The element type of a bare empty-array literal `[]`. Unconstrained, it
    /// cannot satisfy a required position.
    EmptyArrayElem,
    /// The `Ok` payload of a function that only ever returns `error(...)`. Its
    /// type cannot be inferred, so it cannot satisfy a required position.
    ErrorOnlyOk,
    /// The `Ok` payload of an instantiation every live path of which returns
    /// an error and which cannot fall through: no value ever has this type,
    /// so reading it is rejected, and like `ErrorOnlyOk` it cannot satisfy a
    /// required position.
    UninhabitedOk,
}

/// The inference solver: a substitution, variable classification, and a fresh
/// variable counter.
#[derive(Clone)]
pub struct Solver {
    subst: Subst,
    var_kinds: HashMap<u32, InferenceVarKind>,
    next_var: u32,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            subst: Subst::new(),
            var_kinds: HashMap::default(),
            next_var: 0,
        }
    }

    /// Restore semantic state without replacing the publication consumer's mutation feed.
    pub fn restore_checkpoint(&mut self, checkpoint: Self) {
        self.subst.restore_checkpoint(checkpoint.subst);
        self.var_kinds = checkpoint.var_kinds;
        self.next_var = checkpoint.next_var;
    }

    /// Seed the fresh-variable counter above the ids HIR already minted, so
    /// `fresh` never collides with an externally assigned `Unknown` id.
    pub fn seed_var_counter(&mut self, next: u32) {
        self.next_var = self.next_var.max(next);
    }

    /// Allocate a fresh inference variable of the given kind.
    pub fn fresh(&mut self, kind: InferenceVarKind) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        self.var_kinds.insert(id, kind);
        Type::Unknown(id)
    }

    /// Register the kind of an externally allocated inference variable.
    pub fn record_var(&mut self, id: u32, kind: InferenceVarKind) {
        self.var_kinds.insert(id, kind);
        self.next_var = self.next_var.max(id + 1);
    }

    /// The kind recorded for variable `id`; `None` for a variable minted
    /// without one.
    pub fn kind_of(&self, id: u32) -> Option<InferenceVarKind> {
        self.var_kinds.get(&id).copied()
    }

    /// The inference variables free in `ty` under the current solution (bound
    /// variables are followed and excluded). Recurses into every type component,
    /// including a nominal type's generic substitution (e.g. `Result` payloads).
    pub fn free_vars(&self, ty: &Type) -> HashSet<u32> {
        let mut out = HashSet::default();
        self.collect_free(ty, &mut out);
        out
    }

    fn collect_free(&self, ty: &Type, out: &mut HashSet<u32>) {
        match self.subst.resolve(ty) {
            Type::Unknown(id) => {
                out.insert(id);
            }
            Type::Array(inner, _)
            | Type::Slice(inner)
            | Type::Nullable(inner)
            | Type::ConstOf(inner)
            | Type::Mut(inner)
            | Type::Ref(inner) => self.collect_free(&inner, out),
            Type::Fun(params, ret) => {
                params.iter().for_each(|p| self.collect_free(p, out));
                self.collect_free(&ret, out);
            }
            Type::Tuple(elems) => elems.iter().for_each(|t| self.collect_free(t, out)),
            Type::Record(n) | Type::Sum(n) => {
                n.substitution
                    .iter()
                    .for_each(|(_, t)| self.collect_free(t, out));
            }
            _ => {}
        }
    }

    /// Resolve a type through the substitution, recursing into components.
    pub fn resolve(&self, t: &Type) -> Type {
        self.subst.resolve_deep(t)
    }

    /// Resolve a value and every solution variable read, including bound aliases.
    pub fn resolve_with_dependencies(&self, t: &Type) -> (Type, Vec<u32>) {
        self.subst.resolve_with_dependencies(t)
    }

    /// Consume the mutation window for the single channel publication consumer.
    pub fn take_publication_changes(&self) -> crate::unify::PublicationChanges {
        self.subst.take_publication_changes()
    }

    /// Resolve without publication caches for differential verification.
    pub fn resolve_reference(&self, t: &Type) -> Type {
        self.subst.resolve_reference(t)
    }

    /// Resolve only the outer inference-variable chain, leaving components and
    /// nominal substitutions structurally unchanged.
    pub fn resolve_head(&self, t: &Type) -> Type {
        self.subst.resolve_head(t)
    }

    /// [`Self::resolve_head`] without copying the type (see
    /// `Subst::resolve_head_ref`).
    pub fn resolve_head_ref<'a>(&'a self, t: &'a Type) -> &'a Type {
        self.subst.resolve_head_ref(t)
    }

    /// Commit a unification into the persistent solution.
    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), String> {
        self.subst.unify(a, b)
    }

    /// Whether variable `id` occurs in `ty` under the current solution: binding
    /// `id` to `ty` would build an infinite type, which [`Solver::unify`]
    /// refuses. Lets a caller name that failure (a value applied to itself)
    /// instead of reporting a generic conflict.
    pub fn occurs(&self, id: u32, ty: &Type) -> bool {
        self.subst.occurs(id, ty)
    }

    /// Mark the current solution for a later [`Self::rollback`].
    pub fn snapshot(&self) -> Snapshot {
        self.subst.snapshot()
    }

    /// Undo every binding made since `snapshot`.
    pub fn rollback(&mut self, snapshot: Snapshot) {
        self.subst.rollback(snapshot);
    }

    /// Whether `a` and `b` can unify under the *current* solution, without
    /// committing any new bindings. Unlike unifying in a throwaway substitution,
    /// this respects variables already solved, then rolls back so the probe has
    /// no side effects.
    #[cfg(test)]
    pub fn can_unify(&mut self, a: &Type, b: &Type) -> bool {
        let snapshot = self.snapshot();
        let ok = self.subst.unify(a, b).is_ok();
        self.rollback(snapshot);
        ok
    }
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use brass_hir::{IntKind, Type};

    #[test]
    fn restoring_a_checkpoint_preserves_publication_and_variable_kinds() {
        let mut solver = Solver::new();
        solver.take_publication_changes();
        solver.record_var(7, InferenceVarKind::EmptyArrayElem);
        solver.unify(&Type::Unknown(5), &Type::Bool).unwrap();
        let checkpoint = solver.clone();
        solver.record_var(7, InferenceVarKind::Source);
        solver.unify(&Type::Unknown(7), &Type::Str).unwrap();
        solver.restore_checkpoint(checkpoint);
        assert_eq!(solver.resolve(&Type::Unknown(7)), Type::Unknown(7));
        assert_eq!(solver.kind_of(7), Some(InferenceVarKind::EmptyArrayElem));
        let changes = solver.take_publication_changes();
        assert_eq!(changes.variables, [5, 7].into_iter().collect());
        assert!(changes.epoch >= 3);
        solver.unify(&Type::Unknown(7), &Type::Bool).unwrap();
        assert_eq!(
            solver.take_publication_changes().variables,
            [7].into_iter().collect()
        );
    }

    #[test]
    fn rollback_undoes_speculative_bindings() {
        let mut solver = Solver::new();
        let var = Type::Unknown(0);
        let snap = solver.snapshot();
        solver.unify(&var, &Type::Int(IntKind::I32)).unwrap();
        assert_eq!(solver.resolve(&var), Type::Int(IntKind::I32));
        solver.rollback(snap);
        assert_eq!(solver.resolve(&var), var, "binding undone");
    }

    #[test]
    fn can_unify_does_not_commit() {
        let mut solver = Solver::new();
        let var = Type::Unknown(1);
        assert!(solver.can_unify(&var, &Type::Str));
        assert_eq!(solver.resolve(&var), var, "probe left no binding");
        // A committed binding then constrains a later probe.
        solver.unify(&var, &Type::Str).unwrap();
        assert!(solver.can_unify(&var, &Type::Str));
        assert!(
            !solver.can_unify(&var, &Type::Int(IntKind::I32)),
            "solved var respects its solution"
        );
    }

    #[test]
    fn var_kinds_are_recorded() {
        let mut solver = Solver::new();
        solver.record_var(7, InferenceVarKind::EmptyArrayElem);
        assert_eq!(solver.kind_of(7), Some(InferenceVarKind::EmptyArrayElem));
        assert_eq!(solver.kind_of(8), None);
    }
}
