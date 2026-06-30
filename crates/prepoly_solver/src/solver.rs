//! The inference solver facade.
//!
//! This wraps the persistent `Subst` with stable inference-variable identity and
//! classification, snapshot/rollback for speculative unification, and a place to
//! accumulate deferred constraints. It is the single owner of the substitution
//! so that resolving, unifying, probing (non-committing assignability), and
//! pinning a variable across uses all go through one path. Variable *allocation*
//! stays with the checker's counter (kept in sync with the ids HIR already
//! assigned), so `record_var` registers a kind for an externally minted id.

use std::collections::{HashMap, HashSet};

use prepoly_hir::{NominalType, Substitution, Type};

use crate::unify::{Snapshot, Subst};

/// Stable identity of an inference variable. Wraps the `Type::Unknown(u32)` id
/// that flows through HIR so the solver can attach a kind without changing the
/// external representation.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct InferenceVarId(pub u32);

/// Why an inference variable exists. The kind decides whether an unresolved
/// variable is a legal deferred contract or a diagnostic at a required position
/// for the inference pipeline.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum InferenceVarKind {
    /// A genuine source-level unknown (unannotated binding/parameter).
    Source,
    /// A fresh variable minted while instantiating a scheme at a call site.
    Instantiation,
    /// The element type of a bare empty-array literal `[]`. Unconstrained, it
    /// cannot satisfy a required position.
    EmptyArrayElem,
    /// The `Ok` payload of a function that only ever returns `error(...)`. Its
    /// type cannot be inferred, so it cannot satisfy a required position.
    ErrorOnlyOk,
    /// A placeholder created after an earlier diagnostic, to avoid cascades.
    Invalid,
}

/// Deferred constraints accumulated during checking. Equalities are applied
/// eagerly through `Solver::unify`; the other buckets reserve space for the
/// structural/numeric/result constraints the checker records elsewhere today and
/// that future migration will route here.
#[derive(Default)]
pub struct ConstraintSet {
    pub equalities: Vec<(Type, Type)>,
}

/// A polymorphic type scheme `forall vars. ty` -- the HM let-generalized type of
/// a binding. The quantified `vars` are instantiated to fresh variables at each
/// use, which is what lets `let id = (x) -> x` be applied at many argument types
/// in one program without the first use pinning the rest.
#[derive(Clone, Debug)]
pub struct Scheme {
    pub vars: Vec<u32>,
    pub ty: Type,
}

impl Scheme {
    /// A monomorphic scheme: the type as-is, nothing quantified.
    pub fn mono(ty: Type) -> Self {
        Self {
            vars: Vec::new(),
            ty,
        }
    }
}

/// The inference solver: a substitution, variable classification, and a fresh
/// variable counter. Owns generalization/instantiation so let-polymorphism goes
/// through the same substitution as unification.
pub struct Solver {
    subst: Subst,
    var_kinds: HashMap<u32, InferenceVarKind>,
    next_var: u32,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            subst: Subst::new(),
            var_kinds: HashMap::new(),
            next_var: 0,
        }
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

    pub fn kind_of(&self, id: u32) -> Option<InferenceVarKind> {
        self.var_kinds.get(&id).copied()
    }

    /// The inference variables free in `ty` under the current solution (bound
    /// variables are followed and excluded). Recurses into every type component,
    /// including a nominal type's generic substitution (e.g. `Result` payloads).
    pub fn free_vars(&self, ty: &Type) -> HashSet<u32> {
        let mut out = HashSet::new();
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

    /// Generalize `ty` into a scheme by quantifying every variable free in it but
    /// not free in the surrounding environment (`env_free`). The HM `let` rule:
    /// variables still constrained by something in scope stay monomorphic.
    pub fn generalize(&self, env_free: &HashSet<u32>, ty: &Type) -> Scheme {
        let resolved = self.resolve(ty);
        let mut vars: Vec<u32> = self
            .free_vars(&resolved)
            .into_iter()
            .filter(|v| !env_free.contains(v))
            .collect();
        vars.sort_unstable();
        tracing::debug!(ty = %resolved.display(), quantified = ?vars, "generalize");
        Scheme { vars, ty: resolved }
    }

    /// Instantiate a scheme: replace each quantified variable with a fresh one,
    /// so distinct uses of a polymorphic binding get independent types.
    pub fn instantiate(&mut self, scheme: &Scheme) -> Type {
        if scheme.vars.is_empty() {
            return self.resolve(&scheme.ty);
        }
        let mapping: HashMap<u32, Type> = scheme
            .vars
            .iter()
            .map(|&v| (v, self.fresh(InferenceVarKind::Instantiation)))
            .collect();
        let instance = apply_var_map(&scheme.ty, &mapping);
        tracing::debug!(scheme = %scheme.ty.display(), instance = %instance.display(), "instantiate");
        instance
    }

    /// Resolve a type through the substitution, recursing into components.
    pub fn resolve(&self, t: &Type) -> Type {
        self.subst.resolve_deep(t)
    }

    /// Commit a unification into the persistent solution.
    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), String> {
        self.subst.unify(a, b)
    }

    pub fn snapshot(&self) -> Snapshot {
        self.subst.snapshot()
    }

    pub fn rollback(&mut self, snapshot: Snapshot) {
        self.subst.rollback(snapshot);
    }

    /// Whether `a` and `b` can unify under the *current* solution, without
    /// committing any new bindings. Unlike unifying in a throwaway substitution,
    /// this respects variables already solved, then rolls back so the probe has
    /// no side effects (`can_assign` for diagnostics).
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

/// Replace each `Unknown(id)` listed in `map` with its mapped type, recursing
/// through every type component (including nominal generic substitutions). Used
/// by scheme instantiation; ids not in `map` are left untouched.
fn apply_var_map(ty: &Type, map: &HashMap<u32, Type>) -> Type {
    match ty {
        Type::Unknown(id) => map.get(id).cloned().unwrap_or_else(|| ty.clone()),
        Type::Array(inner, n) => Type::Array(Box::new(apply_var_map(inner, map)), *n),
        Type::Slice(inner) => Type::Slice(Box::new(apply_var_map(inner, map))),
        Type::Nullable(inner) => Type::Nullable(Box::new(apply_var_map(inner, map))),
        Type::ConstOf(inner) => Type::ConstOf(Box::new(apply_var_map(inner, map))),
        Type::Mut(inner) => Type::Mut(Box::new(apply_var_map(inner, map))),
        Type::Ref(inner) => Type::Ref(Box::new(apply_var_map(inner, map))),
        Type::Fun(params, ret) => Type::Fun(
            params.iter().map(|p| apply_var_map(p, map)).collect(),
            Box::new(apply_var_map(ret, map)),
        ),
        Type::Tuple(elems) => Type::Tuple(elems.iter().map(|t| apply_var_map(t, map)).collect()),
        Type::Record(n) => Type::Record(map_nominal(n, map)),
        Type::Sum(n) => Type::Sum(map_nominal(n, map)),
        other => other.clone(),
    }
}

fn map_nominal(n: &NominalType, map: &HashMap<u32, Type>) -> NominalType {
    let mut sub = Substitution::empty();
    for (key, t) in n.substitution.iter() {
        sub.insert(key, apply_var_map(t, map));
    }
    NominalType::with_substitution(n.id, n.name.clone(), sub)
}

#[cfg(test)]
mod tests {
    use super::*;
    use prepoly_hir::{IntKind, Type};

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

    #[test]
    fn generalize_then_instantiate_gives_independent_uses() {
        // The crux of HM let-polymorphism: a generalized `(x) -> x` instantiated
        // twice yields two independent argument types, so one use at `int32` does
        // not force the other to `int32`.
        let mut solver = Solver::new();
        let v = solver.fresh(InferenceVarKind::Source);
        let id_ty = Type::Fun(vec![v.clone()], Box::new(v.clone()));
        let scheme = solver.generalize(&HashSet::new(), &id_ty);
        assert_eq!(scheme.vars.len(), 1, "the one free var is generalized");

        let Type::Fun(p1, r1) = solver.instantiate(&scheme) else {
            panic!("function type");
        };
        let Type::Fun(p2, _) = solver.instantiate(&scheme) else {
            panic!("function type");
        };
        // First use at int32; return follows the argument.
        solver.unify(&p1[0], &Type::Int(IntKind::I32)).unwrap();
        assert_eq!(solver.resolve(&r1), Type::Int(IntKind::I32));
        // Second use at string is unaffected by the first.
        assert!(
            solver.can_unify(&p2[0], &Type::Str),
            "second instantiation is independent of the first"
        );
    }

    #[test]
    fn monomorphic_var_in_env_is_not_generalized() {
        // A variable still free in the environment must stay monomorphic (it is
        // shared with an outer binding), so it is not quantified.
        let mut solver = Solver::new();
        let shared = solver.fresh(InferenceVarKind::Source);
        let ty = Type::Fun(vec![shared.clone()], Box::new(shared.clone()));
        let env_free = solver.free_vars(&shared); // `shared` is in scope
        let scheme = solver.generalize(&env_free, &ty);
        assert!(
            scheme.vars.is_empty(),
            "env-bound variable is not generalized"
        );
        // So instantiating reuses the same variable; pinning it once pins all.
        let inst = solver.instantiate(&scheme);
        let Type::Fun(p, _) = inst else {
            panic!("function type")
        };
        solver.unify(&p[0], &Type::Bool).unwrap();
        assert_eq!(solver.resolve(&shared), Type::Bool);
    }

    #[test]
    fn instantiate_recurses_into_result_payloads() {
        // A generalized `Result<T, string>` instantiates its `Ok` payload var.
        let mut solver = Solver::new();
        let t = solver.fresh(InferenceVarKind::Source);
        let res = Type::result(t.clone(), Type::Str);
        let scheme = solver.generalize(&HashSet::new(), &res);
        assert_eq!(scheme.vars.len(), 1);
        let inst = solver.instantiate(&scheme);
        let (ok, err) = match &inst {
            Type::Sum(n) => n.result_payloads().expect("result payloads"),
            _ => panic!("result type"),
        };
        assert!(matches!(ok, Type::Unknown(_)), "Ok payload is a fresh var");
        assert_eq!(*err, Type::Str, "Err payload preserved");
        // The fresh Ok var is independent: unify it freely.
        solver.unify(ok, &Type::Int(IntKind::I32)).unwrap();
    }
}
