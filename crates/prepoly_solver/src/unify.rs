//! Unification over `Type` with a substitution for `Unknown` variables
//! (DESIGN.md 5.7 Phase 4). Records use structural compatibility; sum types are
//! nominal.

use std::collections::HashMap;

use prepoly_hir::Type;

#[derive(Default)]
pub struct Subst {
    table: HashMap<u32, Type>,
    /// Keys inserted in order, so a snapshot can be rolled back. Every variable
    /// is bound at most once (unify resolves before binding), so undoing a
    /// binding is just removing the key.
    trail: Vec<u32>,
}

/// An opaque marker for the substitution state, used to roll back speculative
/// unifications (e.g. a non-committing assignability probe). DESIGN.md 5.7.
#[derive(Clone, Copy)]
pub struct Snapshot(usize);

impl Subst {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record the current substitution state for a later `rollback`.
    pub fn snapshot(&self) -> Snapshot {
        Snapshot(self.trail.len())
    }

    /// Undo every binding made since `snapshot`, restoring the prior state.
    pub fn rollback(&mut self, snapshot: Snapshot) {
        while self.trail.len() > snapshot.0 {
            if let Some(id) = self.trail.pop() {
                self.table.remove(&id);
            }
        }
    }

    /// Follow substitutions to a representative type.
    pub fn resolve(&self, t: &Type) -> Type {
        match t {
            Type::Unknown(id) => match self.table.get(id) {
                Some(bound) => self.resolve(bound),
                None => t.clone(),
            },
            _ => t.clone(),
        }
    }

    /// Resolve a type and recurse into its components so that nested inference
    /// variables are substituted too. Used when instantiating a polymorphic
    /// closure call: the argument types are unified into the parameter
    /// variables, then the closure's return type is resolved through this
    /// substitution to recover the concrete result type (e.g. `(x) -> x`
    /// applied to an `int32` yields `int32`, not an unconstrained unknown).
    pub fn resolve_deep(&self, t: &Type) -> Type {
        match self.resolve(t) {
            Type::Array(inner, n) => Type::Array(Box::new(self.resolve_deep(&inner)), n),
            Type::Slice(inner) => Type::Slice(Box::new(self.resolve_deep(&inner))),
            Type::Nullable(inner) => Type::Nullable(Box::new(self.resolve_deep(&inner))),
            Type::ConstOf(inner) => Type::ConstOf(Box::new(self.resolve_deep(&inner))),
            Type::Mut(inner) => Type::Mut(Box::new(self.resolve_deep(&inner))),
            Type::Ref(inner) => Type::Ref(Box::new(self.resolve_deep(&inner))),
            Type::Fun(params, ret) => Type::Fun(
                params.iter().map(|p| self.resolve_deep(p)).collect(),
                Box::new(self.resolve_deep(&ret)),
            ),
            Type::Tuple(elems) => Type::Tuple(elems.iter().map(|t| self.resolve_deep(t)).collect()),
            other => other,
        }
    }

    /// Unify two types, extending the substitution. Returns an error message on
    /// a concrete-vs-concrete conflict.
    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), String> {
        let a = self.resolve(a);
        let b = self.resolve(b);
        if let (Some((a_ok, a_err)), Some((b_ok, b_err))) =
            (a.result_payloads(), b.result_payloads())
        {
            self.unify(a_ok, b_ok)?;
            return self.unify(a_err, b_err);
        }
        if a.is_result_type() && b.is_result_type() {
            return Ok(());
        }
        match (&a, &b) {
            (Type::Unknown(i), Type::Unknown(j)) if i == j => Ok(()),
            (Type::Unknown(i), other) | (other, Type::Unknown(i)) => {
                // Occurs check: refuse to bind a variable to a term that
                // mentions it. Self-application such as `(x) -> x` applied to
                // itself would otherwise create a cyclic substitution
                // (`U = (U) -> U`) that makes `resolve`/`resolve_deep` recurse
                // forever. Treat the infinite type as a unification failure.
                if self.occurs(*i, other) {
                    tracing::debug!(var = *i, ty = %other.display(), "occurs check failed: infinite type");
                    return Err(format!(
                        "cannot construct an infinite type for `{}`",
                        other.display()
                    ));
                }
                tracing::debug!(var = *i, bound_to = %other.display(), "binding inference variable");
                self.table.insert(*i, other.clone());
                self.trail.push(*i);
                Ok(())
            }
            (Type::Nullable(x), Type::Nullable(y))
                if matches!(x.as_ref(), Type::Never) || matches!(y.as_ref(), Type::Never) =>
            {
                Ok(())
            }
            (Type::Nullable(x), Type::Nullable(y)) => self.unify(x, y),
            (Type::Never, Type::Nullable(_)) | (Type::Nullable(_), Type::Never) => Ok(()),
            (Type::ConstOf(x), Type::ConstOf(y)) => self.unify(x, y),
            (Type::ConstOf(x), other) | (other, Type::ConstOf(x)) => self.unify(x, other),
            // `mut(T)` is transparent to unification: it unifies with `T` (and with
            // `mut(T)`) on its inner type. Mutability itself is not enforced by
            // unification but by the mutation/parameter-position checks, which
            // inspect the declared `mut(...)` wrapper directly.
            (Type::Mut(x), Type::Mut(y)) => self.unify(x, y),
            (Type::Mut(x), other) | (other, Type::Mut(x)) => self.unify(x, other),
            // A reference unifies with its referent type: the reference is created
            // implicitly from the parameter annotation, so the argument value type
            // matches. Whether to borrow or copy is decided separately at the call.
            (Type::Ref(x), Type::Ref(y)) => self.unify(x, y),
            (Type::Ref(x), other) | (other, Type::Ref(x)) => self.unify(x, other),
            (Type::Slice(x), Type::Slice(y)) => self.unify(x, y),
            (Type::Array(x, n), Type::Array(y, m)) if n == m => self.unify(x, y),
            (Type::Fun(p1, r1), Type::Fun(p2, r2)) if p1.len() == p2.len() => {
                for (x, y) in p1.iter().zip(p2) {
                    self.unify(x, y)?;
                }
                self.unify(r1, r2)
            }
            (Type::Tuple(xs), Type::Tuple(ys)) if xs.len() == ys.len() => {
                for (x, y) in xs.iter().zip(ys) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (Type::Sum(n1), Type::Sum(n2)) => {
                if n1.same_nominal(n2) {
                    Ok(())
                } else {
                    tracing::debug!(left = %n1, right = %n2, "sum type mismatch");
                    Err(format!("cannot unify sum types `{n1}` and `{n2}`"))
                }
            }
            _ if a == b => Ok(()),
            _ => {
                tracing::debug!(left = %a.display(), right = %b.display(), "unification conflict");
                Err(format!(
                    "cannot unify `{}` with `{}`",
                    a.display(),
                    b.display()
                ))
            }
        }
    }

    /// Whether inference variable `id` occurs inside `ty`. Variables already
    /// bound in the substitution are followed so the check reflects the current
    /// solution, not just the syntactic shape of `ty`.
    fn occurs(&self, id: u32, ty: &Type) -> bool {
        match self.resolve(ty) {
            Type::Unknown(j) => j == id,
            Type::Array(inner, _)
            | Type::Slice(inner)
            | Type::Nullable(inner)
            | Type::ConstOf(inner)
            | Type::Mut(inner)
            | Type::Ref(inner) => self.occurs(id, &inner),
            Type::Fun(params, ret) => {
                params.iter().any(|p| self.occurs(id, p)) || self.occurs(id, &ret)
            }
            Type::Tuple(elems) => elems.iter().any(|t| self.occurs(id, t)),
            // Nominal records and sums (including `Result`) carry their component
            // types in the substitution, and a variable can occur there -- e.g.
            // `o = Result<o, e>` arising from `[x, x!]`. Descend so the occurs
            // check matches `Solver::collect_free`, which traverses these: without
            // it a cyclic binding is committed and the later generalization that
            // walks the substitution recurses until the stack overflows.
            Type::Record(n) | Type::Sum(n) => {
                n.substitution.iter().any(|(_, t)| self.occurs(id, t))
            }
            _ => false,
        }
    }
}
