//! Unification over `Type` with a substitution for `Unknown` variables.
//! Declared records and sums are nominal: two instances of one declaration
//! unify through the substitution entries both carry (see
//! `Subst::unify_shared_keys`); structural records are compared elsewhere.

mod changes;
mod reference;

pub use changes::PublicationChanges;

use fxhash::FxHashMap as HashMap;

use brass_hir::{NominalType, Substitution, Type, passing_modes_match, split_passing_mode};

/// A substitution: the binding of every solved inference variable, plus the
/// trail of bindings a [`Snapshot`] rolls back to.
#[derive(Clone, Default)]
pub struct Subst {
    table: HashMap<u32, Type>,
    /// Keys inserted in order, so a snapshot can be rolled back. Every variable
    /// is bound at most once (unify resolves before binding), so undoing a
    /// binding is just removing the key.
    trail: Vec<u32>,
    publication: changes::PublicationFeed,
}

/// An opaque marker for the substitution state, used to roll back speculative
/// unifications (e.g. a non-committing assignability probe).
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
                self.publication.record(id);
            }
        }
    }

    /// Restore checkpoint bindings while retaining the committed mutation feed.
    pub(crate) fn restore_checkpoint(&mut self, checkpoint: Self) {
        for (id, ty) in &self.table {
            if checkpoint.table.get(id) != Some(ty) {
                self.publication.record(*id);
            }
        }
        for id in checkpoint
            .table
            .keys()
            .filter(|id| !self.table.contains_key(id))
        {
            self.publication.record(*id);
        }
        self.table = checkpoint.table;
        self.trail = checkpoint.trail;
    }

    /// Follow substitutions to a representative type.
    ///
    /// A `Nullable` is looked through as well, because `T??` is not a type the
    /// language can distinguish from `T?` (there is one `null`) yet it is
    /// exactly what a `?`-wrapped inference variable becomes once that variable
    /// pins to a nullable type -- see the return re-wrap in the checker's
    /// `check_block_root`. Collapsing here, rather than at each consumer, keeps
    /// the nesting from ever escaping the substitution.
    pub fn resolve(&self, t: &Type) -> Type {
        match t {
            Type::Unknown(id) => match self.table.get(id) {
                Some(bound) => self.resolve(bound),
                None => t.clone(),
            },
            Type::Nullable(inner) => match self.resolve(inner) {
                nested @ Type::Nullable(_) => nested,
                other => Type::Nullable(Box::new(other)),
            },
            _ => t.clone(),
        }
    }

    /// [`Self::resolve_head`] without copying: the representative of the
    /// top-level inference-variable chain of `t`, borrowed from `t` or from
    /// the substitution, for callers that only inspect its constructor.
    pub fn resolve_head_ref<'a>(&'a self, t: &'a Type) -> &'a Type {
        match t {
            Type::Unknown(id) => match self.table.get(id) {
                Some(bound) => self.resolve_head_ref(bound),
                None => t,
            },
            _ => t,
        }
    }

    /// Follow only a top-level inference-variable chain to its representative.
    /// Nested components stay untouched for callers that only inspect the outer
    /// constructor and do not need a fully materialized type.
    pub fn resolve_head(&self, t: &Type) -> Type {
        match t {
            Type::Unknown(id) => match self.table.get(id) {
                Some(bound) => self.resolve_head(bound),
                None => t.clone(),
            },
            _ => t.clone(),
        }
    }

    /// Resolve a type and recurse into its components so that nested inference
    /// variables are substituted too: the fully solved form of a type (e.g.
    /// the result of `(x) -> x` applied to an `int32` is `int32` once the
    /// argument has unified into the parameter variable, not an unconstrained
    /// unknown).
    pub fn resolve_deep(&self, t: &Type) -> Type {
        self.resolve_read(t, &mut |_| {})
    }

    /// Resolve a type while collecting bound aliases and unresolved variables.
    /// Both are dependencies because rollback can remove an alias's binding.
    pub fn resolve_with_dependencies(&self, t: &Type) -> (Type, Vec<u32>) {
        let mut variables = Vec::new();
        let ty = self.resolve_read(t, &mut |id| variables.push(id));
        variables.sort_unstable();
        variables.dedup();
        (ty, variables)
    }

    /// Consume coalesced mutations for the single channel publication consumer.
    /// The first read enables tracking; subsequent reads reclaim the window.
    pub fn take_publication_changes(&self) -> PublicationChanges {
        self.publication.take()
    }

    fn resolve_read(&self, t: &Type, read: &mut impl FnMut(u32)) -> Type {
        match t {
            Type::Unknown(id) => {
                read(*id);
                match self.table.get(id) {
                    Some(bound) => self.resolve_read(bound, read),
                    None => t.clone(),
                }
            }
            Type::Array(inner, n) => Type::Array(Box::new(self.resolve_read(inner, read)), *n),
            Type::Slice(inner) => Type::Slice(Box::new(self.resolve_read(inner, read))),
            // Resolving the payload can expose another nullable layer.
            // Collapse it without constructing an intermediate owned subtree.
            Type::Nullable(inner) => match self.resolve_read(inner, read) {
                nested @ Type::Nullable(_) => nested,
                other => Type::Nullable(Box::new(other)),
            },
            Type::ConstOf(inner) => Type::ConstOf(Box::new(self.resolve_read(inner, read))),
            Type::Mut(inner) => Type::Mut(Box::new(self.resolve_read(inner, read))),
            Type::Ref(inner) => Type::Ref(Box::new(self.resolve_read(inner, read))),
            Type::Fun(params, ret) => Type::Fun(
                params.iter().map(|p| self.resolve_read(p, read)).collect(),
                Box::new(self.resolve_read(ret, read)),
            ),
            Type::Tuple(elems) => {
                Type::Tuple(elems.iter().map(|t| self.resolve_read(t, read)).collect())
            }
            // A nominal type carries the concrete types of its unannotated fields
            // (and a Result's payloads) in its substitution; resolve those too, so
            // e.g. `HashMap<entries=?[]>` whose element was pinned by a `push`
            // becomes `HashMap<entries=_Entry<...>[]>`.
            Type::Record(n) => Type::Record(self.resolve_nominal_read(n, read)),
            Type::Sum(n) => Type::Sum(self.resolve_nominal_read(n, read)),
            other => other.clone(),
        }
    }

    /// Deep-resolve every type in a nominal's substitution.
    fn resolve_nominal_read(&self, n: &NominalType, read: &mut impl FnMut(u32)) -> NominalType {
        let mut substitution = Substitution::empty();
        for (key, ty) in n.substitution.iter() {
            substitution.insert(key, self.resolve_read(ty, read));
        }
        NominalType::with_substitution(n.id, n.name.clone(), substitution)
    }

    /// Unify a type nested in a function signature without erasing its calling
    /// convention. Direct calls may match `T` against `ref(T)` because the call
    /// creates the reference, but two function values are interchangeable only
    /// when their parameter and result conventions agree.
    fn unify_function_part(&mut self, a: &Type, b: &Type) -> Result<(), String> {
        let a = self.resolve(a);
        let b = self.resolve(b);
        // A whole open signature part has not chosen a calling convention yet.
        // Bind it to the complete counterpart before splitting wrappers;
        // otherwise `U` unified with `ref(T)` or `mut(T)` would become bare `T`.
        if matches!(a, Type::Unknown(_)) || matches!(b, Type::Unknown(_)) {
            return self.unify(&a, &b);
        }
        if !passing_modes_match(&a, &b) {
            return Err(format!(
                "function passing mode mismatch between `{}` and `{}`",
                a.display(),
                b.display()
            ));
        }
        let (_, a) = split_passing_mode(&a);
        let (_, b) = split_passing_mode(&b);
        self.unify(a, b)
    }

    /// Unify two types, extending the substitution. Returns an error message on
    /// a concrete-vs-concrete conflict or an infinite type (occurs check). A
    /// failed unification may leave the bindings it made before the conflict;
    /// callers that probe take a [`Snapshot`] and roll back.
    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), String> {
        let a = self.resolve(a);
        let b = self.resolve(b);
        // Two instances of the SAME `Result` declaration unify by their
        // payloads; an instance missing its payload entries (a bare
        // annotation) constrains nothing. The id gate matters: a module's
        // shadowing `Result` and the prelude's are distinct declarations that
        // must not unify just because both carry the name (they fall through
        // to the strict sum arm below).
        if let (Type::Sum(na), Type::Sum(nb)) = (&a, &b)
            && na.is_result_type()
            && nb.is_result_type()
            && na.id == nb.id
        {
            if let (Some((a_ok, a_err)), Some((b_ok, b_err))) =
                (na.result_payloads(), nb.result_payloads())
            {
                let (a_ok, a_err) = (a_ok.clone(), a_err.clone());
                let (b_ok, b_err) = (b_ok.clone(), b_err.clone());
                self.unify(&a_ok, &b_ok)?;
                return self.unify(&a_err, &b_err);
            }
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
                self.publication.record(*i);
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
                    self.unify_function_part(x, y)?;
                }
                self.unify_function_part(r1, r2)
            }
            (Type::Tuple(xs), Type::Tuple(ys)) if xs.len() == ys.len() => {
                for (x, y) in xs.iter().zip(ys) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            // Two instances of the same sum declaration unify like same-id
            // records: a refinement (the concrete type of an unannotated
            // variant field, recorded at construction) is extra information,
            // not a different type. Only the keys both sides carry are unified;
            // a key present on one side only belongs to a sparser instance
            // (`Opt.Nothing` knows nothing about `Some.v`) and constrains
            // nothing, so `[Opt.Nothing, Opt.Some { v: 1 }]` has one element
            // type. Synthetic negative ids identify by name as well.
            (Type::Sum(n1), Type::Sum(n2))
                if n1.id == n2.id && (n1.id >= 0 || n1.name == n2.name) =>
            {
                self.unify_shared_keys(n1, n2)
            }
            (Type::Sum(n1), Type::Sum(n2)) => {
                tracing::debug!(left = %n1, right = %n2, "sum type mismatch");
                Err(format!("cannot unify sum types `{n1}` and `{n2}`"))
            }
            // Two records of the same *declared* nominal (id >= 0) unify by
            // unifying the shared entries of their generic substitutions, so a
            // record's inferred field types propagate: storing an `_Entry<string,
            // string>` into an element typed `_Entry<?, ?>` refines the element's
            // open key/value variables. Note this is NOT `same_nominal`, which also
            // requires identical substitutions and so would never relate two
            // differently-instantiated records -- the whole point here. Structural
            // records (the synthetic negative `STRUCTURAL_RECORD_ID`) are excluded:
            // their field-presence/compatibility is checked structurally elsewhere,
            // not by unification, so they keep the strict `a == b` behavior below.
            // Only keys present on both sides are unified; a key on just one side is
            // a sparser instance (a bare nominal, or a record whose annotated field
            // is absent from the dynamic substitution) and is left unconstrained.
            (Type::Record(n1), Type::Record(n2)) if n1.id >= 0 && n2.id >= 0 => {
                if n1.id != n2.id {
                    tracing::debug!(left = %n1, right = %n2, "record type mismatch");
                    return Err(format!("cannot unify record types `{n1}` and `{n2}`"));
                }
                self.unify_shared_keys(n1, n2)
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

    /// Unify the substitution entries two instances of one nominal declaration
    /// both carry. A key present on only one side is left unconstrained: that
    /// side is a sparser instance of the same declaration.
    fn unify_shared_keys(&mut self, n1: &NominalType, n2: &NominalType) -> Result<(), String> {
        let pairs: Vec<(Type, Type)> = n1
            .substitution
            .iter()
            .filter_map(|(k, v1)| n2.substitution.get(k).map(|v2| (v1.clone(), v2.clone())))
            .collect();
        for (v1, v2) in pairs {
            self.unify(&v1, &v2)?;
        }
        Ok(())
    }

    /// Whether inference variable `id` occurs inside `ty`. Variables already
    /// bound in the substitution are followed so the check reflects the current
    /// solution, not just the syntactic shape of `ty`.
    pub fn occurs(&self, id: u32, ty: &Type) -> bool {
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
            // check matches `Solver::free_vars` and `resolve_deep`, which
            // traverse these: a cyclic binding there would make every later
            // walk of the substitution recurse until the stack overflows.
            Type::Record(n) | Type::Sum(n) => {
                n.substitution.iter().any(|(_, t)| self.occurs(id, t))
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use brass_hir::{IntKind, Type};

    use super::Subst;

    fn nullable(t: Type) -> Type {
        Type::Nullable(Box::new(t))
    }

    /// A `?` wrapped over a variable that later pins to a nullable type must
    /// not resolve to `T??`: the language has one `null`, and generated code
    /// would build a cell holding a cell. Both the shallow and the deep
    /// resolution normalize it, at any nesting depth.
    #[test]
    fn nullable_over_a_variable_pinned_to_a_nullable_collapses() {
        let mut s = Subst::new();
        let var = Type::Unknown(0);
        s.unify(&var, &nullable(Type::Str)).unwrap();

        let wrapped = nullable(var.clone());
        assert_eq!(s.resolve(&wrapped), nullable(Type::Str));
        assert_eq!(s.resolve_deep(&wrapped), nullable(Type::Str));
        // Through a chain of variables, and under a component of a larger type.
        let outer = Type::Unknown(1);
        s.unify(&outer, &wrapped).unwrap();
        assert_eq!(s.resolve(&nullable(outer.clone())), nullable(Type::Str));
        assert_eq!(
            s.resolve_deep(&Type::Slice(Box::new(nullable(outer)))),
            Type::Slice(Box::new(nullable(Type::Str)))
        );
    }

    /// Head resolution follows a solved outer variable but deliberately keeps
    /// variables inside the resolved constructor for allocation-free probing.
    #[test]
    fn head_resolution_leaves_nested_variables_unresolved() {
        let mut s = Subst::new();
        let inner = Type::Unknown(0);
        s.unify(&inner, &Type::Str).unwrap();
        let slice = Type::Slice(Box::new(inner.clone()));
        let outer = Type::Unknown(1);
        s.unify(&outer, &slice).unwrap();

        assert_eq!(s.resolve_head(&outer), slice);
        assert_eq!(s.resolve_deep(&outer), Type::Slice(Box::new(Type::Str)));
    }

    /// Collapsing is confined to nested nullables: a single `?` over a concrete
    /// or still-open payload is preserved.
    #[test]
    fn a_single_nullable_is_preserved() {
        let mut s = Subst::new();
        assert_eq!(s.resolve(&nullable(Type::Str)), nullable(Type::Str));
        let var = Type::Unknown(0);
        assert_eq!(s.resolve(&nullable(var.clone())), nullable(var.clone()));
        s.unify(&var, &Type::Int(IntKind::I32)).unwrap();
        assert_eq!(s.resolve(&nullable(var)), nullable(Type::Int(IntKind::I32)));
    }

    /// Same-declaration sums unify through the substitution keys both carry,
    /// like records: a sparser instance constrains nothing, a shared open slot
    /// is bound, and a shared slot pinned two ways is still a conflict.
    #[test]
    fn same_sum_instances_unify_by_shared_refinements() {
        use brass_hir::{NominalType, Substitution};
        let sum = |entries: &[(&str, Type)]| {
            let mut substitution = Substitution::empty();
            for (key, ty) in entries {
                substitution.insert(*key, ty.clone());
            }
            Type::Sum(NominalType::with_substitution(3, "Opt", substitution))
        };
        let int = Type::Int(IntKind::I32);
        let mut s = Subst::new();
        assert!(s.unify(&sum(&[]), &sum(&[("Some.v", int.clone())])).is_ok());
        let open = Type::Unknown(0);
        s.unify(
            &sum(&[("Some.v", open.clone())]),
            &sum(&[("Some.v", int.clone())]),
        )
        .unwrap();
        assert_eq!(s.resolve(&open), int);
        assert!(
            s.unify(&sum(&[("Some.v", int)]), &sum(&[("Some.v", Type::Str)]))
                .is_err()
        );
        let other = Type::Sum(NominalType::new(4, "Other"));
        assert!(s.unify(&sum(&[]), &other).is_err());
    }

    #[test]
    fn whole_function_unknowns_retain_inferred_passing_modes() {
        // A signature-level unknown represents the entire parameter type, so
        // inference must retain reference/copy wrappers chosen by its peer.
        let mut s = Subst::new();
        let borrowed = Type::Unknown(0);
        let mutable = Type::Unknown(1);
        let ref_string = Type::Ref(Box::new(Type::Str));
        let mut_int = Type::Mut(Box::new(Type::Int(brass_hir::IntKind::I32)));

        s.unify_function_part(&borrowed, &ref_string).unwrap();
        s.unify_function_part(&mut_int, &mutable).unwrap();

        assert_eq!(s.resolve_deep(&borrowed), ref_string);
        assert_eq!(s.resolve_deep(&mutable), mut_int);
    }
}
