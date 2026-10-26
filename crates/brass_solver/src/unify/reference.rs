//! Independent owned resolution for opt-in differential checks.

use super::*;

impl Subst {
    /// Resolve through an owned recursive walk for differential verification.
    pub fn resolve_reference(&self, t: &Type) -> Type {
        match self.resolve(t) {
            Type::Array(inner, n) => Type::Array(Box::new(self.resolve_reference(&inner)), n),
            Type::Slice(inner) => Type::Slice(Box::new(self.resolve_reference(&inner))),
            // The shallow `resolve` above already collapsed a variable that
            // pinned to a nullable; deep-resolving the payload can expose one
            // more level (a variable bound to `T?` reached only now).
            Type::Nullable(inner) => match self.resolve_reference(&inner) {
                nested @ Type::Nullable(_) => nested,
                other => Type::Nullable(Box::new(other)),
            },
            Type::ConstOf(inner) => Type::ConstOf(Box::new(self.resolve_reference(&inner))),
            Type::Mut(inner) => Type::Mut(Box::new(self.resolve_reference(&inner))),
            Type::Ref(inner) => Type::Ref(Box::new(self.resolve_reference(&inner))),
            Type::Fun(params, ret) => Type::Fun(
                params.iter().map(|p| self.resolve_reference(p)).collect(),
                Box::new(self.resolve_reference(&ret)),
            ),
            Type::Tuple(elems) => {
                Type::Tuple(elems.iter().map(|t| self.resolve_reference(t)).collect())
            }
            // A nominal type carries the concrete types of its unannotated fields
            // (and a Result's payloads) in its substitution; resolve those too, so
            // e.g. `HashMap<entries=?[]>` whose element was pinned by a `push`
            // becomes `HashMap<entries=_Entry<...>[]>`.
            Type::Record(n) => Type::Record(self.resolve_nominal_reference(&n)),
            Type::Sum(n) => Type::Sum(self.resolve_nominal_reference(&n)),
            other => other,
        }
    }

    /// Deep-resolve every type in a nominal's substitution.
    fn resolve_nominal_reference(&self, n: &NominalType) -> NominalType {
        let mut substitution = Substitution::empty();
        for (key, ty) in n.substitution.iter() {
            substitution.insert(key, self.resolve_reference(ty));
        }
        NominalType::with_substitution(n.id, n.name.clone(), substitution)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_resolution(subst: &Subst, types: &[Type]) {
        for ty in types {
            assert_eq!(subst.resolve_deep(ty), subst.resolve_reference(ty));
        }
    }

    #[test]
    fn borrowed_resolution_matches_owned_across_bindings_and_rollback() {
        // Include nested substitution payloads and every recursive wrapper;
        // partial failures and rollback must invalidate the same leaves.
        let mut fields = Substitution::empty();
        fields.insert("item", Type::Unknown(1));
        let nominal = NominalType::with_substitution(42, "Container", fields);
        let mut types = vec![Type::Record(nominal.clone()), Type::Sum(nominal)];
        types.extend((0..4).map(Type::Unknown));
        for _ in 0..3 {
            let inner = Type::Tuple(types.clone());
            types = vec![
                Type::Array(Box::new(inner.clone()), 3),
                Type::Slice(Box::new(inner.clone())),
                Type::Nullable(Box::new(inner.clone())),
                Type::ConstOf(Box::new(inner.clone())),
                Type::Mut(Box::new(inner.clone())),
                Type::Ref(Box::new(inner.clone())),
                Type::Fun(vec![inner.clone()], Box::new(inner)),
            ];
        }
        let mut subst = Subst::new();
        assert_resolution(&subst, &types);
        let original = subst.snapshot();
        subst
            .unify(
                &Type::Unknown(1),
                &Type::Nullable(Box::new(Type::Unknown(2))),
            )
            .unwrap();
        subst
            .unify(&Type::Unknown(2), &Type::Nullable(Box::new(Type::Str)))
            .unwrap();
        assert_resolution(&subst, &types);
        let partial = subst.snapshot();
        assert!(
            subst
                .unify(
                    &Type::Tuple(vec![Type::Unknown(3), Type::Bool]),
                    &Type::Tuple(vec![Type::Str, Type::Void])
                )
                .is_err()
        );
        assert_resolution(&subst, &types);
        subst.rollback(partial);
        assert_resolution(&subst, &types);
        subst.rollback(original);
        subst
            .unify(&Type::Unknown(1), &Type::Slice(Box::new(Type::Bool)))
            .unwrap();
        assert_resolution(&subst, &types);
    }
}
