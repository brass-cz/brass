//! Coalesced solution mutations for a single publication consumer.

use fxhash::FxHashSet;
use std::cell::RefCell;

/// Bindings changed since the publication consumer's preceding read.
#[derive(Default)]
pub struct PublicationChanges {
    /// Monotonic solution version, including bindings removed by rollback.
    pub epoch: u64,
    /// Variables whose bindings were inserted or removed in this window.
    pub variables: FxHashSet<u32>,
}

/// Monotonic mutation version with collection enabled by its sole consumer.
#[derive(Default)]
pub(super) struct PublicationFeed {
    epoch: u64,
    pending: RefCell<Option<FxHashSet<u32>>>,
}

impl Clone for PublicationFeed {
    fn clone(&self) -> Self {
        // A solution fork has no publication consumer. Keep the version but
        // leave its collection disabled; the original retains its pending set.
        Self {
            epoch: self.epoch,
            pending: RefCell::new(None),
        }
    }
}

impl PublicationFeed {
    /// Record a binding insertion or removal without retaining speculative values.
    pub(super) fn record(&mut self, variable: u32) {
        self.epoch = self.epoch.checked_add(1).expect("solution epoch exhausted");
        if let Some(pending) = self.pending.get_mut() {
            pending.insert(variable);
        }
    }

    /// Drain one mutation window and enable collection for subsequent windows.
    pub(super) fn take(&self) -> PublicationChanges {
        let mut pending = self.pending.borrow_mut();
        PublicationChanges {
            epoch: self.epoch,
            variables: std::mem::take(pending.get_or_insert_with(Default::default)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::unify::Subst;
    use brass_hir::Type;

    #[test]
    fn solution_forks_do_not_copy_or_consume_pending_mutations() {
        let mut subst = Subst::new();
        subst.take_publication_changes();
        let snapshot = subst.snapshot();
        subst.unify(&Type::Unknown(7), &Type::Bool).unwrap();
        let mut fork = subst.clone();
        assert!(fork.publication.pending.borrow().is_none());
        fork.rollback(snapshot);
        fork.unify(&Type::Unknown(8), &Type::Str).unwrap();
        assert!(fork.publication.pending.borrow().is_none());
        assert_eq!(subst.resolve(&Type::Unknown(7)), Type::Bool);
        assert_eq!(subst.resolve(&Type::Unknown(8)), Type::Unknown(8));
        // A committed rollback after the fork must still wake the real reader.
        subst.rollback(snapshot);
        let changes = subst.take_publication_changes();
        assert_eq!(changes.variables, [7].into_iter().collect());
        assert_eq!(changes.epoch, 2);
    }

    #[test]
    fn partial_failure_rollback_and_rebinding_advance_the_publication_epoch() {
        let mut subst = Subst::new();
        assert_eq!(subst.take_publication_changes().epoch, 0);
        let snapshot = subst.snapshot();
        // Tuple unification binds the first slot before the second disagrees.
        assert!(
            subst
                .unify(
                    &Type::Tuple(vec![Type::Unknown(7), Type::Bool]),
                    &Type::Tuple(vec![Type::Str, Type::Void]),
                )
                .is_err()
        );
        let bound = subst.take_publication_changes();
        assert_eq!(bound.variables, [7].into_iter().collect());
        subst.rollback(snapshot);
        let undone = subst.take_publication_changes();
        assert!(undone.epoch > bound.epoch);
        assert_eq!(undone.variables, [7].into_iter().collect());
        subst.unify(&Type::Unknown(7), &Type::Bool).unwrap();
        let rebound = subst.take_publication_changes();
        assert!(rebound.epoch > undone.epoch);
        assert_eq!(rebound.variables, [7].into_iter().collect());
        assert!(subst.take_publication_changes().variables.is_empty());
        assert_eq!(
            subst.resolve_with_dependencies(&Type::Unknown(7)),
            (Type::Bool, vec![7])
        );
    }
}
