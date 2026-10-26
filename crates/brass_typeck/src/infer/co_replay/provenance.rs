//! Qualified read provenance shared by ordinary and co memo windows.

use super::methods::QualifiedGlobal;
use crate::infer::Checker;
use brass_hir::Type;
use std::rc::Rc;

/// Exact reads in first-encounter order. Repeated identities with different
/// types remain distinct; an unknown identity never certifies an empty set.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(in crate::infer) struct GlobalReadProvenance {
    /// Defining identities and types resolved at the actual reads.
    pub reads: Vec<(QualifiedGlobal, Type)>,
    /// Untracked shared-state reads prevent method admission.
    pub untracked: bool,
}

impl GlobalReadProvenance {
    /// Include a complete child window without losing conflicting read types.
    pub(in crate::infer) fn extend(&mut self, child: &Self) {
        self.untracked |= child.untracked;
        for read in &child.reads {
            if !self.reads.contains(read) {
                self.reads.push(read.clone());
            }
        }
    }

    /// Empty provenance needs no retained allocation in the common memo entry.
    pub(in crate::infer) fn retained(self) -> Option<Rc<Self>> {
        (self.untracked || !self.reads.is_empty()).then(|| Rc::new(self))
    }
}

impl Checker<'_> {
    /// Skip global identity resolution when no journal or observer needs reads.
    #[inline]
    pub(in crate::infer) fn has_global_dependency_observer(&self) -> bool {
        !self.elaboration_journals.is_empty()
            || !self.co_validation.is_empty()
            || self.method_inventory.is_some()
    }

    /// Record a value read independently of the unqualified reporting set.
    /// Ordinary entries need the same evidence when replayed inside a method.
    pub(in crate::infer) fn record_global_dependency(
        &mut self,
        name: &str,
        ty: &Type,
        qualified: bool,
    ) {
        if !self.has_global_dependency_observer() {
            return;
        }
        let identity = self.method_global_identity(name, qualified);
        let resolved = self.resolve(ty);
        let reads = GlobalReadProvenance {
            untracked: identity.is_none(),
            reads: identity.map(|id| (id, resolved)).into_iter().collect(),
        };
        if self.validate_global_provenance(&reads) {
            return;
        }
        if let Some(frame) = self.elaboration_journals.last_mut() {
            frame.global_reads.extend(&reads);
        }
        if self.method_inventory.is_some() {
            self.observe_method_global(name, ty, qualified);
        }
    }

    /// A recursive fallback reads shared return state that qualified global
    /// provenance cannot certify. Enclosing method entries remain ineligible.
    pub(in crate::infer) fn record_untracked_method_dependency(&mut self) {
        let reads = GlobalReadProvenance {
            untracked: true,
            ..Default::default()
        };
        if self.validate_global_provenance(&reads) {
            return;
        }
        if let Some(frame) = self.elaboration_journals.last_mut() {
            frame.global_reads.untracked = true;
        }
        if self.method_inventory.is_some() {
            self.observe_method_replay(Some(&reads));
        }
    }

    /// A hit contributes its exact read set to its parent, including empty
    /// provenance. Dry validation replays never enter actual parent windows.
    #[inline]
    pub(in crate::infer) fn replay_global_provenance(
        &mut self,
        reads: Option<&GlobalReadProvenance>,
    ) {
        if let Some(reads) = reads
            && self.validate_global_provenance(reads)
        {
            return;
        }
        if self
            .co_validation
            .last()
            .is_some_and(|probe| probe.is_replay())
        {
            return;
        }
        if let Some(frame) = self.elaboration_journals.last_mut() {
            frame.memo_replayed = true;
            if let Some(reads) = reads {
                frame.global_reads.extend(reads);
            }
        }
        if self.method_inventory.is_some() {
            self.observe_method_replay(reads);
        }
    }
}
