//! Publication and replay of completed numeric storage contracts.

use super::instances::TagRef;
use super::*;

/// One committed call and the enclosing instance under which it was checked.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct Observation {
    /// Call or closure-creation site selecting the body.
    pub(super) span: Span,
    /// Enclosing instance, unresolved until its parameter types settle.
    pub(super) instance: Option<TagRef>,
    /// Completed layout; None explicitly selects the ordinary body.
    pub(super) ty: Option<brass_hir::NumericLayout>,
}

impl Checker<'_> {
    /// Record a completed storage contract through the elaboration journal.
    pub(super) fn record_numeric_call(
        &mut self,
        span: Span,
        ty: Option<brass_hir::NumericLayout>,
        instance: Option<TagRef>,
    ) {
        self.journal_elaboration(ElaborationJournalEntry::NumericCall {
            span,
            ty: ty.clone(),
            instance: instance.clone(),
        });
        let observation = Observation { span, ty, instance };
        if self.numeric_observed.insert(observation.clone()) {
            self.numeric_observations.push(observation);
        }
    }

    /// Final call contracts whose enclosing identities are fully known.
    pub(super) fn numeric_call_map(&self) -> brass_hir::NumericCalls {
        self.numeric_observations
            .iter()
            .filter_map(|observation| {
                let instance = match &observation.instance {
                    Some(tag) => Some(self.instance_key_of(tag)?),
                    None => None,
                };
                Some(((observation.span, instance), observation.ty.clone()))
            })
            .collect()
    }
}
