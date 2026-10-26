//! Reclaim inference scratch state after terminal stream publication.

use super::Checker;

/// Owns completed checker scratch state after its analysis outputs are extracted.
/// Streaming callers keep it until `Finished` is sent, so terminal settlement
/// does not wait for solver and memo deallocation. Drop only reclaims memory.
#[derive(Default)]
pub(crate) struct InferenceCleanup<'p> {
    _checker: Option<Box<Checker<'p>>>,
}

impl<'p> InferenceCleanup<'p> {
    /// Retain streaming scratch state; reclaim eager state at this boundary.
    pub(super) fn retain(checker: Checker<'p>, streaming: bool) -> Self {
        Self {
            _checker: streaming.then(|| Box::new(checker)),
        }
    }
}
