//! Input reads that can invalidate a retained mono root, including absent entries.

use super::*;
use brass_mir::ChangedInputs;
use brass_parser::Span;

/// A channel lookup; absence has the same invalidation key as presence.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum Read {
    Seed(Span),
    Dispatch(Span),
    Return(String, Vec<Type>),
    NumericCalls,
}

impl Read {
    /// Whether this refresh replaces or removes the observed input.
    pub(super) fn changed(&self, changes: &ChangedInputs) -> bool {
        fn contains<K: Eq + std::hash::Hash>(keys: &brass_mir::ChangedKeys<K>, key: &K) -> bool {
            keys.changed.contains(key) || keys.removed.contains(key)
        }
        match self {
            Self::Seed(span) => {
                contains(&changes.seeds, span) || contains(&changes.instance_seeds, span)
            }
            Self::Dispatch(span) => {
                contains(&changes.dispatch, span) || contains(&changes.instance_dispatch, span)
            }
            Self::NumericCalls => {
                !changes.numeric_calls.changed.is_empty()
                    || !changes.numeric_calls.removed.is_empty()
            }
            Self::Return(base, args) => contains(&changes.returns, &(base.clone(), args.clone())),
        }
    }
}
