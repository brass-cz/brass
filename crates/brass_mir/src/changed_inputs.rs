//! Invalidation information accompanying a committed checker-channel refresh.

use std::hash::Hash;

use brass_hir::Type;
use brass_parser::Span;
use fxhash::FxHashSet;

/// Keys whose final value changed or disappeared during a refresh window.
/// Sets are disjoint; repeated writes may conservatively report an unchanged value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChangedKeys<K: Eq + Hash> {
    /// Keys to reread from the refreshed channel.
    pub changed: FxHashSet<K>,
    /// Keys absent from the refreshed channel.
    pub removed: FxHashSet<K>,
}

impl<K: Eq + Hash> Default for ChangedKeys<K> {
    fn default() -> Self {
        Self {
            changed: FxHashSet::default(),
            removed: FxHashSet::default(),
        }
    }
}

impl<K: Eq + Hash> ChangedKeys<K> {
    /// Record replacement, superseding an earlier removal in this window.
    pub fn change(&mut self, key: K) {
        self.removed.remove(&key);
        self.changed.insert(key);
    }

    /// Record absence, superseding an earlier replacement in this window.
    pub fn remove(&mut self, key: K) {
        self.changed.remove(&key);
        self.removed.insert(key);
    }
}

/// Inputs changed since a consumer's preceding channel refresh.
///
/// Epochs belong to one merged checker stream. A consumer must reset if it changes
/// streams, misses `base_epoch`, or sees `full_reset`. Full reset also covers
/// untracked lowering channels, new/rebuilt MIR bodies and continuation snapshots.
/// Read every refresh record, even when its channel epoch is unchanged: a
/// body-only refresh can still require `full_reset`.
/// Return contracts have no source span: their keys are the symbol and structural
/// argument types, matching the return channel supplied separately to mono.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ChangedInputs {
    /// Epoch the consumer must already hold for this window to be incremental.
    pub base_epoch: u64,
    /// Epoch after all channel changes in this window have been merged.
    pub epoch: u64,
    /// Exact invalidation is unavailable; discard all cached derived state.
    pub full_reset: bool,
    /// Shared aggregate seeds, keyed by expression span.
    pub seeds: ChangedKeys<Span>,
    /// Per-instance seed maps, replaced or removed as whole span entries.
    pub instance_seeds: ChangedKeys<Span>,
    /// Shared keyed-dispatch targets, keyed by call span.
    pub dispatch: ChangedKeys<Span>,
    /// Per-instance dispatch maps, replaced or removed as whole span entries.
    pub instance_dispatch: ChangedKeys<Span>,
    /// Return contracts, keyed by structural call inputs rather than spans.
    pub returns: ChangedKeys<(String, Vec<Type>)>,
    /// Numeric storage selections, including the complete caller identity.
    pub numeric_calls: ChangedKeys<(Span, Option<brass_hir::InstanceKey>)>,
}

impl ChangedInputs {
    /// Start an empty window immediately after `epoch`.
    pub fn since(epoch: u64) -> Self {
        Self {
            base_epoch: epoch,
            epoch,
            ..Self::default()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn final_presence_wins_within_a_refresh_window() {
        // Consumers see the final map, including remove-then-reinsert sequences.
        let span = Span::new(1, 2);
        let mut keys = ChangedKeys::default();
        keys.change(span);
        keys.remove(span);
        assert!(keys.changed.is_empty());
        assert!(keys.removed.contains(&span));
        keys.change(span);
        assert!(keys.removed.is_empty());
        assert!(keys.changed.contains(&span));
    }
}
