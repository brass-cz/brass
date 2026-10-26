//! Coalesced channel writes reconciled only at committed publication boundaries.

use super::*;

/// A span-keyed channel whose raw value was touched by elaboration.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Channel {
    FieldCall,
    ViewArg,
    LiftErr,
    NullProp,
    FieldsLoop,
    SumView,
    TypeName,
    TypeOf,
    TypeTest,
    KeyedCall,
}

/// Candidate changes since the last boundary. Rollback may leave extra candidates;
/// readers always consult the restored authoritative tables before emitting them.
#[derive(Default)]
pub(super) struct ChannelChanges {
    /// A checker fork has no authority to publish or drain committed changes.
    pub(super) forked: bool,
    /// Whether a streaming consumer has read the initial channel tables.
    pub(super) enabled: bool,
    /// Coalesced span writes, including candidates whose current value is absent.
    pub(super) spans: HashMap<Channel, HashSet<Span>>,
    /// Instance returns use structural call inputs rather than source spans.
    pub(super) returns: HashSet<(String, Vec<Type>)>,
}

impl Clone for ChannelChanges {
    fn clone(&self) -> Self {
        // Probe clones own their semantic tables, but neither copy nor share
        // the committed checker's potentially large dirty-key collection.
        Self {
            forked: true,
            ..Self::default()
        }
    }
}

impl ChannelChanges {
    /// Mark a raw write without publishing inside a speculative elaboration.
    pub(super) fn mark(&mut self, channel: Channel, span: Span) {
        if self.enabled {
            self.spans.entry(channel).or_default().insert(span);
        }
    }

    /// Mark a return write only while a streaming consumer needs invalidations.
    pub(super) fn mark_return(&mut self, symbol: &str, args: &[Type]) {
        if self.enabled {
            self.returns.insert((symbol.to_string(), args.to_vec()));
        }
    }

    /// Activate tracking and drain the preceding window. An inactive returned
    /// window requests an initial full read of the authoritative tables.
    pub(super) fn drain(&mut self) -> Self {
        assert!(!self.forked, "publication inside a checker fork");
        std::mem::replace(
            self,
            Self {
                enabled: true,
                ..Self::default()
            },
        )
    }

    /// Consume candidates for one channel, reclaiming this boundary's storage.
    pub(super) fn take(&mut self, channel: Channel) -> HashSet<Span> {
        self.spans.remove(&channel).unwrap_or_default()
    }
}
