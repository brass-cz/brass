//! Append-only selector checkpoints contain no checker facts or borrowed HIR.
//! Rebinding the retained catalog keeps integer identities and settled frames;
//! generated roots and catalog-sensitive frames enter the worklist. Existing
//! body ASTs must be unchanged; changed method-name reads invalidate effect caches.

use super::{CheckSelection, ItemIndex, ItemKey, Reachability, Widening, inhabited};
use std::collections::VecDeque;

/// Settled worklist state, indexed by the retained catalog (three frames per item).
#[derive(Clone, Debug)]
pub(super) struct State {
    pub(super) pending: VecDeque<usize>,
    pub(super) queued: Vec<bool>,
    pub(super) frames: Vec<bool>,
    pub(super) revisits: Vec<bool>,
    pub(super) visited_at: Vec<usize>,
    pub(super) reasons: Vec<u8>,
    pub(super) widenings: Vec<Widening>,
    pub(super) causes: Vec<Vec<&'static str>>,
    pub(super) inhabited: inhabited::Inhabited,
    pub(super) open_frames: Vec<bool>,
    pub(super) required_roots: Vec<bool>,
    pub(super) callers: Vec<Vec<usize>>,
}

impl State {
    /// Allocate three checking frames per original catalog item.
    pub(super) fn new(count: usize) -> Self {
        Self {
            pending: VecDeque::new(),
            queued: vec![false; count * 3],
            frames: vec![false; count * 3],
            revisits: vec![false; count * 3],
            visited_at: vec![0; count * 3],
            reasons: vec![0; count],
            widenings: Vec::new(),
            causes: vec![Vec::new(); count],
            inhabited: inhabited::Inhabited::default(),
            open_frames: vec![false; count * 3],
            required_roots: vec![false; count * 3],
            callers: vec![Vec::new(); count * 3],
        }
    }

    fn extend(&mut self, count: usize) {
        assert!(
            self.pending.is_empty(),
            "only settled selectors can be rebound"
        );
        self.queued.resize(count * 3, false);
        self.frames.resize(count * 3, false);
        self.revisits.resize(count * 3, false);
        self.visited_at.resize(count * 3, 0);
        self.reasons.resize(count, 0);
        self.causes.resize_with(count, Vec::new);
        self.open_frames.resize(count * 3, false);
        self.required_roots.resize(count * 3, false);
        self.callers.resize_with(count * 3, Vec::new);
    }
}

/// Acceleration state only: selection equality deliberately compares requested
/// items/reasons, not caches or the allocation identity of their checkpoint.
pub(super) struct Continuation {
    catalog: super::index::snapshot::Snapshot,
    state: State,
}

impl std::fmt::Debug for Continuation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Continuation")
    }
}
impl Continuation {
    /// Retain stable catalog handles and a settled worklist, without HIR borrows.
    pub(super) fn new(index: &ItemIndex<'_>, state: State) -> Self {
        Self {
            catalog: index.snapshot(),
            state,
        }
    }

    /// Rebind unchanged bodies, append generated identities and resume affected frames.
    pub(super) fn append(
        &self,
        program: &brass_hir::Program,
        selection: &CheckSelection,
        generated: &[brass_hir::GeneratedDecl],
        extra: impl IntoIterator<Item = ItemKey>,
    ) -> CheckSelection {
        let changed = self.catalog.changes_reads(generated);
        let mut index = self.catalog.bind(program, changed);
        index.append_generated(generated);
        let mut state = self.state.clone();
        state.extend(index.len());
        let mut prior = selection.clone();
        prior.continuation = None;
        let mut reach = Reachability {
            index: &index,
            selection: prior,
            state,
        };
        // Changed method families invalidate dispatch frames. Only owners with
        // appended methods need a new shared-producer decision otherwise.
        for frame in 0..self.state.frames.len() {
            let affected = match &index.entries[frame / 3].declaration {
                super::index::Declaration::Initializer(_) => true,
                super::index::Declaration::Type(owner) => {
                    changed
                        || generated
                            .iter()
                            .any(|g| g.receiver == owner.name && g.module == owner.module)
                }
                _ => changed,
            };
            if self.state.frames[frame] && affected {
                reach.enqueue(frame);
            }
        }
        let mut extra: Vec<_> = extra.into_iter().collect();
        extra.sort_by_key(|key| index.lookup[key]);
        for key in extra {
            let id = index.lookup[&key];
            reach.state.required_roots[id * 3 + 2] = true;
            reach.add(id, brass_hir::Reason::Generated, 2);
        }
        reach.close();
        reach.into_selection()
    }
}
