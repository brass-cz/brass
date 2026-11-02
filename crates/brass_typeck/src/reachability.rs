//! Monotone item selection over the combined declaration catalog.
//!
//! The driver bypasses selection when all dependencies are embedded core. Core
//! has a small, bounded checking cost and no omitted user diagnostics; disk, std,
//! package and include modules always require the ordinary selection authority.
//!
//! The catalog and its diagnostics remain complete. This module never invokes
//! inference, claims body coverage, or changes a checker pass. Unknown dispatch
//! widens explicitly; it cannot prove an absent edge by a failed name lookup.
//!
//! Soundness: a value of T requires a producer in reached code. Producers are
//! record/sum/anonymous and scalar literals, constructors and static conversions,
//! default/typed bindings (including keyed decoder destinations), declared and
//! body-derived callable results, closure results, plugin boundary returns, and
//! global initializers. Declared inputs and receivers of checked callable roots
//! are abstract producers too. Arrays, nullables, tuples and map substitutions propagate
//! their possible contained values; instantiated declaration fields do likewise.
//! Generated and demanded bodies enter through the same worklist. Merely visible
//! imports and type-test annotations are not value producers.
//!
//! Open root parameters (including closure parameters without a determined type)
//! are an abstract boundary admitting any type: their frame retains conservative
//! same-name/display/reflection widening. Execution frames propagate this bit to
//! callees and back to callers that may consume their results. Shared-preparation
//! frames are separate: open scheme slots are not arbitrary execution inputs and
//! cannot open an execution caller. Their unknown dispatch uses inhabited targets.
//! Reached keyed templates also seed a generated-preparation root frame before
//! the entry gate. Its declared inputs anticipate the generated checking frame;
//! openness flows only within that third frame, never into execution callers.
//! This deliberately over-approximates intra-frame value flow rather than
//! losing an open input through a local, capture, helper or return. Exact literal
//! and constructor dispatch remains exact even in an open frame.
//!
//! Other unknown dispatch/reflection ranges over inhabited families only. Growth
//! revisits selected sources with virtual dispatch, including empty target sets, until
//! both item selection and inhabitation stop growing. This over-approximates
//! structural flow and all branch arms without running a second type checker.
//! Shared producers are selected only for used owners, independently of runtime
//! dispatch; retaining one conservatively contributes its body producers too.
//! Global cells belong to rooted initializers. Their transitive readers and
//! writers remain shared producers even without a call or an inhabited method
//! owner: an ordinary body walk can constrain an open global through a read.

mod certificate;
mod continuation;
mod cost;
mod edges;
mod effects;
mod index;
mod inhabited;
mod layout;
mod names;
mod view;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod view_tests;

pub use brass_hir::diagnostics::{DiagnosticOwner, DiagnosticOwners};
pub use certificate::{SharedObligation, shared_obligation};
pub use effects::EffectSummary;
pub use index::{BodyId, ItemIndex, ItemKey};
pub use view::{AnalysisView, ItemCoverage, SharedComponentCoverage};

use brass_hir::{ItemId, ProjectScope, Reason};
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

/// A reason-carrying selection, not evidence that any body has been checked.
#[derive(Clone, Debug, Default)]
pub struct CheckSelection {
    /// All declarations owned by the input package.
    pub own_roots: HashSet<ItemKey>,
    /// Selected functions, method checking contexts, and module initializers.
    pub body_roots: HashSet<BodyId>,
    /// Selected layouts and aliases; unused method signatures do not seed these.
    pub type_roots: HashSet<ItemId>,
    /// All distinct reasons, in discovery order within each item.
    pub reasons: HashMap<ItemKey, Vec<Reason>>,
    /// Increases for each new item or reason; never decreases within a graph.
    pub revision: u64,
    /// Settled selector state for append-only generated declarations; no checked facts.
    continuation: Option<std::sync::Arc<continuation::Continuation>>,
}

// Continuations accelerate the same request and are not part of its semantics.
impl PartialEq for CheckSelection {
    fn eq(&self, other: &Self) -> bool {
        self.own_roots == other.own_roots
            && self.body_roots == other.body_roots
            && self.type_roots == other.type_roots
            && self.reasons == other.reasons
            && self.revision == other.revision
    }
}

/// One conservative widening at a source item, retaining its cause for review.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Widening {
    /// The source whose syntax cannot identify an exact dispatch target.
    pub source: ItemKey,
    /// The operation or unresolved fact that requires retaining candidates.
    pub cause: &'static str,
}

/// The sole worklist authority for selection growth. Stable source identities
/// are exported at the boundary; work queues and frame membership use catalog
/// indices so revisiting a body never clones a module path.
pub struct Reachability<'a, 'p> {
    index: &'a ItemIndex<'p>,
    selection: CheckSelection,
    state: continuation::State,
}

impl<'a, 'p> Reachability<'a, 'p> {
    fn empty(index: &'a ItemIndex<'p>) -> Self {
        let count = index.entries.len();
        Self {
            index,
            selection: CheckSelection::default(),
            state: continuation::State::new(count),
        }
    }

    /// Seed all owned declarations and every loaded initializer in source order.
    pub fn new(index: &'a ItemIndex<'p>, scope: &ProjectScope) -> Self {
        let mut this = Self::empty(index);
        for (id, entry) in index.entries.iter().enumerate() {
            if entry.source.is_none_or(|source| scope.owns(source)) {
                this.selection.own_roots.insert(entry.key.clone());
                this.add(id, Reason::Own, 0);
            }
            if matches!(entry.key, ItemKey::Body(BodyId::Initializer(_))) {
                this.add(id, Reason::Initializer, 0);
            }
        }
        this.close();
        this
    }

    /// Close an additional preparation dependency with the same authority as
    /// source reachability. Existing shared-only roots keep their abstract frame.
    pub(crate) fn extend(
        index: &'a ItemIndex<'p>,
        selection: &CheckSelection,
        extra: ItemKey,
    ) -> CheckSelection {
        Self::extend_root(index, selection, extra, Reason::SharedInference)
    }

    /// Close an additional execution or generated root with the existing authority.
    /// Existing shared-only frames stay separate from concrete execution inputs.
    pub(crate) fn extend_root(
        index: &'a ItemIndex<'p>,
        selection: &CheckSelection,
        extra: ItemKey,
        reason: Reason,
    ) -> CheckSelection {
        Self::extend_roots(index, selection, [extra], reason)
    }

    /// Close one generated batch in a single fixpoint, preserving prior abstract frames.
    pub(crate) fn extend_roots(
        index: &'a ItemIndex<'p>,
        selection: &CheckSelection,
        extra: impl IntoIterator<Item = ItemKey>,
        reason: Reason,
    ) -> CheckSelection {
        let mut this = Self::empty(index);
        this.selection.own_roots = selection.own_roots.clone();
        for (id, entry) in index.entries.iter().enumerate() {
            if let Some(reasons) = selection.reasons.get(&entry.key) {
                for reason in reasons {
                    this.add(id, *reason, usize::from(*reason == Reason::SharedInference));
                }
            }
        }
        for extra in extra {
            let id = index.lookup[&extra];
            let scope = match reason {
                Reason::SharedInference => 1,
                Reason::Generated => 2,
                _ => 0,
            };
            if scope != 1 {
                this.state.required_roots[id * 3 + scope] = true;
                this.enqueue(id * 3 + scope);
            }
            this.add(id, reason, scope);
        }
        this.close();
        this.into_selection()
    }

    /// Add an explicit, generated, or runtime root and close its dependencies.
    /// The identity must belong to this catalog; repeated additions are inert.
    pub fn require(&mut self, item: ItemKey, reason: Reason) {
        let id = self.index.lookup[&item];
        let scope = if reason == Reason::Generated { 2 } else { 0 };
        if !self.state.required_roots[id * 3 + scope] {
            self.state.required_roots[id * 3 + scope] = true;
            self.enqueue(id * 3 + scope);
        }
        self.add(id, reason, scope);
        self.close();
    }

    /// Borrow the current selection without claiming analysis coverage.
    pub fn selection(&self) -> &CheckSelection {
        &self.selection
    }

    /// Transfer the settled request without cloning its source identities.
    pub fn into_selection(mut self) -> CheckSelection {
        if self.index.entries.iter().enumerate().any(|(id, entry)| self.state.reasons[id] != 0 && matches!(&entry.declaration, index::Declaration::Method(_, m) if brass_hir::keyed_return(m.decl.ret.as_ref()))) {
            self.selection.continuation = Some(std::sync::Arc::new(continuation::Continuation::new(self.index, self.state)));
        }
        self.selection
    }

    /// Explain each unresolved edge that retained more than one possible body.
    pub fn widenings(&self) -> &[Widening] {
        &self.state.widenings
    }

    fn enqueue(&mut self, frame: usize) {
        if !self.state.queued[frame] {
            self.state.queued[frame] = true;
            self.state.pending.push_back(frame);
        }
    }

    fn add(&mut self, id: usize, reason: Reason, scope: usize) {
        let bit = 1 << reason as u8;
        let fresh = self.state.reasons[id] == 0;
        let new_reason = self.state.reasons[id] & bit == 0;
        let new_root = new_reason && matches!(reason, Reason::Own | Reason::Initializer);
        if new_reason {
            self.state.reasons[id] |= bit;
            let key = &self.index.entries[id].key;
            self.selection
                .reasons
                .entry(key.clone())
                .or_default()
                .push(reason);
            self.selection.revision += 1;
            if fresh {
                match key {
                    ItemKey::Body(body) => {
                        self.selection.body_roots.insert(body.clone());
                    }
                    ItemKey::Type(id) => {
                        self.selection.type_roots.insert(id.clone());
                    }
                }
            }
        }
        // Shared scheme preparation and generated root preparation never feed
        // their open inputs back into the concrete execution frame.
        let scope = if reason == Reason::SharedInference {
            1
        } else {
            scope
        };
        let frame = id * 3 + scope;
        if !self.state.frames[frame] || new_root {
            self.state.frames[frame] = true;
            self.enqueue(frame);
        }
        if let index::Declaration::Method(_, method) = &self.index.entries[id].declaration
            && brass_hir::keyed_return(method.decl.ret.as_ref())
        {
            let generated = id * 3 + 2;
            if !self.state.required_roots[generated] {
                self.state.required_roots[generated] = true;
                self.state.frames[generated] = true;
                self.enqueue(generated);
            }
        }
    }

    fn close(&mut self) {
        let started = cost::start();
        let certificates = self.index.certificate_time.get();
        let effects = self.index.effect_time.get();
        loop {
            if self.state.pending.is_empty() {
                let generation = self.state.inhabited.len();
                for frame in 0..self.state.frames.len() {
                    if self.state.frames[frame]
                        && self.state.revisits[frame]
                        && self.state.visited_at[frame] < generation
                    {
                        self.enqueue(frame);
                    }
                }
            }
            let Some(frame) = self.state.pending.pop_front() else {
                break;
            };
            self.state.queued[frame] = false;
            let source = frame / 3;
            let scope = frame % 3;
            let shared = scope == 1;
            let before = self.state.inhabited.len();
            let root = self.state.required_roots[frame]
                || (scope == 0
                    && self.state.reasons[source]
                        & ((1 << Reason::Own as u8) | (1 << Reason::Initializer as u8))
                        != 0);
            let edges::Dependencies {
                edges,
                causes,
                open,
                inhabited_dependent,
                ..
            } = edges::dependencies(
                self.index,
                source,
                &mut self.state.inhabited,
                root,
                self.state.open_frames[frame],
                false,
                false,
            );
            self.state.revisits[frame] = inhabited_dependent;
            self.state.visited_at[frame] = before;
            let callees: Vec<_> = edges
                .iter()
                .filter_map(|(target, reason)| {
                    (matches!(self.index.entries[*target].key, ItemKey::Body(_))
                        && *reason != Reason::SharedInference)
                        .then_some(target * 3 + scope)
                })
                .collect();
            for &callee in &callees {
                if !self.state.callers[callee].contains(&frame) {
                    self.state.callers[callee].push(frame);
                }
            }
            let mut opened = Vec::new();
            if !shared && (open || callees.iter().any(|&callee| self.state.open_frames[callee])) {
                opened.push(frame);
                opened.extend(callees);
                let mut callers = self.state.callers[frame].clone();
                callers.sort_unstable();
                opened.extend(callers.into_iter().filter(|frame| frame % 3 == scope));
            }
            for frame in opened {
                if !self.state.open_frames[frame] {
                    self.state.open_frames[frame] = true;
                    self.enqueue(frame);
                }
            }
            for (target, reason) in edges {
                if self.state.reasons[target] & (1 << reason as u8) == 0 {
                    tracing::trace!(target: "brass::item_selection",
                        source = self.index.entries[source].label,
                        destination = self.index.entries[target].label,
                        shared, open, ?reason, "item: edge");
                }
                self.add(target, reason, scope);
            }
            if before != self.state.inhabited.len() {
                let produced: Vec<_> = self
                    .state
                    .inhabited
                    .nominal
                    .iter()
                    .filter_map(|id| self.index.types.get(id).copied())
                    .collect();
                for id in produced {
                    self.add(id, Reason::ImplicitUse, scope);
                }
            }
            for cause in causes {
                if !self.state.causes[source].contains(&cause) {
                    self.state.causes[source].push(cause);
                    self.state.widenings.push(Widening {
                        source: self.index.entries[source].key.clone(),
                        cause,
                    });
                }
            }
        }
        if let Some(started) = started {
            let certificates = self.index.certificate_time.get() - certificates;
            cost::elapsed(
                "reachability",
                started
                    .elapsed()
                    .saturating_sub(certificates + self.index.effect_time.get() - effects),
            );
            cost::elapsed("certificate", certificates);
        }
    }
}
