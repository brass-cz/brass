//! Execution-side checker progress and demand settlement.

use super::demand::{BatchIds, BatchOutcome, DemandBatch};
use super::{BodySpans, CheckerPause, MergedChannels, changed_inputs, trace};
use crate::render_warnings;
use brass_hir::Program;
use brass_parser::Span;
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

/// The execution side of the lazy pipeline: replays the checker thread's
/// events into the merged channel state, tracks which bodies are settled,
/// and sends the priority requests -- the demanded function's path plus the
/// concrete argument types of the call that needs it -- that pull bodies to
/// the front of the checking order.
pub(super) struct LazyState {
    /// Eligible source bodies, distinct from actual checked-body observations.
    pub(super) selected_bodies: Option<std::sync::Arc<HashSet<Span>>>,
    /// Optional auto-policy observations; absent in the default demand-only mode.
    pub(super) completion: Option<super::policy::CompletionState>,
    pub(super) counters: trace::LazyCounters,
    pub(super) events: tokio::sync::mpsc::UnboundedReceiver<brass_typeck::stream::CheckEvent>,
    pub(super) sources: brass_resolve::SourceMap,
    pub(super) merged: MergedChannels,
    pub(super) checked_fns: HashSet<String>,
    pub(super) inits_checked: usize,
    /// Every diagnostic reported so far, HELD: lazy checking ignores an
    /// error unless execution needs the body it lives in (see
    /// [`LazyState::fatal`] and [`BodySpans`]).
    pub(super) held: Vec<brass_typeck::TypeError>,
    /// Warnings are printed as soon as their body delta arrives. The set keeps
    /// terminal and generated-continuation snapshots from printing a warning
    /// already delivered by an earlier window.
    pub(super) printed_warnings: HashSet<(String, Span)>,
    /// The bodies execution needs: `main`, every demanded free function, and
    /// every method in a batch about to enter native compilation.
    /// (Top-level code needs no entry here -- its spans lie outside every
    /// body, which is always fatal.) Grows at each demand; held errors are
    /// re-judged against it at every gate.
    pub(super) needed: HashSet<String>,
    /// Tell the checker to stop at the next body boundary (the program
    /// ended; what it never executed no longer needs checking).
    pub(super) stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
    /// While set, the checker serves only demanded bodies and holds its
    /// background queue (see `Scheduler::paused`). Cleared when execution
    /// begins -- and before any wait that needs the checker to make progress
    /// of its own (a fatal confirmation, a transient-failure retry), which
    /// would otherwise wait forever on a held queue.
    pub(super) paused: std::sync::Arc<CheckerPause>,
    /// A keyed call first discovered by a body demanded after the entry gate
    /// opened requires the narrow eager fallback: reflective specialization
    /// does not run per demand.
    pub(super) needs_eager: bool,
    /// The event channel closed (the checker finished and hung up).
    pub(super) closed: bool,
    /// A delta carried channel content since the last MIR revision. Bodies
    /// lowered before it may be missing entries the checker settled later
    /// (a cross-body pinning: an init's array literal fixed by a function's
    /// `push`), so stale owners are refreshed before output is trusted.
    pub(super) dirty: bool,
    /// Free-function declaration ranges used to invalidate only lowered MIR
    /// bodies whose span-keyed channel inputs changed.
    pub(super) function_ranges: Vec<(String, usize, usize)>,
    pub(super) dirty_functions: HashSet<String>,
    /// A channel change outside every free function belongs to a method or
    /// initializer and still requires rebuilding the subset base.
    pub(super) dirty_non_functions: bool,
    /// The entry gate remains closed between first keyed discovery and the
    /// append-only continuation event.
    pub(super) awaiting_keyed: bool,
    /// Set once the initial entry gate has completed.
    pub(super) entry_open: bool,
    pub(super) generated: Vec<brass_hir::GeneratedDecl>,
    pub(super) batch_ids: BatchIds,
    /// Sent batches awaiting an explicit seal, in send order.
    pub(super) outstanding_batches: std::collections::VecDeque<u64>,
    /// The terminal event settles every outstanding batch after its effects.
    pub(super) finished: bool,
}

const DEMAND_LOOP_STALLED: &str = "internal error: lazy demand loop made no progress";

/// Enforce the demand-loop progress invariant: every retry must discover a
/// new demand, observe a requested body settle, or add a missing MIR body.
pub(super) fn demand_loop_progress(
    new_demands: usize,
    newly_settled: usize,
    supplied_bodies: usize,
) -> Result<(), &'static str> {
    if new_demands + newly_settled + supplied_bodies == 0 {
        Err(DEMAND_LOOP_STALLED)
    } else {
        Ok(())
    }
}

impl LazyState {
    /// Methods already have checked and lowered bodies when free-function
    /// demands begin. Match their MIR body identities against this batch so
    /// their held diagnostics gate native compilation too. Storage symbols
    /// distinguish identically named types in different modules.
    /// Reached certified-region functions also join needed here, before codegen.
    pub(super) fn need_monomorphized_bodies(
        &mut self,
        mir: &brass_mir::MirProgram,
        mono: &brass_engine::MonoProgram<'_>,
    ) {
        let compiled: HashSet<*const brass_mir::MirBody> = mono
            .functions
            .iter()
            .map(|f| std::ptr::from_ref(f.body))
            .collect();
        self.needed.extend(
            mir.methods
                .iter()
                .filter(|m| compiled.contains(&std::ptr::from_ref(&m.body)))
                .map(|m| format!("method:{}:{}", m.type_symbol, m.method)),
        );
        if let Some(region) = self
            .completion
            .as_ref()
            .and_then(|policy| policy.region.as_ref())
            .filter(|region| !region.is_empty())
        {
            self.needed.extend(
                mir.functions
                    .iter()
                    .filter(|f| {
                        compiled.contains(&std::ptr::from_ref(&f.body))
                            && region.contains(&f.symbol)
                    })
                    .map(|f| f.symbol.clone()),
            );
        }
    }

    /// Release the checker's background queue (idempotent). Called when
    /// execution begins, and before any wait on the checker's own progress.
    pub(super) fn resume_background(&self) {
        self.paused.resume();
    }

    pub(super) fn take(&mut self, event: brass_typeck::stream::CheckEvent) {
        use brass_typeck::stream::{BodyId, CheckEvent};
        match &event {
            CheckEvent::SelectedBodies(spans) => {
                debug_assert!(
                    self.selected_bodies
                        .as_ref()
                        .is_none_or(|old| old.is_subset(spans))
                );
                if self.selected_bodies.as_ref() != Some(spans)
                    && let Some(policy) = &mut self.completion
                {
                    policy.selection_changed();
                }
                self.selected_bodies = Some(spans.clone());
            }
            CheckEvent::ContextChecked(symbols) => {
                if let Some(policy) = &mut self.completion {
                    policy.observe_context(symbols);
                }
            }
            CheckEvent::StaticChecked(errors) => self.held.extend(errors.iter().cloned()),
            CheckEvent::ContextReady(d) | CheckEvent::BatchSettled(d) => self.absorb_delta(d),
            CheckEvent::BodyChecked(id, d) => {
                self.absorb_delta(d);
                match id {
                    BodyId::Init(_) => self.inits_checked += 1,
                    BodyId::Function(symbol) => {
                        self.checked_fns.insert(symbol.clone());
                    }
                }
            }
            CheckEvent::Finished(d, errors) => {
                self.absorb_delta(d);
                self.held.extend(errors.iter().cloned());
            }
            CheckEvent::KeyedReady(generated, _, d) => {
                self.absorb_delta(d);
                // The continuation event carries the complete final verdict;
                // replace provisional keyed-statement errors from pass one.
                self.held = d.errors.clone();
                self.generated.extend(generated.iter().cloned());
                self.awaiting_keyed = false;
            }
        }
        let (seal, finished) = match &event {
            CheckEvent::SelectedBodies(_)
            | CheckEvent::StaticChecked(_)
            | CheckEvent::ContextChecked(_) => (None, false),
            CheckEvent::ContextReady(d)
            | CheckEvent::BodyChecked(_, d)
            | CheckEvent::BatchSettled(d)
            | CheckEvent::KeyedReady(_, _, d) => (d.settles_batch, false),
            CheckEvent::Finished(d, _) => (d.settles_batch, true),
        };
        self.merged.apply(event);
        if let Some(id) = seal {
            debug_assert_eq!(
                self.outstanding_batches.front(),
                Some(&id),
                "out-of-order batch seal"
            );
            self.outstanding_batches.pop_front();
        }
        if finished {
            self.finished = true;
            self.outstanding_batches.clear();
        }
    }

    /// Track a delta: errors are held for span-attributed judgement, channel
    /// content marks the current lowering stale.
    pub(super) fn absorb_delta(&mut self, d: &brass_typeck::stream::ChannelDelta) {
        self.held.extend(d.errors.iter().cloned());
        self.emit_warnings(&d.warnings);
        if !d.keyed_calls.is_empty() {
            if let Some(policy) = &mut self.completion {
                policy.block();
            }
            if self.entry_open {
                // Specialization does not run per demand. Before execution
                // this flag reaches `finish_eagerly`; an already-running
                // program fails without replaying prior side effects.
                self.needs_eager = true;
            } else {
                self.awaiting_keyed = true;
            }
        }
        self.dirty |= !d.expr_types.is_empty()
            || !d.expr_types_removed.is_empty()
            || !d.view_args.is_empty()
            || !d.numeric_calls.is_empty()
            || !d.numeric_calls_removed.is_empty()
            || !d.lift_errs.is_empty()
            || !d.null_props.is_empty()
            || !d.fields_loops.is_empty()
            || !d.instance_fields.is_empty()
            || !d.sum_views.is_empty()
            || !d.type_names.is_empty()
            || !d.typeof_types.is_empty()
            || !d.typeof_types_removed.is_empty()
            || !d.type_tests.is_empty()
            || !d.type_tests_removed.is_empty();
        let mut mark = |span: Span| {
            if let Some((symbol, _, _)) = self
                .function_ranges
                .iter()
                .find(|(_, lo, hi)| *lo <= span.lo && span.lo < *hi)
            {
                self.dirty_functions.insert(symbol.clone());
            } else {
                self.dirty_non_functions = true;
            }
        };
        d.expr_types.iter().for_each(|(span, _)| mark(*span));
        d.expr_types_removed.iter().for_each(|span| mark(*span));
        d.view_args.iter().for_each(|span| mark(*span));
        d.numeric_calls
            .iter()
            .for_each(|((span, _), _)| mark(*span));
        d.numeric_calls_removed
            .iter()
            .for_each(|(span, _)| mark(*span));
        d.lift_errs.iter().for_each(|span| mark(*span));
        d.null_props.iter().for_each(|span| mark(*span));
        d.fields_loops.iter().for_each(|(span, _)| mark(*span));
        d.instance_fields.iter().for_each(|(span, _)| mark(*span));
        d.sum_views.iter().for_each(|(span, _)| mark(*span));
        d.type_names.iter().for_each(|(span, _)| mark(*span));
        d.typeof_types.iter().for_each(|(span, _)| mark(*span));
        d.typeof_types_removed.iter().for_each(|span| mark(*span));
        d.type_tests.iter().for_each(|(span, _)| mark(*span));
        d.type_tests_removed.iter().for_each(|span| mark(*span));
    }

    pub(super) fn emit_warnings(&mut self, warnings: &[brass_typeck::TypeError]) {
        let fresh: Vec<(String, Span)> = warnings
            .iter()
            .filter_map(|warning| {
                let key = (warning.message.clone(), warning.span);
                self.printed_warnings.insert(key.clone()).then_some(key)
            })
            .collect();
        for line in render_warnings(&fresh, &self.sources) {
            eprintln!("{line}");
        }
    }

    /// Refresh only stale free-function MIR. `false` asks the caller to rebuild
    /// the base because a method or initializer channel changed.
    pub(super) fn refresh_lowering(
        &mut self,
        lowering: &mut brass_mir::SubsetLowering,
        program: &Program,
        tables: &brass_mir::LowerTables,
        call_locations: &HashMap<Span, (String, u32, u32)>,
    ) -> bool {
        if self.dirty_non_functions {
            return false;
        }
        let dirty = std::mem::take(&mut self.dirty_functions);
        let channels = self.channels(call_locations);
        let refreshed =
            changed_inputs::refresh_functions(dirty, lowering, program, tables, &channels);
        tracing::debug!(
            target: "brass::perf",
            count = refreshed,
            "lazy: lowering refresh"
        );
        self.dirty = false;
        true
    }

    pub(super) fn pump_blocking(&mut self) {
        match self.events.blocking_recv() {
            Some(event) => self.take(event),
            None => self.closed = true,
        }
    }

    /// Absorb everything already queued without blocking.
    pub(super) fn pump_pending(&mut self) {
        while let Ok(event) = self.events.try_recv() {
            self.take(event);
        }
    }

    /// The held diagnostics execution cannot ignore: those inside a NEEDED
    /// body and those inside no known body at all (top-level statements,
    /// declarations, spanless internal reports). Sorted and deduplicated
    /// like the eager report.
    pub(super) fn fatal(&self, bodies: &BodySpans) -> Vec<(String, Span)> {
        let mut out: Vec<(String, Span)> = self
            .held
            .iter()
            .filter(|e| match bodies.owner(e.span) {
                Some(owner) => self.needed.contains(owner),
                None => true,
            })
            .map(|e| (e.message.clone(), e.span))
            .collect();
        out.sort_by(|a, b| (a.1.lo, &a.0).cmp(&(b.1.lo, &b.0)));
        out.dedup();
        out
    }

    /// Every held diagnostic, needed or not: once the checker has finished,
    /// the complete verdict -- the report of every confirmed failure, and of
    /// one the span attribution cannot explain (a mono rejection against the
    /// checker's final state).
    pub(super) fn held_all(&self) -> Vec<(String, Span)> {
        let mut out: Vec<(String, Span)> = self
            .held
            .iter()
            .map(|e| (e.message.clone(), e.span))
            .collect();
        out.sort_by(|a, b| (a.1.lo, &a.0).cmp(&(b.1.lo, &b.0)));
        out.dedup();
        out
    }

    /// Block until the entry is settled: every module initializer and (when
    /// the program has one) `main`. False means the checker hung up (or
    /// requested the eager fallback) before settling them; held diagnostics are the caller's
    /// judgement to make.
    pub(super) fn wait_gate(&mut self, inits: usize, entry: Option<&str>) -> bool {
        let settled = |s: &Self| {
            s.inits_checked >= inits
                && entry.is_none_or(|symbol| s.checked_fns.contains(symbol))
                && !s.awaiting_keyed
        };
        while !self.needs_eager && !self.closed && !settled(self) {
            if self.awaiting_keyed {
                self.resume_background();
            }
            self.pump_blocking();
        }
        !self.needs_eager && settled(self)
    }

    /// Mark every member needed and wait for the sent batch's explicit seal.
    /// Already-checked batches complete without sending a priority request.
    pub(super) fn settle(&mut self, batch: DemandBatch) -> BatchOutcome {
        let started = std::time::Instant::now();
        // An interrupted stream can retain unsealed ids under its existing
        // symbol-based verdict. Live settlements must consume their seal first.
        debug_assert!(
            self.outstanding_batches.is_empty() || self.closed || self.needs_eager,
            "live settlement started with an outstanding batch"
        );
        if !self.closed
            && !self.needs_eager
            && batch
                .members
                .iter()
                .any(|demand| !self.checked_fns.contains(&demand.symbol))
        {
            // These queued background events precede any new request's seal.
            // Absorb their full deltas before deciding which requests remain.
            // An already-checked batch must keep its no-read path: draining it
            // could print warnings from otherwise unobserved background bodies.
            self.pump_pending();
        }
        let mut pending = Vec::new();
        let mut requests = Vec::new();
        for demand in batch.members {
            self.needed.insert(demand.symbol.clone());
            if !self.checked_fns.contains(&demand.symbol) {
                pending.push(demand.symbol.clone());
                requests.push(brass_typeck::stream::BodyRequest {
                    symbol: demand.symbol,
                    type_args: demand.type_args,
                    batch: batch.id,
                });
            }
        }
        let new_requests = requests.len();
        if new_requests != 0 && !self.finished {
            self.outstanding_batches.push_back(batch.id);
            self.paused.request(requests);
        }
        while !self.needs_eager && !self.closed && self.outstanding_batches.contains(&batch.id) {
            self.pump_blocking();
        }
        // A closed stream without Finished retains the symbol-based verdict
        // of an interrupted analysis; it is not a new protocol failure.
        let complete = !self.needs_eager
            && (!self.outstanding_batches.contains(&batch.id)
                || (self.closed && pending.iter().all(|s| self.checked_fns.contains(s))));
        let newly_settled = pending
            .iter()
            .filter(|s| self.checked_fns.contains(*s))
            .count();
        tracing::debug!(
            target: "brass::perf",
            count = pending.len(),
            elapsed_ms = started.elapsed().as_secs_f64() * 1000.0,
            "lazy: demand batch settled"
        );
        self.counters.record_demand(new_requests, started.elapsed());
        if let Some(policy) = &mut self.completion {
            policy.settled(new_requests, started.elapsed());
        }
        BatchOutcome {
            complete,
            new_requests,
            newly_settled,
        }
    }

    /// The merged channel state as the lowering bundle. Call locations are
    /// computed by the executor from its own module ASTs, not streamed.
    pub(super) fn channels<'a>(
        &'a self,
        call_locations: &'a HashMap<Span, (String, u32, u32)>,
    ) -> brass_mir::CheckerChannels<'a> {
        brass_mir::CheckerChannels {
            selected_bodies: self.selected_bodies.as_deref(),
            expr_types: &self.merged.expr_types,
            receiver_types: &self.merged.receiver_types,
            receiver_owners: &self.merged.receiver_owners,
            view_args: &self.merged.view_args,
            numeric_calls: &self.merged.numeric_calls,
            field_calls: &self.merged.field_calls,
            sum_views: &self.merged.sum_views,
            call_locations,
            lift_errs: &self.merged.lift_errs,
            fields_loops: &self.merged.fields_loops,
            instance_fields: &self.merged.instance_fields,
            type_names: &self.merged.type_names,
            typeof_types: &self.merged.typeof_types,
            null_props: &self.merged.null_props,
            type_tests: &self.merged.type_tests,
            keyed_dispatch: &self.merged.keyed_dispatch,
            instance_seeds: &self.merged.instance_seeds,
            instance_dispatch: &self.merged.instance_dispatch,
            instance_returns: &self.merged.instance_returns,
        }
    }
}
