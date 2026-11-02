//! Optional completion of a live checker after a sustained runtime demand cascade.

use std::time::Duration;

use brass_hir::Program;
use brass_mir::LoweringRegion;
use fxhash::FxHashSet as HashSet;

use super::{LazyState, region::RegionGraph};

/// Require sustained demand before draining: 32 resolves and batches separate
/// the inference/deep chains from short czpm help/run paths in the tuning workloads.
const MIN_RUNTIME_CASCADE: u32 = 32;

/// Allow for refresh/mono savings even when settlement finds an already checked
/// body. The 250 us floor was tuned on the inference and deep-chain workloads.
const BATCH_SAVINGS_FLOOR: Duration = Duration::from_micros(250);

/// Bound cold work relative to observed demand. Twice the resolver count limits
/// draining large unused libraries while admitting the measured chain cascades.
const MAX_UNCHECKED_PER_RESOLVE: usize = 2;

/// Seed the remaining-check estimate before a requested body supplies a wait.
/// The 100 us estimate is below the tuned per-batch allowance; the cascade and
/// cold-work guards still prevent an unmeasured short run from draining.
const INITIAL_RECENT_CHECK: Duration = Duration::from_micros(100);

/// How the driver obtains checked bodies from its one checker stream.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LazyPolicy {
    /// Settle only explicit executor demands.
    Demand,
    /// Resume the same checker and wait for its terminal event.
    Completing,
    /// The terminal event has supplied final diagnostics for a closed region.
    Complete,
}

/// Measured demand-cascade inputs; tests inject durations without sleeping.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct PolicyInputs {
    /// Settled demand batches since native entry.
    pub retries: u32,
    /// Cumulative time spent settling those batches.
    pub demand_wait: Duration,
    /// Last observed wait per newly requested body that settled.
    pub recent_check: Duration,
    /// Free functions not yet reported checked by this stream.
    pub unchecked_bodies: usize,
    /// Resolver entries since native entry, excluding spawn precompilation.
    pub runtime_resolves: u32,
}

/// Choose a monotonic policy transition from observed demand work.
pub(crate) trait CostModel {
    /// Return the next policy without running the checker or reading the clock.
    fn next(&self, current: LazyPolicy, inputs: &PolicyInputs) -> LazyPolicy;
}

/// Require sustained runtime demand and a bounded remaining check estimate.
pub(crate) struct DefaultCostModel;

impl CostModel for DefaultCostModel {
    fn next(&self, current: LazyPolicy, inputs: &PolicyInputs) -> LazyPolicy {
        if current != LazyPolicy::Demand {
            return current;
        }
        // A short entry or a large cold library stays demand-driven. The small
        // per-batch floor accounts for refresh/mono work even when checking has
        // already finished in the background and settlement itself is cheap.
        let saved = inputs.demand_wait.max(BATCH_SAVINGS_FLOOR * inputs.retries);
        let remaining = inputs
            .recent_check
            .saturating_mul(u32::try_from(inputs.unchecked_bodies).unwrap_or(u32::MAX));
        if inputs.runtime_resolves >= MIN_RUNTIME_CASCADE
            && inputs.retries >= MIN_RUNTIME_CASCADE
            && inputs.unchecked_bodies
                <= inputs.runtime_resolves as usize * MAX_UNCHECKED_PER_RESOLVE
            && remaining <= saved
        {
            LazyPolicy::Completing
        } else {
            current
        }
    }
}

/// Auto-only observations and the region certified by a completed stream.
pub(super) struct CompletionState {
    /// Current policy, changed only at frontier boundaries.
    mode: LazyPolicy,
    /// Measurements accumulated after native entry.
    inputs: PolicyInputs,
    /// Native execution has started; startup and spawn work are not cascade evidence.
    entered: bool,
    /// Syntax or observed discovery forbids draining ahead of execution.
    blocked: bool,
    /// Context-seeded passes that the background queue will skip.
    checked_context: HashSet<String>,
    /// Cached reference graph, built only once a runtime cascade is observed.
    graph: Option<RegionGraph>,
    /// Bodies whose diagnostics and dependency closure are final.
    pub(super) region: Option<LoweringRegion>,
}

impl CompletionState {
    /// Parse the completion policy: `off` disables automatic completion;
    /// `auto`, an absent value, and unknown values select the default, auto.
    pub(super) fn enabled() -> bool {
        std::env::var("BRASS_LAZY_COMPLETE").as_deref() != Ok("off")
    }
    /// Allocate observations when the environment selects automatic completion.
    pub(super) fn from_env() -> Option<Self> {
        Self::enabled().then_some(Self {
            mode: LazyPolicy::Demand,
            inputs: PolicyInputs {
                recent_check: INITIAL_RECENT_CHECK,
                ..PolicyInputs::default()
            },
            entered: false,
            blocked: false,
            checked_context: HashSet::default(),
            graph: None,
            region: None,
        })
    }

    /// Observe context metadata without changing ordinary checked-body settlement.
    pub(super) fn observe_context(&mut self, symbols: &[String]) {
        self.checked_context.extend(symbols.iter().cloned());
    }

    /// New eligible bodies invalidate the warning and region screen. A selection
    /// published during a drain cannot receive a certificate from the old graph.
    pub(super) fn selection_changed(&mut self) {
        self.graph = None;
        self.blocked |= self.mode != LazyPolicy::Demand;
    }

    /// A keyed discovery cannot be brought forward by draining this stream.
    pub(super) fn block(&mut self) {
        self.blocked = true;
    }

    /// Record runtime settlement cost without changing ordinary demand counters.
    pub(super) fn settled(&mut self, requested: usize, elapsed: Duration) {
        if self.entered {
            self.inputs.retries += 1;
            self.inputs.demand_wait += elapsed;
            if requested != 0 {
                self.inputs.recent_check = elapsed / requested as u32;
            }
        }
    }
}

impl LazyState {
    /// Open cascade observations at the existing startup-summary boundary.
    pub(super) fn begin_execution(&mut self) {
        if let Some(policy) = &mut self.completion {
            policy.entered = true;
        }
        self.counters.emit_startup();
    }

    /// Observe a resolver entry only for the optional cost model.
    pub(super) fn observe_resolve(&mut self) {
        if let Some(policy) = &mut self.completion
            && policy.entered
        {
            policy.inputs.runtime_resolves += 1;
        }
    }

    /// At a frontier boundary, optionally drain the same checker to `Finished`.
    /// No events are consumed in off mode. Regions require terminal diagnostics;
    /// an interrupted or keyed stream never receives a partial certificate.
    /// True supplies a new region to this runtime frontier exactly once. The
    /// model cannot switch before native entry, where base rebuilds are allowed.
    pub(super) fn maybe_complete(&mut self, program: &Program) -> bool {
        let Some(policy) = &mut self.completion else {
            return false;
        };
        if policy.blocked
            || policy.mode != LazyPolicy::Demand
            || policy.inputs.runtime_resolves < MIN_RUNTIME_CASCADE
            || policy.inputs.retries < MIN_RUNTIME_CASCADE
        {
            return false;
        }
        if policy.graph.is_none() {
            let completed = policy
                .checked_context
                .union(&self.checked_fns)
                .cloned()
                .collect();
            let graph = RegionGraph::new(program, &completed, self.selected_bodies.as_deref());
            if !graph.can_drain() {
                tracing::debug!(target: "brass::perf", "lazy: policy preserves discovery timing");
                policy.blocked = true;
                return false;
            }
            policy.graph = Some(graph);
        }
        // Already-checked demands do not otherwise consume queued progress.
        // The syntax guard proved these events cannot move warning/keyed output;
        // fold their revisions into this frontier before estimating work left.
        self.pump_pending();
        let policy = self.completion.as_mut().expect("auto observations");
        if policy.graph.is_none() || policy.blocked {
            return false;
        }
        policy.inputs.unchecked_bodies = program
            .functions
            .iter()
            .filter(|(s, f)| {
                self.selected_bodies
                    .as_ref()
                    .is_none_or(|spans| spans.contains(&f.decl.span))
                    && !self.checked_fns.contains(*s)
                    && !policy.checked_context.contains(*s)
            })
            .count();
        tracing::debug!(target: "brass::perf", resolves = policy.inputs.runtime_resolves,
            retries = policy.inputs.retries, unchecked = policy.inputs.unchecked_bodies,
            recent_check_us = policy.inputs.recent_check.as_micros(),
            wait_us = policy.inputs.demand_wait.as_micros(), "lazy: policy inputs");
        if DefaultCostModel.next(policy.mode, &policy.inputs) != LazyPolicy::Completing {
            return false;
        }
        let resolves = policy.inputs.runtime_resolves;
        let retries = policy.inputs.retries;
        policy.mode = LazyPolicy::Completing;
        tracing::debug!(target: "brass::perf", phase = "runtime", resolves, retries,
            unchecked = policy.inputs.unchecked_bodies, "lazy: policy completing");
        let started = std::time::Instant::now();
        self.resume_background();
        while !self.finished && !self.closed && !self.needs_eager {
            self.pump_blocking();
        }
        if self.finished
            && !self.needs_eager
            && !self.awaiting_keyed
            && self
                .completion
                .as_ref()
                .is_some_and(|policy| !policy.blocked && policy.graph.is_some())
        {
            let graph = self
                .completion
                .as_mut()
                .expect("auto observations")
                .graph
                .take()
                .expect("screened references");
            let region = graph.certify(program, self);
            tracing::debug!(target: "brass::perf", phase = "runtime", resolves,
                bodies = region.len(), elapsed_ms = started.elapsed().as_secs_f64() * 1000.0,
                "lazy: policy complete");
            let policy = self.completion.as_mut().expect("auto observations");
            policy.mode = LazyPolicy::Complete;
            policy.region = Some(region);
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::{CostModel, DefaultCostModel, LazyPolicy, PolicyInputs};
    use std::time::Duration;

    /// Completion wakes the existing paused checker and certifies only its terminal event.
    #[test]
    fn completing_waits_for_the_same_stream_to_finish() {
        let (mut lazy, mut requests) = crate::lazy::tests::state(vec![]);
        let (events, receiver) = tokio::sync::mpsc::unbounded_channel();
        lazy.events = receiver;
        lazy.completion = Some(super::CompletionState {
            mode: LazyPolicy::Demand,
            inputs: PolicyInputs {
                retries: 32,
                runtime_resolves: 32,
                ..PolicyInputs::default()
            },
            entered: true,
            blocked: false,
            checked_context: Default::default(),
            graph: None,
            region: None,
        });
        let checker = std::thread::spawn(move || {
            assert!(matches!(requests.blocking_recv(), Some(None)));
            events
                .send(brass_typeck::stream::CheckEvent::Finished(
                    Default::default(),
                    vec![],
                ))
                .unwrap();
        });
        let (program, errors) = brass_hir::lower(&[]);
        assert!(errors.is_empty());
        assert!(lazy.maybe_complete(&program));
        checker.join().unwrap();
        assert!(lazy.finished);
        let policy = lazy.completion.as_ref().unwrap();
        assert_eq!(policy.mode, LazyPolicy::Complete);
        assert!(policy.region.as_ref().unwrap().is_empty());
        assert!(
            !lazy.maybe_complete(&program),
            "a certificate is supplied once"
        );
        assert!(lazy.needed.is_empty());
    }

    /// A newly selected body must be screened even if an earlier graph allowed draining.
    #[test]
    fn selection_growth_invalidates_cached_preflight() {
        let (mut lazy, _) = crate::lazy::tests::state(vec![]);
        let (program, _) = brass_hir::lower(&[]);
        lazy.completion = Some(super::CompletionState {
            mode: LazyPolicy::Demand,
            inputs: PolicyInputs::default(),
            entered: true,
            blocked: false,
            checked_context: Default::default(),
            graph: Some(super::RegionGraph::new(&program, &Default::default(), None)),
            region: None,
        });
        lazy.take(brass_typeck::stream::CheckEvent::SelectedBodies(
            Default::default(),
        ));
        let policy = lazy.completion.as_ref().unwrap();
        assert!(policy.graph.is_none());
        assert!(!policy.blocked);
        assert!(!lazy.finished);
    }

    /// Short paths, cold libraries and expensive remaining checks must not switch.
    #[test]
    fn completion_requires_a_sustained_affordable_runtime_cascade() {
        let cascade = PolicyInputs {
            retries: 64,
            runtime_resolves: 64,
            demand_wait: Duration::from_millis(64),
            recent_check: Duration::from_millis(1),
            unchecked_bodies: 32,
        };
        assert_eq!(
            DefaultCostModel.next(LazyPolicy::Demand, &cascade),
            LazyPolicy::Completing
        );
        for input in [
            PolicyInputs {
                runtime_resolves: 0,
                ..cascade
            },
            PolicyInputs {
                retries: 2,
                runtime_resolves: 2,
                ..cascade
            },
            PolicyInputs {
                unchecked_bodies: 1000,
                ..cascade
            },
            PolicyInputs {
                recent_check: Duration::from_secs(1),
                ..cascade
            },
        ] {
            assert_eq!(
                DefaultCostModel.next(LazyPolicy::Demand, &input),
                LazyPolicy::Demand
            );
        }
        for current in [LazyPolicy::Completing, LazyPolicy::Complete] {
            assert_eq!(
                DefaultCostModel.next(current, &PolicyInputs::default()),
                current
            );
        }
    }
}
