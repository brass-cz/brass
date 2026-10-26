//! Consume one settled demand set against a single checker-channel snapshot.

use brass_hir::Program;
use brass_mir::{ChangedInputs, LowerTables, SubsetLowering};
use brass_parser::Span;
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use super::LazyState;
use super::changed_inputs::refresh_functions;
use super::demand::Demand;

/// Bodies and MIR revisions consumed together before the next mono pass.
/// Only explicit mono demands enter `added`; a returned contract keeps a
/// contract-only demand deferred. No static callees are discovered here.
#[derive(Default)]
pub(crate) struct LoweringFrontier {
    added: Vec<String>,
    dirty: HashSet<String>,
    dirty_non_functions: bool,
}

impl LoweringFrontier {
    /// Capture settled demands and their dirty free-function owners. The caller
    /// authorizes absent-contract bodies only for runtime's demand rule or a
    /// startup retry proven to have the same missing result.
    pub(super) fn settled(
        demands: impl IntoIterator<Item = Demand>,
        lazy: &mut LazyState,
        lower_absent_contracts: bool,
    ) -> Self {
        let mut added: Vec<_> = demands
            .into_iter()
            .filter_map(|demand| {
                (demand.needs_body
                    || (lower_absent_contracts
                        && !lazy
                            .merged
                            .instance_returns
                            .contains_key(&(demand.symbol.clone(), demand.type_args))))
                .then_some(demand.symbol)
            })
            .collect();
        added.sort_unstable();
        added.dedup();
        Self {
            added,
            dirty: std::mem::take(&mut lazy.dirty_functions),
            dirty_non_functions: std::mem::take(&mut lazy.dirty_non_functions),
        }
    }

    /// Number of missing bodies this frontier will supply; used by the retry
    /// progress gate before consuming the frontier.
    pub(super) fn supplied_bodies(&self, lowering: &SubsetLowering) -> usize {
        self.added
            .iter()
            .filter(|symbol| !lowering.is_lowered(symbol))
            .count()
    }

    /// Refresh channels once, then append demanded bodies in symbol order.
    /// MIR edits force a mono-session reset even when the channel epoch is
    /// unchanged. Non-function revisions remain dirty for the base rebuild
    /// gate; changes absorbed after this call belong to the next revision.
    pub(super) fn apply(
        mut self,
        lowering: &mut SubsetLowering,
        lazy: &mut LazyState,
        program: &Program,
        tables: &LowerTables,
        call_locations: &HashMap<Span, (String, u32, u32)>,
    ) -> ChangedInputs {
        let new_region = lazy.maybe_complete(program);
        self.dirty.extend(std::mem::take(&mut lazy.dirty_functions));
        lazy.dirty_non_functions |= self.dirty_non_functions;
        let channels = lazy.channels(call_locations);
        refresh_functions(self.dirty, lowering, program, tables, &channels);
        lazy.dirty = lazy.dirty_non_functions;
        lazy.refresh_channels(lowering, call_locations);
        let channels = lazy.channels(call_locations);
        let mut added = self
            .added
            .iter()
            .filter(|symbol| lowering.add_function(program, tables, symbol, &channels))
            .count();
        if new_region
            && let Some(region) = lazy
                .completion
                .as_ref()
                .and_then(|policy| policy.region.as_ref())
        {
            added += lowering.add_region(region, program, tables, &channels);
        }
        lazy.counters.record_lowering_appends(added);
        lowering.finish_changes()
    }
}

/// A checker batch plus repeat demands whose bodies were withheld for contracts.
/// Diagnostic gates inspect `members` before consuming any bodies for lowering.
pub(super) struct SettledDemands {
    pub(super) members: Vec<Demand>,
    pub(super) outcome: super::demand::BatchOutcome,
    repeated: Vec<Demand>,
    runtime: bool,
}

impl SettledDemands {
    /// Consume the gated batch with the latest return contracts and revisions.
    pub(super) fn into_lowering(self, lazy: &mut LazyState) -> LoweringFrontier {
        // Absence of one contract alone does not prove the whole pass repeats:
        // another revised input or newly supplied body could change which sites
        // are live. Fold a startup retry only when its MIR, channels and return
        // inputs are all unchanged and every demand is still contract-only.
        let changes = &lazy.merged.changed_inputs;
        let unchanged = !lazy.dirty
            && *changes
                == ChangedInputs {
                    base_epoch: changes.base_epoch,
                    epoch: changes.epoch,
                    ..ChangedInputs::default()
                };
        let same_missing = unchanged
            && self.repeated.is_empty()
            && self.members.iter().all(|demand| {
                !demand.needs_body
                    && !lazy
                        .merged
                        .instance_returns
                        .contains_key(&(demand.symbol.clone(), demand.type_args.clone()))
            });
        LoweringFrontier::settled(
            self.repeated.into_iter().chain(self.members),
            lazy,
            self.runtime || same_missing,
        )
    }
}

/// Settle the missing bodies of one mono stop. Startup remembers contract-only
/// demands across passes; a repeat explicitly needs its withheld body. Runtime
/// stops send every still-missing symbol, including already-checked members.
pub(super) fn settle_demands(
    demands: Vec<(String, Vec<brass_hir::Type>, bool)>,
    program: &Program,
    lowering: &SubsetLowering,
    lazy: &mut LazyState,
    demanded: Option<&[String]>,
) -> SettledDemands {
    let mut frontier = super::demand::DemandFrontier::default();
    let mut repeated = Vec::new();
    for (symbol, type_args, needs_body) in demands {
        if !program.functions.contains_key(&symbol) || lowering.is_lowered(&symbol) {
            continue;
        }
        if demanded.is_some_and(|previous| previous.contains(&symbol)) {
            repeated.push(Demand {
                symbol,
                type_args,
                needs_body: true,
            });
        } else {
            frontier.push(Demand {
                symbol,
                type_args,
                needs_body,
            });
        }
    }
    let batch = frontier.seal(&mut lazy.batch_ids);
    let members = batch
        .as_ref()
        .map(|batch| batch.members.clone())
        .unwrap_or_default();
    let outcome = batch.map(|batch| lazy.settle(batch)).unwrap_or_default();
    SettledDemands {
        members,
        outcome,
        repeated,
        runtime: demanded.is_none(),
    }
}
