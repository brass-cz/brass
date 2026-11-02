//! Merged checker channels and cumulative delta replay.

use brass_parser::Span;
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

/// The main-thread accumulation of the checker thread's event stream: the
/// channels [`Checked`] carries except `call_locations` (which the executor
/// computes itself, see [`super::LazyState::channels`]), built by replaying channel
/// deltas as they arrive (removals first -- a delta never removes and
/// re-adds one span). Generated continuation deltas overwrite by span like
/// ordinary body deltas.
#[derive(Default)]
pub(super) struct MergedChannels {
    pub(super) changed_inputs: brass_mir::ChangedInputs,
    pub(super) expr_types: HashMap<Span, brass_hir::Type>,
    pub(super) receiver_types: HashMap<Span, brass_hir::Type>,
    pub(super) receiver_owners: HashMap<Span, Vec<brass_hir::Type>>,
    /// Checker-reported instance returns of demanded UNANNOTATED bodies,
    /// keyed by `(symbol, argument types)`: the runtime-deferral contracts
    /// `monomorphize_entry_with_returns` compiles call sites against.
    pub(super) instance_returns: HashMap<(String, Vec<brass_hir::Type>), brass_hir::Type>,
    pub(super) view_args: HashSet<Span>,
    pub(super) numeric_calls: brass_hir::NumericCalls,
    pub(super) field_calls: HashMap<Span, Option<Vec<brass_hir::Type>>>,
    pub(super) sum_views: HashMap<Span, brass_hir::Type>,
    pub(super) lift_errs: HashSet<Span>,
    pub(super) fields_loops: HashMap<Span, Vec<String>>,
    /// Field lists for loops whose callable instances disagree.
    pub(super) instance_fields: brass_hir::InstanceChannel<Vec<String>>,
    pub(super) type_names: HashMap<Span, String>,
    pub(super) typeof_types: HashMap<Span, brass_hir::Type>,
    pub(super) null_props: HashSet<Span>,
    pub(super) type_tests: HashMap<Span, brass_hir::Type>,
    pub(super) keyed_dispatch: HashMap<Span, String>,
    pub(super) instance_seeds: brass_hir::InstanceChannel<brass_hir::Type>,
    pub(super) instance_dispatch: brass_hir::InstanceChannel<String>,
}

impl MergedChannels {
    pub(super) fn apply(&mut self, event: brass_typeck::stream::CheckEvent) {
        use brass_typeck::stream::CheckEvent;
        match event {
            // Diagnostics are held by `LazyState::take`; only channel content
            // is merged here.
            CheckEvent::SelectedBodies(_)
            | CheckEvent::StaticChecked(_)
            | CheckEvent::ContextChecked(_) => {}
            CheckEvent::ContextReady(d)
            | CheckEvent::BatchSettled(d)
            | CheckEvent::BodyChecked(_, d)
            | CheckEvent::Finished(d, _) => self.apply_delta(d),
            CheckEvent::KeyedReady(_, dispatch, d) => {
                self.apply_delta(d);
                self.changed_inputs.full_reset = true;
                for (span, _) in &dispatch {
                    self.changed_inputs.dispatch.change(*span);
                }
                self.keyed_dispatch.extend(dispatch);
            }
        }
    }

    pub(super) fn apply_delta(&mut self, d: brass_typeck::stream::ChannelDelta) {
        self.record_changed_inputs(&d);
        for s in &d.expr_types_removed {
            self.expr_types.remove(s);
        }
        for s in &d.receiver_types_removed {
            self.receiver_types.remove(s);
        }
        for s in &d.typeof_types_removed {
            self.typeof_types.remove(s);
        }
        for s in &d.type_tests_removed {
            self.type_tests.remove(s);
        }
        self.expr_types.extend(d.expr_types);
        for (span, seeds) in d.instance_seeds {
            if seeds.is_empty() {
                self.instance_seeds.remove(&span);
            } else {
                self.instance_seeds
                    .insert(span, seeds.into_iter().collect());
            }
        }
        for (span, targets) in d.instance_dispatch {
            if targets.is_empty() {
                self.instance_dispatch.remove(&span);
            } else {
                self.keyed_dispatch.remove(&span);
                self.instance_dispatch
                    .insert(span, targets.into_iter().collect());
            }
        }
        self.receiver_types.extend(d.receiver_types);
        self.receiver_owners.extend(d.receiver_owners);
        for (symbol, args, ret) in d.instance_returns {
            self.instance_returns.insert((symbol, args), ret);
        }
        self.view_args.extend(d.view_args);
        for key in d.numeric_calls_removed {
            self.numeric_calls.remove(&key);
        }
        self.numeric_calls.extend(d.numeric_calls);
        self.field_calls.extend(d.field_calls);
        self.sum_views.extend(d.sum_views);
        self.lift_errs.extend(d.lift_errs);
        self.fields_loops.extend(d.fields_loops);
        for (span, entries) in d.instance_fields {
            if entries.is_empty() {
                self.instance_fields.remove(&span);
            } else {
                self.instance_fields
                    .insert(span, entries.into_iter().collect());
            }
        }
        self.type_names.extend(d.type_names);
        self.typeof_types.extend(d.typeof_types);
        self.type_tests.extend(d.type_tests);
        self.null_props.extend(d.null_props);
    }
}
