//! Coalesced mono invalidations from the driver's merged checker stream.

use super::{LazyState, MergedChannels};
use brass_hir::Program;
use brass_parser::Span;
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

/// Refresh free-function bodies in symbol order, fixing closure allocation order.
pub(super) fn refresh_functions(
    dirty: HashSet<String>,
    lowering: &mut brass_mir::SubsetLowering,
    program: &Program,
    tables: &brass_mir::LowerTables,
    channels: &brass_mir::CheckerChannels<'_>,
) -> usize {
    let mut symbols: Vec<_> = dirty.into_iter().collect();
    symbols.sort_unstable();
    symbols
        .iter()
        .filter(|symbol| lowering.refresh_function(program, tables, symbol, channels))
        .count()
}

impl MergedChannels {
    /// Take one refresh window for the driver's single active lowering.
    pub(super) fn take_changed_inputs(&mut self) -> brass_mir::ChangedInputs {
        let next = brass_mir::ChangedInputs::since(self.changed_inputs.epoch);
        std::mem::replace(&mut self.changed_inputs, next)
    }

    /// Record candidates before consuming the delta's owned map entries.
    pub(super) fn record_changed_inputs(&mut self, delta: &brass_typeck::stream::ChannelDelta) {
        let changes = &mut self.changed_inputs;
        changes.epoch = changes
            .epoch
            .checked_add(1)
            .expect("channel epoch exhausted");
        for span in &delta.expr_types_removed {
            changes.seeds.remove(*span);
        }
        for (span, _) in &delta.expr_types {
            changes.seeds.change(*span);
        }
        for (span, seeds) in &delta.instance_seeds {
            if seeds.is_empty() {
                changes.instance_seeds.remove(*span);
            } else {
                changes.instance_seeds.change(*span);
            }
        }
        for (span, targets) in &delta.instance_dispatch {
            if targets.is_empty() {
                changes.instance_dispatch.remove(*span);
            } else {
                changes.instance_dispatch.change(*span);
                if self.keyed_dispatch.contains_key(span) {
                    changes.dispatch.remove(*span);
                }
            }
        }
        for (symbol, args, _) in &delta.instance_returns {
            changes.returns.change((symbol.clone(), args.clone()));
        }
        for key in &delta.numeric_calls_removed {
            changes.numeric_calls.remove(key.clone());
        }
        for (key, _) in &delta.numeric_calls {
            changes.numeric_calls.change(key.clone());
        }
        // These channels can change lowered bodies, so span-only mono inputs
        // cannot describe their effects without a broader dependency interface.
        changes.full_reset |= !delta.receiver_types.is_empty()
            || !delta.receiver_types_removed.is_empty()
            || !delta.receiver_owners.is_empty()
            || !delta.view_args.is_empty()
            || !delta.numeric_calls.is_empty()
            || !delta.numeric_calls_removed.is_empty()
            || !delta.field_calls.is_empty()
            || !delta.sum_views.is_empty()
            || !delta.lift_errs.is_empty()
            || !delta.fields_loops.is_empty()
            || !delta.type_names.is_empty()
            || !delta.typeof_types.is_empty()
            || !delta.typeof_types_removed.is_empty()
            || !delta.null_props.is_empty()
            || !delta.type_tests.is_empty()
            || !delta.type_tests_removed.is_empty();
    }
}

impl LazyState {
    /// Refresh the sole active lowering and expose its accumulated invalidations.
    pub(super) fn refresh_channels(
        &mut self,
        lowering: &mut brass_mir::SubsetLowering,
        call_locations: &HashMap<Span, (String, u32, u32)>,
    ) {
        self.counters.record_channel_refresh();
        let changed = self.merged.take_changed_inputs();
        lowering.refresh_instance_channels_with_changes(&self.channels(call_locations), changed);
    }
}

#[cfg(test)]
mod tests {
    use super::{MergedChannels, refresh_functions};
    use brass_hir::{InstanceCallable, InstanceKey, Type};
    use brass_parser::Span;
    use brass_typeck::stream::ChannelDelta;
    use fxhash::FxHashSet as HashSet;

    #[test]
    fn refresh_order_fixes_closure_ids_and_labels() {
        // Both owners allocate closures from one counter. Hash-table capacity and
        // insertion order must not decide which owner receives the first id.
        let ast = brass_parser::parse("fun alpha() { let f = (x) -> x + 1\n return f(1) }\nfun zeta() { let f = (x) -> x + 2\n return f(1) }\n").unwrap();
        let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty());
        let tables = brass_mir::LowerTables::new(&program);
        let channels = brass_mir::CheckerChannels {
            expr_types: &Default::default(),
            receiver_types: &Default::default(),
            receiver_owners: &Default::default(),
            view_args: &Default::default(),
            numeric_calls: &Default::default(),
            field_calls: &Default::default(),
            sum_views: &Default::default(),
            call_locations: &Default::default(),
            lift_errs: &Default::default(),
            fields_loops: &Default::default(),
            type_names: &Default::default(),
            typeof_types: &Default::default(),
            null_props: &Default::default(),
            type_tests: &Default::default(),
            keyed_dispatch: &Default::default(),
            instance_seeds: &Default::default(),
            instance_dispatch: &Default::default(),
            instance_returns: &Default::default(),
        };
        let run = |names: &[&str], capacity| {
            let mut lowering = brass_mir::SubsetLowering::new(&program, &tables, &channels);
            for symbol in ["alpha", "zeta"] {
                assert!(lowering.add_function(&program, &tables, symbol, &channels));
            }
            let mut dirty = HashSet::with_capacity_and_hasher(capacity, Default::default());
            dirty.extend(names.iter().map(|name| name.to_string()));
            assert_eq!(
                refresh_functions(dirty, &mut lowering, &program, &tables, &channels),
                2
            );
            lowering
                .mir
                .functions
                .iter()
                .map(|function| {
                    let ids: Vec<_> = function
                        .body
                        .blocks
                        .iter()
                        .flat_map(|block| &block.stmts)
                        .filter_map(|stmt| match stmt {
                            brass_mir::MirStmt::Assign(
                                _,
                                brass_mir::Rvalue::Closure { id, .. },
                            ) => Some(id.0),
                            _ => None,
                        })
                        .collect();
                    (function.symbol.clone(), ids)
                })
                .collect::<Vec<_>>()
        };
        let expected = vec![
            ("alpha".to_string(), vec![2]),
            ("zeta".to_string(), vec![3]),
        ];
        assert_eq!(run(&["zeta", "alpha"], 3), expected);
        assert_eq!(run(&["alpha", "zeta"], 128), expected);
    }

    #[test]
    fn numeric_refreshes_keep_exact_identity_and_lowering_reset() {
        let span = Span::new(10, 20);
        let mut instance = InstanceKey {
            numeric_layout: None,
            callable: InstanceCallable::Function("f".into()),
            args: vec![Type::Bool],
        };
        instance.numeric_layout = Some(std::sync::Arc::new(vec![(
            vec![(0, 1)],
            Type::Int(brass_hir::IntKind::I64),
        )]));
        let key = (span, Some(instance));
        let mut merged = MergedChannels::default();
        merged.apply_delta(ChannelDelta {
            numeric_calls: vec![(key.clone(), None)],
            ..ChannelDelta::default()
        });
        let first = merged.take_changed_inputs();
        assert!(first.numeric_calls.changed.contains(&key));
        // Numeric wrappers and creation sites can require new MIR bodies.
        assert!(first.full_reset);
        merged.apply_delta(ChannelDelta {
            numeric_calls_removed: vec![key.clone()],
            ..ChannelDelta::default()
        });
        let next = merged.take_changed_inputs();
        assert!(next.numeric_calls.removed.contains(&key));
        assert!(next.numeric_calls.changed.is_empty());
        assert!(next.full_reset);
    }

    #[test]
    fn merged_windows_report_replacements_removals_and_dispatch_fallback_loss() {
        let span = Span::new(1, 2);
        let mut merged = MergedChannels::default();
        merged.keyed_dispatch.insert(span, "shared".into());
        let key = InstanceKey {
            numeric_layout: None,
            callable: InstanceCallable::Function("f".into()),
            args: vec![Type::Bool],
        };
        merged.apply_delta(ChannelDelta {
            expr_types: vec![(span, Type::Bool)],
            instance_dispatch: vec![(span, vec![(key, "specialized".into())])],
            instance_returns: vec![("f".into(), vec![Type::Bool], Type::Str)],
            ..ChannelDelta::default()
        });
        let first = merged.take_changed_inputs();
        assert_eq!((first.base_epoch, first.epoch), (0, 1));
        assert!(first.seeds.changed.contains(&span));
        assert!(first.dispatch.removed.contains(&span));
        assert!(first.instance_dispatch.changed.contains(&span));
        assert!(
            first
                .returns
                .changed
                .contains(&("f".into(), vec![Type::Bool]))
        );
        assert!(!merged.keyed_dispatch.contains_key(&span));
        merged.apply_delta(ChannelDelta {
            expr_types_removed: vec![span],
            instance_dispatch: vec![(span, Vec::new())],
            ..ChannelDelta::default()
        });
        let next = merged.take_changed_inputs();
        assert_eq!((next.base_epoch, next.epoch), (1, 2));
        assert!(next.seeds.removed.contains(&span));
        assert!(next.instance_dispatch.removed.contains(&span));
        assert!(next.seeds.changed.is_empty());
        // A channel with effects outside these tracked inputs requires reset.
        merged.apply_delta(ChannelDelta {
            type_names: vec![(span, "Record".into())],
            ..ChannelDelta::default()
        });
        assert!(merged.take_changed_inputs().full_reset);
        // Continuation snapshots advance the epoch even with an empty delta.
        merged.apply(brass_typeck::stream::CheckEvent::KeyedReady(
            Vec::new(),
            vec![(span, "continued".into())],
            ChannelDelta::default(),
        ));
        let continuation = merged.take_changed_inputs();
        assert_eq!((continuation.base_epoch, continuation.epoch), (3, 4));
        assert!(continuation.full_reset);
        assert!(continuation.dispatch.changed.contains(&span));
        assert_eq!(
            merged.keyed_dispatch.get(&span).map(String::as_str),
            Some("continued")
        );
    }
}
