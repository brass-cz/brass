//! Lazy driver coordination tests.

use super::{CheckerCleanup, CheckerPause, demand_loop_progress};

#[test]
fn demand_loop_rejects_a_retry_without_state_change() {
    // This is the synthetic stuck round: mono returned a missing body, but
    // the driver neither queued, settled, nor lowered anything before retry.
    let error = demand_loop_progress(0, 0, 0).expect_err("stuck retry must abort");
    assert!(error.contains("demand loop made no progress"));
}

#[test]
fn checker_cleanup_wakes_a_paused_checker() {
    // Every post-startup return must make the request wait observable.
    let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let (requests, mut receiver) =
        tokio::sync::mpsc::unbounded_channel::<Option<Vec<brass_typeck::stream::BodyRequest>>>();
    let paused = std::sync::Arc::new(CheckerPause {
        paused: std::sync::atomic::AtomicBool::new(true),
        requests,
    });
    drop(CheckerCleanup {
        stop: stop.clone(),
        paused,
    });

    assert!(stop.load(std::sync::atomic::Ordering::Relaxed));
    assert!(matches!(receiver.try_recv(), Ok(None)));
}

use super::demand::{BatchIds, Demand, DemandFrontier};
use super::{LazyState, MergedChannels, trace::LazyCounters};
use brass_hir::Type;
use brass_typeck::stream::{BodyId, ChannelDelta, CheckEvent};
use fxhash::FxHashSet as HashSet;

/// Construct an isolated driver and its existing checker request channel.
pub(super) fn state(
    events: Vec<CheckEvent>,
) -> (
    LazyState,
    tokio::sync::mpsc::UnboundedReceiver<Option<Vec<brass_typeck::stream::BodyRequest>>>,
) {
    let (sender, receiver) = tokio::sync::mpsc::unbounded_channel();
    for event in events {
        sender.send(event).unwrap();
    }
    let (requests, request_rx) = tokio::sync::mpsc::unbounded_channel();
    (
        LazyState {
            completion: None,
            counters: LazyCounters::default(),
            events: receiver,
            sources: Default::default(),
            merged: MergedChannels::default(),
            checked_fns: HashSet::default(),
            inits_checked: 0,
            held: vec![],
            printed_warnings: HashSet::default(),
            needed: HashSet::default(),
            stop: std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false)),
            paused: std::sync::Arc::new(CheckerPause {
                paused: std::sync::atomic::AtomicBool::new(true),
                requests,
            }),
            needs_eager: false,
            closed: false,
            dirty: false,
            function_ranges: vec![],
            dirty_functions: HashSet::default(),
            dirty_non_functions: false,
            awaiting_keyed: false,
            entry_open: false,
            generated: vec![],
            batch_ids: BatchIds::default(),
            outstanding_batches: Default::default(),
            finished: false,
        },
        request_rx,
    )
}

fn one(lazy: &mut LazyState) -> super::demand::DemandBatch {
    let mut frontier = DemandFrontier::default();
    frontier.push(Demand {
        symbol: "f".into(),
        type_args: vec![],
        needs_body: true,
    });
    frontier.seal(&mut lazy.batch_ids).unwrap()
}

#[test]
fn settlement_waits_past_body_flags_until_seal_effects_are_merged() {
    let (mut lazy, mut requests) = state(vec![]);
    let (sender, receiver) = tokio::sync::mpsc::unbounded_channel();
    lazy.events = receiver;
    // Priority events cannot precede the request that owns their seal.
    let checker = std::thread::spawn(move || {
        let request = requests.blocking_recv().unwrap().unwrap();
        assert_eq!(request.len(), 1);
        sender
            .send(CheckEvent::BodyChecked(
                BodyId::Function("f".into()),
                ChannelDelta::default(),
            ))
            .unwrap();
        sender
            .send(CheckEvent::BatchSettled(ChannelDelta {
                settles_batch: Some(request[0].batch),
                instance_returns: vec![("f".into(), vec![], Type::Bool)],
                ..ChannelDelta::default()
            }))
            .unwrap();
    });
    let batch = one(&mut lazy);
    let result = lazy.settle(batch);
    assert!(result.complete);
    assert_eq!((result.new_requests, result.newly_settled), (1, 1));
    assert_eq!(
        lazy.merged.instance_returns.get(&("f".into(), vec![])),
        Some(&Type::Bool)
    );
    assert_eq!(lazy.counters.demand_counts(), (1, 1));
    assert!(lazy.needed.contains("f"));
    assert!(!lazy.closed, "settlement did not wait for stream closure");
    checker.join().unwrap();
}

#[test]
fn queued_background_body_settles_without_a_request_and_keeps_its_delta() {
    let span = brass_parser::Span::new(1, 2);
    let (mut lazy, mut requests) = state(vec![CheckEvent::BodyChecked(
        BodyId::Function("f".into()),
        ChannelDelta {
            expr_types: vec![(span, Type::Bool)],
            instance_returns: vec![("f".into(), vec![], Type::Bool)],
            ..ChannelDelta::default()
        },
    )]);
    let batch = one(&mut lazy);
    let result = lazy.settle(batch);
    assert!(result.complete);
    assert_eq!((result.new_requests, result.newly_settled), (0, 0));
    assert!(requests.try_recv().is_err());
    assert!(lazy.outstanding_batches.is_empty());
    assert!(!lazy.closed, "no wait for closure or Finished is needed");
    assert!(lazy.checked_fns.contains("f"));
    assert!(lazy.needed.contains("f"));
    assert_eq!(lazy.merged.expr_types.get(&span), Some(&Type::Bool));
    assert_eq!(
        lazy.merged.instance_returns.get(&("f".into(), vec![])),
        Some(&Type::Bool)
    );
    assert!(lazy.dirty);
    // A demand call still counts as a batch; a body already checked when
    // requests are selected does not contribute to demanded_bodies.
    assert_eq!(lazy.counters.demand_counts(), (1, 0));
}

#[test]
fn already_checked_members_need_no_request_or_seal() {
    let (mut lazy, mut requests) = state(vec![CheckEvent::BodyChecked(
        BodyId::Function("unused".into()),
        ChannelDelta {
            warnings: vec![brass_typeck::TypeError {
                message: "background warning".into(),
                span: brass_parser::Span::new(1, 2),
            }],
            ..ChannelDelta::default()
        },
    )]);
    lazy.checked_fns.insert("f".into());
    let batch = one(&mut lazy);
    let result = lazy.settle(batch);
    assert!(result.complete);
    assert_eq!((result.new_requests, result.newly_settled), (0, 0));
    assert!(requests.try_recv().is_err());
    assert!(lazy.needed.contains("f"));
    assert!(!lazy.closed);
    // This path does not wait, so background warnings must stay unobserved.
    assert_eq!(lazy.events.len(), 1);
    assert!(lazy.printed_warnings.is_empty());
    assert_eq!(lazy.counters.demand_counts(), (1, 0));
}

#[test]
fn finished_settles_every_outstanding_batch_after_its_effects() {
    let (mut lazy, _) = state(vec![]);
    lazy.outstanding_batches.extend([98, 99]);
    lazy.take(CheckEvent::Finished(
        ChannelDelta {
            instance_returns: vec![("f".into(), vec![], Type::Bool)],
            ..ChannelDelta::default()
        },
        vec![],
    ));
    assert!(lazy.outstanding_batches.is_empty());
    assert!(lazy.finished);
    assert_eq!(
        lazy.merged.instance_returns.get(&("f".into(), vec![])),
        Some(&Type::Bool)
    );
}

#[test]
fn interrupted_stream_keeps_its_existing_symbol_verdict() {
    for checked in [false, true] {
        let (mut lazy, mut requests) = state(vec![]);
        let (sender, receiver) = tokio::sync::mpsc::unbounded_channel();
        lazy.events = receiver;
        // Interrupt an actual in-flight batch, with or without its body flag.
        let checker = std::thread::spawn(move || {
            requests.blocking_recv().unwrap().unwrap();
            if checked {
                sender
                    .send(CheckEvent::BodyChecked(
                        BodyId::Function("f".into()),
                        ChannelDelta::default(),
                    ))
                    .unwrap();
            }
        });
        let batch = one(&mut lazy);
        assert_eq!(lazy.settle(batch).complete, checked);
        assert!(lazy.closed);
        assert!(!lazy.finished);
        assert!(!lazy.outstanding_batches.is_empty());
        checker.join().unwrap();
        // A closed stream can be visited again after its symbol-based verdict;
        // unsealed ids must neither panic nor turn an unchecked body complete.
        let batch = one(&mut lazy);
        assert_eq!(lazy.settle(batch).complete, checked);
    }
}

#[test]
fn eager_interruption_keeps_unsealed_body_events_pending() {
    let (mut lazy, _) = state(vec![CheckEvent::BodyChecked(
        BodyId::Function("f".into()),
        ChannelDelta::default(),
    )]);
    // A keyed interruption can leave an earlier batch unsealed. Its body
    // flags cannot be treated as background progress by another settlement.
    lazy.needs_eager = true;
    lazy.outstanding_batches.push_back(99);
    let batch = one(&mut lazy);
    assert!(!lazy.settle(batch).complete);
    assert!(!lazy.checked_fns.contains("f"));
    assert_eq!(lazy.events.len(), 1);
}

#[test]
fn seals_retire_outstanding_batches_in_send_order() {
    let (mut lazy, _) = state(vec![]);
    lazy.outstanding_batches.extend([1, 2]);
    for id in [1, 2] {
        assert_eq!(lazy.outstanding_batches.front(), Some(&id));
        lazy.take(CheckEvent::BatchSettled(ChannelDelta {
            settles_batch: Some(id),
            ..ChannelDelta::default()
        }));
    }
    assert!(lazy.outstanding_batches.is_empty());
}

#[test]
fn eager_fallback_rebuilds_execution_locations() {
    use std::sync::Arc;
    use std::sync::atomic::AtomicBool;
    use tokio::sync::mpsc::unbounded_channel;

    // A completed streaming worker contributes no execution payload. The
    // fallback must analyze again and give the executed call its real location.
    let runtime = tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap();
    let checker = runtime.spawn_blocking(|| Err(Vec::new()));
    let stop = Arc::new(AtomicBool::new(false));
    let (requests, _requests_rx) = unbounded_channel();
    let paused = Arc::new(CheckerPause {
        paused: AtomicBool::new(true),
        requests,
    });
    let (events_tx, events) = unbounded_channel();
    drop(events_tx);
    let source = "fun capture(loc: Location) {\nassert(loc.line == 5)\nassert(loc.col == 14)\n}\nfun main() { capture() }\n";
    assert_eq!(
        super::finish_eagerly(
            &runtime,
            checker,
            &stop,
            &paused,
            events,
            "<fallback>",
            source,
            std::path::Path::new("."),
        ),
        Ok(())
    );
}

#[test]
fn lowering_frontier_preserves_contracts_and_resets_after_body_only_appends() {
    use super::frontier::LoweringFrontier;
    let ast = brass_parser::parse(
        "fun absent() { return 1 }\nfun contract() { return 2 }\nfun required() { return 3 }\nfun untouched() { return 4 }\n",
    ).unwrap();
    let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty());
    let (mut lazy, _) = state(vec![]);
    let locations = Default::default();
    let tables = brass_mir::LowerTables::new(&program);
    let mut lowering =
        brass_mir::SubsetLowering::new(&program, &tables, &lazy.channels(&locations));
    // Consume the constructor reset so the next reset must come from appends.
    lazy.refresh_channels(&mut lowering, &locations);
    lazy.refresh_channels(&mut lowering, &locations);
    assert!(!lowering.changed_inputs().full_reset);
    lazy.merged
        .instance_returns
        .insert(("contract".into(), vec![]), Type::Bool);
    lazy.merged
        .instance_returns
        .insert(("required".into(), vec![]), Type::Bool);
    let frontier = LoweringFrontier::settled(
        [
            Demand {
                symbol: "required".into(),
                type_args: vec![],
                needs_body: true,
            },
            Demand {
                symbol: "contract".into(),
                type_args: vec![],
                needs_body: false,
            },
            Demand {
                symbol: "absent".into(),
                type_args: vec![],
                needs_body: false,
            },
        ],
        &mut lazy,
        true,
    );
    assert_eq!(frontier.supplied_bodies(&lowering), 2);
    let changes = frontier.apply(&mut lowering, &mut lazy, &program, &tables, &locations);
    assert!(
        changes.full_reset,
        "new MIR bodies invalidate the mono session immediately"
    );
    assert_eq!((changes.base_epoch, changes.epoch), (0, 0));
    lazy.refresh_channels(&mut lowering, &locations);
    assert!(
        !lowering.changed_inputs().full_reset,
        "the body reset was already consumed"
    );
    let symbols: Vec<_> = lowering
        .mir
        .functions
        .iter()
        .map(|f| f.symbol.as_str())
        .collect();
    assert_eq!(symbols, ["absent", "required"]);
    assert!(!lowering.is_lowered("contract"));
    assert!(!lowering.is_lowered("untouched"));
    assert!(
        lazy.needed.is_empty(),
        "frontier consumption never extends the needed set"
    );
}

#[test]
fn lowering_frontier_keeps_base_revisions_and_later_deltas_dirty() {
    use super::frontier::LoweringFrontier;
    let program = brass_hir::Program::empty();
    let tables = brass_mir::LowerTables::new(&program);
    let locations = Default::default();
    let (mut lazy, _) = state(vec![]);
    let mut lowering =
        brass_mir::SubsetLowering::new(&program, &tables, &lazy.channels(&locations));
    // A method/init revision still needs the startup base-rebuild gate.
    lazy.dirty = true;
    lazy.dirty_non_functions = true;
    LoweringFrontier::default().apply(&mut lowering, &mut lazy, &program, &tables, &locations);
    assert!(lazy.dirty);
    assert!(lazy.dirty_non_functions);
    lazy.dirty = false;
    lazy.dirty_non_functions = false;
    LoweringFrontier::default().apply(&mut lowering, &mut lazy, &program, &tables, &locations);
    assert!(!lazy.dirty);
    // An event absorbed after apply must not be hidden by the consumed window.
    lazy.take(CheckEvent::BatchSettled(ChannelDelta {
        expr_types: vec![(brass_parser::Span::new(1, 2), Type::Bool)],
        ..ChannelDelta::default()
    }));
    assert!(lazy.dirty);
    assert!(lazy.dirty_non_functions);
}

#[test]
fn startup_contract_retry_requires_an_unchanged_missing_pass() {
    use super::frontier::settle_demands;
    let ast = brass_parser::parse("fun f() { return 1 }\nfun g() { return 2 }\n").unwrap();
    let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty());
    let (mut lazy, _) = state(vec![]);
    lazy.checked_fns.extend(["f".into(), "g".into()]);
    let locations = Default::default();
    let tables = brass_mir::LowerTables::new(&program);
    let lowering = brass_mir::SubsetLowering::new(&program, &tables, &lazy.channels(&locations));
    let one = || vec![("f".into(), vec![], false)];
    let settle = |demands, lazy: &mut LazyState, startup: bool| {
        settle_demands(
            demands,
            &program,
            &lowering,
            lazy,
            startup.then_some(&[][..]),
        )
        .into_lowering(lazy)
        .supplied_bodies(&lowering)
    };
    assert_eq!(settle(one(), &mut lazy, true), 1);
    // A different input could prune the missing site or change its instance.
    lazy.merged
        .changed_inputs
        .returns
        .change(("g".into(), vec![]));
    assert_eq!(settle(one(), &mut lazy, true), 0);
    assert_eq!(
        settle(one(), &mut lazy, false),
        1,
        "runtime keeps its existing rule"
    );
    lazy.merged.changed_inputs = Default::default();
    // Supplying another body also changes the next pass, even without a delta.
    assert_eq!(
        settle(
            vec![("f".into(), vec![], false), ("g".into(), vec![], true)],
            &mut lazy,
            true
        ),
        1
    );
    lazy.dirty = true;
    assert_eq!(settle(one(), &mut lazy, true), 0);
}

#[test]
fn queued_background_revision_prevents_the_startup_absent_contract_fold() {
    use super::frontier::settle_demands;
    let ast = brass_parser::parse("fun f() { return 1 }\nfun g() { return 2 }\n").unwrap();
    let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty());
    let (mut lazy, mut requests) = state(vec![CheckEvent::BodyChecked(
        BodyId::Function("f".into()),
        ChannelDelta {
            instance_returns: vec![("g".into(), vec![], Type::Bool)],
            ..ChannelDelta::default()
        },
    )]);
    let locations = Default::default();
    let tables = brass_mir::LowerTables::new(&program);
    let lowering = brass_mir::SubsetLowering::new(&program, &tables, &lazy.channels(&locations));
    let settled = settle_demands(
        vec![("f".into(), vec![], false)],
        &program,
        &lowering,
        &mut lazy,
        Some(&[]),
    );
    assert!(settled.outcome.complete);
    assert_eq!(settled.outcome.new_requests, 0);
    assert!(requests.try_recv().is_err());
    // A return-only delta leaves dirty false, but its changed-input window
    // still prevents assuming that the preceding mono pass will repeat.
    assert!(!lazy.dirty);
    assert_eq!(
        settled.into_lowering(&mut lazy).supplied_bodies(&lowering),
        0
    );
    assert_eq!(
        lazy.merged.instance_returns.get(&("g".into(), vec![])),
        Some(&Type::Bool)
    );
}
