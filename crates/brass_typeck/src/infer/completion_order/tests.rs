//! Differential checks of ordinary dedicated passes with and without ordering.

use super::{CompletionGraph, Eligibility, IneligibleReason};
use crate::infer::{Checker, driver};
use brass_hir::{InstanceKey, IntKind, Program, Type};
use fxhash::FxHashSet as HashSet;
use std::rc::Rc;

fn program(source: &str) -> Program {
    let ast = brass_parser::parse(source).unwrap();
    let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    program
}

fn checker(program: &Program) -> Checker<'_> {
    let mut checker = Checker::new(program, Rc::new(brass_typesys::RowInfo::analyze(program)));
    checker.lazy_profile = true;
    checker.keyed_tainted = crate::taint::keyed_reachable(program);
    checker.precompute_returns();
    checker
}

fn pass(checker: &mut Checker<'_>, key: &InstanceKey) {
    let brass_hir::InstanceCallable::Function(symbol) = &key.callable else {
        unreachable!()
    };
    driver::check_stream_function(
        checker,
        symbol,
        Some(&key.args),
        &mut brass_utils::PerfLog::start("test/completion"),
    );
}

fn run<'a>(
    program: &'a Program,
    demands: &[InstanceKey],
    ordered: bool,
) -> (Checker<'a>, Vec<InstanceKey>) {
    let mut checker = checker(program);
    let mut done = HashSet::default();
    let mut completed = Vec::new();
    for key in demands {
        let brass_hir::InstanceCallable::Function(symbol) = &key.callable else {
            unreachable!()
        };
        checker.completion.assert_demand(program, symbol, &key.args);
        if done.contains(symbol) {
            continue;
        }
        if ordered
            && checker.completion.was_capped(key)
            && checker.completion_eligibility(key) == Eligibility::Closed
        {
            while let Some(next) = checker.completion.completion_order(key).into_iter().find(|next| {
                matches!(&next.callable, brass_hir::InstanceCallable::Function(s) if !done.contains(s))
            }) {
                let brass_hir::InstanceCallable::Function(s) = &next.callable else { unreachable!() };
                done.insert(s.clone());
                checker.completion.active = true;
                pass(&mut checker, &next);
                checker.completion.completed(next.clone());
                completed.push(next);
            }
        }
        done.insert(symbol.clone());
        checker.completion.active = ordered;
        pass(&mut checker, key);
        checker.completion.active = false;
    }
    (checker, completed)
}

fn chain(depth: usize, generic: bool) -> String {
    let (params, args, leaf) = if generic {
        ("x", "x", "x")
    } else {
        ("", "", "1")
    };
    (0..depth)
        .map(|i| format!("fun f{i}({params}) {{ return f{}({args}) }}\n", i + 1))
        .collect::<String>()
        + &format!("fun f{depth}({params}) {{ return {leaf} }}\n")
}

#[test]
fn depth_boundary_contracts_and_transitive_cap_guard() {
    large_stack(depth_boundaries);
}

fn depth_boundaries() {
    for depth in [63, 64, 65, 140] {
        let p = program(&chain(depth, false));
        let demands: Vec<_> = (0..=depth)
            .map(|i| InstanceKey::function(&p, &format!("f{i}"), &[]).unwrap())
            .collect();
        let (baseline, _) = run(&p, &demands, false);
        let (ordered, completed) = run(&p, &demands, true);
        assert_eq!(baseline.errors, ordered.errors);
        assert_eq!(baseline.warnings, ordered.warnings);
        // Completion can add valid contracts earlier. Every common full identity
        // must still denote the baseline return; a capped root stays unpublished.
        for (key, value) in &baseline.instance_returns {
            assert_eq!(ordered.instance_returns.get(key), Some(value));
        }
        assert_eq!(
            ordered.stats.dedicated_passes,
            baseline.stats.dedicated_passes
        );
        assert!(ordered.depth_capped <= baseline.depth_capped);
        assert!(ordered.elaborations <= baseline.elaborations);
        if depth > 65 {
            assert!(!completed.is_empty());
        }
        let (first, _) = run(&p, &demands[..1], true);
        if depth > 64 {
            assert!(!first.instance_returns.contains_key(&("f0".into(), vec![])));
        }
    }
}

#[test]
fn generic_first_frame_keeps_both_full_instance_identities() {
    large_stack(generic_instances);
}

fn generic_instances() {
    let p = program(
        &(chain(70, true)
            + "fun both() { let a = f0(1)\n let b = f0(5000000000)\n let c = f10(5000000000)\n return b }\n"),
    );
    let demands: Vec<_> = [Type::Int(IntKind::I32), Type::Int(IntKind::I64)]
        .into_iter()
        .flat_map(|ty| (0..=70).map(move |i| (i, ty.clone())))
        .map(|(i, ty)| InstanceKey::function(&p, &format!("f{i}"), &[ty]).unwrap())
        .collect();
    let demands = [
        vec![InstanceKey::function(&p, "both", &[]).unwrap()],
        demands,
    ]
    .concat();
    let (baseline, _) = run(&p, &demands, false);
    let (ordered, completed) = run(&p, &demands, true);
    assert!(completed.is_empty());
    for ty in [Type::Int(IntKind::I32), Type::Int(IntKind::I64)] {
        assert!(
            baseline
                .instance_returns
                .contains_key(&("f70".into(), vec![ty]))
        );
    }
    assert_eq!(baseline.instance_returns, ordered.instance_returns);
    assert_eq!(
        baseline.finalized_instance_typed(),
        ordered.finalized_instance_typed()
    );
    assert_eq!(baseline.depth_capped, ordered.depth_capped);
    assert_eq!(baseline.stats.memo_hits, ordered.stats.memo_hits);
    assert_eq!(baseline.stats.memo_misses, ordered.stats.memo_misses);
    assert_eq!(baseline.errors, ordered.errors);
}

#[test]
fn graph_diamond_is_deterministic_and_never_discovers_syntax_edges() {
    large_stack(diamond);
}

fn diamond() {
    let p = program(
        "fun a() { return b() + c() }\nfun b() { return d() }\nfun c() { return d() }\nfun d() { return 1 }\n",
    );
    let keys: Vec<_> = ["a", "b", "c", "d"]
        .map(|s| InstanceKey::function(&p, s, &[]).unwrap())
        .into();
    let mut checker = checker(&p);
    assert_eq!(
        checker.completion_eligibility(&keys[0]),
        Eligibility::Closed
    );
    assert!(checker.completion.completion_order(&keys[0]).is_empty());
    for (a, b) in [(0, 1), (0, 2), (1, 3), (2, 3)] {
        checker.completion.observe(&keys[a], &keys[b], true);
    }
    assert_eq!(
        checker.completion.completion_order(&keys[0]),
        vec![keys[3].clone(), keys[1].clone(), keys[2].clone()]
    );
    // A probe cannot publish edges into the original shared graph.
    checker.completion.active = true;
    let probe = checker.fork_probe();
    assert!(!probe.completion.active);
    let (baseline, _) = run(&p, &keys, false);
    let (ordered, _) = run(&p, &keys, true);
    assert_eq!(baseline.instance_returns, ordered.instance_returns);
    // Both branches reach the same capped tail. It receives one completion
    // pass per symbol, and a second identical demand script chooses the same order.
    let p = program(
        &(chain(140, false)
            + "fun a() { return b() + c() }\nfun b() { return f0() }\nfun c() { return f0() }\n"),
    );
    let names = ["a".to_owned(), "b".into(), "c".into()]
        .into_iter()
        .chain((0..=140).map(|i| format!("f{i}")));
    let demands: Vec<_> = names
        .map(|name| InstanceKey::function(&p, &name, &[]).unwrap())
        .collect();
    let (baseline, _) = run(&p, &demands, false);
    let (ordered, order) = run(&p, &demands, true);
    let (again, repeated) = run(&p, &demands, true);
    assert!(!order.is_empty());
    assert_eq!(order, repeated);
    assert_eq!(ordered.stats.memo_hits, again.stats.memo_hits);
    assert_eq!(ordered.stats.memo_misses, again.stats.memo_misses);
    assert_eq!(ordered.depth_capped, again.depth_capped);
    assert!(ordered.elaborations < baseline.elaborations);
    for (key, ret) in &baseline.instance_returns {
        assert_eq!(ordered.instance_returns.get(key), Some(ret));
    }
}

#[test]
fn uncertified_effects_and_cycles_keep_ordinary_order() {
    let p =
        program("fun a() { return a() }\nfun b(x) { return x }\nfun c() { let x = 1\nreturn x }\n");
    let mut checker = checker(&p);
    for (name, args, reason) in [
        ("a", vec![], IneligibleReason::Recursive),
        (
            "b",
            vec![Type::Int(IntKind::I32)],
            IneligibleReason::SharedSymbolPass,
        ),
        ("c", vec![], IneligibleReason::UncertifiedBody),
    ] {
        let key = InstanceKey::function(&p, name, &args).unwrap();
        assert_eq!(
            checker.completion_eligibility(&key),
            Eligibility::Ineligible(reason)
        );
    }
    let graph = CompletionGraph::default();
    assert!(!graph.active);
    let leaf = program("fun leaf() { return 1 }\n");
    let key = InstanceKey::function(&leaf, "leaf", &[]).unwrap();
    let mut bounded = self::checker(&leaf);
    bounded.elaborations = crate::infer::instantiate::ELABORATION_BUDGET - 2;
    assert_eq!(
        bounded.completion_eligibility(&key),
        Eligibility::Ineligible(IneligibleReason::BudgetBound)
    );
}

// Deep checker recursion runs on the same stack size as the CLI driver.
fn large_stack(test: fn()) {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(test)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn completion_events_preserve_the_last_members_seal() {
    large_stack(|| {
        use crate::stream::{BodyId, BodyRequest, ChannelDelta, CheckEvent, Scheduler};
        struct Recorder {
            requests: Vec<BodyRequest>,
            events: Vec<CheckEvent>,
            settled: bool,
        }
        impl Scheduler for Recorder {
            fn drain_requests(&mut self) -> Vec<BodyRequest> {
                std::mem::take(&mut self.requests)
            }
            fn paused(&self) -> bool {
                true
            }
            fn stopped(&self) -> bool {
                self.settled
            }
            fn emit(&mut self, event: CheckEvent) {
                if matches!(&event, CheckEvent::BodyChecked(_, d) | CheckEvent::BatchSettled(d) if d.settles_batch == Some(9))
                {
                    self.settled = true;
                }
                self.events.push(event);
            }
        }
        let p = program(&chain(140, false));
        let mut recorder = Recorder {
            requests: ["f0", "f1"]
                .map(|symbol| BodyRequest {
                    symbol: symbol.into(),
                    type_args: vec![],
                    batch: 9,
                })
                .into(),
            events: vec![],
            settled: false,
        };
        crate::analyze_streaming(&p, None, &mut recorder);
        let bodies: Vec<(&String, &ChannelDelta)> = recorder
            .events
            .iter()
            .filter_map(|event| match event {
                CheckEvent::BodyChecked(BodyId::Function(name), delta) => Some((name, delta)),
                _ => None,
            })
            .collect();
        assert_eq!(bodies.first().unwrap().0, "f0");
        assert_eq!(bodies.last().unwrap().0, "f1");
        assert_eq!(bodies.len(), 141);
        // The cached production order must match recomputing the graph after
        // every pass, including the passes that discover a new capped tail.
        let demands = ["f0", "f1"].map(|name| InstanceKey::function(&p, name, &[]).unwrap());
        let (_, expected) = run(&p, &demands, true);
        let observed: Vec<_> = bodies[1..bodies.len() - 1]
            .iter()
            .map(|(name, _)| InstanceKey::function(&p, name, &[]).unwrap())
            .collect();
        assert_eq!(observed, expected);
        assert_eq!(
            bodies
                .iter()
                .map(|(name, _)| *name)
                .collect::<HashSet<_>>()
                .len(),
            141
        );
        assert!(
            bodies[..bodies.len() - 1]
                .iter()
                .all(|(_, delta)| delta.is_empty())
        );
        let delta = bodies.last().unwrap().1;
        assert_eq!(delta.settles_batch, Some(9));
        assert!(!delta.instance_returns.is_empty());
        assert!(matches!(
            recorder.events.last(),
            Some(CheckEvent::Finished(_, _))
        ));
    });
}
