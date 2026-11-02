//! Exact replay effects beyond construction leaves and rejected storage cases.

use super::{call, checker, program};
use crate::infer::co_replay::snapshot::{EffectHistory, EffectSnapshot};
use crate::infer::journal::MemoFlavor;
use brass_hir::Type;

/// Compare a real nested walk and a memo hit under a different enclosing root.
/// Repeated return paths retain duplicate links and do not publish contracts.
#[test]
fn nested_links_replay_into_current_root() {
    for body in [
        "fun twice(x, flag: bool) { let y = choose(x, flag)\nreturn choose(y, flag) }",
        "fun left(x, flag: bool) { return choose(x, flag) }\nfun right(x, flag: bool) { return choose(x, flag) }\nfun twice(x, flag: bool) { let a = left(x, flag)\nreturn [a, right(x, flag)] }",
    ] {
        let p = program(&format!(
            "fun choose(x, flag: bool) {{ if flag {{ return [] }}\nreturn [x] }}\n{body}"
        ));
        for rooted in [false, true] {
            let mut seed = checker(&p);
            seed.co_checking = true;
            if rooted {
                seed.current_co_method = Some(("A".into(), "first".into()));
            }
            let args = [Type::Str, Type::Bool];
            call(&mut seed, "twice", &args);
            assert!(seed.errors.is_empty(), "{:?}", seed.errors);
            if rooted {
                assert!(!seed.co_return_links[seed.current_co_method.as_ref().unwrap()].is_empty());
                seed.current_co_method = Some(("B".into(), "second".into()));
            }
            let mut walked = EffectSnapshot::fork(&seed);
            let mut replayed = EffectSnapshot::fork(&seed);
            walked.elaboration_memo.clear();
            let a = call(&mut walked, "twice", &args);
            let b = call(&mut replayed, "twice", &args);
            if std::env::var("BRASS_MEMO_CHECK").as_deref() == Ok("1") {
                assert!(replayed.stats.co_hits > seed.stats.co_hits);
            } else {
                assert_eq!(replayed.stats.co_hits, seed.stats.co_hits + 1);
            }
            let mut ah = EffectHistory::new(&seed);
            let mut bh = EffectHistory::new(&seed);
            ah.boundary(&walked);
            bh.boundary(&replayed);
            // The full snapshot compares one walk to one replay. Memo validation
            // deliberately applies ordinary observations twice and may retain
            // additional fresh typed observations; its co effects are checked by
            // assert_co_validation at each hit instead.
            if std::env::var("BRASS_MEMO_CHECK").as_deref() != Ok("1") {
                EffectSnapshot::capture(&walked, &args, &walked.resolve(&a), &ah)
                    .compare(&EffectSnapshot::capture(
                        &replayed,
                        &args,
                        &replayed.resolve(&b),
                        &bh,
                    ))
                    .unwrap();
            }
            assert!(replayed.instance_returns.is_empty());
        }
    }
}

/// Links with unresolved non-input variables cannot be detached from shared
/// outer state by allocating fresh placeholders in a later call.
#[test]
fn outer_link_variables_prevent_storage() {
    let p = program("fun leaf(x) { return x }");
    let mut c = checker(&p);
    c.co_checking = true;
    c.current_co_method = Some(("Owner".into(), "get".into()));
    let outer = c.fresh_unknown();
    let mut context = c
        .elaboration_memo_key("fn", "leaf", None, &[Type::Str], &[])
        .unwrap();
    context.key.flavor = MemoFlavor::CoCheck { has_root: true };
    c.begin_elaboration_journal();
    c.record_co_return_link(Type::Str, outer);
    let frame = c.finish_elaboration_journal();
    assert!(
        c.build_elaboration_memo_entry(&Type::Str, frame, &context)
            .is_none()
    );
}

/// Deduplication across nested shared journals must not remove repeated links;
/// links and return types share fresh placeholders while globals form a set.
#[test]
fn nested_journal_preserves_duplicate_links_and_fresh_aliases() {
    let p = program("fun leaf(x) { return x }");
    let mut c = checker(&p);
    c.co_checking = true;
    c.current_co_method = Some(("A".into(), "get".into()));
    let context = c
        .elaboration_memo_key("fn", "leaf", None, &[Type::Str], &[])
        .unwrap();
    c.begin_elaboration_journal();
    let fresh = c.fresh_unknown();
    c.record_co_return_link(fresh.clone(), Type::Str);
    c.record_co_return_link(fresh.clone(), Type::Str);
    c.record_co_return_link(Type::Str, fresh.clone());
    c.record_co_global_read("global");
    let frame = c.finish_elaboration_journal();
    let entry = c
        .build_elaboration_memo_entry(&fresh, frame, &context)
        .unwrap();
    c.current_co_method = Some(("B".into(), "get".into()));
    c.begin_elaboration_journal();
    let first = c.replay_elaboration_memo_entry(&entry, &context);
    let second = c.replay_elaboration_memo_entry(&entry, &context);
    assert_ne!(first, second);
    let frame = c.finish_elaboration_journal();
    let combined = c
        .build_elaboration_memo_entry(&Type::Tuple(vec![first, second]), frame, &context)
        .unwrap();
    c.current_co_method = Some(("C".into(), "get".into()));
    let returned = c.replay_elaboration_memo_entry(&combined, &context);
    let Type::Tuple(vars) = returned else {
        panic!("tuple return")
    };
    let links = &c.co_return_links[c.current_co_method.as_ref().unwrap()];
    assert_eq!(links.len(), 6);
    for (chunk, var) in links.as_chunks::<3>().0.iter().zip(vars) {
        assert_eq!(
            chunk,
            &[
                (var.clone(), Type::Str),
                (var.clone(), Type::Str),
                (Type::Str, var)
            ]
        );
    }
    assert_eq!(c.co_global_reads.len(), 1);
}

/// The validation observer sees already-known globals and suppresses only its
/// dry replay. Actual nested walks append once to every enclosing observation.
#[test]
fn differential_observer_keeps_global_reads_and_link_multiplicity() {
    let p = program("fun leaf(x) { return x }");
    let mut c = checker(&p);
    c.current_co_method = Some(("Root".into(), "get".into()));
    c.record_co_global_read("global");
    c.begin_co_validation(true);
    for _ in 0..2 {
        c.record_co_return_link(Type::Str, Type::Str);
    }
    c.record_co_global_read("global");
    let replay = c.finish_co_validation();
    assert!(c.co_return_links.is_empty());
    c.begin_co_validation(false);
    for _ in 0..2 {
        c.record_co_return_link(Type::Str, Type::Str);
    }
    c.record_co_global_read("global");
    let walk = c.finish_co_validation();
    c.assert_co_validation("leaf", replay, walk, &Type::Str, &Type::Str);
    assert_eq!(
        c.co_return_links[c.current_co_method.as_ref().unwrap()].len(),
        2
    );
}

/// Global reads replay even when the dependency was already present; concrete
/// mutable globals remain one shared value rather than copied memo state.
#[test]
fn global_read_replay_matches_walk() {
    let p = program("let global: int32 = 1\nfun read() { return global }");
    let mut seed = checker(&p);
    seed.precompute_global_bindings();
    seed.co_checking = true;
    call(&mut seed, "read", &[]);
    assert!(seed.errors.is_empty(), "{:?}", seed.errors);
    assert!(seed.co_global_reads.contains("global"));
    let mut walk = EffectSnapshot::fork(&seed);
    let mut replay = EffectSnapshot::fork(&seed);
    walk.elaboration_memo.clear();
    let a = call(&mut walk, "read", &[]);
    let b = call(&mut replay, "read", &[]);
    assert_eq!(replay.stats.co_hits, seed.stats.co_hits + 1);
    let mut ah = EffectHistory::new(&seed);
    let mut bh = EffectHistory::new(&seed);
    ah.boundary(&walk);
    bh.boundary(&replay);
    EffectSnapshot::capture(&walk, &[], &walk.resolve(&a), &ah)
        .compare(&EffectSnapshot::capture(
            &replay,
            &[],
            &replay.resolve(&b),
            &bh,
        ))
        .unwrap();
}

/// Capped transitive results never become memo entries; clean subchains do.
/// Neither cap nor completion observations become co-check publications.
#[test]
fn co_chain_depth_boundaries_and_budget() {
    // Deep elaboration uses the CLI worker's stack size, not libtest's stack.
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(check_depth_boundaries_and_budget)
        .unwrap()
        .join()
        .unwrap();
}

/// Exercise all three depth boundaries in one ordinary-sized checker worker.
fn check_depth_boundaries_and_budget() {
    for depth in [63, 64, 65] {
        let mut source = String::new();
        for index in 0..depth {
            let body = if index + 1 == depth {
                "x".to_owned()
            } else {
                format!("f{}(x)", index + 1)
            };
            source.push_str(&format!("fun f{index}(x) {{ return {body} }}\n"));
        }
        let p = program(&source);
        let mut c = checker(&p);
        c.co_checking = true;
        c.numeric_enabled = false;
        call(&mut c, "f0", &[Type::Str]);
        assert!(c.errors.is_empty(), "depth {depth}: {:?}", c.errors);
        let capped = c.depth_capped != 0;
        assert_eq!(capped, depth >= 64, "depth {depth}");
        assert_eq!(
            c.elaboration_memo.keys().any(|key| key.callable == "fn:f0"),
            !capped
        );
        assert!(c.instance_returns.is_empty());
    }
    let p = program("fun leaf(x) { return x }\nfun other(x) { return x }");
    let mut c = checker(&p);
    c.co_checking = true;
    call(&mut c, "leaf", &[Type::Str]);
    c.elaborations = crate::infer::instantiate::ELABORATION_BUDGET
        - u64::from(std::env::var("BRASS_MEMO_CHECK").as_deref() == Ok("1"));
    call(&mut c, "leaf", &[Type::Str]);
    assert!(!c.elaboration_budget_reported);
    call(&mut c, "other", &[Type::Str]);
    assert!(c.elaboration_budget_reported);
    assert_eq!(c.errors.len(), 1);
}

/// A receiver declaration with an open fallback bypasses method co reuse.
#[test]
fn receiver_functions_remain_methods_for_admission() {
    let ast = brass_parser::parse("fun string.identity(self) { return self }").unwrap();
    let (p, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        source: None,
        path: vec!["core".into(), "fixture".into()],
        is_prelude: true,
        ast,
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    let mut c = checker(&p);
    c.co_checking = true;
    for function in p.functions.values().filter(|info| info.decl.recv.is_some()) {
        assert!(!c.co_memo_eligible(&function.symbol));
        for _ in 0..2 {
            call(&mut c, &function.symbol, &[Type::Str]);
        }
    }
    assert!(c.stats.co_walks > 0);
    assert_eq!(c.stats.co_hits, 0);
    assert_eq!(c.stats.co_misses, 0);
}
