//! Flavor isolation and complete walk/replay effects for construction leaves.

use super::{call, checker, program};
use crate::infer::co_replay::snapshot::{EffectHistory, EffectSnapshot};
use crate::infer::journal::MemoFlavor;
use brass_hir::{IntKind, LoadedModule, Program, Type};

/// Ordinary, rooted and rootless co-check entries never satisfy one another.
/// Different enclosing roots may share an absence-certified entry.
#[test]
fn memo_flavors_separate_publication_contracts() {
    let p = program("fun leaf(x) { return x }");
    let mut c = checker(&p);
    c.co_checking = true;
    call(&mut c, "leaf", &[Type::Str]);
    call(&mut c, "leaf", &[Type::Str]);
    assert_eq!(
        (c.stats.co_hits, c.stats.co_misses, c.stats.co_walks),
        (1, 1, 0)
    );
    assert!(c.instance_returns.is_empty());
    c.current_co_method = Some(("A".into(), "method".into()));
    call(&mut c, "leaf", &[Type::Str]);
    c.current_co_method = Some(("B".into(), "other".into()));
    call(&mut c, "leaf", &[Type::Str]);
    assert_eq!((c.stats.co_hits, c.stats.co_misses), (2, 2));
    assert!(c.co_return_links.is_empty());
    assert!(c.co_global_reads.is_empty());
    assert!(c.instance_returns.is_empty());
    c.co_checking = false;
    c.current_co_method = None;
    call(&mut c, "leaf", &[Type::Str]);
    assert_eq!(c.stats.memo_misses, 3);
    assert_eq!(c.stats.memo_hits, 2);
    assert_eq!(c.elaboration_memo.len(), 3);
    for flavor in [
        MemoFlavor::Ordinary,
        MemoFlavor::CoCheck { has_root: false },
        MemoFlavor::CoCheck { has_root: true },
    ] {
        assert!(c.elaboration_memo.keys().any(|key| key.flavor == flavor));
    }
}

/// Reuse remains subject to open-input, probe, recursion and speculative-store
/// exclusions. Failed walks retain their diagnostics instead of being stored.
#[test]
fn co_admission_keeps_existing_rejections() {
    let p = program(
        "fun leaf(x, y) { return x }\nfun bad(x, y) -> bool { return x }\nfun capture(x, y) { return (z) -> x }",
    );
    for mode in [
        "open-shared",
        "open-distinct",
        "closure",
        "numeric",
        "type-test",
        "recursive",
        "speculative",
        "error",
    ] {
        let mut c = checker(&p);
        c.co_checking = true;
        let mut arg = Type::Str;
        match mode {
            "open-shared" | "open-distinct" => arg = c.fresh_unknown(),
            "numeric" => c.numeric.probing = true,
            "type-test" => {
                c.type_test_holes.insert(0);
            }
            "recursive" => {
                c.instantiating.insert("fn:leaf".into());
            }
            "speculative" => c.speculation_depth = 1,
            "error" | "closure" => {}
            _ => unreachable!(),
        }
        let other = if mode == "open-distinct" {
            c.fresh_unknown()
        } else {
            arg.clone()
        };
        for _ in 0..2 {
            call(
                &mut c,
                if mode == "error" {
                    "bad"
                } else if mode == "closure" {
                    "capture"
                } else {
                    "leaf"
                },
                &[arg.clone(), other.clone()],
            );
        }
        assert!(c.elaboration_memo.is_empty(), "{mode}");
        assert_eq!(c.stats.co_hits, 0, "{mode}");
        assert!(c.instance_returns.is_empty(), "{mode}");
    }
}

/// Numeric provenance adaptation may clear the ordinary probe flag, but a
/// co-check nested inside that adaptation must still walk its body.
#[test]
fn annotated_numeric_probe_keeps_co_reuse_disabled() {
    let p = program("fun leaf(x) -> string { return x }");
    let mut c = checker(&p);
    c.co_checking = true;
    c.numeric.probing = true;
    for _ in 0..2 {
        call(&mut c, "leaf", &[Type::Str]);
    }
    assert_eq!((c.stats.co_hits, c.stats.co_misses), (0, 0));
    assert_eq!(c.stats.co_walks, 2);
    assert!(c.elaboration_memo.is_empty());
    assert!(c.numeric.probing);
    assert!(!c.co_memo_suspended);
}

/// The same co-check hit takes the ordinary validation path when memo checking
/// is enabled. Run this fixture both with and without BRASS_MEMO_CHECK=1.
#[test]
fn co_hit_uses_memo_check_walk() {
    let p = program("fun leaf(x) { return [x, x] }");
    let mut c = checker(&p);
    c.co_checking = true;
    call(&mut c, "leaf", &[Type::Str]);
    let before = c.elaborations;
    call(&mut c, "leaf", &[Type::Str]);
    assert_eq!(c.stats.co_hits, 1);
    let validating = std::env::var("BRASS_MEMO_CHECK").as_deref() == Ok("1");
    assert_eq!(c.elaborations - before, u64::from(validating));
    assert!(c.instance_returns.is_empty());
}

/// Compare fresh authoritative forks after warming only their shared seed.
/// The walk fork drops the memo; the replay fork must actually hit it.
fn compare_leaf(p: &Program, symbol: &str, args: &[Type], rooted: bool) {
    let mut seed = checker(p);
    seed.co_checking = true;
    if rooted {
        seed.current_co_method = Some(("Owner".into(), "method".into()));
    }
    call(&mut seed, symbol, args);
    assert!(seed.errors.is_empty(), "{:?}", seed.errors);
    assert!(!seed.elaboration_memo.is_empty(), "{symbol}");
    let mut walked = EffectSnapshot::fork(&seed);
    let mut replayed = EffectSnapshot::fork(&seed);
    walked.elaboration_memo.clear();
    // The caller consumes the resolved return: a walk may return a bound
    // fresh hole where the memo returns that hole's already resolved value.
    let a = call(&mut walked, symbol, args);
    let a = walked.resolve(&a);
    let b = call(&mut replayed, symbol, args);
    let b = replayed.resolve(&b);
    assert_eq!(replayed.stats.co_hits, seed.stats.co_hits + 1);
    assert_eq!(walked.stats.co_hits, seed.stats.co_hits);
    assert!(walked.instance_returns.is_empty());
    assert!(replayed.instance_returns.is_empty());
    let mut ah = EffectHistory::new(&seed);
    let mut bh = EffectHistory::new(&seed);
    ah.boundary(&walked);
    bh.boundary(&replayed);
    EffectSnapshot::capture(&walked, args, &a, &ah)
        .compare(&EffectSnapshot::capture(&replayed, args, &b, &bh))
        .unwrap();
}

/// Structural leaves preserve all effects for rooted and rootless co-checks.
#[test]
fn construction_leaf_effects_match() {
    for source in [
        "fun leaf(x) { return x }",
        "fun leaf(x) { let copy = x\nreturn [copy, x] }",
        "type Box = { item }\nfun leaf(x) { return Box { item: x } }",
        "type Choice = Empty | Full { item }\nfun leaf(x) { return Choice.Full { item: x } }",
    ] {
        let p = program(source);
        for rooted in [false, true] {
            compare_leaf(&p, "leaf", &[Type::Str], rooted);
        }
    }
}

/// Use the actual prelude constructor rather than a simplified test substitute.
/// Its two payloads share the construction spans but retain distinct instances.
#[test]
fn actual_error_leaf_preserves_both_payload_instances() {
    let ast = brass_parser::parse(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../core/error.cz"
    )))
    .unwrap();
    let (p, errors) = brass_hir::lower(&[LoadedModule {
        is_prelude: true,
        path: vec!["error".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    let function = p
        .functions
        .values()
        .find(|f| f.signature.name == "error")
        .unwrap();
    let location = p
        .types
        .values()
        .find(|ty| ty.name == "Location")
        .unwrap()
        .type_ref();
    for rooted in [false, true] {
        for payload in [Type::Int(IntKind::I32), Type::Str] {
            compare_leaf(&p, &function.symbol, &[payload, location.clone()], rooted);
        }
    }
    let mut c = checker(&p);
    c.co_checking = true;
    for _ in 0..2 {
        for payload in [Type::Int(IntKind::I32), Type::Str] {
            call(&mut c, &function.symbol, &[payload, location.clone()]);
        }
    }
    assert!(c.errors.is_empty(), "{:?}", c.errors);
    assert_eq!((c.stats.co_hits, c.stats.co_misses), (2, 2));
    assert!(c.instance_returns.is_empty());
    let payloads: std::collections::HashSet<_> = c.instance_typed.iter()
        .filter(|item| matches!(&item.tag.callable, brass_hir::InstanceCallable::Function(symbol) if symbol == &function.symbol))
        .map(|item| item.tag.args[0].clone())
        .collect();
    assert!(payloads.contains(&Type::Str));
    assert!(payloads.contains(&Type::Int(IntKind::I32)));
    // Replay both instantiations through separate boundaries in one checker:
    // agreement per payload alone would not catch cross-instance poisoning.
    let mut walked = EffectSnapshot::fork(&c);
    let mut replayed = EffectSnapshot::fork(&c);
    walked.elaboration_memo.clear();
    let mut ah = EffectHistory::new(&c);
    let mut bh = EffectHistory::new(&c);
    let mut inputs = Vec::new();
    let mut a = Vec::new();
    let mut b = Vec::new();
    for payload in [Type::Int(IntKind::I32), Type::Str] {
        let args = [payload, location.clone()];
        let returned = call(&mut walked, &function.symbol, &args);
        a.push(walked.resolve(&returned));
        let returned = call(&mut replayed, &function.symbol, &args);
        b.push(replayed.resolve(&returned));
        inputs.extend(args);
        ah.boundary(&walked);
        bh.boundary(&replayed);
    }
    EffectSnapshot::capture(&walked, &inputs, &Type::Tuple(a), &ah)
        .compare(&EffectSnapshot::capture(
            &replayed,
            &inputs,
            &Type::Tuple(b),
            &bh,
        ))
        .unwrap();
}
