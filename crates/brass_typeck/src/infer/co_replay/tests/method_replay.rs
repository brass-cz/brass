//! Closed method replay preserves complete effects and validates shared reads.

use super::{call, checker, program};
use crate::infer::co_replay::snapshot::{EffectHistory, EffectSnapshot};
use crate::infer::journal::MemoFlavor;
use brass_hir::{IntKind, Type};

/// Both forks start with identical solver and channel histories. Only one may
/// consume the recorded method entries; its enclosing function still walks.
fn compare_methods(source: &str, inputs: &[Vec<Type>], rooted: bool) {
    let p = program(source);
    let mut seed = checker(&p);
    seed.co_checking = true;
    if rooted {
        seed.current_co_method = Some(("A".into(), "first".into()));
    }
    for _ in 0..2 {
        for args in inputs {
            // Keep method entries but force the enclosing free function to walk
            // so the second touch reaches each method instead of replaying it.
            seed.elaboration_memo
                .retain(|_, entry| entry.method_dependencies.is_some());
            call(&mut seed, "entry", args);
        }
    }
    assert!(seed.errors.is_empty(), "{:?}", seed.errors);
    assert!(
        seed.elaboration_memo
            .values()
            .any(|entry| entry.method_dependencies.is_some())
    );
    seed.elaboration_memo
        .retain(|_, entry| entry.method_dependencies.is_some());
    if rooted {
        seed.current_co_method = Some(("B".into(), "second".into()));
    }
    let mut walk = EffectSnapshot::fork(&seed);
    let mut replay = EffectSnapshot::fork(&seed);
    let mut wh = EffectHistory::new(&seed);
    let mut rh = EffectHistory::new(&seed);
    for args in inputs {
        walk.elaboration_memo.clear();
        replay
            .elaboration_memo
            .retain(|_, entry| entry.method_dependencies.is_some());
        let hits = replay.stats.co_hits;
        let a = call(&mut walk, "entry", args);
        let b = call(&mut replay, "entry", args);
        assert!(replay.stats.co_hits > hits, "method must hit");
        assert!(walk.errors.is_empty(), "{:?}", walk.errors);
        wh.boundary(&walk);
        rh.boundary(&replay);
        if std::env::var("BRASS_MEMO_CHECK").as_deref() != Ok("1") {
            EffectSnapshot::capture(&walk, args, &walk.resolve(&a), &wh)
                .compare(&EffectSnapshot::capture(
                    &replay,
                    args,
                    &replay.resolve(&b),
                    &rh,
                ))
                .unwrap();
        }
        assert!(replay.instance_returns.is_empty());
    }
}

/// Concrete receiver payloads retain distinct keys; nested generic returns keep
/// ordered co links under both different roots and rootless execution.
#[test]
fn closed_receivers_replay_nested_effects_at_two_payloads() {
    let source = "type Box = { value }\nfun choose(x, flag: bool) { if flag { return [] }\nreturn [x] }\nfun Box.text(self, flag: bool) -> string { let value = choose(self.value, flag)\nreturn \"done\" }\nfun entry(x, flag: bool) { return Box { value: x }.text(flag) }";
    for rooted in [false, true] {
        compare_methods(
            source,
            &[
                vec![Type::Str, Type::Bool],
                vec![Type::Int(IntKind::I64), Type::Bool],
            ],
            rooted,
        );
    }
}

/// Static and variant-qualified entries preserve the same complete snapshots.
#[test]
fn static_and_variant_methods_replay_separate_identities() {
    for source in [
        "type Item = { value: string }\nfun Item.make(x: string) -> Item { return Item { value: x } }\nfun entry(x: string) { return Item.make(x) }",
        "type Choice = | A { value: string } | B { value: string }\nfun Choice.get(self) -> string { return self.value }\nfun entry(x: string) { return [Choice.A { value: x }.get(), Choice.B { value: x }.get()] }",
    ] {
        for rooted in [false, true] {
            compare_methods(source, &[vec![Type::Str]], rooted);
        }
    }
}

/// Receiver declarations use function elaboration but require method certificates.
#[test]
fn annotated_receiver_function_has_method_certificate() {
    let (p, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        path: vec!["core".into()],
        is_prelude: true,
        ast: brass_parser::parse("fun string.copy_value(self) -> string { return self }").unwrap(),
    }]);
    assert!(errors.is_empty());
    let mut c = checker(&p);
    c.co_checking = true;
    let symbol = &p
        .functions
        .values()
        .find(|f| f.decl.recv.is_some())
        .unwrap()
        .symbol;
    call(&mut c, symbol, &[Type::Str]);
    assert!(c.elaboration_memo.is_empty());
    assert_eq!((c.stats.co_misses, c.stats.co_walks), (1, 0));
    assert_eq!(c.method_co_seen.len(), 1);
    assert!(c.elaboration_journals.is_empty());
    call(&mut c, symbol, &[Type::Str]);
    assert!(
        c.elaboration_memo
            .values()
            .any(|entry| entry.method_dependencies.is_some())
    );
    let hits = c.stats.co_hits;
    call(&mut c, symbol, &[Type::Str]);
    assert_eq!(c.stats.co_hits, hits + 1);
    assert!(c.instance_returns.is_empty());
}

/// A qualified read retained by an ordinary entry must reach every enclosing
/// journal when that entry is replayed, without borrowing its reporting name.
#[test]
fn ordinary_and_co_entries_retain_transitive_qualified_reads() {
    let p = program("const value = \"ok\"\nfun leaf() -> string { return value }");
    for co in [false, true] {
        let mut c = checker(&p);
        c.co_checking = co;
        c.global_defs.insert(
            vec!["main".into()],
            [("value".into(), Type::Str)].into_iter().collect(),
        );
        call(&mut c, "leaf", &[]);
        let context = c
            .co_memo_context(c.elaboration_memo_key("fn", "leaf", None, &[], &[]))
            .unwrap();
        let entry = c.elaboration_memo[&context.key].clone();
        let reads = entry.global_reads.as_ref().unwrap();
        assert_eq!(reads.reads.len(), 1);
        assert_eq!(reads.reads[0].0.module, ["main"]);
        assert_eq!(reads.reads[0].0.name, "value");
        assert_eq!(reads.reads[0].1, Type::Str);
        c.begin_elaboration_journal();
        c.begin_elaboration_journal();
        c.replay_elaboration_memo_entry(&entry, &context);
        let child = c.finish_elaboration_journal();
        let parent = c.finish_elaboration_journal();
        assert_eq!(&child.global_reads, reads.as_ref());
        assert_eq!(&parent.global_reads, reads.as_ref());
        assert!(parent.memo_replayed);
    }
}

/// Method certificates invalidate on qualified global settlement, scheme
/// replacement and fallback changes; ordinary lookup is not changed by metadata.
#[test]
fn method_certificates_reject_stale_shared_state() {
    let p = program("fun leaf() -> string { return \"ok\" }");
    let mut c = checker(&p);
    c.global_defs.insert(
        vec!["main".into()],
        [("value".into(), Type::Str)].into_iter().collect(),
    );
    c.current_module = vec!["main".into()];
    let mut context = c
        .elaboration_memo_key("m", "Item::read", Some(&Type::Str), &[], &[])
        .unwrap();
    context.key.flavor = MemoFlavor::CoCheck { has_root: false };
    let initial = c.method_memo_dependencies(None, &Type::Str);
    c.begin_elaboration_journal();
    c.record_global_dependency("value", &Type::Str, false);
    let frame = c.finish_elaboration_journal();
    assert!(c.method_storage_precheck("Item::read", true, &frame));
    let mut untracked = frame.clone();
    untracked.global_reads.untracked = true;
    assert!(!c.method_storage_precheck("Item::read", true, &untracked));
    assert!(c.method_storage_precheck("Item::read", false, &untracked));
    let mut rejected = c
        .build_elaboration_memo_entry(&Type::Str, untracked, &context)
        .unwrap();
    assert!(!c.certify_method_entry("Item::read", false, &mut rejected, Some(initial.clone()),));
    let mut entry = c
        .build_elaboration_memo_entry(&Type::Str, frame, &context)
        .unwrap();
    assert!(c.certify_method_entry("Item::read", false, &mut entry, Some(initial.clone())));
    c.elaboration_memo
        .insert(context.key.clone(), std::rc::Rc::new(entry));
    assert!(
        c.lookup_elaboration_entry(&context, Some(&initial))
            .is_some()
    );
    c.global_defs
        .get_mut(&vec!["main".into()])
        .unwrap()
        .insert("value".into(), Type::Bool);
    assert!(
        c.lookup_elaboration_entry(&context, Some(&initial))
            .is_none()
    );
    c.global_defs
        .get_mut(&vec!["main".into()])
        .unwrap()
        .insert("value".into(), Type::Str);
    let changed_return = c.method_memo_dependencies(None, &Type::Bool);
    assert!(
        c.lookup_elaboration_entry(&context, Some(&changed_return))
            .is_none()
    );
    c.observe_scheme_install();
    let changed_scheme = c.method_memo_dependencies(None, &Type::Str);
    assert!(
        c.lookup_elaboration_entry(&context, Some(&changed_scheme))
            .is_none()
    );
    assert!(c.lookup_elaboration_entry(&context, None).is_some());
}

/// Probes and unresolved inputs are rejected before any method key is built.
#[test]
fn method_precheck_rejects_open_and_probe_frames() {
    let p = program("fun entry() {}");
    let mut c = checker(&p);
    let unknown = c.fresh_unknown();
    assert_eq!(
        c.method_co_precheck(Some(&unknown), &[], &[], Some(&Type::Str), &Type::Str),
        Some("open_frame")
    );
    assert_eq!(
        c.method_co_precheck(
            Some(&Type::Str),
            &[],
            &[Some(unknown.clone())],
            Some(&Type::Str),
            &Type::Str
        ),
        Some("open_frame")
    );
    assert_eq!(
        c.method_co_precheck(Some(&Type::Str), &[], &[], None, &unknown),
        Some("open_return")
    );
    c.speculation_depth = 1;
    assert_eq!(
        c.method_co_precheck(Some(&Type::Str), &[], &[], Some(&Type::Str), &Type::Str),
        Some("speculative")
    );
    c.speculation_depth = 0;
    c.numeric.probing = true;
    assert_eq!(
        c.method_co_precheck(Some(&Type::Str), &[], &[], Some(&Type::Str), &Type::Str),
        Some("numeric_probe")
    );
}

/// Recursive method fallbacks have no exact shared-return provenance and cannot
/// enter the cache even when their concrete declared return would mask the read.
#[test]
fn recursive_method_walk_stays_uncertified() {
    let p = program(
        "type Item = { value: string }\nfun Item.again(self, flag: bool) -> string { if flag { return self.value }\nreturn self.again(true) }\nfun entry(flag: bool) { return Item { value: \"ok\" }.again(flag) }",
    );
    let mut c = checker(&p);
    c.co_checking = true;
    call(&mut c, "entry", &[Type::Bool]);
    assert!(c.errors.is_empty(), "{:?}", c.errors);
    assert!(
        c.elaboration_memo
            .values()
            .all(|entry| entry.method_dependencies.is_none())
    );
}

/// Transitive depth caps withhold every affected method entry; the whole call
/// chain includes its free-function root when counting the 63/64/65 boundary.
#[test]
fn method_depth_boundary_never_certifies_capped_returns() {
    // Match the CLI checker's worker stack, as the free-function cap test does.
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(check_method_depth_boundaries)
        .unwrap()
        .join()
        .unwrap();
}

/// Exercise depth limits with the same stack allowance as production checking.
fn check_method_depth_boundaries() {
    for depth in [63, 64, 65] {
        let mut source = String::from("type Item = { value: string }\n");
        for index in 0..depth - 1 {
            let ret = if index + 1 == depth - 1 {
                "self.value".into()
            } else {
                format!("self.f{}()", index + 1)
            };
            source.push_str(&format!(
                "fun Item.f{index}(self) -> string {{ return {ret} }}\n"
            ));
        }
        source.push_str("fun entry() { return Item { value: \"ok\" }.f0() }");
        let p = program(&source);
        let mut c = checker(&p);
        c.co_checking = true;
        c.numeric_enabled = false;
        call(&mut c, "entry", &[]);
        c.elaboration_memo.clear();
        call(&mut c, "entry", &[]);
        assert!(c.errors.is_empty(), "{:?}", c.errors);
        assert_eq!(c.depth_capped != 0, depth >= 64);
        assert_eq!(
            c.elaboration_memo
                .values()
                .any(|entry| entry.method_dependencies.is_some()),
            depth < 64
        );
        assert!(c.instance_returns.is_empty());
    }
}

/// An unjournaled first child walk feeds an admitted parent's channels, ordered
/// links and qualified reads exactly as a journaled child does. The parent entry
/// then replays the complete effects even though the child has no stored entry.
#[test]
fn first_touch_inside_admitted_parent_preserves_effects() {
    let p = program(
        "const value = \"ok\"\ntype Item = { value: string }\nfun choose(x, flag: bool) { if flag { return [] }\nreturn [x] }\nfun Item.inner(self, flag: bool) -> string { let values = choose(value, flag)\nreturn self.value }\nfun Item.outer(self, flag: bool) -> string { return self.inner(flag) }\nfun entry(flag: bool) { return Item { value: \"ok\" }.outer(flag) }",
    );
    let mut seed = checker(&p);
    seed.co_checking = true;
    seed.current_co_method = Some(("Root".into(), "method".into()));
    seed.global_defs.insert(
        vec!["main".into()],
        [("value".into(), Type::Str)].into_iter().collect(),
    );
    seed.global_scopes.clear();
    call(&mut seed, "entry", &[Type::Bool]);
    assert!(seed.errors.is_empty(), "{:?}", seed.errors);
    let touched = seed.method_co_seen.clone();
    // Construct the storage-policy boundary directly: the parent has been seen,
    // while this child's canonical key has not. Solver state is identical.
    seed.method_co_seen
        .retain(|key| key.callable.ends_with(":outer"));
    assert_eq!(seed.method_co_seen.len(), 1);
    seed.elaboration_memo.clear();
    let mut first = EffectSnapshot::fork(&seed);
    let mut journaled = EffectSnapshot::fork(&seed);
    journaled.method_co_seen = touched;
    let mut fh = EffectHistory::new(&seed);
    let mut jh = EffectHistory::new(&seed);
    let a = call(&mut first, "entry", &[Type::Bool]);
    let b = call(&mut journaled, "entry", &[Type::Bool]);
    fh.boundary(&first);
    jh.boundary(&journaled);
    EffectSnapshot::capture(&first, &[Type::Bool], &a, &fh)
        .compare(&EffectSnapshot::capture(&journaled, &[Type::Bool], &b, &jh))
        .unwrap();
    assert!(first.elaboration_journals.is_empty());
    assert!(
        !first
            .elaboration_memo
            .keys()
            .any(|key| key.callable.ends_with(":inner"))
    );
    assert!(
        journaled
            .elaboration_memo
            .keys()
            .any(|key| key.callable.ends_with(":inner")),
        "memo={:?}, errors={:?}",
        journaled.elaboration_memo.keys(),
        journaled.errors
    );
    let (key, entry) = first
        .elaboration_memo
        .iter()
        .find(|(key, _)| key.callable.ends_with(":outer"))
        .unwrap();
    let deps = entry.method_dependencies.as_ref().unwrap();
    assert_eq!(deps.globals.len(), 1);
    assert_eq!(deps.globals[0].0.module, ["main"]);
    assert_eq!(deps.globals[0].0.name, "value");
    assert_eq!(deps.globals[0].1, Type::Str);
    assert_eq!(
        entry.global_reads,
        journaled.elaboration_memo[key].global_reads
    );
    assert!(entry.observation_counts().1 > 0);
    first
        .elaboration_memo
        .retain(|key, _| key.callable.ends_with(":outer"));
    let mut walk = EffectSnapshot::fork(&first);
    let mut replay = EffectSnapshot::fork(&first);
    walk.elaboration_memo.clear();
    let mut wh = EffectHistory::new(&first);
    let mut rh = EffectHistory::new(&first);
    let hits = replay.stats.co_hits;
    let a = call(&mut walk, "entry", &[Type::Bool]);
    let b = call(&mut replay, "entry", &[Type::Bool]);
    assert!(replay.stats.co_hits > hits);
    wh.boundary(&walk);
    rh.boundary(&replay);
    if std::env::var("BRASS_MEMO_CHECK").as_deref() != Ok("1") {
        EffectSnapshot::capture(&walk, &[Type::Bool], &a, &wh)
            .compare(&EffectSnapshot::capture(&replay, &[Type::Bool], &b, &rh))
            .unwrap();
    }
}
