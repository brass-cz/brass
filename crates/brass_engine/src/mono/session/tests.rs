use super::*;

/// Lower a standalone source without loading packages.
pub(super) fn program(source: &str) -> Program {
    let ast = brass_parser::parse(source).unwrap();
    let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    program
}

/// Compare all owned mono facts and borrowed bodies deterministically.
pub(super) fn snapshot(result: Result<MonoProgram<'_>, MonoStop>) -> String {
    match result {
        Err(stop) => format!("{stop:?}"),
        Ok(mono) => {
            let mut functions: Vec<_> = mono
                .functions
                .iter()
                .map(|f| {
                    format!(
                        "{} {:?} {:?} {:?} {:?} {} {} {:?} {:?} {:?}",
                        f.symbol,
                        f.type_args,
                        f.ret,
                        f.local_types,
                        f.captures,
                        f.is_closure,
                        f.fallible,
                        f.keyed,
                        f.closure_targets,
                        f.body
                    )
                })
                .collect();
            functions.sort();
            let mut deferred: Vec<_> = mono
                .deferred
                .iter()
                .map(|(s, d)| format!("{s} {d:?}"))
                .collect();
            deferred.sort();
            format!(
                "{functions:?} {:?} {:?} {:?} {deferred:?}",
                mono.globals, mono.init_symbols, mono.main_skip
            )
        }
    }
}

#[test]
fn warm_roots_restore_globals_closures_and_recursive_instances() {
    let program = program(
        "let global = 3\nfun fib(n: int32) -> int32 { if n < 2 { return n }\n return fib(n - 1) + fib(n - 2) }\nfun main() { let offset = 2\n let f = (x) -> x + offset + global\n println(f(fib(4))) }\n",
    );
    let mir = brass_mir::lower_program(&program);
    let mut session = MonoSession::default();
    let fresh = monomorphize_entry_with_returns(&mir, &program, true, HashMap::default()).unwrap();
    assert!(
        fresh
            .functions
            .iter()
            .any(|f| f.is_closure && !f.captures.is_empty())
    );
    let expected = snapshot(Ok(fresh));
    assert!(
        !expected.contains("Fail(")
            && !expected.contains("MissingBodies")
            && !expected.contains("Some(\""),
        "{expected}"
    );
    let changes = brass_mir::ChangedInputs::since(0);
    assert_eq!(
        snapshot(session.entry(&mir, &program, true, HashMap::default(), &changes)),
        expected
    );
    let ids = session.cache.next_id;
    assert_eq!(
        snapshot(session.entry(&mir, &program, true, HashMap::default(), &changes)),
        expected
    );
    assert_eq!(session.cache.next_id, ids, "every warm root must replay");
    assert!(!session.cache.scans.is_empty());
}

#[test]
fn negative_contract_reads_wake_demands_and_removals_restore_them() {
    let program = program("fun missing(x) { return x }\nfun main() { println(missing(1)) }\n");
    let mut mir = brass_mir::lower_program(&program);
    mir.functions.retain(|f| f.symbol == "main");
    let mut session = MonoSession::default();
    let changes = brass_mir::ChangedInputs::since(0);
    let expected = snapshot(monomorphize_entry_with_returns(
        &mir,
        &program,
        true,
        HashMap::default(),
    ));
    assert!(expected.contains("MissingBodies"), "{expected}");
    assert_eq!(
        snapshot(session.entry(&mir, &program, true, HashMap::default(), &changes)),
        expected
    );
    let id = session.cache.next_id;
    assert_eq!(
        snapshot(session.entry(&mir, &program, true, HashMap::default(), &changes)),
        expected
    );
    assert_eq!(session.cache.next_id, id);
    let key = ("missing".to_string(), vec![Type::Int(IntKind::I32)]);
    let returns = HashMap::from_iter([(key.clone(), Type::Int(IntKind::I32))]);
    let mut changed = brass_mir::ChangedInputs::since(0);
    changed.epoch = 1;
    changed.returns.change(key.clone());
    let expected_ready = snapshot(monomorphize_entry_with_returns(
        &mir,
        &program,
        true,
        returns.clone(),
    ));
    assert!(
        !expected_ready.contains("MissingBodies"),
        "{expected_ready}"
    );
    assert_eq!(
        snapshot(session.entry(&mir, &program, true, returns.clone(), &changed)),
        expected_ready
    );
    assert!(session.cache.next_id > id);
    let warm = brass_mir::ChangedInputs::since(1);
    assert_eq!(
        snapshot(session.entry(&mir, &program, true, returns, &warm)),
        expected_ready
    );
    let mut removed = brass_mir::ChangedInputs::since(1);
    removed.epoch = 2;
    removed.returns.remove(key);
    assert_eq!(
        snapshot(session.entry(&mir, &program, true, HashMap::default(), &removed)),
        expected
    );
}

#[test]
fn unchanged_and_unrelated_refreshes_reuse_but_missing_epochs_reset() {
    let program = program("fun main() { println(1) }\n");
    let mir = brass_mir::lower_program(&program);
    let mut session = MonoSession::default();
    let run = |session: &mut MonoSession, changes: &brass_mir::ChangedInputs| {
        snapshot(session.entry(&mir, &program, true, HashMap::default(), changes))
    };
    let first = run(&mut session, &brass_mir::ChangedInputs::since(0));
    let id = session.cache.next_id;
    let mut unrelated = brass_mir::ChangedInputs::since(0);
    unrelated.epoch = 1;
    unrelated
        .returns
        .change(("unused".into(), vec![Type::Bool]));
    assert_eq!(run(&mut session, &unrelated), first);
    assert_eq!(session.cache.next_id, id);
    assert_eq!(
        run(&mut session, &brass_mir::ChangedInputs::since(2)),
        first
    );
    assert!(session.cache.next_id > id);
    let generation = session.cache.generation;
    let mut body_only = brass_mir::ChangedInputs::since(2);
    body_only.full_reset = true;
    assert_eq!(run(&mut session, &body_only), first);
    assert!(session.cache.generation > generation);
}

#[test]
fn span_reads_include_absent_seeds_and_dispatch_and_preserve_exact_keys() {
    // A read in a closure's inherited instance must stay distinct from another
    // instance at the same span. Span invalidation conservatively wakes both.
    let program = program("fun f(x) { return x }\n");
    let mir = brass_mir::lower_program(&program);
    let mut session = MonoSession::default();
    let mut mono = Monomorphizer::new(&mir, &program);
    mono.session = session.start(
        &mir,
        &brass_mir::ChangedInputs::since(0),
        Context::Entry(true),
    );
    let seed = brass_parser::Span::new(100, 101);
    let dispatch = brass_parser::Span::new(102, 103);
    let mut decl = mir.functions[0].body.locals[0].clone();
    decl.seed_site = Some(seed);
    mono.local_seed(&decl);
    assert!(mono.keyed_target(dispatch, "missing").is_err());
    let reads = mono.session.reads.borrow();
    assert!(reads.contains(&Read::Seed(seed)));
    assert!(reads.contains(&Read::Dispatch(dispatch)));
    let mut changes = brass_mir::ChangedInputs::since(0);
    changes.instance_seeds.remove(seed);
    changes.instance_dispatch.change(dispatch);
    assert!(reads.iter().all(|read| read.changed(&changes)));
    let key = |ty| Root::Function {
        base: "f".into(),
        args: vec![ty],
        instance: brass_hir::InstanceKey::function(&program, "f", &[Type::Bool]),
    };
    assert_ne!(key(Type::Bool), key(Type::Str));
    // Whole InstanceKey equality is used, without projecting its fields.
    let left = Root::Function {
        base: "f".into(),
        args: vec![Type::Bool],
        instance: brass_hir::InstanceKey::function(&program, "f", &[Type::Bool]),
    };
    let right = Root::Function {
        base: "f".into(),
        args: vec![Type::Bool],
        instance: brass_hir::InstanceKey::function(&program, "f", &[Type::Str]),
    };
    assert_ne!(left, right);
}

#[test]
fn runtime_contexts_do_not_share_different_globals_or_argument_types() {
    let program = program("let value = 1\nfun f(x) { return value + x }\n");
    let mir = brass_mir::lower_program(&program);
    let mut session = MonoSession::default();
    let changes = brass_mir::ChangedInputs::since(0);
    for ty in [Type::Int(IntKind::I32), Type::Int(IntKind::I64)] {
        let target = DeferredSig {
            base: "f".into(),
            type_args: vec![ty.clone()],
            params: vec![ty.clone()],
            ret: ty.clone(),
        };
        let globals = vec![(global_name(&mir), ty)];
        let expected = snapshot(monomorphize_instance_deferred_with_returns(
            &mir,
            &program,
            "f",
            target.type_args.clone(),
            &globals,
            HashMap::default(),
        ));
        assert!(!expected.contains("Fail("), "{expected}");
        assert_eq!(
            snapshot(session.instance(
                &mir,
                &program,
                &target,
                &globals,
                HashMap::default(),
                &changes
            )),
            expected
        );
        let id = session.cache.next_id;
        assert_eq!(
            snapshot(session.instance(
                &mir,
                &program,
                &target,
                &globals,
                HashMap::default(),
                &changes
            )),
            expected
        );
        assert_eq!(session.cache.next_id, id);
    }
}

#[test]
fn failed_recursive_root_never_retains_partial_descendants() {
    let program = program(
        "fun a(n: int32) -> int32 { return b(n) }\nfun b(n: int32) -> int32 { if n == 0 { return a(1) }\n return missing(n) }\nfun missing(n) { return n }\nfun main() { println(a(1)) }\n",
    );
    let mut mir = brass_mir::lower_program(&program);
    mir.functions.retain(|f| f.symbol != "missing");
    let mut session = MonoSession::default();
    let expected = snapshot(monomorphize_entry_with_returns(
        &mir,
        &program,
        true,
        HashMap::default(),
    ));
    assert!(expected.contains("MissingBodies"), "{expected}");
    let changes = brass_mir::ChangedInputs::since(0);
    for _ in 0..2 {
        assert_eq!(
            snapshot(session.entry(&mir, &program, true, HashMap::default(), &changes)),
            expected
        );
        assert!(
            session
                .cache
                .entries
                .values()
                .filter(|entry| entry.result.is_err())
                .all(|entry| entry.facts.is_empty())
        );
    }
}

#[test]
fn replay_keeps_cross_root_demand_order_and_needs_body_merge() {
    let program = program(
        "fun missing(x) { return x }\nlet first = missing(1)\nfun main() { let f = () -> missing(1)\n println(f()) }\n",
    );
    let mut mir = brass_mir::lower_program(&program);
    mir.functions.retain(|f| f.symbol != "missing");
    let mut session = MonoSession::default();
    let changes = brass_mir::ChangedInputs::since(0);
    let expected = snapshot(monomorphize_entry_with_returns(
        &mir,
        &program,
        true,
        HashMap::default(),
    ));
    assert!(
        expected.contains("true"),
        "closure demand needs the body: {expected}"
    );
    for _ in 0..2 {
        assert_eq!(
            snapshot(session.entry(&mir, &program, true, HashMap::default(), &changes)),
            expected
        );
    }
}

#[test]
fn refreshed_seed_types_match_fresh_local_types() {
    let program = program("fun main() { let xs = []\n println(xs) }\n");
    let mut mir = brass_mir::lower_program(&program);
    let body = &mir
        .functions
        .iter()
        .find(|f| f.symbol == "main")
        .unwrap()
        .body;
    let span = body
        .locals
        .iter()
        .find_map(|decl| decl.seed_site)
        .expect("array seed site");
    let instance = brass_hir::InstanceKey::function(&program, "main", &[]).unwrap();
    let mut session = MonoSession::default();
    let mut prior = String::new();
    for (epoch, kind) in [IntKind::I32, IntKind::I64].into_iter().enumerate() {
        mir.instance_seeds.insert(
            span,
            HashMap::from_iter([(instance.clone(), Type::Slice(Box::new(Type::Int(kind))))]),
        );
        let mut changes = brass_mir::ChangedInputs::since(epoch as u64);
        changes.epoch += 1;
        changes.instance_seeds.change(span);
        let expected = snapshot(monomorphize_entry_with_returns(
            &mir,
            &program,
            true,
            HashMap::default(),
        ));
        assert_ne!(expected, prior);
        assert_eq!(
            snapshot(session.entry(&mir, &program, true, HashMap::default(), &changes)),
            expected
        );
        let warm = brass_mir::ChangedInputs::since(changes.epoch);
        let id = session.cache.next_id;
        assert_eq!(
            snapshot(session.entry(&mir, &program, true, HashMap::default(), &warm)),
            expected
        );
        assert_eq!(session.cache.next_id, id);
        prior = expected;
    }
}

#[test]
fn a_global_change_invalidates_the_same_runtime_target() {
    let program = program("let value = 1\nfun f() { return value }\n");
    let mir = brass_mir::lower_program(&program);
    let target = DeferredSig {
        base: "f".into(),
        type_args: Vec::new(),
        params: Vec::new(),
        ret: Type::Int(IntKind::I32),
    };
    let mut session = MonoSession::default();
    let changes = brass_mir::ChangedInputs::since(0);
    let mut previous = String::new();
    for ty in [Type::Int(IntKind::I32), Type::Str] {
        // Only the supplied global environment changes, not the target identity,
        // MIR bodies or channel epoch. A cached local/return type must not survive.
        let globals = vec![(global_name(&mir), ty)];
        let expected = snapshot(monomorphize_instance_deferred_with_returns(
            &mir,
            &program,
            "f",
            Vec::new(),
            &globals,
            HashMap::default(),
        ));
        assert!(!expected.contains("Fail("), "{expected}");
        assert_ne!(expected, previous);
        assert_eq!(
            snapshot(session.instance(
                &mir,
                &program,
                &target,
                &globals,
                HashMap::default(),
                &changes
            )),
            expected
        );
        previous = expected;
    }
}

fn global_name(mir: &MirProgram) -> String {
    mir.inits
        .iter()
        .flat_map(|init| &init.body.blocks)
        .flat_map(|block| &block.stmts)
        .find_map(|stmt| match stmt {
            MirStmt::SetGlobal(name, _) => Some(name.clone()),
            _ => None,
        })
        .expect("initializer global")
}
