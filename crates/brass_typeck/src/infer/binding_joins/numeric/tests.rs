use brass_hir::{IntKind, LoadedModule, Type, TypedExprKind};

fn program(source: &str) -> brass_hir::Program {
    let (program, errors) = brass_hir::lower(&[LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast: brass_parser::parse(source).expect("parse"),
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    program
}

fn analyze(source: &str) -> crate::Analysis {
    crate::analyze(&program(source))
}

fn binding_types(result: &crate::Analysis, name: &str) -> Vec<Type> {
    let first = result
        .typed
        .expressions
        .iter()
        .filter(|e| matches!(&e.kind, TypedExprKind::Ident(n) if n == name))
        .map(|e| e.span.lo)
        .min();
    result
        .typed
        .expressions
        .iter()
        .filter(|e| {
            Some(e.span.lo) == first && matches!(&e.kind, TypedExprKind::Ident(n) if n == name)
        })
        .map(|e| e.ty.clone())
        .collect()
}

#[test]
fn defaults_are_floors_and_arithmetic_demands_reach_copied_sources() {
    let result = analyze(
        "fun main() {\nlet tiny: int8 = 1\nlet fixed = 0\nfixed = tiny\nlet x = 0\nlet copy = x\nlet sum = copy + 1\nlet wide: int64 = 5000000000\nsum = wide\n}\n",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    for name in ["x", "copy", "sum"] {
        let types = binding_types(&result, name);
        assert!(!types.is_empty(), "missing {name}");
        assert!(
            types.iter().all(|ty| *ty == Type::Int(IntKind::I64)),
            "{name}: {types:?}"
        );
    }
    assert!(
        binding_types(&result, "fixed")
            .iter()
            .all(|ty| *ty == Type::Int(IntKind::I32))
    );
}

#[test]
fn folded_arms_use_the_least_self_consistent_solution() {
    let result = analyze(
        "fun main() {\nlet x = 0\nlet wide: int64 = 5000000000\nif x : int64 { x = wide }\n}\n",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert!(
        binding_types(&result, "x")
            .iter()
            .all(|ty| *ty == Type::Int(IntKind::I32))
    );
    let conflict = analyze(
        "fun main() {\nlet x = 0\nlet wide: int64 = 5000000000\nif x : int32 { x = wide }\n}\n",
    );
    assert!(
        conflict
            .errors
            .iter()
            .any(|e| e.message.contains("no self-consistent type")),
        "{:?}",
        conflict.errors
    );
}

#[test]
fn typed_shadow_does_not_inherit_the_hidden_bindings_origin() {
    let result = analyze(
        "fun main() {\nlet x = 0\nlet value: int32 = 0\nlet x = value\nlet wide: int64 = 5000000000\nx = wide\n}\n",
    );
    assert!(!result.errors.is_empty());
    assert!(
        binding_types(&result, "x")
            .iter()
            .all(|ty| *ty == Type::Int(IntKind::I32))
    );
}

#[test]
fn returned_local_origins_have_distinct_completed_instance_contracts() {
    let result = analyze(
        "fun seed() {\nlet x = 0\nreturn x\n}\nfun main() {\nlet a = seed()\nlet wide: int64 = 5000000000\na = wide\nlet b = seed()\n}\n",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert!(
        result
            .numeric_calls
            .values()
            .flatten()
            .any(|layout| layout.iter().any(|(_, ty)| *ty == Type::Int(IntKind::I64)))
    );
    assert!(result.numeric_calls.values().any(Option::is_none));
}

#[test]
fn typed_instances_remove_a_numeric_only_shared_storage_seed() {
    let program = program(
        "fun copy(v) { let x = v\nreturn x }\nfun main() { let value = copy(1)\nlet wide: int64 = 5000000000\nvalue = wide\ncopy(\"s\") }\n",
    );
    let result = crate::analyze(&program);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let span = result
        .typed
        .expressions
        .iter()
        .find(|e| {
            matches!(
                &e.kind,
                TypedExprKind::NumericBinding | TypedExprKind::InstanceNumericBinding
            ) && e.ty == Type::Int(IntKind::I64)
        })
        .unwrap()
        .span;
    let shared = crate::stream::aggregate_result_types(&result.typed, &program);
    assert!(!shared.contains_key(&span));
    let seeds = crate::stream::aggregate_instance_seeds(
        &result.instance_typed,
        &result.typed,
        &shared,
        &program,
    );
    let types = &seeds[&span];
    assert!(!types.keys().any(|key| key.args == [Type::Str]));
    assert!(types.values().any(|ty| *ty == Type::Int(IntKind::I64)));
}

#[test]
fn numeric_demands_reach_both_shift_operands() {
    let result = analyze(
        "fun main() { let value = 1\nlet count = 1\nlet shifted = value << count\nlet wide: int64 = 5000000000\nshifted = wide }\n",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    for name in ["value", "count", "shifted"] {
        assert!(
            binding_types(&result, name)
                .iter()
                .all(|ty| *ty == Type::Int(IntKind::I64))
        );
    }
}

#[test]
fn replay_certificate_rejects_transitive_external_reads_and_parameter_calls() {
    let source = "let external = 1\nfun a(x) { return b(x) + external }\nfun b(x) { return a(x) }\nfun identity(x) { return x }\nfun invoke(identity) { return identity(0) }\nfun pure(x) { return identity(x) + 1 }\nfun main() {}\n";
    let program = program(source);
    let pure = super::pure::bodies(&program);
    assert!(pure.contains("identity"));
    assert!(pure.contains("pure"));
    for name in ["a", "b", "invoke"] {
        assert!(!pure.contains(name));
    }
}

#[test]
fn provisional_replay_preserves_argument_origin_aliases() {
    let result = analyze(
        "fun second(a, b) { return b }\nfun main() { let x = 0\nlet unused = second(x, x)\nlet left = 0\nlet right = 0\nlet chosen = second(left, right)\nlet wide: int64 = 5000000000\nchosen = wide }\n",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert!(
        binding_types(&result, "left")
            .iter()
            .all(|ty| *ty == Type::Int(IntKind::I32))
    );
    assert!(
        binding_types(&result, "right")
            .iter()
            .all(|ty| *ty == Type::Int(IntKind::I64))
    );
}

#[test]
fn origin_free_replay_certificate_checks_locals_and_transitive_literals() {
    // Local aliases are safe only when neither inputs nor any callee creates an origin.
    let source = "fun leaf(x) { return x + \"a\" }\nfun local(x) { let a = leaf(x)\nlet b = leaf(x)\nreturn a + b }\nfun numeric(x) { let a = 0\nreturn a }\nfun indirect(x) { let a = numeric(x)\nreturn a }\nfun main() { println(len(local(\"x\"))) }\n";
    let program = program(source);
    let closed = super::pure::closed_bodies(&program);
    assert!(closed.contains("leaf"));
    assert!(closed.contains("local"));
    assert!(closed.contains("main"));
    assert!(!closed.contains("numeric"));
    assert!(!closed.contains("indirect"));
}

#[test]
fn ordinary_certificates_use_annotated_effective_inputs_only() {
    use crate::infer::Checker;
    use std::rc::Rc;

    let program = program("fun fixed(x: int64) { return x }\nfun open(x) { return x }\n");
    let mut checker = Checker::new_with_numeric(
        &program,
        Rc::new(brass_typesys::RowInfo::analyze(&program)),
        false,
    );
    for symbol in ["fixed", "open"] {
        let info = &program.functions[symbol];
        checker.instantiate_function_call(
            symbol,
            &info.module,
            &info.signature.params,
            &info.decl.body,
            None,
            Type::Int(IntKind::I64),
            &[Type::Int(IntKind::I64)],
            info.decl.body.span,
        );
        checker.enter_instance(
            brass_hir::InstanceCallable::Function(symbol.to_owned()),
            &[Type::Int(IntKind::I32)],
        );
        assert_eq!(checker.numeric_body_is_settled(), symbol == "fixed");
        checker.leave_instance();
    }
    checker.numeric_seed_ordinary = false;
    checker.enter_instance(
        brass_hir::InstanceCallable::Function("fixed".into()),
        &[Type::Int(IntKind::I64)],
    );
    assert!(!checker.numeric_body_is_settled());
}

#[test]
fn standalone_retry_proof_requires_the_entire_graph_to_be_storage_free() {
    use crate::infer::Checker;
    use std::rc::Rc;

    let program = program(
        "fun leaf(x) { return x + 1 }\nfun chain(x) { return leaf(x) }\nfun storage(x) { let total = 0\ntotal = x\nreturn total }\nfun indirect(x) { return storage(x) }\nfun dynamic(f) { return f(0) }\n",
    );
    let checker = Checker::new_with_numeric(
        &program,
        Rc::new(brass_typesys::RowInfo::analyze(&program)),
        false,
    );
    for (name, expected) in [
        ("leaf", true),
        ("chain", true),
        ("storage", false),
        ("indirect", false),
        ("dynamic", false),
    ] {
        assert_eq!(
            checker.numeric_body_has_no_storage(program.functions[name].decl.body.span),
            expected,
            "{name}"
        );
    }
}

#[test]
fn structural_growth_proof_follows_stores_shadows_and_callees() {
    let program = program(
        "fun counter(a: int64) { let closed = a + 1\nlet i = 0\nwhile i < 4 { closed = closed + a\ni += 1 }\nreturn closed }\nfun copy(v) { let x = v\nx = 5000000000\nreturn x }\nfun indirect() { return copy(0) }\nfun shadow(a: int64) { let x = a\n{ let x = 0\nx = a } }\nfun dynamic(f) { return f(0) }\nfun closed() { let x = 0\nreturn x }\n",
    );
    let proof = super::eligibility::Eligibility::new(&program, |_| false);
    for (name, expected) in [
        ("counter", true),
        ("copy", true),
        ("indirect", false),
        ("shadow", false),
        ("dynamic", false),
        ("closed", true),
    ] {
        assert_eq!(
            proof.body(program.functions[name].decl.body.span),
            expected,
            "{name}"
        );
    }
}

#[test]
fn callable_fields_cannot_borrow_an_intrinsics_growth_proof() {
    let program = program(
        "fun use(x) { x.push(0) }\nfun make() { return { push: (v) -> { v = 5000000000\nreturn v } } }\n",
    );
    let proof = super::eligibility::Eligibility::new(&program, |_| false);
    assert!(!proof.body(program.functions["use"].decl.body.span));
}

#[test]
fn private_numeric_walk_does_not_need_committed_observation_history() {
    use crate::infer::Checker;
    use std::rc::Rc;

    let program = program(
        "fun seed() { let x = 0\nreturn x }\nfun main() { let x = seed()\nlet wide: int64 = 5000000000\nx = wide\n}\n",
    );
    let mut checker = Checker::new_with_numeric(
        &program,
        Rc::new(brass_typesys::RowInfo::analyze(&program)),
        true,
    );
    let seed = &program.functions["seed"];
    checker.instantiate_function_call(
        "seed",
        &seed.module,
        &seed.signature.params,
        &seed.decl.body,
        None,
        Type::Int(IntKind::I32),
        &[],
        seed.decl.body.span,
    );
    assert!(!checker.typed.expressions.is_empty());
    let mut complete = checker.clone();
    let mut private = checker.fork_numeric_probe();
    let main = &program.functions["main"];
    for probe in [&mut complete, &mut private] {
        probe.numeric = super::NumericState {
            active: true,
            probing: true,
            ..Default::default()
        };
        probe.speculation_depth += 1;
        let mut scopes = probe.signature_scopes(&main.signature.params);
        probe.check_block_root(&main.decl.body, &mut scopes, None);
    }
    // The provisional solution is independent of already published sidecars.
    assert!(complete.numeric.bindings == private.numeric.bindings);
    assert!(complete.numeric.argument_types == private.numeric.argument_types);
    assert!(complete.numeric.layouts == private.numeric.layouts);
    assert!(
        complete
            .numeric
            .roots
            .iter()
            .map(|r| (&r.site, &r.ty, &r.floor))
            .eq(private
                .numeric
                .roots
                .iter()
                .map(|r| (&r.site, &r.ty, &r.floor)))
    );
    assert_eq!(complete.errors, private.errors);
}

#[test]
fn method_seed_certificate_requires_fixed_receiver_and_parameter_types() {
    use crate::infer::Checker;
    use std::rc::Rc;

    let (program, errors) = brass_hir::lower(&[LoadedModule {
        is_prelude: false,
        path: vec!["library".into()],
        ast: brass_parser::parse("type Fixed = { value: int64 }\nfun Fixed.make(v: int64) { return Self { value: v } }\nfun Fixed.read(self, i: int64) { return self.value + i }\ntype Open = { value }\nfun Open.make(v: int64) { return Self { value: v } }\n").unwrap(),
    }]);
    assert!(errors.is_empty());
    let mut checker = Checker::new_with_numeric(
        &program,
        Rc::new(brass_typesys::RowInfo::analyze(&program)),
        false,
    );
    checker.entry_only = true;
    let fixed = program.types["Fixed"].type_ref();
    let mut refined = fixed.clone();
    if let Type::Record(nominal) = &mut refined {
        nominal
            .substitution
            .insert("value", Type::Int(IntKind::I32));
    }
    for (owner, method, args, expected) in [
        ("Fixed", "make", vec![Type::Int(IntKind::I64)], true),
        ("Fixed", "read", vec![fixed, Type::Int(IntKind::I64)], true),
        (
            "Fixed",
            "read",
            vec![refined, Type::Int(IntKind::I64)],
            false,
        ),
        ("Open", "make", vec![Type::Int(IntKind::I64)], false),
    ] {
        checker.enter_instance(
            brass_hir::InstanceCallable::Method {
                owner: owner.into(),
                method: method.into(),
            },
            &args,
        );
        assert_eq!(
            checker.numeric_body_is_settled(),
            expected,
            "{owner}.{method}"
        );
        checker.leave_instance();
    }
    // An unresolved global can change the method's type environment after seeding.
    checker
        .global_defs
        .entry(vec!["library".into()])
        .or_default()
        .insert("pending".into(), Type::Unknown(9000));
    checker.enter_instance(
        brass_hir::InstanceCallable::Method {
            owner: "Fixed".into(),
            method: "make".into(),
        },
        &[Type::Int(IntKind::I64)],
    );
    assert!(!checker.numeric_body_is_settled());
}

#[test]
fn integer_self_updates_remain_zero_growth_across_branches_and_interpolation() {
    let program = program(
        "fun counter() { println(\"begin\")\nlet v = 12345\nv = (v * 7 + 3) % 1000033\nif v % 3 == 0 { v = (v * 2 + 108) % 999983 } else { v = (v + 108) % 1000003 }\nprintln(\"checksum = {v}\") }\n",
    );
    let body = &program.functions["counter"].decl.body;
    assert!(super::eligibility::Eligibility::local(
        &body.stmts,
        true,
        |callee, _| matches!(callee, brass_parser::ast::Expr::Ident(name, _) if name == "println")
            .then_some((true, true))
    ));
    assert!(
        super::eligibility::Eligibility::new(&program, |name| name == "println").body(body.span)
    );
}

#[test]
fn integer_local_groups_decline_wider_inputs_and_opaque_shadows() {
    let program = program(
        "fun counters() { let a = 0\nlet b = 1\nwhile b < 4 { a = a + b\nb += 1 }\nreturn a }\nfun wide(v: int64) { let a = 0\nlet b = 1\na = a + b\nb = v\nreturn a }\nfun shadow() { let a = 0\nlet b = 1\n{ let b: int64 = 2\na = a + b }\nreturn a }\n",
    );
    for (name, expected) in [("counters", true), ("wide", false), ("shadow", false)] {
        let body = &program.functions[name].decl.body;
        assert_eq!(
            super::eligibility::Eligibility::local(&body.stmts, true, |_, _| None),
            expected,
            "{name}"
        );
        assert_eq!(
            super::eligibility::Eligibility::new(&program, |_| false).body(body.span),
            expected,
            "{name}"
        );
    }
}

#[test]
fn dynamic_calls_without_origins_keep_independent_roots() {
    let program = program(
        "fun closed(f, x) { return f(x) }\nfun literal(f) { return f(0) }\nfun returned(f, x: int64) { let a = f()\na = x\nreturn a }\nfun capture(x: int64) { let a = 0\nlet f = () -> { a = x }\nf()\nreturn a }\n",
    );
    for (name, expected) in [
        ("closed", true),
        ("literal", false),
        ("returned", false),
        ("capture", false),
    ] {
        assert_eq!(
            super::eligibility::Eligibility::local(
                &program.functions[name].decl.body.stmts,
                true,
                |_, _| None
            ),
            expected,
            "{name}"
        );
    }
}

#[test]
fn annotated_receiver_arguments_do_not_require_a_program_graph() {
    use crate::infer::Checker;
    use std::rc::Rc;

    let program = program(
        "type Counter = { value: int64 }\nfun Counter.add(self, n: int64) { self.value = self.value + n }\nfun apply(c) { c.add(10) }\nfun shadow(c) { let c = { add: (x) -> { x = 5000000000\nreturn x } }\nc.add(0) }\n",
    );
    let mut checker = Checker::new_with_numeric(
        &program,
        Rc::new(brass_typesys::RowInfo::analyze(&program)),
        false,
    );
    checker.current_module = program.functions["apply"].module.clone();
    let mut scopes = checker.signature_scopes(&program.functions["apply"].signature.params);
    scopes
        .last_mut()
        .unwrap()
        .insert("c".into(), program.types["Counter"].type_ref());
    // The existing receiver lookup supplies the annotation barrier directly.
    assert!(
        !checker.numeric_unsettled_body_needs_settlement(
            &program.functions["apply"].decl.body,
            &scopes
        )
    );
    assert!(checker.numeric_eligibility.get().is_none());
    // A lexical shadow cannot reuse the outer receiver's annotation proof.
    assert!(
        checker.numeric_unsettled_body_needs_settlement(
            &program.functions["shadow"].decl.body,
            &scopes
        )
    );
}

#[test]
fn literal_leaf_calls_skip_the_graph_but_keep_forwarded_demands() {
    use crate::infer::Checker;
    use std::rc::Rc;

    let program = program(
        "type Boxed = { value }\nfun Boxed.new(v) { return Self { value: v } }\nfun echo(v) { return v }\nfun widen(v) { v = 5000000000\nreturn v }\nfun calls() { let a = echo(0)\nlet b = Boxed.new(1)\nreturn a }\nfun demand() { let a = echo(0)\na = 5000000000\nreturn a }\nfun parameter() { return widen(0) }\n",
    );
    let mut checker = Checker::new_with_numeric(
        &program,
        Rc::new(brass_typesys::RowInfo::analyze(&program)),
        false,
    );
    checker.current_module = program.functions["calls"].module.clone();
    let scopes = checker.signature_scopes(&[]);
    assert!(
        !checker.numeric_unsettled_body_needs_settlement(
            &program.functions["calls"].decl.body,
            &scopes
        )
    );
    assert!(checker.numeric_eligibility.get().is_none());
    // A leaf return still carries an origin when its caller demands a wider binding.
    for name in ["demand", "parameter"] {
        assert!(
            checker.numeric_unsettled_body_needs_settlement(
                &program.functions[name].decl.body,
                &scopes
            )
        );
    }
}

#[test]
fn local_calls_only_query_input_proofs_when_an_origin_reaches_the_call() {
    use std::cell::Cell;

    let program = program("fun closed(x) { return apply(x) }\nfun literal() { return apply(0) }\n");
    for (name, expected) in [("closed", 0), ("literal", 1)] {
        let queries = Cell::new(0);
        assert!(super::eligibility::Eligibility::local(
            &program.functions[name].decl.body.stmts,
            true,
            |_, inputs| {
                queries.set(queries.get() + usize::from(inputs));
                Some((true, true))
            }
        ));
        // Typed arguments do not need a callee body scan to establish the barrier.
        assert_eq!(queries.get(), expected);
    }
}
