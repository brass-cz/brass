use super::*;

fn program(closure: &str) -> Program {
    let ast = brass_parser::parse(&format!("fun main() {{ let f = {closure} }}")).unwrap();
    let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty());
    program
}

fn literal(program: &Program) -> &Expr {
    let body = &program.functions.values().next().unwrap().decl.body;
    let Stmt::Let {
        value: Some(expr), ..
    } = &body.stmts[0]
    else {
        panic!("closure binding")
    };
    expr
}

fn checker(program: &Program) -> Checker<'_> {
    let mut checker = Checker::new(program, Rc::new(brass_typesys::RowInfo::analyze(program)));
    checker.closure_memo_disabled = false;
    checker
}

fn remember(checker: &mut Checker<'_>, expr: &Expr, explicit: bool) -> (Vec<Type>, Type) {
    let Expr::Closure(args, _, _) = expr else {
        panic!("closure")
    };
    let params: Vec<_> = args.iter().map(|_| checker.fresh_unknown()).collect();
    let ret = checker.fresh_unknown();
    let Type::Unknown(id) = ret else {
        unreachable!()
    };
    checker.remember_closure(
        expr,
        &params,
        &vec![Scope::new(HashMap::default())],
        explicit,
        Some(id),
    );
    (params, ret)
}

fn apply(
    checker: &mut Checker<'_>,
    params: &[Type],
    ret: &Type,
    arg: Type,
    expected: Option<Type>,
) -> Option<Type> {
    let snapshot = checker.solver.snapshot();
    for param in params {
        checker.solver.unify(param, &arg).unwrap();
    }
    if let Some(expected) = expected {
        checker.solver.unify(ret, &expected).unwrap();
    }
    let result = checker.check_callable_body(params, ret);
    checker.solver.rollback(snapshot);
    result
}

fn same_observations(left: &Checker<'_>, right: &Checker<'_>) {
    assert_eq!(
        format!("{:?}", left.typed.expressions),
        format!("{:?}", right.typed.expressions)
    );
    assert_eq!(left.typed_seen, right.typed_seen);
    assert_eq!(left.numeric_call_map(), right.numeric_call_map());
    // Independently checked closures intern equal tags in different allocations.
    let observations = |checker: &Checker<'_>| {
        checker
            .instance_typed
            .iter()
            .map(|entry| ((*entry.tag).clone(), entry.index))
            .collect::<Vec<_>>()
    };
    assert_eq!(observations(left), observations(right));
    let seen = |checker: &Checker<'_>| {
        checker
            .instance_typed_seen
            .iter()
            .map(|entry| ((*entry.tag).clone(), entry.index))
            .collect::<HashSet<_>>()
    };
    assert_eq!(seen(left), seen(right));
    assert_eq!(format!("{:?}", left.errors), format!("{:?}", right.errors));
    assert_eq!(
        format!("{:?}", left.warnings),
        format!("{:?}", right.warnings)
    );
    assert_eq!(left.return_literals, right.return_literals);
    assert_eq!(left.return_value_spans, right.return_value_spans);
    assert_eq!(left.last_closure_result, right.last_closure_result);
    assert_eq!(left.diverging_exprs, right.diverging_exprs);
    assert_eq!(left.static_divergence, right.static_divergence);
    assert_eq!(left.fixed_array_binding, right.fixed_array_binding);
}

#[test]
fn replay_matches_body_walk_across_rollback_global_pinning_and_instances() {
    let program = program("(x) -> { let y = x + 1\ny += x\nreturn y * 2 }");
    let mut cached = checker(&program);
    let (params, ret) = remember(&mut cached, literal(&program), false);
    let global = cached.fresh_unknown();
    let mut globals = HashMap::default();
    globals.insert("global".to_owned(), global.clone());
    let Type::Unknown(result_id) = ret else {
        unreachable!()
    };
    cached.remember_closure(
        literal(&program),
        &params,
        &vec![Scope::new(globals)],
        false,
        Some(result_id),
    );
    let tag = cached.intern_tag(brass_hir::InstanceCallable::Function("outer".into()), &[]);
    cached.instance_stack.push(tag);
    let mut walked = cached.clone();
    walked.closure_memo_disabled = true;
    for (index, arg) in [
        IntKind::I32,
        IntKind::I32,
        IntKind::I64,
        IntKind::I64,
        IntKind::I32,
    ]
    .into_iter()
    .enumerate()
    {
        cached.diverging_exprs.clear();
        walked.diverging_exprs.clear();
        if index == 1 {
            cached.solver.unify(&global, &Type::Bool).unwrap();
            walked.solver.unify(&global, &Type::Bool).unwrap();
        }
        assert_eq!(
            apply(&mut cached, &params, &ret, Type::Int(arg), None),
            apply(&mut walked, &params, &ret, Type::Int(arg), None)
        );
        same_observations(&cached, &walked);
        assert_eq!(cached.resolve(&global), walked.resolve(&global));
    }
    assert_eq!(cached.closure_memo_hits, 3);
    assert_eq!(cached.closure_memo.len(), 2);
    let tag = cached.intern_tag(brass_hir::InstanceCallable::Function("other".into()), &[]);
    cached.instance_stack[0] = tag.clone();
    walked.instance_stack[0] = tag;
    for _ in 0..2 {
        assert_eq!(
            apply(&mut cached, &params, &ret, Type::Int(IntKind::I32), None),
            apply(&mut walked, &params, &ret, Type::Int(IntKind::I32), None)
        );
        same_observations(&cached, &walked);
    }
    assert_eq!(cached.closure_memo_hits, 4);
    assert_eq!(cached.closure_memo.len(), 3);
}

#[test]
fn body_identity_expected_return_and_zero_arguments_are_distinct() {
    let program = program("() -> 1");
    let mut cached = checker(&program);
    let (params, ret) = remember(&mut cached, literal(&program), true);
    for expected in [IntKind::I32, IntKind::I64, IntKind::I32] {
        assert!(
            apply(
                &mut cached,
                &params,
                &ret,
                Type::Int(IntKind::I32),
                Some(Type::Int(expected))
            )
            .is_some()
        );
    }
    assert_eq!(cached.closure_memo_hits, 1);
    assert_eq!(cached.closure_memo.len(), 2);
    // A new saved environment at the same source span is a new body identity.
    let (params, ret) = remember(&mut cached, literal(&program), true);
    apply(
        &mut cached,
        &params,
        &ret,
        Type::Int(IntKind::I32),
        Some(Type::Int(IntKind::I32)),
    );
    assert_eq!(cached.closure_memo_hits, 1);
    assert_eq!(cached.closure_memo.len(), 3);
}

#[test]
fn unsupported_dependencies_and_failed_checks_never_replay() {
    for source in [
        "(x) -> x + global",
        "(x: int32) -> x + 1",
        "(x) -> g(x)",
        "(x) -> { if x > 0 { return x }\nreturn 0 }",
        "(x) -> [x]",
        "(x) -> { let y = (z) -> z\nreturn x }",
        "(x) -> x.foo",
        "(x) -> { let y = x\nlet y = y + 1\nreturn y }",
    ] {
        let program = program(source);
        assert!(!closed_numeric_body(literal(&program)), "{source}");
    }
    let program = program("(x) -> x << 1");
    let mut cached = checker(&program);
    let (params, ret) = remember(&mut cached, literal(&program), false);
    let mut walked = cached.clone();
    walked.closure_memo_disabled = true;
    for _ in 0..2 {
        assert_eq!(
            apply(
                &mut cached,
                &params,
                &ret,
                Type::Float(FloatKind::F64),
                None
            ),
            apply(
                &mut walked,
                &params,
                &ret,
                Type::Float(FloatKind::F64),
                None
            )
        );
        same_observations(&cached, &walked);
    }
    assert!(!cached.errors.is_empty());
    assert!(cached.closure_memo.is_empty());
    assert_eq!(cached.closure_memo_hits, 0);
}

#[test]
fn probes_recursion_and_open_instance_tags_decline_before_replay() {
    let program = program("(x) -> x + 1");
    let mut cached = checker(&program);
    let (params, ret) = remember(&mut cached, literal(&program), false);
    apply(&mut cached, &params, &ret, Type::Int(IntKind::I32), None);
    assert_eq!(cached.closure_memo.len(), 1);
    cached.static_divergence = true;
    apply(&mut cached, &params, &ret, Type::Int(IntKind::I32), None);
    cached.static_divergence = false;
    cached.fixed_array_binding = true;
    apply(&mut cached, &params, &ret, Type::Int(IntKind::I32), None);
    cached.fixed_array_binding = false;
    cached.speculation_depth = 1;
    apply(&mut cached, &params, &ret, Type::Int(IntKind::I32), None);
    cached.speculation_depth = 0;
    let tag = cached.intern_tag(
        brass_hir::InstanceCallable::Function("open".into()),
        &params,
    );
    cached.instance_stack.push(tag);
    apply(&mut cached, &params, &ret, Type::Int(IntKind::I32), None);
    cached.instance_stack.pop();
    let key = format!("closure:{}", literal(&program).span().lo);
    cached.instantiating.insert(key);
    assert!(apply(&mut cached, &params, &ret, Type::Int(IntKind::I32), None).is_none());
    assert_eq!(cached.closure_memo_hits, 0);
    assert_eq!(cached.closure_memo.len(), 1);
}
