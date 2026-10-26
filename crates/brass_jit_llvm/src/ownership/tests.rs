use super::analysis::stmts_block;
use super::summaries::each_call;
use super::*;
use brass_parser::ast::{Block, Expr, Pattern, Stmt, TopLevel};
use brass_parser::parse;

fn main_body(src: &str) -> Block {
    let module = parse(src).expect("parse");
    for item in module.items {
        if let TopLevel::Fun(f) = item
            && f.name == "main"
        {
            return f.body;
        }
    }
    panic!("no `main`");
}

fn decisions(src: &str) -> Vec<CaptureDecision> {
    analyze_spawns(&main_body(src), &HashSet::default())
}

fn acquire(body: &mut Block) -> Vec<SpawnError> {
    auto_acquire(
        &mut body.stmts,
        &HashSet::default(),
        &SpawnSummaries::default(),
    )
    .errors
}

/// Render a statement list compactly for structural assertions.
fn contains_call(stmts: &[Stmt], name: &str) -> bool {
    let mut found = false;
    let block = stmts_block(stmts);
    each_call(&block, &mut |callee, _, _| {
        if callee == name {
            found = true;
        }
    });
    found
}

#[test]
fn capture_only_used_by_spawn_is_moved() {
    let d = decisions(
        "fun main() {\n    let data = [1, 2, 3]\n    spawn(() -> { println(data) })\n}\n",
    );
    assert_eq!(
        d,
        vec![CaptureDecision {
            var: "data".into(),
            ownership: Ownership::Move
        }]
    );
}

#[test]
fn capture_read_after_spawn_is_frozen() {
    let d = decisions(
        "fun main() {\n    let data = [1, 2, 3]\n    spawn(() -> { println(data) })\n    println(data)\n}\n",
    );
    assert_eq!(
        d,
        vec![CaptureDecision {
            var: "data".into(),
            ownership: Ownership::Freeze
        }]
    );
}

#[test]
fn capture_mutated_in_spawn_and_live_is_cowned() {
    let d = decisions(
        "fun main() {\n    let count = 0\n    spawn(() -> { count = count + 1 })\n    println(count)\n}\n",
    );
    assert_eq!(
        d,
        vec![CaptureDecision {
            var: "count".into(),
            ownership: Ownership::Cown
        }]
    );
}

#[test]
fn no_spawn_yields_no_decisions() {
    assert!(decisions("fun main() {\n    let x = 1\n    println(x)\n}\n").is_empty());
}

#[test]
fn method_call_on_capture_counts_as_mutation() {
    // A mutating method call (not a direct assignment) must still cown the
    // capture, so it is lock-guarded across threads.
    let d = decisions(
        "fun main() {\n    let c = make()\n    spawn(() -> { c.add(1) })\n    use(c)\n}\n",
    );
    assert_eq!(
        d,
        vec![CaptureDecision {
            var: "c".into(),
            ownership: Ownership::Cown
        }]
    );
}

#[test]
fn mutation_through_a_ref_function_call_counts_as_mutation() {
    // Passing the capture to a function (whose default parameter is a mutable
    // reference) may mutate it, so it must be cowned -- not frozen, which would
    // let two threads race it.
    let d = decisions(
        "fun main() {\n    let c = make()\n    spawn(() -> { bump(c) })\n    use(c)\n}\n",
    );
    assert_eq!(
        d,
        vec![CaptureDecision {
            var: "c".into(),
            ownership: Ownership::Cown
        }]
    );
}

#[test]
fn mutation_inside_a_match_arm_counts_as_mutation() {
    // A mutation nested in a `match` arm body must be found by the full-tree
    // scan; missing it would freeze a mutated capture and race it.
    let d = decisions(
        "fun main() {\n    let c = make()\n    spawn(() -> { match 1 {\n        _ => { c.x = 1 }\n    } })\n    use(c)\n}\n",
    );
    assert_eq!(
        d,
        vec![CaptureDecision {
            var: "c".into(),
            ownership: Ownership::Cown
        }]
    );
}

#[test]
fn spawner_side_mutation_after_a_read_only_spawn_upgrades_to_cown() {
    // The closure only READS `c`, but the spawner passes it to a possibly
    // mutating call afterwards: freezing would let the spawner write while
    // the task reads lock-free. The whole-function mutation rule must cown it
    // so both sides are serialized.
    let d = decisions(
        "fun main() {\n    let c = make()\n    spawn(() -> { println(c) })\n    use(c)\n}\n",
    );
    assert_eq!(
        d,
        vec![CaptureDecision {
            var: "c".into(),
            ownership: Ownership::Cown
        }]
    );
}

#[test]
fn read_only_capture_everywhere_stays_frozen() {
    // Nobody ever mutates `c` (only read-only builtins touch it), so it is
    // genuinely immutable after the spawn and freezing is the right call.
    let d = decisions(
        "fun main() {\n    let c = make()\n    spawn(() -> { println(c) })\n    println(c)\n}\n",
    );
    assert_eq!(
        d,
        vec![CaptureDecision {
            var: "c".into(),
            ownership: Ownership::Freeze
        }]
    );
}

#[test]
fn spawner_mutation_through_a_container_alias_upgrades_to_cown() {
    // The spawner wraps `c` in a record before the spawn and mutates through
    // the wrapper afterwards. The conservative alias rule must see `w` as a
    // handle to `c`'s object and classify the capture a cown.
    let d = decisions(
        "fun main() {\n    let c = make()\n    let w = Wrap { c: c }\n    spawn(() -> { println(c) })\n    w.c.add(1)\n}\n",
    );
    assert_eq!(
        d,
        vec![CaptureDecision {
            var: "c".into(),
            ownership: Ownership::Cown
        }]
    );
}

#[test]
fn auto_acquire_wraps_a_cowned_spawn_body_in_with() {
    // The cowned capture's spawn body is rewritten to acquire it via `with`,
    // so concurrent mutation goes through the lock without any annotation.
    let mut body = main_body(
        "fun main() {\n    let c = make()\n    spawn(() -> { c.add(1) })\n    use(c)\n}\n",
    );
    let errors = acquire(&mut body);
    assert!(errors.is_empty(), "no spawn errors: {errors:?}");
    let wrapped = body.stmts.iter().any(spawn_body_is_with);
    assert!(wrapped, "cowned spawn body should be wrapped in `with`");
}

#[test]
fn multi_cown_spawn_body_uses_the_group_wrap() {
    // A body that mutates two captures must acquire them as a group through
    // `_with_all` (address-ordered at runtime), not as nested name-ordered
    // `with` scopes -- the nesting deadlocked when another spawn captured the
    // same objects under names that sort the other way.
    let mut body = main_body(
        "fun main() {\n    let a = make()\n    let b = make()\n    spawn(() -> { a.add(1)\n        b.add(1) })\n    use(a)\n    use(b)\n}\n",
    );
    let errors = acquire(&mut body);
    assert!(errors.is_empty());
    assert!(
        contains_call(&body.stmts, "_with_all"),
        "two cowns must be acquired via the group form"
    );
}

#[test]
fn mutation_through_an_alias_in_the_closure_counts_as_mutation() {
    // A capture mutated through a local alias (`let a = c; a.add(1)`) is rooted
    // at `a`, but `a` aliases `c`, so the capture must still be cowned -- not
    // frozen, which would race it.
    let d = decisions(
        "fun main() {\n    let c = make()\n    spawn(() -> { let a = c\n        a.add(1) })\n    use(c)\n}\n",
    );
    assert_eq!(
        d,
        vec![CaptureDecision {
            var: "c".into(),
            ownership: Ownership::Cown
        }]
    );
}

#[test]
fn nested_closure_local_is_not_captured_by_the_outer_spawn() {
    // A loop counter bound inside a nested spawn closure belongs to the inner
    // scope; it must not be seen as a capture (and promoted) by the outer spawn.
    let body = main_body(
        "fun main() {\n    let c = make()\n    spawn(() -> {\n        spawn(() -> { let i = 0\n            c.add(i) })\n    })\n}\n",
    );
    // The outer spawn's closure body is the second statement's argument.
    let Stmt::Expr(Expr::Call(_, args, _)) = &body.stmts[1] else {
        panic!("expected spawn statement");
    };
    let Expr::Closure(_, outer_body, _) = &args[0].expr else {
        panic!("expected closure");
    };
    let Expr::Block(b, _) = outer_body.as_ref() else {
        panic!("expected block body");
    };
    let caps = captured(b, &HashSet::default());
    assert!(
        !caps.contains("i"),
        "the inner closure's local `i` must not be a capture of the outer spawn: {caps:?}"
    );
    assert!(
        caps.contains("c"),
        "the outer spawn still captures `c`: {caps:?}"
    );
}

#[test]
fn spawner_access_after_a_cowned_spawn_is_guarded() {
    // The spawner's own later access to a cowned capture must be wrapped in
    // `with` too, so it does not race the spawned task. Here the trailing
    // `c.add(2)` runs concurrently with the spawned `c.add(1)`.
    let mut body = main_body(
        "fun main() {\n    let c = make()\n    spawn(() -> { c.add(1) })\n    c.add(2)\n}\n",
    );
    let errors = acquire(&mut body);
    assert!(errors.is_empty());
    let guarded = body.stmts.iter().any(|s| {
        matches!(s, Stmt::Expr(Expr::Call(callee, _, _))
            if matches!(&**callee, Expr::Ident(n, _) if n == "with"))
    });
    assert!(
        guarded,
        "the spawner's own access to the cown should be guarded by `with`"
    );
}

#[test]
fn spawn_inside_a_loop_guards_accesses_after_the_loop() {
    // A spawn nested in a `while` shares state with everything the function
    // does afterwards; the pass must guard the access *outside* the loop's
    // statement list, which a live set per statement list would miss.
    let mut body = main_body(
        "fun main() {\n    let c = make()\n    let k = 0\n    while k < 2 {\n        spawn(() -> { c.add(1) })\n        k = k + 1\n    }\n    c.add(2)\n}\n",
    );
    let errors = acquire(&mut body);
    assert!(errors.is_empty());
    let guarded = body.stmts.iter().any(|s| {
        matches!(s, Stmt::Expr(Expr::Call(callee, _, _))
            if matches!(&**callee, Expr::Ident(n, _) if n == "with"))
    });
    assert!(
        guarded,
        "the post-loop access must be guarded even though the spawn is nested"
    );
}

#[test]
fn closure_variable_spawn_is_promoted_and_wrapped() {
    // `let task = () -> {...}; spawn(task)` must behave exactly like a
    // literal spawn: the bound closure's body is lock-wrapped and the capture
    // promoted before the spawn, so both threads count it atomically.
    let mut body = main_body(
        "fun main() {\n    let c = make()\n    let task = () -> { c.add(1) }\n    spawn(task)\n    c.add(2)\n}\n",
    );
    let errors = acquire(&mut body);
    assert!(errors.is_empty(), "spawn(var) resolves: {errors:?}");
    assert!(
        contains_call(&body.stmts, "_cown"),
        "the capture must be promoted before the spawn"
    );
    // The bound closure's body is wrapped in a lock acquisition.
    let bound_wrapped = body.stmts.iter().any(|s| {
        let Stmt::Let {
            value: Some(Expr::Closure(_, cbody, _)),
            ..
        } = s
        else {
            return false;
        };
        matches!(cbody.as_ref(), Expr::Call(c, _, _)
            if matches!(&**c, Expr::Ident(n, _) if n == "with"))
    });
    assert!(bound_wrapped, "the bound closure body must be lock-wrapped");
}

#[test]
fn unresolvable_spawn_argument_is_a_compile_error() {
    // A spawn whose argument is not a closure literal (here: a call result)
    // cannot be analyzed; compiling it silently would hand unguarded shared
    // state to a thread, so it must be rejected.
    let mut body = main_body("fun main() {\n    spawn(make())\n}\n");
    let errors = acquire(&mut body);
    assert_eq!(errors.len(), 1, "expected one spawn error: {errors:?}");
    assert!(errors[0].message.contains("closure literal"));
}

#[test]
fn spawn_of_an_unbound_variable_is_a_compile_error() {
    // `spawn(f)` where `f` is a parameter (not bound to a closure literal in
    // this function) is equally opaque and must be rejected.
    let module = parse("fun run(f) {\n    spawn(f)\n}\n").expect("parse");
    let TopLevel::Fun(mut f) = module.items.into_iter().next().unwrap() else {
        panic!("expected fun");
    };
    let params: HashSet<String> = f.params.iter().map(|p| p.name.clone()).collect();
    let errors = auto_acquire(&mut f.body.stmts, &params, &SpawnSummaries::default()).errors;
    assert_eq!(errors.len(), 1, "expected one spawn error: {errors:?}");
}

#[test]
fn summaries_mark_parameters_captured_by_callee_spawns() {
    // `start(c)` spawns a task capturing its parameter; `outer(x)` forwards
    // its own parameter to `start`. Both must be summarized (the second via
    // the call-graph fixpoint).
    let src = "fun start(c) {\n    spawn(() -> { c.add(1) })\n}\nfun outer(x) {\n    start(x)\n}\n";
    let module = parse(src).expect("parse");
    let mut fns: Vec<(String, Vec<String>, Block)> = Vec::new();
    for item in module.items {
        if let TopLevel::Fun(f) = item {
            fns.push((
                f.name.clone(),
                f.params.iter().map(|p| p.name.clone()).collect(),
                f.body,
            ));
        }
    }
    let borrowed: Vec<(String, Vec<String>, &Block)> = fns
        .iter()
        .map(|(n, p, b)| (n.clone(), p.clone(), b))
        .collect();
    let summaries = spawn_capture_summaries(&borrowed);
    assert_eq!(
        summaries.get("start"),
        Some(&HashSet::from_iter([0])),
        "start spawns a task capturing its parameter 0"
    );
    assert_eq!(
        summaries.get("outer"),
        Some(&HashSet::from_iter([0])),
        "outer forwards its parameter into start's captured position"
    );
}

#[test]
fn caller_local_passed_to_a_spawning_callee_is_promoted_and_guarded() {
    // With `start` summarized, a caller's local handed to it must be
    // promoted to a cown and the caller's own accesses guarded -- the spawn
    // in the helper races the caller otherwise.
    let mut summaries = SpawnSummaries::default();
    summaries.insert("start".to_string(), HashSet::from_iter([0]));
    let mut body = main_body("fun main() {\n    let c = make()\n    start(c)\n    c.add(1)\n}\n");
    let errors = auto_acquire(&mut body.stmts, &HashSet::default(), &summaries).errors;
    assert!(errors.is_empty());
    assert!(
        contains_call(&body.stmts, "_cown"),
        "the local must be promoted before the call hands it to the callee"
    );
    assert!(
        contains_call(&body.stmts, "with"),
        "the caller's own accesses must be lock-guarded"
    );
}

#[test]
fn rebinding_a_captured_variable_is_a_spawn_error() {
    // Reassigning a capture (plain or compound) inside a spawned task is
    // rejected; storing into a captured object's field and assigning a
    // task-local binding (even one shadowing a capture) are not.
    let src = "fun main() {\n    let n = 0\n    let p = P { x: 1 }\n    spawn(() -> {\n        n = 5\n        n += 1\n        p.x = 2\n        let k = 1\n        k = 2\n        let p = 3\n        p = 4\n    })\n}\n";
    let module = parse(src).expect("parse");
    let TopLevel::Fun(f) = module.items.into_iter().next().unwrap() else {
        panic!("expected fun");
    };
    let errors = pre_spawn_errors(&f.body.stmts, &HashSet::default(), &HashSet::default());
    let messages: Vec<&str> = errors.iter().map(|e| e.message.as_str()).collect();
    assert_eq!(messages.len(), 2, "{messages:?}");
    assert!(
        messages
            .iter()
            .all(|m| m.starts_with("cannot reassign captured `n` inside `spawn`")),
        "{messages:?}"
    );
}

#[test]
fn range_endpoints_are_captured() {
    // Both range endpoints participate in the closure's lexical captures.
    let d = decisions(
        "fun main() {\n    let lo = 1\n    let hi = 4\n    spawn(() -> { println([lo..hi]) })\n    println(lo)\n}\n",
    );
    assert_eq!(
        d,
        vec![
            CaptureDecision {
                var: "hi".into(),
                ownership: Ownership::Move,
            },
            CaptureDecision {
                var: "lo".into(),
                ownership: Ownership::Freeze,
            },
        ]
    );
}

#[test]
fn nested_shadow_does_not_hide_outer_capture() {
    // A nested closure parameter shadows only its own uses of the name.
    let d = decisions(
        "fun main() {\n    let data = [1, 2]\n    spawn(() -> {\n        println(data)\n        let inner = (data) -> println(data)\n        inner([3])\n    })\n    println(data)\n}\n",
    );
    assert!(
        d.iter().any(|decision| decision.var == "data"),
        "the outer reference remains a capture"
    );
}

#[test]
fn compound_expression_blocks_are_transformed() {
    // A spawn inside a block nested under an array/call expression is visited.
    let mut body = main_body(
        "fun main() {\n    let c = make()\n    consume([if true {\n        spawn(() -> { c.add(1) })\n        1\n    } else { 0 }])\n    c.add(2)\n}\n",
    );
    let errors = acquire(&mut body);
    assert!(errors.is_empty());
    assert!(contains_call(&body.stmts, "_cown"));
}

#[test]
fn expression_bodied_spawn_scope_processes_nested_spawn() {
    // Expression-bodied spawned closures receive the same scoped transform.
    let mut body = main_body(
        "fun main() {\n    let c = make()\n    spawn(() -> spawn(() -> { c.add(1) }))\n    c.add(2)\n}\n",
    );
    let errors = acquire(&mut body);
    assert!(errors.is_empty());
    assert!(contains_call(&body.stmts, "_cown"));
}

#[test]
fn ordinary_closure_cown_access_is_guarded() {
    // A closure invoked while a spawned task may run acquires captured cowns.
    let mut body = main_body(
        "fun main() {\n    let c = make()\n    let helper = () -> { c.add(2) }\n    spawn(() -> { c.add(1) })\n    helper()\n}\n",
    );
    let errors = acquire(&mut body);
    assert!(errors.is_empty());
    let guarded = body.stmts.iter().any(|stmt| {
        let Stmt::Let {
            pat: Pattern::Binding(name, _, _),
            value: Some(Expr::Closure(_, body, _)),
            ..
        } = stmt
        else {
            return false;
        };
        name == "helper"
            && matches!(body.as_ref(), Expr::Call(callee, _, _)
                if matches!(callee.as_ref(), Expr::Ident(name, _) if name == "with"))
    });
    assert!(guarded, "the ordinary closure body acquires the cown");
}

#[test]
fn spawned_closure_variable_resolves_lexically() {
    // A same-named binding in a sibling block is not a candidate at the spawn.
    let mut body = main_body(
        "fun main() {\n    let a = make()\n    let b = make()\n    let task = () -> { a.add(1) }\n    if true {\n        let task = () -> { b.add(1) }\n    }\n    spawn(task)\n    a.add(2)\n}\n",
    );
    let errors = acquire(&mut body);
    assert!(errors.is_empty(), "outer task resolves: {errors:?}");
    let promotion_count = body
        .stmts
        .iter()
        .filter(|stmt| {
            matches!(stmt, Stmt::Expr(Expr::Call(callee, _, _))
                if matches!(callee.as_ref(), Expr::Ident(name, _) if name == "_cown"))
        })
        .count();
    assert_eq!(
        promotion_count, 1,
        "only the visible task capture is promoted"
    );
}

#[test]
fn spawned_binding_diagnostics_resolve_lexically() {
    // A same-named sibling closure is still checked as an ordinary closure.
    let body = main_body(
        "fun main() {\n    let data = make()\n    let task = () -> println(data)\n    if true {\n        let task = () -> spawn(() -> println(data))\n    }\n    spawn(task)\n}\n",
    );
    let errors = pre_spawn_errors(&body.stmts, &HashSet::default(), &HashSet::default());
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("spawn` inside a closure")),
        "the unspawned sibling closure keeps its diagnostic"
    );
}

fn spawn_body_is_with(stmt: &Stmt) -> bool {
    let Stmt::Expr(Expr::Call(callee, args, _)) = stmt else {
        return false;
    };
    if !matches!(&**callee, Expr::Ident(n, _) if n == "spawn") {
        return false;
    }
    let Some(Expr::Closure(_, body, _)) = args.first().map(|a| &a.expr) else {
        return false;
    };
    matches!(&**body, Expr::Call(c, _, _) if matches!(&**c, Expr::Ident(n, _) if n == "with"))
}

/// The arguments of every top-level `name(..)` statement of `stmts`, in
/// order, as identifier names.
fn promoted_names(stmts: &[Stmt], name: &str) -> Vec<String> {
    stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Expr(Expr::Call(callee, args, _))
                if matches!(&**callee, Expr::Ident(n, _) if n == name) =>
            {
                match args.first().map(|a| &a.expr) {
                    Some(Expr::Ident(arg, _)) => Some(arg.clone()),
                    _ => None,
                }
            }
            _ => None,
        })
        .collect()
}

#[test]
fn handles_into_a_cowned_graph_are_promoted_at_the_spawn() {
    // `h` (read out of the cown) and `i` (stored into it) both reach the
    // object the task mutates under `o`'s lock. Both are promoted with the
    // capture, and the spawner's access through `i` takes `o`'s lock.
    let mut body = main_body(
        "fun main() {\n    let i = make()\n    let o = wrap(i)\n    let h = o.inner\n    spawn(() -> { o.inner.add(1) })\n    i.add(2)\n    h.add(3)\n}\n",
    );
    let errors = acquire(&mut body);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(promoted_names(&body.stmts, "_cown"), ["o", "h", "i"]);
    let guarded = body
        .stmts
        .iter()
        .filter(|s| {
            matches!(s, Stmt::Expr(Expr::Call(callee, args, _))
                if matches!(&**callee, Expr::Ident(n, _) if n == "with")
                    && matches!(args.first().map(|a| &a.expr), Some(Expr::Ident(r, _)) if r == "o"))
        })
        .count();
    assert_eq!(guarded, 2, "both spawner-side accesses take `o`'s lock");
}
