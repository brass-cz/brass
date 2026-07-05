//! HIR -> MIR lowering tests.
//!
//! Two styles are used: focused checks lower a single parsed function body
//! against an empty program (enough for control flow, `expr!`, and closures),
//! and end-to-end checks run the full HIR lowering so call routing, types, and
//! `error(...)` resolve as they do in the real pipeline.

use std::collections::HashMap;

use prepoly_hir::{LoadedModule, Program};
use prepoly_mir::{MirBody, body_to_string, lower_body, lower_program, program_to_string};
use prepoly_parser::ast::{FunDecl, TopLevel};

/// An empty program, for lowering bodies that need no call/type resolution.
fn empty_program() -> Program {
    Program {
        types: HashMap::new(),
        functions: HashMap::new(),
        inits: Vec::new(),
        module_imports: HashMap::new(),
        import_origins: HashMap::new(),
        import_renames: HashMap::new(),
        module_aliases: HashMap::new(),
        symbol_aliases: HashMap::new(),
        primitive_methods: HashMap::new(),
        type_aliases: HashMap::new(),
    }
}

/// Parse `src` and return its single top-level function.
fn first_fun(src: &str) -> FunDecl {
    let module = prepoly_parser::parse(src).expect("source parses");
    module
        .items
        .into_iter()
        .find_map(|item| match item {
            TopLevel::Fun(decl) => Some(decl),
            _ => None,
        })
        .expect("a function declaration")
}

/// Lower the first function of `src` against an empty program.
fn lower_first(src: &str) -> (MirBody, Vec<prepoly_mir::MirClosure>) {
    let decl = first_fun(src);
    let prog = empty_program();
    lower_body(&prog, &[], None, &decl.params, &decl.body)
}

/// Lower a whole single-module program through HIR and render it.
fn lower_whole(src: &str) -> String {
    let ast = prepoly_parser::parse(src).expect("source parses");
    let modules = [LoadedModule {
        path: vec!["main".to_string()],
        ast,
    }];
    let (program, _errors) = prepoly_hir::lower(&modules);
    program_to_string(&lower_program(&program))
}

#[test]
fn three_addresses_arithmetic() {
    // `a + b * c` flattens to two binaries naming intermediate temporaries.
    let (body, _) = lower_first("fun f(a, b, c) { return a + b * c }");
    let text = body_to_string(&body);
    // Multiplication is computed first, then the addition over its result.
    assert!(text.contains("_3 = _1 Mul _2"), "{text}");
    assert!(text.contains("_4 = _0 Add _3"), "{text}");
    assert!(text.contains("return _4"), "{text}");
    // Parameters map to the first three locals in order.
    assert!(text.contains("params: [_0, _1, _2]"), "{text}");
}

#[test]
fn if_expression_merges_through_a_result_local() {
    // Both arms of a value `if` write the same result local; control rejoins at
    // the merge block.
    let (body, _) = lower_first("fun f(c) { let x = if c { 1 } else { 2 } return x }");
    let text = body_to_string(&body);
    assert!(text.contains("if _0 -> bb1 else bb2"), "{text}");
    // The then/else arms both assign the shared if-result local _1.
    assert!(text.contains("_1 = 1"), "{text}");
    assert!(text.contains("_1 = 2"), "{text}");
    assert!(text.contains("goto bb3"), "{text}");
}

#[test]
fn short_circuit_and_only_evaluates_rhs_when_needed() {
    // `a && b`: the true edge evaluates b, the false edge yields the constant.
    let (body, _) = lower_first("fun f(a, b) { return a && b }");
    let text = body_to_string(&body);
    // And: cond true -> rhs block, false -> skip block.
    assert!(text.contains("if _0 -> bb1 else bb2"), "{text}");
    // Skip block short-circuits to the constant `false`.
    assert!(text.contains("= false"), "{text}");
}

#[test]
fn while_loop_has_back_edge_and_break_target() {
    let (body, _) = lower_first("fun f(n) { let i = 0 while i < n { i = i + 1 } return i }");
    let text = body_to_string(&body);
    // The condition block branches to body or end; the body jumps back.
    assert!(text.contains("Lt"), "{text}");
    // Two distinct gotos back to the condition block (entry + back edge).
    assert!(text.matches("goto bb1").count() >= 2, "{text}");
}

#[test]
fn for_loop_desugars_to_indexed_iteration() {
    let (body, _) = lower_first("fun f(xs) { for v in xs { print(v) } }");
    let text = body_to_string(&body);
    assert!(text.contains("builtin array_len"), "{text}");
    // The element is read by indexing the iterable with the loop counter.
    assert!(text.contains("load _"), "{text}");
    assert!(text.contains("Lt"), "{text}");
}

#[test]
fn for_over_range_counts_without_materializing_an_array() {
    // `for v in [lo..hi]` must lower to a direct counting loop: the range is
    // unobservable as a value, and building it (one push per element) costs
    // the full range in memory and time.
    let (body, _) = lower_first("fun f(n) { for v in [0..n] { print(v) } }");
    let text = body_to_string(&body);
    assert!(!text.contains("push"), "range was materialized: {text}");
    assert!(!text.contains("= []"), "range was materialized: {text}");
    assert!(
        !text.contains("array_len"),
        "range was materialized: {text}"
    );
    // The counter still drives a bounded loop.
    assert!(text.contains("Lt"), "{text}");
    assert!(text.contains("Add 1"), "{text}");
}

#[test]
fn range_as_a_value_still_materializes() {
    // Outside a `for` head the range IS the value, so the fill loop remains.
    let (body, _) = lower_first("fun f() { let xs = [0..3] return xs }");
    let text = body_to_string(&body);
    assert!(text.contains("push"), "{text}");
}

#[test]
fn const_array_literal_promotes_to_a_shared_global() {
    // A constant literal only read by the callee (indexed, measured) is
    // rewritten into a read of a synthetic global built once by the prepended
    // consts init, so a call inside a loop stops allocating per iteration.
    let text = lower_whole(
        "fun total(a) -> int32 {\n  let t = 0\n  for i in [0..a.len()] {\n    t += a[i]\n  }\n  return t\n}\n\
         println(total([1, 2, 3]))\n",
    );
    assert!(text.contains("global __arr0@consts = "), "{text}");
    assert!(text.contains("= global __arr0@consts"), "{text}");
    // The literal itself must no longer be constructed at the call site: the
    // only [1, 2, 3] construction left is the consts init's.
    assert_eq!(text.matches("= [1, 2, 3]").count(), 1, "{text}");
}

#[test]
fn mutated_and_escaping_literals_keep_per_evaluation_construction() {
    // A literal mutated through its binding, and one stored into a mutable
    // global structure, must stay a fresh value per evaluation -- sharing one
    // frozen global would leak writes across evaluations.
    let text = lower_whole(
        "fun stash(x) {\n  holder[0] = x\n}\n\
         let holder = [[0]]\n\
         let m = [10, 20]\n\
         m[0] = 11\n\
         stash([5, 6])\n",
    );
    assert!(!text.contains("@consts"), "{text}");
    assert!(text.contains("= [10, 20]"), "{text}");
    assert!(text.contains("= [5, 6]"), "{text}");
}

#[test]
fn error_propagation_branches_and_returns_on_err() {
    // `r!` tests the Result, unwraps on Ok, returns the Result on Err.
    let (body, _) = lower_first("fun f(r) { let x = r! return x }");
    let text = body_to_string(&body);
    assert!(text.contains("builtin result_is_ok(_0)"), "{text}");
    assert!(text.contains("load _0.value"), "{text}");
    // The Err edge propagates the original Result by returning it.
    assert!(text.contains("return _0"), "{text}");
}

#[test]
fn match_chains_pattern_tests_and_panics_on_fallthrough() {
    let src = "fun f(n) { return match n { 0 => 10, _ => 20 } }";
    let (body, _) = lower_first(src);
    let text = body_to_string(&body);
    // Literal arm compares the subject to the literal.
    assert!(text.contains("Eq 0"), "{text}");
    // Unmatched fallthrough panics and is unreachable.
    assert!(text.contains("builtin panic"), "{text}");
    assert!(text.contains("unreachable"), "{text}");
}

#[test]
fn closure_captures_enclosing_local() {
    // The closure references `base`, which is bound in the enclosing function,
    // so it becomes a capture; `x` is its own parameter and is not captured.
    let src = "fun f(base) { let g = (x) -> x + base return g(1) }";
    let (body, closures) = lower_first(src);
    assert_eq!(closures.len(), 1, "one closure lowered");
    let clo = &closures[0];
    assert_eq!(clo.capture_names, vec!["base".to_string()]);
    assert_eq!(clo.params.len(), 1);
    let text = body_to_string(&body);
    // The closure value captures the enclosing `base` local (_0).
    assert!(text.contains("clo0[_0]"), "{text}");
    // The call site dispatches indirectly through the closure value.
    assert!(text.contains("indirect"), "{text}");
    // Inside the closure body, the capture is read as its own local and the
    // parameter is added to it.
    let clo_text = body_to_string(&clo.body);
    assert!(clo_text.contains("Add"), "{clo_text}");
}

#[test]
fn whole_program_routes_calls_and_constructs() {
    let src = "\
type Point = {
    x
    y
}

fun Point.new(x, y) {
    return Self { x: x, y: y }
}

fun mk() {
    return Point.new(1, 2)
}

fun bad() {
    return error(\"no\")
}
";
    let text = lower_whole(src);
    // `Point.new(...)` is a static call keyed on the type symbol.
    assert!(text.contains("static Point.new(1, 2)"), "{text}");
    // `Self { ... }` resolves to a Point record construction.
    assert!(text.contains("Point { x: _"), "{text}");
    // `error(\"no\")` desugars to a Result.Err variant, and the function is
    // marked fallible.
    assert!(text.contains("Result.Err { error:"), "{text}");
    assert!(text.contains("fn bad [bad] (fallible)"), "{text}");
}

#[test]
fn method_and_init_bodies_are_lowered() {
    let src = "\
let counter = 0

type Box = {
    value
}

fun Box.get(self) {
    return self.value
}
";
    let text = lower_whole(src);
    // The top-level `let` initializes a module global in an init body; the
    // global is keyed by its defining module so same-named globals in other
    // modules stay distinct.
    assert!(text.contains("global counter@main = 0"), "{text}");
    // The instance method reads `self.value` via a field load.
    assert!(text.contains("method Box.get"), "{text}");
    assert!(text.contains("load _0.value"), "{text}");
}
