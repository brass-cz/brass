//! Independent checker forks test omission against the real shared-body driver.

use super::{Checker, check_method_bodies};
use crate::infer::co_replay::snapshot::EffectSnapshot;
use crate::reachability::{ItemIndex, shared_obligation};
use brass_hir::{LoadedModule, Program, TypeKind};
use std::rc::Rc;

fn program(source: &str) -> Program {
    let (p, errors) = brass_hir::lower(&[LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["main".into()],
        ast: brass_parser::parse(source).unwrap(),
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    p
}

/// Keep all declarations and signatures; only bodies with an absence proof are
/// omitted on the second fork. This is a test harness, not a production filter.
fn compare(source: &str, expected_omissions: usize) {
    let full = program(source);
    let mut selected = program(source);
    let index = ItemIndex::new(&full);
    let mut omitted = 0;
    for (symbol, info) in &mut selected.types {
        let original = &full.types[symbol];
        match &mut info.kind {
            TypeKind::Record { methods, .. } => {
                for method in methods.values_mut() {
                    if shared_obligation(&index, original, method).is_none() {
                        Rc::make_mut(&mut method.decl).body = None;
                        omitted += 1;
                    }
                }
            }
            TypeKind::Sum { variants } => {
                for variant in variants {
                    for method in variant.methods.values_mut() {
                        if shared_obligation(&index, original, method).is_none() {
                            Rc::make_mut(&mut method.decl).body = None;
                            omitted += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(omitted, expected_omissions, "{source}");
    let rows = Rc::new(brass_typesys::RowInfo::analyze(&full));
    let mut seed = Checker::new(&full, rows);
    seed.precompute_global_bindings();
    seed.precompute_returns();
    seed.settle_numeric_globals();
    for schemes_only in [true, false] {
        let mut all = EffectSnapshot::fork(&seed);
        let mut subset = EffectSnapshot::fork(&seed);
        subset.program = &selected;
        check_method_bodies(&mut all, &full, schemes_only);
        check_method_bodies(&mut subset, &selected, schemes_only);
        EffectSnapshot::capture_shared(&all)
            .compare(&EffectSnapshot::capture_shared(&subset))
            .unwrap();
        // A reached function is walked on both forks after shared preparation,
        // including its full instance return identity and error payload.
        if let Some(function) = full.functions.get("reached") {
            let mut results = Vec::new();
            for checker in [&mut all, &mut subset] {
                checker.schemes = checker.build_schemes();
                let result = checker.instantiate_function_call(
                    "reached",
                    &function.module,
                    &function.signature.params,
                    &function.decl.body,
                    function.signature.ret_ty.clone(),
                    brass_hir::Type::Unknown(0),
                    &[],
                    function.decl.body.span,
                );
                results.push((
                    checker.resolve(&result),
                    checker.errors.clone(),
                    checker.instance_returns.clone(),
                ));
            }
            assert_eq!(results[0], results[1]);
            EffectSnapshot::capture_shared(&all)
                .compare(&EffectSnapshot::capture_shared(&subset))
                .unwrap();
        }
    }
}

#[test]
fn certified_closed_and_recursive_layouts_preserve_shared_state() {
    compare(
        "type Box = { value: int32 }\nfun Box.unused(self) -> int32 { return 7 }\nfun reached() { return Box { value: 3 }.value }",
        1,
    );
    compare(
        "type Link = { next: Link? }\nfun Link.unused(self) -> int32 { return 1 }\nfun reached() { return Link { next: null } }",
        1,
    );
    compare(
        "type Choice = | A { value: string } | B { value: string }\nfun Choice.unused(self) { return 1 }\nfun reached() { return Choice.A { value: \"ok\" } }",
        2,
    );
}

#[test]
fn open_fields_nested_links_globals_and_error_payloads_are_retained() {
    compare(
        "type Box = { value }\nfun Box.set(self, value) { self.value = value }\nfun Box.get_or(self, fallback) { if false { return fallback }\nreturn self.value }\nfun reached() { let b = Box { value: 1 }\nreturn b.get_or(2) }",
        0,
    );
    compare(
        "fun id(value) { return value }\ntype Box = { values: infer[] }\nfun Box.insert(self, x) { self.values.push(id(x))\nself.values.push(id(x)) }\nfun Box.nested(self, x) { self.insert(x) }\nfun reached() { return 1 }",
        0,
    );
    compare(
        "type A = { x: int32 }\nconst shared = []\nfun A.write(self) -> int32 { shared.push(1)\nreturn 1 }\nfun A.void(self) {}\nfun reached() { return 1 }",
        0,
    );
    compare(
        "type Result = | Ok { value } | Err { error }\nfun error(x) { return Result.Err { error: x } }\ntype A = { x: int32 }\nfun A.text(self) -> int32! { return error(\"text\") }\nfun A.number(self) -> int32! { return error(7) }\nfun reached() { return 1 }",
        0,
    );
    compare(
        "type Inner = { type value\nitems: Self.value[] }\ntype Alias = Inner\ntype Outer = { inner: Alias }\nfun Outer.touch(self) -> int32 { return 1 }\nfun reached() { return 1 }",
        0,
    );
}

#[test]
fn recursive_substituted_map_layout_preserves_shared_state() {
    compare(
        "type Map = { type key\ntype value\nkeys: Self.key[]\nvalues: Self.value[] }\ntype Tree = | Leaf | Node { children: Map { key: string, value: Tree } }\nfun Tree.unused(self) -> int32 { return 1 }\nfun reached() { return Tree.Leaf }",
        2,
    );
}

#[test]
fn clean_call_chain_preserves_shared_state() {
    // Closed results do not refine a shared scheme through either free call.
    compare(
        "fun leaf() -> int32 { return 7 }\nfun middle() -> int32 { return leaf() }\ntype A = { x: int32 }\nfun A.unused(self) -> int32 { return middle() }\nfun reached() -> int32 { return 1 }",
        1,
    );
}

#[test]
fn depth_two_global_write_is_retained() {
    // The writer's footprint must reach the method through both call edges.
    compare(
        "let shared = 0\nfun leaf() -> int32 { shared = 7\nreturn shared }\nfun middle() -> int32 { return leaf() }\ntype A = { x: int32 }\nfun A.unused(self) -> int32 { return middle() }\nfun reached() -> int32 { return shared }",
        0,
    );
}

#[test]
fn recursive_clean_and_writing_components_preserve_shared_state() {
    // Recursion is a graph fixed point; no body is assumed clean just because
    // the other member was visited first. The checker still applies its cap.
    compare(
        "fun a(x: int32) -> int32 { if x == 0 { return 0 }\nreturn b(x - 1) }\nfun b(x: int32) -> int32 { return a(x) }\ntype A = { x: int32 }\nfun A.unused(self) -> int32 { return a(1) }\nfun reached() -> int32 { return 1 }",
        1,
    );
    compare(
        "let shared = 0\nfun a(x: int32) -> int32 { if x == 0 { shared = 1\nreturn 0 }\nreturn b(x - 1) }\nfun b(x: int32) -> int32 { return a(x) }\ntype A = { x: int32 }\nfun A.unused(self) -> int32 { return a(1) }\nfun reached() -> int32 { return 1 }",
        0,
    );
}

#[test]
fn dynamic_call_is_not_an_absence_certificate() {
    // A declared callback result is insufficient to constrain its effects.
    compare(
        "type A = { x: int32 }\nfun A.unused(self, callback: () -> int32) -> int32 { return callback() }\nfun reached() -> int32 { return 1 }",
        0,
    );
}

#[test]
fn closed_method_call_chain_preserves_shared_state() {
    compare(
        "type A = { x: int32 }\nfun A.n(self) -> int32 { return self.x }\nfun A.m(self) -> int32 { return self.n() }\nfun reached() -> int32 { return A { x: 3 }.x }",
        2,
    );
}

#[test]
fn sum_method_parameter_constraints_do_not_feed_record_schemes() {
    compare(
        "fun helper(x: int32) -> int32 { return x }\ntype Choice = | A | B\nfun Choice.unused(self, x) -> int32 { return helper(x) }\nfun reached() -> int32 { return 1 }",
        2,
    );
}

mod converters;
