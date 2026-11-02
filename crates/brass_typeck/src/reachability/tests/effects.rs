//! Footprint and context regressions exercise the single shadow authority.

use super::{ItemIndex, Reason, has, program, selected};

#[test]
fn initializer_keeps_uncalled_shared_global_contributors() {
    // A read followed by push constrains the initializer's open array even
    // without execution. Compare independent checker runs and their published
    // globals; dropping the writer would reject the reached initializer.
    for writer in [
        "fun writer() { values.push(1) }",
        "type Unused = | A\nfun Unused.writer(self) { values.push(1) }",
    ] {
        let p = program(
            &format!(
                "let values = []\n{writer}\nfun reached() {{ return values.len() }}\nfun untouched() {{ return 1 }}"
            ),
            "import lib.{ reached }\nlet count = reached()",
        );
        let index = ItemIndex::new(&p);
        let reach = super::Reachability::new(&index, &super::scope());
        let view = crate::reachability::AnalysisView::new(
            &p,
            reach.selection().clone(),
            Default::default(),
            Default::default(),
        );
        assert!(!has(&selected(&p), "untouched", Reason::SharedInference));
        let full = crate::analyze(&p);
        let selected = crate::analyze_selected(&p, None, &view);
        assert!(full.errors.is_empty(), "{:?}", full.errors);
        assert_eq!(selected.errors, full.errors);
        assert_eq!(
            selected.context_tables.global_defs,
            full.context_tables.global_defs
        );
        assert_eq!(
            selected.function_returns["reached"],
            full.function_returns["reached"]
        );
    }
}

#[test]
fn clean_static_calls_are_not_shared_obligations() {
    let p = program(
        "type A = { x: int32 }\nfun leaf() -> int32 { return 1 }\nfun A.n(self) -> int32 { return leaf() }\nfun A.m(self) -> int32 { return self.n() }",
        "import lib.{ A }\nconst value = A { x: 0 }",
    );
    let index = ItemIndex::new(&p);
    for (_, label, summary) in index.effect_summaries() {
        if label.starts_with("A.") || label == "leaf" {
            assert!(summary.is_clean(), "{label}: {summary:?}");
        }
    }
    assert!(!has(&selected(&p), "A.m:", Reason::SharedInference));
}

#[test]
fn recursive_components_propagate_reads_writes_and_unknown_calls() {
    let p = program(
        "let shared = 0\nfun a() -> int32 { return b() }\nfun b() -> int32 { shared = 2\nif false { return a() }\nreturn shared }\nfun dynamic(f: () -> int32) -> int32 { return f() }\nfun wrapper(f: () -> int32) -> int32 { return dynamic(f) }",
        "",
    );
    let index = ItemIndex::new(&p);
    for (_, label, summary) in index.effect_summaries() {
        match label {
            "a" | "b" => {
                assert!(
                    summary
                        .global_reads
                        .contains(&(vec!["lib".into()], "shared".into()))
                );
                assert!(
                    summary
                        .global_writes
                        .contains(&(vec!["lib".into()], "shared".into()))
                );
            }
            "dynamic" | "wrapper" => {
                assert!(summary.unknown_calls.iter().any(|s| s.ends_with(":f")))
            }
            _ => {}
        }
    }
}

#[test]
fn shared_scheme_openness_does_not_open_a_concrete_caller() {
    let p = program(
        "type Box = { value }\nfun Box.get(self) { return self.value }\ntype Unused = { x: int32 }\nfun Unused.unused(self) -> int32 { return 1 }\nfun decode(value: Box) -> int32 { const ret = value.get()\nfor field in fields(ret) {}\nreturn 1 }",
        "import lib.{ Box, decode }\ndecode(Box { value: 1 })",
    );
    let items = selected(&p);
    assert!(has(&items, "Box.get:", Reason::SharedInference));
    assert!(
        !items.iter().any(|(name, _)| name.starts_with("Unused")),
        "{items:?}"
    );
}

#[test]
fn abstract_shared_reflection_stays_with_inhabited_layouts() {
    let p = program(
        "type Box = { value }\nfun Box.unused(self, value) { for field in fields(value) {} }\ntype Unused = { x: int32 }",
        "import lib.{ Box }\nconst value = Box { value: 1 }",
    );
    assert!(!selected(&p).iter().any(|(name, _)| name == "Unused"));
}

#[test]
fn qualified_and_renamed_global_reads_keep_defining_identity() {
    let p = program(
        "const shared = 1",
        "import lib as dep\nimport lib.{ shared as alias }\nfun read() -> int32 { return dep.shared + alias }",
    );
    let index = ItemIndex::new(&p);
    let summary = index
        .effect_summaries()
        .find(|(_, name, _)| *name == "read")
        .unwrap()
        .2;
    assert_eq!(
        summary.global_reads.iter().cloned().collect::<Vec<_>>(),
        vec![(vec!["lib".into()], "shared".into())]
    );
}

#[test]
fn nested_mutation_and_capture_taint_the_calling_method() {
    let p = program(
        "type A = { x: int32 }\nfun mutate(a: A) -> int32 { if true { a.x = 2 }\nreturn 1 }\nfun A.m(self) -> int32 { return mutate(self) }\nfun capture() -> int32 { const f = () -> 2\nreturn f() }\nfun A.c(self) -> int32 { return capture() }",
        "",
    );
    let index = ItemIndex::new(&p);
    for (_, label, summary) in index.effect_summaries() {
        if label.starts_with("A.m:") {
            assert!(!summary.shared_cells.is_empty());
        }
        if label.starts_with("A.c:") {
            assert!(!summary.captures.is_empty());
            assert!(!summary.unknown_calls.is_empty());
        }
    }
}

#[test]
fn generated_conversion_edge_is_not_an_independent_open_root() {
    // A generated edge with a reached caller uses that caller's values. In
    // contrast, require(Generated) has its own checking frame (tested separately).
    let p = program(
        "type A = { x: int32 }\nfun A.from(value) -> A { for field in fields(value) {}\nreturn A { x: 1 } }\ntype Unused = { x: int32 }",
        "import lib.{ A }\ninfer.from(A { x: 1 })",
    );
    let items = selected(&p);
    assert!(has(&items, "A.from:", Reason::Generated));
    assert!(!items.iter().any(|(name, _)| name == "Unused"), "{items:?}");
}

#[test]
fn function_value_edges_carry_potential_keyed_discovery_effects() {
    // Lazy discovery may walk a referenced function before it is called. Follow
    // value edges as selection does; an uncalled spelling is not a purity proof.
    let p = program(
        "let shared = 0\nfun dirty() -> int32 { shared = 1\nreturn 1 }\nfun value() { return dirty }\ntype A = { x: int32 }\nfun A.callback(self) { return value }",
        "",
    );
    let index = ItemIndex::new(&p);
    for (_, name, summary) in index.effect_summaries() {
        if name == "value" || name.starts_with("A.callback:") {
            assert!(
                summary
                    .global_writes
                    .contains(&(vec!["lib".into()], "shared".into())),
                "{name}: {summary:?}"
            );
        }
    }
}

#[test]
fn rootless_sums_separate_local_constraints_from_external_dependencies() {
    let p = program(
        "type Box = { value }\nfun Box.set(self, x) { self.value = x }\nfun Box.get(self) { return self.value }\nfun helper(x: int32) -> int32 { return x }\ntype Choice = | A | B\nfun Choice.local(self, x) { let b = Box { value: helper(x) }\nb.set(2)\nreturn b.get() }",
        "import lib.{ Choice }\nconst c = Choice.A",
    );
    assert!(!has(
        &selected(&p),
        "Choice.local:",
        Reason::SharedInference
    ));
    for body in [
        "let shared = 0\nfun leaf() { shared = 1 }\nfun middle() { leaf() }\nfun Choice.touch(self) { middle() }",
        "const shared = []\nfun leaf() { return shared }\nfun Choice.touch(self) { const x = leaf }",
        "fun Choice.touch(self, callback: () -> int32) { return callback() }",
        "fun Choice.touch(self) { const callback = () -> 1\nreturn callback() }",
        "const shared = []\nfun leaf() { return shared }\ntype Callable = { get: () -> int32 }\ntype Other = { x: int32 }\nfun Other.get(self) -> int32 { return 1 }\nfun Choice.touch(self) { const c = Callable { get: leaf }\nreturn c.get() }",
    ] {
        let p = program(
            &format!("type Choice = | A | B\n{body}"),
            "import lib.{ Choice }\nconst c = Choice.A",
        );
        assert!(
            has(&selected(&p), "Choice.touch:", Reason::SharedInference),
            "{body}"
        );
    }
}

#[test]
fn rootless_annotations_cannot_borrow_another_owners_open_cells() {
    for body in [
        "fun Choice.touch(self, b: Box) { return b.value.field }",
        "fun helper(b: Box) { return b.value.field }\nfun Choice.touch(self, b) { return helper(b) }",
        "fun Choice.touch(self) { let b: Box\nreturn b.value.field }",
    ] {
        let p = program(
            &format!("type Box = {{ value }}\ntype Choice = | A | B\n{body}"),
            "import lib.{ Choice }\nconst c = Choice.A",
        );
        assert!(
            has(&selected(&p), "Choice.touch:", Reason::SharedInference),
            "{body}"
        );
    }
}

#[test]
fn qualified_sum_patterns_do_not_use_other_imported_sums() {
    let p = program(
        "type Used = | Array { value: int32 } | Empty\ntype Other = | Array { value: string } | Empty\nfun inspect(v: Used) -> int32 { match v { Used.Array { value } => { return value }, _ => {} }\nreturn 0 }",
        "import lib.{ Used, Other, inspect }\ninspect(Used.Array { value: 1 })",
    );
    assert!(!selected(&p).iter().any(|(label, _)| label == "Other"));
}

#[test]
fn bare_type_test_views_keep_shared_field_constraints() {
    for access in ["b.value.field", "b.touch()"] {
        let p = program(
            &format!(
                "type Box = {{ value }}\nfun Box.touch(self) {{ return self.value.field }}\ntype Choice = | A | B\nfun Choice.unused(self, b) {{ if b: Box {{ return {access} }}\nreturn 1 }}"
            ),
            "import lib.{ Choice }\nconst c = Choice.A",
        );
        assert!(has(
            &selected(&p),
            "Choice.unused:",
            Reason::SharedInference
        ));
    }
}

#[test]
fn matching_an_open_call_result_keeps_borrowed_payloads() {
    let p = program(
        "type Payload = | A { value } | B\nfun id(x) { return x }\ntype Choice = | A | B\nfun Choice.unused(self, x) { match id(x) { Payload.A { value } => { return value.field }, _ => {} }\nreturn 1 }",
        "import lib.{ Choice }\nconst c = Choice.A",
    );
    assert!(has(
        &selected(&p),
        "Choice.unused:",
        Reason::SharedInference
    ));
}
