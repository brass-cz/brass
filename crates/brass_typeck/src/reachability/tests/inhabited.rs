//! Each producer family must make virtual targets available at the fixpoint.

use super::{ItemIndex, METHODS, Reachability, Reason, has, program, scope, selected};

#[test]
fn each_nominal_producer_reopens_virtual_dispatch() {
    for producer in [
        "const value = A { x: 1 }",
        "let value: A",
        "const value: A = factory()",
        // Declaration evidence is independent of a body producer; the shadow
        // does not diagnose the intentionally incompatible body here.
        "fun factory() -> A { return 0 }\nfactory()",
        "fun factory() { return A { x: 1 } }\nfactory()",
        "const make = () -> A { x: 1 }\nmake()",
        "const value = A.from(B { x: 1 })",
        "const value = A.new()",
        "const value = A.default()",
        "const values: A?[] = []",
    ] {
        let p = program(
            &format!("{METHODS}\nfun virtual(x) {{ return x.hit() }}"),
            &format!("import lib.{{ A, B, virtual }}\nvirtual(0)\n{producer}"),
        );
        assert!(
            has(&selected(&p), "A.hit:", Reason::ExplicitUse),
            "{producer}"
        );
    }
}

#[test]
fn imports_and_type_tests_do_not_invent_values() {
    let p = program(METHODS, "import lib.{ A }\nif 0: A { println(1) }");
    let index = ItemIndex::new(&p);
    let reach = Reachability::new(&index, &scope());
    assert!(!reach.state.inhabited.nominal.contains(&p.types["A"].id));
    assert!(
        !selected(&p)
            .iter()
            .any(|(label, _)| label.starts_with("A.hit:"))
    );
}

#[test]
fn annotated_unused_own_root_produces_its_declared_input() {
    let p = program(
        METHODS,
        "import lib.{ A }\nfun unused(x: A) { return x.hit() }",
    );
    assert!(has(&selected(&p), "A.hit:", Reason::ExplicitUse));
}

#[test]
fn open_unused_own_root_retains_the_same_name_family() {
    let p = program(METHODS, "fun unused(x) { return x.hit() }");
    for name in ["A.hit:", "B.hit:"] {
        assert!(has(&selected(&p), name, Reason::ExplicitUse));
    }
}

#[test]
fn open_closure_input_inside_own_root_retains_the_family() {
    let p = program(METHODS, "fun unused() { const invoke = (x) -> x.hit() }");
    for name in ["A.hit:", "B.hit:"] {
        assert!(has(&selected(&p), name, Reason::ExplicitUse));
    }
}

#[test]
fn open_root_flows_through_locals_and_dependency_helpers() {
    let p = program(
        &format!("{METHODS}\nfun helper(x) {{ return x.hit() }}"),
        "import lib.{ helper }\nfun unused(x) { const local = x\nreturn helper(local) }",
    );
    for name in ["A.hit:", "B.hit:"] {
        assert!(has(&selected(&p), name, Reason::ExplicitUse));
    }
}

#[test]
fn exact_string_rendering_cannot_reach_uninhabited_display() {
    let p = program(
        "type A = { x: int32 }\nfun A.display(self) -> string { return \"A\" }",
        "println(\"ready\")",
    );
    assert!(!selected(&p).iter().any(|(label, _)| label.starts_with("A")));
}

#[test]
fn sum_variants_recursive_maps_and_global_initializers_produce_values() {
    let p = program(
        "type Choice = | Empty | Value { x: int32 }\nfun Choice.hit(self) -> int32 { return 1 }\nconst global = Choice.Empty\ntype Map = { type value\nvalues: Self.value[] }\ntype Box = { map: Map { value: Choice } }\nfun Box.make() -> Box { let b: Box\nreturn b }",
        "import lib.{ Box }\nBox.make()\nfun use(x) { return x.hit() }",
    );
    let index = ItemIndex::new(&p);
    let reach = Reachability::new(&index, &scope());
    for name in ["Choice", "Map", "Box"] {
        assert!(
            reach.state.inhabited.nominal.contains(&p.types[name].id),
            "{name}"
        );
    }
    assert!(has(&selected(&p), "Choice.hit:", Reason::ExplicitUse));
}

#[test]
fn plugin_and_builtin_returns_propagate_wrapped_element_families() {
    let p = program(
        "",
        "_plugin_fcall_aas()\n_argv()\nlen([])\nconst nullable = null\nconst mixed = [1, \"x\"]",
    );
    let index = ItemIndex::new(&p);
    let reach = Reachability::new(&index, &scope());
    for name in ["array", "string", "int64"] {
        assert!(reach.state.inhabited.primitive.contains(name), "{name}");
    }
    assert!(reach.state.inhabited.wrappers.contains("nullable"));
}

#[test]
fn generated_and_demanded_bodies_feed_the_same_producer_closure() {
    let p = program(
        &format!("{METHODS}\nfun generated() {{ return A {{ x: 1 }} }}"),
        "",
    );
    for reason in [Reason::Generated, Reason::Demand, Reason::ExplicitUse] {
        let index = ItemIndex::new(&p);
        let mut reach = Reachability::new(&index, &scope());
        assert!(!reach.state.inhabited.nominal.contains(&p.types["A"].id));
        let target = index
            .items()
            .find(|(_, label)| *label == "generated")
            .unwrap()
            .0
            .clone();
        reach.require(target.clone(), reason);
        assert!(reach.state.inhabited.nominal.contains(&p.types["A"].id));
        assert!(reach.selection().reasons.contains_key(&target));
    }
}

#[test]
fn reflected_callback_values_are_reached_at_their_producer() {
    let p = program(
        "fun callback() -> int32 { return 1 }\ntype Box = { callback: () -> int32 }",
        "import lib.{ Box, callback }\nconst b = Box { callback: callback }\nfor key in fields(b) { b[key]() }",
    );
    assert!(has(&selected(&p), "callback", Reason::ExplicitUse));
}

#[test]
fn substituted_recursive_layout_is_closed_but_unpinned_layout_is_not() {
    let p = program(
        "type Map = { type key\ntype value\nkeys: Self.key[]\nvalues: Self.value[] }\ntype Tree = | Leaf | Node { children: Map { key: string, value: Tree } }\nfun Tree.unused(self) -> int32 { return 1 }\ntype Open = { children: Map { key: string } }\nfun Open.unused(self) -> int32 { return 1 }",
        "",
    );
    for (name, closed) in [("Tree", true), ("Open", false)] {
        let info = &p.types[name];
        let methods = match &info.kind {
            brass_hir::TypeKind::Record { methods, .. } => methods,
            brass_hir::TypeKind::Sum { variants } => &variants[0].methods,
        };
        assert_eq!(
            super::shared_obligation(&ItemIndex::new(&p), info, &methods["unused"]).is_none(),
            closed,
            "{name}"
        );
    }
}

#[test]
fn exact_rendering_does_not_dispatch_to_other_inhabited_types() {
    let p = program(
        "type A = { x: int32 }\nfun A.display(self) -> string { return \"A\" }\ntype B = { x: int32 }\nfun B.display(self) -> string { return \"B\" }",
        "import lib.{ A, B }\nconst b = B { x: 1 }\nprintln(A { x: 1 })\nprintln([\"literal\"])\nprintln(null)",
    );
    let items = selected(&p);
    assert!(has(&items, "A.display:", Reason::ImplicitUse));
    assert!(!items.iter().any(|(name, _)| name.starts_with("B.display:")));
}

#[test]
fn a_module_global_value_can_shadow_a_static_qualifier() {
    let p = program(
        METHODS,
        "import lib.{ A, B }\nconst A = B { x: 1 }\nfun use() { return A.hit() }",
    );
    assert!(has(&selected(&p), "B.hit:", Reason::ExplicitUse));
}

#[test]
fn open_root_rendering_and_reflection_keep_conservative_targets() {
    let p = program(
        "type A = { x: int32 }\nfun A.display(self) -> string { return \"A\" }",
        "fun unused(x) { println(x) }",
    );
    assert!(has(&selected(&p), "A.display:", Reason::ImplicitUse));
    let p = program(
        METHODS,
        "fun unused(x) { for key in fields(x) { println(key) } }",
    );
    let index = ItemIndex::new(&p);
    let reach = Reachability::new(&index, &scope());
    assert_eq!(reach.selection().reasons.len(), index.len());
}

#[test]
fn open_root_results_cannot_be_narrowed_in_a_closed_caller() {
    let p = program(
        METHODS,
        "fun identity(x) { return x }\nfun consumer() { return identity(0).hit() }",
    );
    for name in ["A.hit:", "B.hit:"] {
        assert!(has(&selected(&p), name, Reason::ExplicitUse));
    }
}

#[test]
fn structural_type_test_mentions_do_not_produce_field_values() {
    let p = program(
        METHODS,
        "import lib.{ A }\nif 0: anonymous { value: A } { println(1) }",
    );
    let index = ItemIndex::new(&p);
    let reach = Reachability::new(&index, &scope());
    assert!(!reach.state.inhabited.nominal.contains(&p.types["A"].id));
}

#[test]
fn own_method_receiver_is_an_abstract_producer() {
    let p = program(
        METHODS,
        "import lib.{ A }\ntype Owner = { value: A }\nfun Owner.unused(self) { return self.value.hit() }",
    );
    assert!(has(&selected(&p), "A.hit:", Reason::ExplicitUse));
}

#[test]
fn externally_required_callable_seeds_its_declared_inputs() {
    let p = program(
        &format!("{METHODS}\nfun generated(x: A) {{ return x.hit() }}"),
        "",
    );
    for reason in [Reason::Generated, Reason::Demand, Reason::ExplicitUse] {
        let index = ItemIndex::new(&p);
        let mut reach = Reachability::new(&index, &scope());
        let target = index
            .items()
            .find(|(_, label)| *label == "generated")
            .unwrap()
            .0
            .clone();
        reach.require(target, reason);
        assert!(reach.state.inhabited.nominal.contains(&p.types["A"].id));
        let hit = index
            .items()
            .find(|(_, label)| label.starts_with("A.hit:"))
            .unwrap()
            .0;
        assert!(reach.selection().reasons.contains_key(hit));
    }
}

#[test]
fn explicit_required_open_callable_is_an_abstract_root() {
    let p = program(
        &format!("{METHODS}\nfun external(x) {{ return x.hit() }}"),
        "",
    );
    let index = ItemIndex::new(&p);
    let mut reach = Reachability::new(&index, &scope());
    let target = index
        .items()
        .find(|(_, label)| *label == "external")
        .unwrap()
        .0
        .clone();
    reach.require(target, Reason::ExplicitUse);
    for prefix in ["A.hit:", "B.hit:"] {
        let hit = index
            .items()
            .find(|(_, label)| label.starts_with(prefix))
            .unwrap()
            .0;
        assert!(reach.selection().reasons.contains_key(hit));
    }
}

#[test]
fn a_later_local_binding_cannot_erase_a_static_call() {
    let p = program(
        &format!("{METHODS}\nfun A.make() -> int32 {{ return 1 }}"),
        "import lib.{ A, B }\nif true { A.make()\nconst A = B { x: 1 }\nA.hit() }",
    );
    let items = selected(&p);
    for prefix in ["A.make:", "B.hit:"] {
        assert!(has(&items, prefix, Reason::ExplicitUse));
    }
}
