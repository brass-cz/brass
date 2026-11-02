//! Shadow closure and ownership are checked independently of production policy.

use super::{
    BodyId, DiagnosticOwner, DiagnosticOwners, ItemIndex, ItemKey, Reachability, SharedObligation,
    shared_obligation,
};
use brass_hir::{
    LoadedModule, ModuleSource, PackageId, Program, ProjectScope, Reason, SourceOrigin, TypeKind,
};
use brass_parser::Span;
use std::path::PathBuf;
use std::sync::Arc;

fn module(name: &str, source: &str, base: usize, own: bool) -> LoadedModule {
    let location = PathBuf::from(format!("/project/{name}.cz"));
    LoadedModule {
        path: vec![name.into()],
        is_prelude: false,
        ast: brass_parser::parse_with_base(source, base).unwrap(),
        source: Some(Arc::new(ModuleSource {
            location,
            origin: if own {
                SourceOrigin::Own(PackageId::new("/project".as_ref()))
            } else {
                SourceOrigin::Dependency(PackageId::new("/project/vendor".as_ref()))
            },
            base,
            len: source.len(),
        })),
    }
}

fn program(dependency: &str, entry: &str) -> Program {
    let (p, errors) = brass_hir::lower(&[
        module("lib", dependency, 0, false),
        module("main", entry, 100_000, true),
    ]);
    assert!(errors.is_empty(), "{errors:?}");
    p
}

fn scope() -> ProjectScope {
    ProjectScope::new("/project/main.cz".into(), None, None)
}

fn selected(p: &Program) -> Vec<(String, Vec<Reason>)> {
    let index = ItemIndex::new(p);
    let reach = Reachability::new(&index, &scope());
    index
        .items()
        .filter_map(|(key, label)| {
            reach
                .selection()
                .reasons
                .get(key)
                .map(|reasons| (label.into(), reasons.clone()))
        })
        .collect()
}

fn has(items: &[(String, Vec<Reason>)], prefix: &str, reason: Reason) -> bool {
    items
        .iter()
        .any(|(label, reasons)| label.starts_with(prefix) && reasons.contains(&reason))
}

#[test]
fn imports_are_not_uses_but_own_unused_bodies_and_all_initializers_are_roots() {
    let p = program(
        "fun unused() -> int32 { return 1 }\nconst initialized = helper()\nfun helper() -> int32 { return 2 }",
        "import lib.{ unused }\nfun own_unused() -> int32 { return 3 }",
    );
    let items = selected(&p);
    assert!(!has(&items, "unused", Reason::ExplicitUse));
    assert!(has(&items, "helper", Reason::ExplicitUse));
    assert!(has(&items, "own_unused", Reason::Own));
    assert!(has(&items, "init:lib", Reason::Initializer));
    assert!(has(&items, "init:main", Reason::Initializer));
}

#[test]
fn renamed_functions_and_callback_values_follow_hir_resolution() {
    let p = program(
        "fun target() -> int32 { return 1 }\nfun sink(f) { return f() }\nfun untouched() { return 0 }",
        "import lib.{ target as alias, sink }\nconst callback = () -> alias()\nsink(alias)\nsink(callback)",
    );
    let items = selected(&p);
    assert!(has(&items, "target", Reason::ExplicitUse));
    assert!(has(&items, "sink", Reason::ExplicitUse));
    assert!(!has(&items, "untouched", Reason::ExplicitUse));
}

const METHODS: &str = "type A = { x: int32 }\nfun A.hit(self) -> int32 { return 1 }\nfun A.miss(self) -> int32 { return 2 }\ntype B = { x: int32 }\nfun B.hit(self) -> int32 { return 3 }";

#[test]
fn static_method_alias_and_constructor_receivers_are_exact() {
    for body in ["A.hit()", "A { x: 1 }.hit()", "type Alias = A\nAlias.hit()"] {
        let p = program(METHODS, &format!("import lib.{{ A }}\n{body}"));
        let items = selected(&p);
        assert!(has(&items, "A.hit:", Reason::ExplicitUse), "{items:?}");
        assert!(
            !items
                .iter()
                .any(|(name, _)| name.starts_with("B.hit:") || name.starts_with("A.miss:")),
            "{items:?}"
        );
    }
}

#[test]
fn open_receiver_widens_same_name_and_self_dispatch_keeps_owner() {
    let p = program(
        METHODS,
        "import lib.{ A, B }\nconst a = A { x: 1 }\nconst b = B { x: 2 }\nfun use(value) { return value.hit() }",
    );
    let items = selected(&p);
    assert!(has(&items, "A.hit:", Reason::ExplicitUse));
    assert!(has(&items, "B.hit:", Reason::ExplicitUse));
    assert!(!items.iter().any(|(name, _)| name.starts_with("A.miss:")));
    let p = program(
        &format!("{METHODS}\nfun A.forward(self) -> int32 {{ return self.hit() }}"),
        "import lib.{ A }\nA.forward()",
    );
    assert!(has(&selected(&p), "A.hit:", Reason::ExplicitUse));
}

#[test]
fn unused_method_signature_does_not_reach_its_return_layout() {
    let p = program(
        "type ResultType = { value: int32 }\ntype A = { x: int32 }\nfun A.unused(self) -> ResultType { return ResultType { value: 1 } }",
        "import lib.{ A }\nconst a = A { x: 1 }",
    );
    let items = selected(&p);
    assert!(has(&items, "A", Reason::ExplicitUse));
    assert!(
        !items
            .iter()
            .any(|(name, _)| name == "ResultType" || name.starts_with("A.unused:")),
        "{items:?}"
    );
}

#[test]
fn annotation_alias_pattern_and_default_reach_layouts() {
    let p = program(
        "type Inner = { x: int32 }\ntype Outer = { inner: Inner }\ntype Alias = Outer\ntype Choice = | Some { value: Inner } | None",
        "import lib.{ Alias, Inner, Choice }\nlet value: Alias\nfun inspect(x) { return match x { Choice.Some { value } => value\nChoice.None => Inner { x: 0 } } }",
    );
    let items = selected(&p);
    for name in ["Alias", "Outer", "Inner", "Choice"] {
        assert!(has(&items, name, Reason::ExplicitUse), "{name}: {items:?}");
    }
}

#[test]
fn rendering_recurses_conservatively_and_keeps_primitive_extensions() {
    let p = program(
        "type A = { x: int32 }\nfun A.display(self) -> string { return \"A\" }\nfun A.debug(self) -> string { return \"D\" }",
        "import lib.{ A }\nconst a = A { x: 1 }\nfun render(x) { print(x)\nprintln(x)\nstring.from(x)\nx.debug()\nreturn \"{x}\" }",
    );
    let items = selected(&p);
    assert!(has(&items, "A.display:", Reason::ImplicitUse));
    assert!(has(&items, "A.debug:", Reason::ExplicitUse));
    // Primitive extensions use the same function catalog, not nominal methods.
    let (p, errors) = brass_hir::lower(&[
        module(
            "core",
            "fun string.quoted(self) -> string { return self }\nfun infer[].visit(self) { return self }",
            0,
            false,
        ),
        module(
            "main",
            "fun use(x) { return x.quoted() }\nfun arrays(x) { return x.visit() }\nuse(\"s\")\narrays([1])",
            100_000,
            true,
        ),
    ]);
    assert!(errors.is_empty(), "{errors:?}");
    let items = selected(&p);
    for symbol in p.primitive_methods.values() {
        assert!(has(&items, symbol, Reason::ExplicitUse), "{items:?}");
    }
}

#[test]
fn operators_and_compound_assignments_visit_operands_without_inventing_overloads() {
    let p = program(
        "fun value() -> int32 { return 1 }\nfun other() -> int32 { return 2 }",
        "import lib.{ value, other }\nlet x = value() + other()\nx += other()\nconst equal = x == value()\nconst negated = -other()",
    );
    let items = selected(&p);
    assert!(has(&items, "value", Reason::ExplicitUse));
    assert!(has(&items, "other", Reason::ExplicitUse));
}

#[test]
fn structural_method_presence_is_catalog_based_and_callback_body_is_selected() {
    let p = program(
        METHODS,
        "import lib.{ A, B }\nconst a = A { x: 1 }\nconst b = B { x: 1 }\nfun use(x) { if x: anonymous { hit: () -> int32 } { return x.hit }\nreturn () -> 0 }",
    );
    let index = ItemIndex::new(&p);
    let before = index.len();
    let items = selected(&p);
    assert!(has(&items, "A.hit:", Reason::ImplicitUse));
    assert!(has(&items, "B.hit:", Reason::ImplicitUse));
    assert!(
        !p.member_presence(&p.types["A"].type_ref(), "absent")
            .unwrap_or(false)
    );
    assert_eq!(index.len(), before);
}

#[test]
fn reflective_fields_retains_inhabited_data_without_inventing_methods() {
    for body in [
        "fun inspect(x) { for f in fields(x) { x[f.name]() } }",
        "fun inspect(x) { for key in fields(x) { x[key]() } }",
    ] {
        let p = program(
            &format!("{METHODS}\n{body}"),
            "import lib.{ A, B, inspect }\nconst a = A { x: 1 }\nconst b = B { x: 1 }\ninspect(a)",
        );
        let index = ItemIndex::new(&p);
        let reach = Reachability::new(&index, &scope());
        assert!(
            reach
                .widenings()
                .iter()
                .any(|w| w.cause.starts_with("reflection without instance"))
        );
        let items = selected(&p);
        for name in ["A", "B"] {
            assert!(has(&items, name, Reason::ImplicitUse));
        }
        assert!(!items.iter().any(|(name, _)| name.starts_with("A.miss:")));
    }
}

#[test]
fn keyed_conversion_has_no_infer_shortcut_and_growth_is_monotone() {
    let p = program(
        "type A = { x: int32 }\nfun A.from(x) -> A { return A { x: 1 } }\nfun A.into(self) -> infer! { return infer.from(self.x) }",
        "import lib.{ A }\nfun use(x: A) { return x.into() }",
    );
    let items = selected(&p);
    assert!(has(&items, "A.into:", Reason::ExplicitUse));
    assert!(has(&items, "A.from:", Reason::Generated));
    let index = ItemIndex::new(&p);
    let mut reach = Reachability::new(&index, &scope());
    let target = index
        .items()
        .find(|(_, label)| label.starts_with("A.from:"))
        .unwrap()
        .0
        .clone();
    let before = reach.selection().revision;
    reach.require(target.clone(), Reason::Demand);
    let after = reach.selection().revision;
    assert!(after > before);
    reach.require(target, Reason::Demand);
    assert_eq!(after, reach.selection().revision);
}

#[test]
fn ownership_respects_dependency_routes_and_unimported_package_files() {
    let scope = ProjectScope::new(
        "/project/vendor/dep.cz".into(),
        Some("/project".into()),
        Some("/ignored".into()),
    );
    let own = module("main", "", 0, true);
    let dep = module("lib", "", 1, false);
    assert!(scope.owns(own.source.as_ref().unwrap()));
    assert!(!scope.owns(dep.source.as_ref().unwrap()));
    assert!(scope.owns_unloaded("/project/unused.cz".as_ref(), &["/project/vendor".into()]));
    assert!(!scope.owns_unloaded(
        "/project/vendor/unused.cz".as_ref(),
        &["/project/vendor".into()]
    ));
    assert!(scope.owns_unloaded(
        "/project/vendor/dep.cz".as_ref(),
        &["/project/vendor".into()]
    ));
    let explicit = ProjectScope::new(dep.source.as_ref().unwrap().location.clone(), None, None);
    assert!(explicit.owns(dep.source.as_ref().unwrap()));
}

#[test]
fn diagnostics_keep_body_method_variants_initializers_and_catalog_distinct() {
    let source = "type A = | First | Second\nfun A.body(self) { missing }\nfun body() { also_missing }\nconst init = absent";
    let p = program(source, "");
    let owners = DiagnosticOwners::new(&p);
    for (name, kind) in [
        ("missing", "method"),
        ("also_missing", "function"),
        ("absent", "init"),
    ] {
        let lo = source.find(name).unwrap();
        let owner = owners.body_owner(Span::new(lo, lo + name.len()));
        match (kind, owner) {
            ("method", DiagnosticOwner::Method(ids)) => assert_eq!(ids.len(), 2),
            ("function", DiagnosticOwner::Function(_))
            | ("init", DiagnosticOwner::Initializer(_)) => {}
            other => panic!("{other:?}"),
        }
    }
    assert_eq!(owners.body_owner(Span::new(0, 6)), DiagnosticOwner::Catalog);
    assert!(matches!(
        owners.body_owner(p.functions["body"].signature.span),
        DiagnosticOwner::Function(_)
    ));
    let TypeKind::Sum { variants } = &p.types["A"].kind else {
        unreachable!()
    };
    assert!(
        matches!(owners.body_owner(variants[0].methods["body"].signature.span), DiagnosticOwner::Method(ids) if ids.len() == 2)
    );
}

#[test]
fn recovered_body_syntax_is_owned_but_hidden_declaration_boundaries_are_catalog() {
    for (source, recoverable) in [
        ("fun bad() { let x =\nreturn 1\n}\nfun good() {}", true),
        ("fun bad( {\nfun hidden() {}", false),
        ("fun bad() {\nfun hidden() {}", false),
    ] {
        let (ast, errors) = brass_parser::parse_recovering(source, 0);
        assert!(!errors.is_empty());
        let mut m = module("lib", "", 0, false);
        m.ast = ast;
        Arc::make_mut(m.source.as_mut().unwrap()).len = source.len();
        let (p, _) = brass_hir::lower(&[m]);
        let owners = DiagnosticOwners::new(&p);
        for error in errors {
            let owner = owners.syntax_owner(error.span, source, 0);
            assert_eq!(
                !matches!(owner, DiagnosticOwner::Catalog),
                recoverable,
                "{source}: {owner:?}"
            );
        }
    }
}

#[test]
fn shared_certificate_rejects_open_layouts_signatures_and_unclassified_effects() {
    let cases = [
        (
            "type A = { x }\nfun A.m(self) -> int32 { return 1 }",
            SharedObligation::OpenLayout,
        ),
        (
            "type A = { xs: infer[] }\nfun A.m(self) -> int32 { return 1 }",
            SharedObligation::OpenLayout,
        ),
        (
            "type A = { type slot\nx: Self.slot }\nfun A.m(self) -> int32 { return 1 }",
            SharedObligation::OpenLayout,
        ),
        (
            "type B = { x }\ntype Alias = B\ntype A = { b: Alias }\nfun A.m(self) -> int32 { return 1 }",
            SharedObligation::OpenLayout,
        ),
        (
            "type A = | One { x } | Two\nfun A.m(self) -> int32 { return 1 }",
            SharedObligation::OpenLayout,
        ),
        (
            "type A = { x: int32 }\nfun A.m(self) {}",
            SharedObligation::OpenSignature,
        ),
        (
            "type A = { x: int32 }\nfun A.m(self, value) -> int32 { return 1 }",
            SharedObligation::OpenSignature,
        ),
        (
            "type A = { x: int32 }\nconst global = []\nfun A.m(self) -> int32 { global.push(1)\nreturn 1 }",
            SharedObligation::UnclassifiedEffects,
        ),
        (
            "type A = { x: int32 }\nfun A.m(self) -> int32 { const f = () -> self.x\nreturn f() }",
            SharedObligation::UnclassifiedEffects,
        ),
    ];
    for (source, expected) in cases {
        let p = program(source, "");
        let owner = &p.types["A"];
        let method = match &owner.kind {
            TypeKind::Record { methods, .. } => &methods["m"],
            TypeKind::Sum { variants } => &variants[0].methods["m"],
        };
        assert_eq!(
            shared_obligation(&ItemIndex::new(&p), owner, method),
            Some(expected),
            "{source}"
        );
    }
}

#[test]
fn identity_is_shared_between_context_and_combined_catalogs() {
    let dep = module("lib", METHODS, 0, false);
    let (context, _) = brass_hir::lower(std::slice::from_ref(&dep));
    let (combined, _) = brass_hir::lower(&[dep, module("main", "fun hit() {}", 100_000, true)]);
    let context = ItemIndex::new(&context);
    let combined = ItemIndex::new(&combined);
    for (key, _) in context.items() {
        assert!(combined.items().any(|(other, _)| key == other));
    }
    assert!(
        combined
            .items()
            .any(|(key, _)| matches!(key, ItemKey::Body(BodyId::Method(_))))
    );
}

#[test]
fn structural_argument_return_flow_retains_concrete_method_implementations() {
    let p = program(
        METHODS,
        "import lib.{ A, B }\nfun accept(value: A) { return value.hit() }\nfun give(value: B) -> A { return value }\naccept(give(B { x: 1 }))",
    );
    let items = selected(&p);
    assert!(has(&items, "A.hit:", Reason::ExplicitUse));
    assert!(has(&items, "B.hit:", Reason::ExplicitUse));
}

#[test]
fn explicit_builtin_and_custom_from_have_distinct_body_requirements() {
    let p = program(
        "type A = { x: int32 }\nfun A.from(x: int32) -> A { return A { x: x } }\ntype B = { x: int32 }",
        "import lib.{ A, B }\nconst a = A.from(1)\nconst b = B.from(a)\nconst n = int64.from(1)",
    );
    let items = selected(&p);
    assert!(has(&items, "A.from:", Reason::ExplicitUse));
    assert!(has(&items, "B", Reason::ExplicitUse));
    assert!(!items.iter().any(|(name, _)| name.starts_with("B.from:")));
}

#[test]
fn string_alias_conversion_keeps_the_implicit_rendering_hook() {
    let p = program(
        "type A = { x: int32 }\nfun A.display(self) -> string { return \"A\" }",
        "import lib.{ A }\ntype Text = string\nText.from(A { x: 1 })",
    );
    assert!(has(&selected(&p), "A.display:", Reason::ImplicitUse));
}

#[test]
fn structural_alias_and_abstract_nominal_requirements_keep_method_bodies() {
    for contract in [
        "type Contract = anonymous { hit: () -> int32 }",
        "type Contract = { hit(self) -> int32 }",
    ] {
        let p = program(
            METHODS,
            &format!(
                "import lib.{{ A, B }}\nconst a = A {{ x: 1 }}\nconst b = B {{ x: 1 }}\n{contract}\nfun inspect(x) {{ if x: Contract {{ return 1 }}\nreturn 0 }}"
            ),
        );
        let items = selected(&p);
        assert!(has(&items, "A.hit:", Reason::ImplicitUse), "{items:?}");
        assert!(has(&items, "B.hit:", Reason::ImplicitUse), "{items:?}");
    }
}

#[test]
fn pattern_bindings_cannot_be_mistaken_for_static_type_qualifiers() {
    for body in [
        "for A in [B { x: 1 }] { A.hit() }",
        "if let A = (B { x: 1 }) { A.hit() }",
        "fun use(x: B) { return match x { A => A.hit() } }",
    ] {
        let p = program(
            METHODS,
            &format!("import lib.{{ A, B }}\nconst b = B {{ x: 1 }}\n{body}"),
        );
        let items = selected(&p);
        assert!(has(&items, "B.hit:", Reason::ExplicitUse), "{items:?}");
    }
}

#[test]
fn renamed_colliding_interface_uses_its_resolved_storage_identity() {
    let (p, errors) = brass_hir::lower(&[
        module("lib", "type Parent = { value: int32 }", 0, false),
        module("other", "type Parent = { other: string }", 1000, false),
        module(
            "main",
            "import lib.{ Parent as Contract }\ntype Child: Contract = { value: int32 }",
            100_000,
            true,
        ),
    ]);
    assert!(errors.is_empty(), "{errors:?}");
    let items = selected(&p);
    assert!(has(&items, "Parent@lib", Reason::ExplicitUse), "{items:?}");
    assert!(
        !items.iter().any(|(name, _)| name == "Parent@other"),
        "{items:?}"
    );
}

#[path = "tests/inhabited.rs"]
mod inhabited;

mod effects;

mod optimization;

#[test]
fn entry_error_propagation_retains_the_lowered_abort_renderer() {
    let p = program(
        "fun _render_unhandled(x) -> string { return \"failure\" }\nfun parse() -> int32! { return 1 }",
        "import lib.{ parse, _render_unhandled }\nlet n = parse()!",
    );
    assert!(has(&selected(&p), "_render_unhandled", Reason::ImplicitUse));
}

#[test]
fn nullable_context_retains_its_lowered_error_constructor() {
    let p = program(
        "fun error(x) -> string { return x }\nfun missing() -> int32? { return null }",
        "import lib.{ missing, error }\nlet n = missing().context(\"required\")",
    );
    assert!(has(&selected(&p), "error", Reason::ImplicitUse));
}

#[test]
fn structural_rendering_selects_nested_debug_without_nested_display() {
    let p = program(
        "type Inner = | Value\nfun Inner.debug(self) -> string { return \"debug\" }\nfun Inner.display(self) -> string { return \"display\" }\ntype Outer = { inner: Inner }\ntype Unused = | Value\nfun Unused.debug(self) -> string { return false }",
        "import lib.{ Inner, Outer }\nprintln(Outer { inner: Inner.Value })",
    );
    let items = selected(&p);
    assert!(has(&items, "Inner.debug:", Reason::ImplicitUse));
    assert!(!has(&items, "Inner.display:", Reason::ImplicitUse));
    assert!(
        !items
            .iter()
            .any(|(label, _)| label.starts_with("Unused.debug:"))
    );
}
