//! Partial context facts must not suppress unprepared work in a consuming analysis.

use super::{AnalysisView, BodyId, CheckSelection, ItemIndex, ItemKey};
use brass_hir::{LoadedModule, Reason};

fn program(source: &str) -> brass_hir::Program {
    let (program, errors) = brass_hir::lower(&[LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["library".into()],
        ast: brass_parser::parse(source).unwrap(),
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    program
}

fn request(program: &brass_hir::Program, labels: &[&str]) -> AnalysisView {
    let index = ItemIndex::new(program);
    let mut selection = CheckSelection::default();
    for (key, _) in index.items().filter(|(_, label)| labels.contains(label)) {
        match key {
            ItemKey::Body(id) => {
                selection.body_roots.insert(id.clone());
            }
            ItemKey::Type(id) => {
                selection.type_roots.insert(id.clone());
            }
        }
        selection
            .reasons
            .insert(key.clone(), vec![Reason::ExplicitUse]);
    }
    AnalysisView::new(program, selection, Default::default(), Default::default())
}

#[test]
fn missing_return_dependency_grows_before_context_publication() {
    // Deliberately under-request the chain to exercise actual light-read closure.
    // The settled result must include the helper, not a provisional Unknown.
    let p = program(
        "fun selected() { return helper() }\nfun helper() -> int32 { return 7 }\nfun unused() { return false }",
    );
    let selected = crate::prepare_context(&p, &request(&p, &["selected"]));
    assert!(selected.errors.is_empty(), "{:?}", selected.errors);
    assert_eq!(
        selected.function_returns["selected"],
        brass_hir::Type::Int(brass_hir::IntKind::I32)
    );
    assert!(selected.function_returns.contains_key("helper"));
    assert!(!selected.function_returns.contains_key("unused"));
    let seed = selected.context_tables;
    let coverage = &seed.items.as_ref().unwrap().coverage;
    assert_eq!(coverage.returns.len(), 2);
    assert!(coverage.bodies.is_empty());
    assert!(!seed.covers_module(&["library".into()]));
    let completed = crate::analyze_with(&p, Some(&seed));
    let full = crate::analyze(&p);
    assert_eq!(completed.errors, full.errors);
    assert_eq!(completed.function_returns, full.function_returns);
    assert_eq!(completed.instance_returns, full.instance_returns);
}

#[test]
fn selected_sum_method_does_not_cover_its_unprepared_sibling() {
    let p = program(
        "type Choice = | A | B\nfun Choice.get(self) { return 7 }\nfun Choice.other(self) { return false }\nfun use() { return Choice.A.get() }",
    );
    let selected = crate::prepare_context(
        &p,
        &request(&p, &["Choice", "Choice.get:Some(0)", "Choice.get:Some(1)"]),
    );
    assert!(selected.errors.is_empty(), "{:?}", selected.errors);
    let seed = selected.context_tables;
    let view = seed.items.as_ref().unwrap();
    assert_eq!(view.coverage.co_checks.len(), 2);
    assert!(view.shared.schemes.is_empty());
    assert!(
        view.coverage
            .co_checks
            .iter()
            .all(|id| matches!(id, BodyId::Method(_)))
    );
    assert!(
        !seed
            .method_returns
            .contains_key(&("Choice.A".into(), "other".into()))
    );
    let completed = crate::analyze_with(&p, Some(&seed));
    let full = crate::analyze(&p);
    assert_eq!(completed.errors, full.errors);
    assert_eq!(completed.method_returns, full.method_returns);
    assert_eq!(completed.function_returns, full.function_returns);
}

#[test]
fn partial_shared_scheme_and_global_coverage_survives_remapping() {
    let p = program(
        "let value = 1\ntype Box = { value: int32 }\nfun Box.get(self) -> int32 { return self.value }\nfun get() { return value }",
    );
    let prepared = crate::prepare_context(&p, &request(&p, &["Box", "Box.get:None", "get"]));
    assert!(prepared.errors.is_empty(), "{:?}", prepared.errors);
    let seed = prepared.context_tables;
    let (mut remapped, _) = seed.remapped(10000);
    assert_eq!(seed.items, remapped.items);
    assert_eq!(remapped.items.as_ref().unwrap().shared.schemes.len(), 1);
    let empty = Default::default();
    assert!(remapped.retain_modules(&p, &empty));
    let items = remapped.items.as_ref().unwrap();
    assert!(items.coverage.returns.is_empty());
    assert!(items.coverage.co_checks.is_empty());
    assert!(items.shared.schemes.is_empty());
    assert!(items.shared.initializers.is_empty());
    assert!(!remapped.covers_module(&["library".into()]));
}

#[test]
fn shared_return_links_and_uncovered_record_are_prepared_before_calls() {
    // One generic record comes from the seed; another must be prepared by the
    // entry. Both calls must retain their field/parameter return relationships.
    let source = "type Box = { value }\nfun Box.get_or(self, fallback) { if false { return fallback }\nreturn self.value }\ntype Other = { value }\nfun Other.get(self) { return self.value }\nfun reached() { let b = Box { value: 1 }\nlet o = Other { value: 2 }\nreturn b.get_or(o.get()) }";
    let p = program(source);
    let prepared = crate::prepare_context(&p, &request(&p, &["Box", "Box.get_or:None"]));
    assert!(prepared.errors.is_empty(), "{:?}", prepared.errors);
    let seed = prepared.context_tables;
    assert!(seed.schemes.contains_key("Box"));
    assert!(!seed.schemes.contains_key("Other"));
    let (combined, errors) = brass_hir::lower(&[
        LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["library".into()],
            ast: brass_parser::parse(source).unwrap(),
        },
        LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["main".into()],
            ast: brass_parser::parse("import library.{ reached }\nlet answer = reached()").unwrap(),
        },
    ]);
    assert!(errors.is_empty(), "{errors:?}");
    let completed = crate::analyze_with(&combined, Some(&seed));
    let full = crate::analyze(&combined);
    assert_eq!(completed.errors, full.errors);
    assert!(completed.errors.is_empty(), "{:?}", completed.errors);
    let module = vec!["main".to_string()];
    assert_eq!(
        completed.context_tables.global_defs[&module]["answer"],
        full.context_tables.global_defs[&module]["answer"]
    );
    assert_eq!(
        completed.context_tables.global_defs[&module]["answer"],
        brass_hir::Type::Int(brass_hir::IntKind::I32)
    );
}

#[test]
fn global_initializer_and_uncovered_writer_keep_reached_results() {
    // Initializers are always prepared, but they do not certify the unrelated
    // function bodies which later constrain the global's open element type.
    let p = program(
        "let values = []\nfun writer() { values.push(1) }\nfun reached() { writer()\nreturn values[0] }",
    );
    let prepared = crate::prepare_context(&p, &request(&p, &[]));
    let completed = crate::analyze_with(&p, Some(&prepared.context_tables));
    let full = crate::analyze(&p);
    assert_eq!(completed.errors, full.errors);
    assert_eq!(
        completed.function_returns["reached"],
        full.function_returns["reached"]
    );
}

#[test]
fn item_seed_rejects_shifted_nominal_identity() {
    // Source body IDs alone do not authorize table values with different nominal IDs.
    let old = program("type Box = { value: int32 }\nfun make() { return Box { value: 1 } }");
    let prepared = crate::prepare_context(&old, &request(&old, &["Box", "make"]));
    let (current, errors) = brass_hir::lower(&[
        LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["earlier".into()],
            ast: brass_parser::parse("type Earlier = { other: bool }").unwrap(),
        },
        LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["library".into()],
            ast: brass_parser::parse(
                "type Box = { value: int32 }\nfun make() { return Box { value: 1 } }",
            )
            .unwrap(),
        },
    ]);
    assert!(errors.is_empty());
    assert!(!prepared.context_tables.item_identity_matches(&current));
    let completed = crate::analyze_with(&current, Some(&prepared.context_tables));
    let full = crate::analyze(&current);
    assert_eq!(completed.errors, full.errors);
    assert_eq!(completed.function_returns, full.function_returns);
}

#[test]
fn newly_activated_return_chains_keep_the_existing_round_budget() {
    // Activation is not a propagation round. Starting a new leaf one round late
    // would falsely exhaust the N+1 budget even for a two-function acyclic chain.
    for length in 2..8 {
        let mut source = (0..length - 1)
            .map(|i| format!("fun a{i}() {{ return a{}() }}\n", i + 1))
            .collect::<String>();
        source.push_str(&format!("fun a{}() {{ return 7 }}", length - 1));
        let p = program(&source);
        let prepared = crate::prepare_context(&p, &request(&p, &["a0"]));
        assert!(
            prepared.errors.is_empty(),
            "length {length}: {:?}",
            prepared.errors
        );
        assert_eq!(
            prepared.function_returns["a0"],
            brass_hir::Type::Int(brass_hir::IntKind::I32)
        );
        assert_eq!(
            prepared
                .context_tables
                .items
                .as_ref()
                .unwrap()
                .coverage
                .returns
                .len(),
            length
        );
    }
}

#[test]
fn selected_body_visitors_preserve_catalog_and_reached_diagnostics() {
    // Each omitted body is independently invalid in a body pass. Its declaration
    // remains visible, and explicitly selecting it must restore the diagnostic.
    let bodies = [
        "fun unused() -> int32 { let x = 1 }",
        "fun unused() { break }",
        "fun unused() { let x: int32\nreturn x }",
        "fun unused() { const x = 1\nx = 2 }",
        "fun unused() { let x: Missing = 1 }",
        "fun unused() { return Missing { x: 1 } }",
        "fun unused() -> int32 { return false }",
        "fun unused() { return missing() }",
    ];
    for body in bodies {
        let p = program(&format!("fun reached() -> int32 {{ return 1 }}\n{body}"));
        let view = request(&p, &["reached"]);
        let selected = crate::analyze_selected(&p, None, &view);
        assert!(selected.errors.is_empty(), "{body}: {:?}", selected.errors);
        assert!(!selected.function_returns.contains_key("unused"), "{body}");
        let all = crate::analyze_selected(&p, None, &request(&p, &["reached", "unused"]));
        assert!(!all.errors.is_empty(), "missing reached diagnostic: {body}");
    }
    // Signature validity belongs to the catalog even when the body is omitted.
    let p = program("fun reached() {}\nfun unused(x: int32, x: int32) {}");
    let selected = crate::analyze_selected(&p, None, &request(&p, &["reached"]));
    assert!(!selected.errors.is_empty());
}

#[test]
fn selected_entry_does_not_prepare_unselected_context_siblings() {
    // A genuine partial seed cannot grant module coverage, but its consumer must
    // also not turn every uncovered sibling into new preparation work.
    let p = program(
        "fun reached() -> int32 { return helper() }\nfun helper() -> int32 { return 1 }\nfun unused() { return missing() }",
    );
    let view = request(&p, &["reached", "helper"]);
    let seed = crate::prepare_context(&p, &view).context_tables;
    let entry = crate::analyze_selected(&p, Some(&seed), &view);
    assert!(entry.errors.is_empty(), "{:?}", entry.errors);
    assert!(!entry.function_returns.contains_key("unused"));
    assert!(entry.function_returns.contains_key("helper"));
}

#[test]
fn appended_method_cannot_inherit_its_templates_source_coverage() {
    // Keyed specializations intentionally share source spans with the template.
    // A seed certifies the original storage key, never a newly appended alias.
    let mut p =
        program("type Box = { value: int32 }\nfun Box.get(self) -> int32 { return self.value }");
    let seed = crate::prepare_context(&p, &request(&p, &["Box", "Box.get:None"])).context_tables;
    let brass_hir::TypeKind::Record { methods, .. } = &mut p.types.get_mut("Box").unwrap().kind
    else {
        unreachable!()
    };
    let mut appended = methods["get"].clone();
    appended.signature.name = "generated".into();
    std::rc::Rc::make_mut(&mut appended.decl).name = "generated".into();
    methods.insert("generated".into(), appended);
    let index = ItemIndex::new(&p);
    let original = index
        .items()
        .find(|(_, label)| *label == "Box.get:None")
        .unwrap()
        .0;
    let generated = index
        .items()
        .find(|(_, label)| *label == "Box.generated:None")
        .unwrap()
        .0;
    assert_ne!(original, generated);
    let projected = AnalysisView::with_selection(
        &p,
        seed.items.as_ref().unwrap().selection.clone(),
        (*seed.items.as_ref().unwrap().coverage).clone(),
        Default::default(),
    );
    assert!(
        !projected
            .coverage
            .co_checks
            .contains(&projected.methods[&("Box".into(), "generated".into())])
    );

    let continued = crate::analyze_generated(&p, &seed, &[]);
    assert!(continued.errors.is_empty(), "{:?}", continued.errors);
    assert!(
        !continued
            .method_returns
            .contains_key(&("Box".into(), "generated".into()))
    );
}

#[test]
fn body_membership_tracks_request_replacement_without_changing_sibling() {
    let p = program(
        "fun selected() {}\nfun later() {}\ntype Choice = | A | B\nfun Choice.value(self) -> int32 { return 1 }",
    );
    let view = request(&p, &["selected", "Choice.value:Some(0)"]);
    let mut fork = view.clone();
    let span = p.functions["later"].decl.span;
    assert!(!view.selects_body(span));
    let mut selection = (*fork.selection).clone();
    selection.body_roots.insert(fork.functions["later"].clone());
    fork.set_selection(selection.into());
    assert!(fork.selects_body(span));
    assert!(!view.selects_body(span));
    let brass_hir::TypeKind::Sum { variants } = &p.types["Choice"].kind else {
        panic!("sum")
    };
    let method_span = variants[0].methods["value"].decl.span;
    assert!(view.selects_body(method_span));
    fork.set_selection(Default::default());
    assert!(!fork.selects_body(span));
    assert!(!fork.selects_body(method_span));
    assert!(view.selects_body(method_span));
}

#[derive(Default)]
struct StreamSelection {
    requests: Vec<crate::stream::BodyRequest>,
    events: Vec<crate::stream::CheckEvent>,
}

impl crate::stream::Scheduler for StreamSelection {
    fn drain_requests(&mut self) -> Vec<crate::stream::BodyRequest> {
        std::mem::take(&mut self.requests)
    }

    fn emit(&mut self, event: crate::stream::CheckEvent) {
        self.events.push(event);
    }
}

#[test]
fn streaming_omission_is_not_checked_coverage() {
    // A visible invalid sibling supplies neither body diagnostics nor a false
    // BodyChecked event. Light return dependencies close before publication.
    let p = program(
        "fun selected() { return helper() }\nfun helper() -> int32 { return 7 }\nfun omitted() -> int32 { return false }",
    );
    let mut stream = StreamSelection::default();
    let analysis =
        crate::analyze_streaming_selected(&p, None, &mut stream, &request(&p, &["selected"]));
    assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
    let names: Vec<_> = stream
        .events
        .iter()
        .filter_map(|event| match event {
            crate::stream::CheckEvent::BodyChecked(crate::stream::BodyId::Function(name), _) => {
                Some(name.as_str())
            }
            _ => None,
        })
        .collect();
    assert_eq!(names, ["helper", "selected"]);
    let coverage = &analysis.context_tables.items.as_ref().unwrap().coverage;
    assert_eq!(coverage.bodies.len(), 2);
    assert!(matches!(
        stream.events.last(),
        Some(crate::stream::CheckEvent::Finished(..))
    ));
    let eligible = stream
        .events
        .iter()
        .position(|e| matches!(e, crate::stream::CheckEvent::SelectedBodies(_)))
        .unwrap();
    let gate = stream
        .events
        .iter()
        .position(|e| matches!(e, crate::stream::CheckEvent::ContextReady(_)))
        .unwrap();
    assert!(eligible < gate);
}

#[test]
fn runtime_selection_growth_precedes_its_single_batch_seal() {
    // A late free-function demand grows only body work: its scalar frame has
    // no new shared owner. Selection itself never manufactures settlement.
    let p = program(
        "fun selected() -> int32 { return 1 }\nfun later() -> int32 { return 7 }\nfun omitted() -> int32 { return false }",
    );
    let mut stream = StreamSelection {
        requests: vec![crate::stream::BodyRequest {
            symbol: "later".into(),
            type_args: vec![],
            batch: 41,
        }],
        ..Default::default()
    };
    let analysis =
        crate::analyze_streaming_selected(&p, None, &mut stream, &request(&p, &["selected"]));
    assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
    let mut eligibility = None;
    let mut sealed = 0;
    for event in &stream.events {
        match event {
            crate::stream::CheckEvent::SelectedBodies(spans) => eligibility = Some(spans),
            crate::stream::CheckEvent::BodyChecked(
                crate::stream::BodyId::Function(name),
                delta,
            ) => {
                assert_ne!(name, "omitted");
                assert!(eligibility.unwrap().contains(&p.functions[name].decl.span));
                if name == "later" {
                    assert_eq!(delta.settles_batch, Some(41));
                    sealed += 1;
                }
            }
            crate::stream::CheckEvent::BatchSettled(delta) => {
                sealed += usize::from(delta.settles_batch == Some(41))
            }
            _ => {}
        }
    }
    assert_eq!(sealed, 1);
    let view = analysis.context_tables.items.as_ref().unwrap();
    assert_eq!(view.coverage.bodies.len(), 2);
    assert!(
        view.selection
            .reasons
            .values()
            .any(|reasons| reasons.contains(&Reason::Demand))
    );
}
