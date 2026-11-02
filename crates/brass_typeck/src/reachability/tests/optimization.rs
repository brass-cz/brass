//! Cache and refresh boundaries must preserve the authority's source decisions.

use super::{ItemIndex, Reason, has, program, scope};
use crate::reachability::{Reachability, effects};
use std::rc::Rc;

#[test]
fn lazy_effect_queries_keep_recursive_footprints_in_any_query_order() {
    let p = program(
        "let shared = 0\nfun a() -> int32 { return b() }\nfun b() -> int32 { shared = 1\nif false { return a() }\nreturn shared }\nfun clean() -> int32 { return 1 }\nfun dynamic(f) { return f() }",
        "",
    );
    let forward = ItemIndex::new(&p);
    let reverse = ItemIndex::new(&p);
    // A partial query must close its entire SCC before publishing a result.
    let id = reverse.functions["a"];
    assert!(
        !effects::summary(&reverse, id, false)
            .global_writes
            .is_empty()
    );
    for id in (0..reverse.len()).rev() {
        effects::summary(&reverse, id, true);
        effects::summary(&reverse, id, false);
    }
    let snapshot = |index: &ItemIndex<'_>| {
        index
            .effect_summaries()
            .map(|(id, _, s)| (id.clone(), s.clone()))
            .chain(
                index
                    .rootless_effect_summaries()
                    .map(|(id, _, s)| (id.clone(), s.clone())),
            )
            .collect::<Vec<_>>()
    };
    assert_eq!(snapshot(&forward), snapshot(&reverse));
}

#[test]
fn body_refresh_invalidates_effects_and_cached_callee_bodies() {
    let original = program(
        "let shared = 0\nfun leaf() -> int32 { return 1 }\ntype A = { x: int32 }\nfun A.m(self) -> int32 { return leaf() }",
        "import lib.{ A }\nconst value = A { x: 1 }",
    );
    let mut rewritten = program(
        "let shared = 0\nfun leaf() -> int32 { return 1 }\ntype A = { x: int32 }\nfun A.m(self) -> int32 { return leaf() }",
        "import lib.{ A }\nconst value = A { x: 1 }",
    );
    let replacement = program("fun leaf() -> int32 { shared = 1\nreturn 1 }", "");
    Rc::make_mut(&mut rewritten.functions.get_mut("leaf").unwrap().decl).body =
        replacement.functions["leaf"].decl.body.clone();
    let mut index = ItemIndex::new(&original);
    let clean = effects::summary(&index, index.functions["leaf"], false);
    assert!(clean.is_clean());
    // Warm a cached resolver as well as the effect certificate before rebinding.
    index.names[&["lib".into()][..]].function("leaf");
    let identities: Vec<_> = index.items().map(|(id, _)| id.clone()).collect();
    index.refresh_bodies(&rewritten);
    assert_eq!(
        identities,
        index.items().map(|(id, _)| id.clone()).collect::<Vec<_>>()
    );
    assert!(
        !effects::summary(&index, index.functions["leaf"], false)
            .global_writes
            .is_empty()
    );
    let actual = Reachability::new(&index, &scope());
    let fresh_index = ItemIndex::new(&rewritten);
    let expected = Reachability::new(&fresh_index, &scope());
    assert_eq!(actual.selection(), expected.selection());
    let items: Vec<_> = index
        .items()
        .filter_map(|(id, label)| {
            actual
                .selection()
                .reasons
                .get(id)
                .map(|r| (label.into(), r.clone()))
        })
        .collect();
    assert!(has(&items, "A.m:", Reason::SharedInference));
}

#[test]
fn cloned_views_share_requests_but_not_established_coverage() {
    let p = program(
        "fun leaf() -> int32 { return 1 }",
        "import lib.{ leaf }\nleaf()",
    );
    let index = ItemIndex::new(&p);
    let selection = Reachability::new(&index, &scope()).selection().clone();
    let view = crate::reachability::AnalysisView::new(
        &p,
        selection,
        Default::default(),
        Default::default(),
    );
    let mut fork = view.clone();
    assert!(std::sync::Arc::ptr_eq(&view.selection, &fork.selection));
    let body = view.functions["leaf"].clone();
    fork.coverage_mut().bodies.insert(body.clone());
    assert!(!view.coverage.bodies.contains(&body));
    // Changing a request requires a new immutable snapshot, not mutating a fork's sibling.
    let mut selection = (*fork.selection).clone();
    selection.body_roots.remove(&body);
    fork.set_selection(selection.into());
    assert!(view.selection.body_roots.contains(&body));
}

#[test]
fn generated_batches_resume_the_same_selection_as_a_fresh_closure() {
    // Two successive appends preserve integer catalog IDs, abstract frames and
    // shared obligations. Generated roots may call a recursive helper.
    let mut p = program(
        "fun helper(n: int32) -> int32 { if n == 0 { return 7 }\nreturn helper(n - 1) }\ntype Box = { value: int32 }\nfun Box.convert(self) -> infer! { return helper(self.value) }",
        "import lib.{ Box }\nlet b = Box { value: 1 }\nb.convert()",
    );
    let index = ItemIndex::new(&p);
    let selection = Reachability::new(&index, &scope()).into_selection();
    let mut view = crate::reachability::AnalysisView::new(
        &p,
        selection,
        Default::default(),
        Default::default(),
    );
    drop(index);
    for name in ["generated_one", "generated_two"] {
        let brass_hir::TypeKind::Record { methods, .. } = &p.types["Box"].kind else {
            unreachable!()
        };
        let method = &methods["convert"].decl;
        let decl = brass_parser::ast::FunDecl {
            name: name.into(),
            name_span: method.name_span,
            params: method.params.clone(),
            ret: None,
            body: method.body.clone().unwrap(),
            span: method.span,
            doc: method.doc.clone(),
            recv: None,
        };
        let generated = brass_hir::GeneratedDecl {
            module: vec!["lib".into()],
            receiver: "Box".into(),
            template: "convert".into(),
            decl,
            key: brass_hir::Type::Int(brass_hir::IntKind::I32),
        };
        brass_hir::lower_generated_into(&mut p, std::slice::from_ref(&generated)).unwrap();
        let old = view.selection.clone();
        view = view.with_generated(&p, std::slice::from_ref(&generated));
        let fresh = ItemIndex::new(&p);
        let extra = view
            .selection
            .body_roots
            .difference(&old.body_roots)
            .cloned()
            .map(crate::reachability::ItemKey::Body)
            .collect::<Vec<_>>();
        let expected = Reachability::extend_roots(&fresh, &old, extra, Reason::Generated);
        assert_eq!(view.selection.body_roots, expected.body_roots);
        assert_eq!(view.selection.type_roots, expected.type_roots);
        assert_eq!(view.selection.own_roots, expected.own_roots);
        for (item, reasons) in &expected.reasons {
            let actual = &view.selection.reasons[item];
            assert_eq!(
                actual.len(),
                reasons.len(),
                "{item:?}: actual {actual:?}, expected {reasons:?}"
            );
            assert!(reasons.iter().all(|r| actual.contains(r)));
        }
        assert!(view.coverage.bodies.is_empty());
    }
}

#[test]
fn appending_a_previously_absent_method_invalidates_effect_proofs() {
    // Negative exact-receiver reads matter as much as positive virtual reads:
    // a new method can turn an unresolved effect into a definite global write.
    let mut p = program(
        "let shared = 0\ntype Box = { value: int32 }\nfun Box.template(self) -> infer! { shared = 1\nreturn 7 }\nfun caller() -> int32 { return Box.future() }",
        "",
    );
    let index = ItemIndex::new(&p);
    let old = effects::summary(&index, index.functions["caller"], false);
    assert!(!old.unknown_calls.is_empty());
    let snapshot = index.snapshot();
    drop(index);
    let brass_hir::TypeKind::Record { methods, .. } = &p.types["Box"].kind else {
        unreachable!()
    };
    let method = &methods["template"].decl;
    let generated = brass_hir::GeneratedDecl {
        module: vec!["lib".into()],
        receiver: "Box".into(),
        template: "template".into(),
        decl: brass_parser::ast::FunDecl {
            name: "future".into(),
            name_span: method.name_span,
            params: method.params.clone(),
            ret: None,
            body: method.body.clone().unwrap(),
            span: method.span,
            doc: method.doc.clone(),
            recv: None,
        },
        key: brass_hir::Type::Int(brass_hir::IntKind::I32),
    };
    let generated = [generated];
    assert!(snapshot.changes_reads(&generated));
    brass_hir::lower_generated_into(&mut p, &generated).unwrap();
    let mut rebound = snapshot.bind(&p, true);
    rebound.append_generated(&generated);
    let fresh = ItemIndex::new(&p);
    let actual = effects::summary(&rebound, rebound.functions["caller"], false);
    assert!(!actual.global_writes.is_empty());
    assert_eq!(
        actual,
        effects::summary(&fresh, fresh.functions["caller"], false)
    );
}
