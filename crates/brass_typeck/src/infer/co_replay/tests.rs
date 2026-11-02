//! Checks for the co-effect inventory and the differential harness itself.

use super::snapshot::{EffectHistory, EffectSnapshot};
use crate::infer::Checker;
use brass_hir::{Constness, IntKind, Program, Type, TypedExprKind};
use brass_parser::Span;
use std::rc::Rc;

mod leaves;
mod method_replay;
mod methods;
mod replay;

/// Lower small fixtures without a standard-library dependency.
fn program(source: &str) -> Program {
    let ast = brass_parser::parse(source).unwrap();
    let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    program
}

/// Prepare the same return environment for both authoritative test forks.
fn checker(program: &Program) -> Checker<'_> {
    let mut checker = Checker::new(program, Rc::new(brass_typesys::RowInfo::analyze(program)));
    checker.precompute_returns();
    checker
}

/// Exercise a real call-site walk, including its nested ordinary journal.
fn call(checker: &mut Checker<'_>, name: &str, args: &[Type]) -> Type {
    let function = &checker.program.functions[name];
    checker.instantiate_function_call(
        name,
        &function.module,
        &function.signature.params,
        &function.decl.body,
        function.signature.ret_ty.clone(),
        Type::Unknown(0),
        args,
        function.decl.body.span,
    )
}

/// Both helpers preserve root ownership, link duplicates and global-set identity.
#[test]
fn inventory_preserves_link_order_and_rootless_behavior() {
    let p = program("fun identity(x) { return x }");
    let mut c = checker(&p);
    c.co_checking = true;
    c.record_co_return_link(Type::Bool, Type::Str);
    assert!(c.co_return_links.is_empty());
    let root = ("Container".into(), "get".into());
    c.current_co_method = Some(root.clone());
    for _ in 0..2 {
        c.record_co_return_link(Type::Bool, Type::Str);
    }
    c.record_co_return_link(Type::Str, Type::Bool);
    assert_eq!(
        c.co_return_links[&root],
        vec![
            (Type::Bool, Type::Str),
            (Type::Bool, Type::Str),
            (Type::Str, Type::Bool)
        ]
    );
    c.record_co_global_read("global");
    c.record_co_global_read("global");
    assert_eq!(c.co_global_reads.len(), 1);
    assert!(c.co_global_reads.contains("global"));
}

/// Any new reference outside the authority requires an inventory review, even
/// when it only reads a table. This catches writes added on unrelated paths.
#[test]
fn inventory_has_no_unreviewed_accesses() {
    /// Collect all non-comment references outside the co-effect authority.
    fn scan(dir: &std::path::Path, found: &mut Vec<(String, usize, usize)>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                if path.file_name().unwrap() != "co_replay" {
                    scan(&path, found);
                }
            } else if path.extension().is_some_and(|ext| ext == "rs")
                && path.file_name().unwrap() != "co_replay.rs"
            {
                let text = std::fs::read_to_string(&path).unwrap();
                let links = text
                    .lines()
                    .filter(|line| !line.trim_start().starts_with("//"))
                    .map(|line| line.matches("co_return_links").count())
                    .sum();
                let globals = text
                    .lines()
                    .filter(|line| !line.trim_start().starts_with("//"))
                    .map(|line| line.matches("co_global_reads").count())
                    .sum();
                if links != 0 || globals != 0 {
                    found.push((
                        path.file_name().unwrap().to_str().unwrap().into(),
                        links,
                        globals,
                    ));
                }
            }
        }
    }
    let mut found = Vec::new();
    scan(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/infer"),
        &mut found,
    );
    found.sort();
    assert_eq!(
        found,
        vec![("mod.rs".into(), 2, 2), ("precompute.rs".into(), 1, 1)]
    );
}

/// Independent walks and ordinary memo replay agree on leaves at concrete
/// inputs, including their complete semantic effects and publication history.
#[test]
fn equivalent_walks_and_ordinary_replay() {
    for source in ["fun leaf(x) { return x }", "fun leaf(x) { return [x, x] }"] {
        let p = program(source);
        let seed = checker(&p);
        let mut walked = EffectSnapshot::fork(&seed);
        let mut repeated = EffectSnapshot::fork(&seed);
        let args = [Type::Int(IntKind::I32)];
        let a = call(&mut walked, "leaf", &args);
        let b = call(&mut repeated, "leaf", &args);
        let mut ah = EffectHistory::new(&seed);
        let mut bh = EffectHistory::new(&seed);
        ah.boundary(&walked);
        bh.boundary(&repeated);
        EffectSnapshot::capture(&walked, &args, &a, &ah)
            .compare(&EffectSnapshot::capture(&repeated, &args, &b, &bh))
            .unwrap();
        // Warm the memo in both forks; remove only the walk fork's memo.
        let mut replayed = EffectSnapshot::fork(&walked);
        let mut walked = EffectSnapshot::fork(&walked);
        walked.elaboration_memo.clear();
        let a = call(&mut walked, "leaf", &args);
        let b = call(&mut replayed, "leaf", &args);
        assert_eq!(replayed.stats.memo_hits, 1);
        let mut ah = EffectHistory::new(&seed);
        let mut bh = EffectHistory::new(&seed);
        ah.boundary(&walked);
        bh.boundary(&replayed);
        EffectSnapshot::capture(&walked, &args, &a, &ah)
            .compare(&EffectSnapshot::capture(&replayed, &args, &b, &bh))
            .unwrap();
    }
}

/// Open co-check calls walk every time, without memo lookups or return
/// publication; recursion fallbacks do not count as body walks.
#[test]
fn co_walk_counter_counts_only_walks() {
    let p = program("fun leaf(x) { return x }");
    let mut c = checker(&p);
    c.co_checking = true;
    let open = c.fresh_unknown();
    for _ in 0..2 {
        call(&mut c, "leaf", std::slice::from_ref(&open));
    }
    assert_eq!(c.stats.co_walks, 2);
    assert_eq!((c.stats.memo_hits, c.stats.memo_misses), (0, 0));
    assert!(c.instance_returns.is_empty());
    c.instantiating.insert("fn:leaf".into());
    call(&mut c, "leaf", &[Type::Str]);
    assert_eq!(c.stats.co_walks, 2);
}

/// A missing effect names its first differing category, including transient
/// channel removal rather than merely comparing equal final map contents.
#[test]
fn snapshot_detects_alias_kind_links_and_stream_removals() {
    let p = program("fun leaf(x) { return x }");
    let seed = checker(&p);
    let mut a = EffectSnapshot::fork(&seed);
    let mut b = EffectSnapshot::fork(&seed);
    let x = a.fresh_unknown();
    let y = a.fresh_unknown();
    let bx = b.fresh_unknown();
    let by = b.fresh_unknown();
    a.solver.unify(&x, &y).unwrap();
    let empty = EffectHistory::new(&seed);
    let diff = EffectSnapshot::capture(&a, &[x.clone(), y.clone()], &Type::Void, &empty)
        .compare(&EffectSnapshot::capture(
            &b,
            &[bx.clone(), by.clone()],
            &Type::Void,
            &empty,
        ))
        .unwrap_err();
    assert!(diff.starts_with("resolved inputs"), "{diff}");
    b.solver.unify(&bx, &by).unwrap();
    if let Type::Unknown(id) = by {
        b.solver
            .record_var(id, crate::solver::InferenceVarKind::EmptyArrayElem);
    }
    assert!(
        EffectSnapshot::capture(&a, &[x.clone(), y.clone()], &Type::Void, &empty)
            .compare(&EffectSnapshot::capture(
                &b,
                &[bx.clone(), by.clone()],
                &Type::Void,
                &empty
            ))
            .unwrap_err()
            .starts_with("solver bindings")
    );
    let mut a = EffectSnapshot::fork(&seed);
    let mut b = EffectSnapshot::fork(&seed);
    a.current_co_method = Some(("Box".into(), "get".into()));
    a.record_co_return_link(Type::Bool, Type::Str);
    assert!(
        EffectSnapshot::capture(&a, &[], &Type::Void, &empty)
            .compare(&EffectSnapshot::capture(&b, &[], &Type::Void, &empty))
            .unwrap_err()
            .starts_with("co return links")
    );
    b.current_co_method = a.current_co_method.clone();
    b.record_co_return_link(Type::Bool, Type::Str);
    let span = Span::new(4, 5);
    let first = Type::Array(Box::new(Type::Str), 1);
    let second = Type::Array(Box::new(Type::Bool), 1);
    let mut ah = EffectHistory::new(&seed);
    let mut bh = EffectHistory::new(&seed);
    for c in [&mut a, &mut b] {
        c.record_typed(
            TypedExprKind::Array { empty: false },
            span,
            first.clone(),
            Constness::Unknown,
        );
    }
    ah.boundary(&a);
    for c in [&mut a, &mut b] {
        c.record_typed(
            TypedExprKind::Array { empty: false },
            span,
            second.clone(),
            Constness::Unknown,
        );
    }
    ah.boundary(&a);
    bh.boundary(&b);
    bh.boundary(&b);
    let diff = EffectSnapshot::capture(&a, &[], &Type::Void, &ah)
        .compare(&EffectSnapshot::capture(&b, &[], &Type::Void, &bh))
        .unwrap_err();
    assert!(diff.starts_with("stream boundary"), "{diff}");
}

/// Variable allocation order is immaterial, while aliases and kinds remain
/// observable. An unused fresh scratch hole is not a retained checker effect.
#[test]
fn snapshot_canonicalizes_fresh_identity_without_erasing_aliases() {
    let p = program("fun leaf(x) { return x }");
    let seed = checker(&p);
    let mut a = EffectSnapshot::fork(&seed);
    let mut b = EffectSnapshot::fork(&seed);
    let x = a.fresh_unknown();
    let y = a.fresh_empty_array_elem();
    b.fresh_unknown();
    let by = b.fresh_empty_array_elem();
    let bx = b.fresh_unknown();
    let left = Type::Tuple(vec![x.clone(), y, x]);
    let right = Type::Tuple(vec![bx.clone(), by, bx]);
    let history = EffectHistory::new(&seed);
    EffectSnapshot::capture(&a, std::slice::from_ref(&left), &left, &history)
        .compare(&EffectSnapshot::capture(
            &b,
            std::slice::from_ref(&right),
            &right,
            &history,
        ))
        .unwrap();
}

/// Real return reconciliation under a co-method records effects through the
/// authority, and equivalent walks preserve them on independent consumers.
#[test]
fn co_walks_retain_enclosing_return_links() {
    let p = program("fun choose(x, y, flag: bool) { if flag { return x }\nreturn y }");
    let mut seed = checker(&p);
    seed.co_checking = true;
    seed.current_co_method = Some(("Container".into(), "get".into()));
    let args = [seed.fresh_unknown(), seed.fresh_unknown(), Type::Bool];
    let mut a = EffectSnapshot::fork(&seed);
    let mut b = EffectSnapshot::fork(&seed);
    let ar = call(&mut a, "choose", &args);
    let br = call(&mut b, "choose", &args);
    assert!(!a.co_return_links.is_empty());
    let mut ah = EffectHistory::new(&seed);
    let mut bh = EffectHistory::new(&seed);
    ah.boundary(&a);
    bh.boundary(&b);
    EffectSnapshot::capture(&a, &args, &ar, &ah)
        .compare(&EffectSnapshot::capture(&b, &args, &br, &bh))
        .unwrap();
}

/// An otherwise equal return cannot hide a lost diagnostic, dependency,
/// deferred shape, scheme or reflective target.
#[test]
fn snapshot_detects_each_independent_effect_family() {
    let p = program("fun leaf(x) { return x }");
    let seed = checker(&p);
    let history = EffectHistory::new(&seed);
    let before = EffectSnapshot::capture(&seed, &[], &Type::Void, &history);
    /// One isolated semantic mutation and the category that must expose it.
    type Mutation = (&'static str, fn(&mut Checker<'_>));
    let mutations: [Mutation; 6] = [
        ("co global reads", |c| c.record_co_global_read("global")),
        ("errors", |c| {
            c.errors.push(crate::TypeError {
                message: "error".into(),
                span: Span::new(1, 2),
            })
        }),
        ("warnings", |c| {
            c.warnings.push(crate::TypeError {
                message: "warning".into(),
                span: Span::new(1, 2),
            })
        }),
        ("deferred shapes", |c| {
            c.shape_constraints.insert(
                0,
                vec![crate::constraint::ShapeConstraint::Equals(Type::Bool)],
            );
        }),
        ("schemes", |c| {
            c.schemes.insert(
                "Container".into(),
                brass_hir::TypeScheme {
                    fields: vec![("value".into(), Type::Str)],
                    ..Default::default()
                },
            );
        }),
        ("keyed observations", |c| {
            c.record_keyed_call(
                Span::new(1, 2),
                "Container".into(),
                "decode".into(),
                Type::Str,
            )
        }),
    ];
    for (field, mutate) in mutations {
        let mut changed = EffectSnapshot::fork(&seed);
        mutate(&mut changed);
        let diff = before
            .compare(&EffectSnapshot::capture(
                &changed,
                &[],
                &Type::Void,
                &history,
            ))
            .unwrap_err();
        assert!(diff.starts_with(field), "{field}: {diff}");
    }
}

/// Equal kinds and resolutions must not erase the identity of distinct caller
/// variables that existed before the operation under comparison.
#[test]
fn snapshot_preserves_preexisting_variable_identity() {
    let p = program("fun leaf(x) { return x }");
    let mut seed = checker(&p);
    let first = seed.fresh_unknown();
    let second = seed.fresh_unknown();
    let history = EffectHistory::new(&seed);
    let a = EffectSnapshot::capture(&seed, &[first], &Type::Void, &history);
    let b = EffectSnapshot::capture(&seed, &[second], &Type::Void, &history);
    assert!(a.compare(&b).unwrap_err().starts_with("inputs"));
}

/// The reserved infer placeholder is a language marker, not a renameable fresh
/// solver variable, even though both use the Unknown type constructor.
#[test]
fn snapshot_keeps_infer_placeholder_distinct() {
    let p = program("fun leaf(x) { return x }");
    let mut seed = checker(&p);
    let history = EffectHistory::new(&seed);
    let fresh = seed.fresh_unknown();
    let a = EffectSnapshot::capture(&seed, &[fresh], &Type::Void, &history);
    let b = EffectSnapshot::capture(
        &seed,
        &[Type::Unknown(brass_hir::INFER_VAR)],
        &Type::Void,
        &history,
    );
    assert!(a.compare(&b).unwrap_err().starts_with("inputs"));
}
