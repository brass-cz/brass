//! Method observation must preserve every effect, with full receiver identities.

use super::{call, checker};

/// Receiver fixtures use the core namespace that owns primitive methods.
fn program(source: &str) -> brass_hir::Program {
    let (p, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["core".into()],
        ast: brass_parser::parse(source).unwrap(),
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    p
}
use crate::infer::co_replay::MethodInventory;
use crate::infer::co_replay::snapshot::{EffectHistory, EffectSnapshot};
use brass_hir::{IntKind, Type, TypeScheme};
use brass_parser::Span;

/// Compare instrumented and uninstrumented method walks, retaining each boundary
/// and checking counters as well as semantic snapshots. Both remain real walks.
fn compare(source: &str, args: &[Vec<Type>], rooted: bool) -> Vec<String> {
    let p = program(source);
    let mut seed = checker(&p);
    seed.co_checking = true;
    if rooted {
        seed.current_co_method = Some(("Root".into(), "method".into()));
    }
    // Warm shared immutable eligibility caches before independent histories.
    for inputs in args {
        call(&mut seed, "entry", inputs);
    }
    seed.elaboration_memo.clear();
    let mut plain = EffectSnapshot::fork(&seed);
    let mut observed = EffectSnapshot::fork(&seed);
    plain.method_inventory = None;
    observed.method_inventory = Some(Box::new(MethodInventory::default()));
    let mut ah = EffectHistory::new(&seed);
    let mut bh = EffectHistory::new(&seed);
    for args in args {
        let a = call(&mut plain, "entry", args);
        let b = call(&mut observed, "entry", args);
        assert!(plain.errors.is_empty(), "{:?}", plain.errors);
        assert_eq!(plain.numeric_call_map(), observed.numeric_call_map());
        ah.boundary(&plain);
        bh.boundary(&observed);
        EffectSnapshot::capture(&plain, args, &plain.resolve(&a), &ah)
            .compare(&EffectSnapshot::capture(
                &observed,
                args,
                &observed.resolve(&b),
                &bh,
            ))
            .unwrap();
        assert_eq!(
            format!("{:?}", plain.stats),
            format!("{:?}", observed.stats)
        );
        assert_eq!(plain.elaborations, observed.elaborations);
        assert_eq!(plain.depth_capped, observed.depth_capped);
        assert_eq!(
            plain.elaboration_memo.len(),
            observed.elaboration_memo.len()
        );
    }
    let records = &observed.method_inventory.as_ref().unwrap().completed;
    assert!(!records.is_empty());
    assert!(observed.instance_returns.is_empty());
    records.iter().map(|(name, _, _)| name.clone()).collect()
}

/// Static construction and instance methods preserve distinct receiver payloads,
/// nested return links, rooted/rootless ownership and repeated memo children.
#[test]
fn receiver_instantiations_and_nested_static_instance_walks() {
    let source = "type Box = { value }\nfun Box.make(x) { return Box { value: x } }\nfun Box.get(self) { return self.value }\nfun Box.nested(self) { return self.get() }\nfun entry(x) { let b = Box.make(x)\nreturn b.nested() }";
    for rooted in [false, true] {
        let names = compare(
            source,
            &[vec![Type::Str], vec![Type::Int(IntKind::I64)]],
            rooted,
        );
        assert!(names.iter().any(|s| s.ends_with(":make")), "{names:?}");
        assert!(names.iter().any(|s| s.ends_with(":get")), "{names:?}");
    }
}

/// Variant qualifiers may share a method body but must retain their identities.
#[test]
fn variant_method_walks_have_complete_identities() {
    let source = "type Choice = | A { value: string } | B { value: string }\nfun Choice.get(self) -> string { return self.value }\nfun entry(x: string) { let a = Choice.A { value: x }\nlet b = Choice.B { value: x }\nreturn [a.get(), b.get()] }";
    for rooted in [false, true] {
        let names = compare(source, &[vec![Type::Str]], rooted);
        assert!(names.iter().any(|s| s.contains(":A:get")), "{names:?}");
        assert!(names.iter().any(|s| s.contains(":B:get")), "{names:?}");
    }
}

/// Receiver declarations routed through the function elaborator are still
/// method observations; enabling observation cannot change their bypass count.
#[test]
fn primitive_receiver_walks_are_inventoried() {
    let source = "fun string.copy_value(self) -> string { return self }\nfun entry(x: string) { return x.copy_value() }";
    let names = compare(source, &[vec![Type::Str]], true);
    assert!(names.iter().any(|s| s.starts_with("fn:")), "{names:?}");
}

/// Qualified identities use defining modules and remote names. Observation
/// must not merge equal short names, or hide a provisional type at settlement.
#[test]
fn qualified_globals_and_mutable_settlement_are_snapshot_effects() {
    let p = program("fun string.read(self) -> string { return self }");
    let mut seed = checker(&p);
    seed.co_checking = true;
    seed.current_module = vec!["main".into()];
    seed.global_defs.insert(
        vec!["main".into()],
        [("value".into(), Type::Str)].into_iter().collect(),
    );
    seed.global_defs.insert(
        vec!["other".into()],
        [("value".into(), Type::Bool)].into_iter().collect(),
    );
    let mut observed = EffectSnapshot::fork(&seed);
    observed.method_inventory = Some(Box::new(MethodInventory::default()));
    let symbol = p.functions.keys().next().unwrap();
    let active =
        observed.begin_receiver_inventory(symbol, &[Type::Str], Some(&Type::Str), &Type::Str);
    assert!(active);
    observed.observe_method_global("value", &Type::Str, false);
    observed.current_module = vec!["other".into()];
    observed.observe_method_global("value", &Type::Bool, false);
    observed.finish_method_inventory(active, &Type::Str);
    observed.current_module = seed.current_module.clone();
    let record = &observed.method_inventory.as_ref().unwrap().completed[0].1;
    assert_eq!(record.globals.len(), 2);
    assert_ne!(record.globals[0].0.module, record.globals[1].0.module);
    assert_eq!(record.globals[0].0.name, record.globals[1].0.name);
    let history = EffectHistory::new(&seed);
    let before = EffectSnapshot::capture(&seed, &[], &Type::Void, &history);
    before
        .compare(&EffectSnapshot::capture(
            &observed,
            &[],
            &Type::Void,
            &history,
        ))
        .unwrap();
    observed.settle_global(&["other".into()], "value", &Type::Str, Span::new(0, 0));
    assert!(
        before
            .compare(&EffectSnapshot::capture(
                &observed,
                &[],
                &Type::Void,
                &history
            ))
            .is_err()
    );
    assert_eq!(recorded_global_type(&observed), Type::Bool);
}

/// Read the captured provisional type after settlement to ensure no late resolve
/// silently changes the evidence to the global's new type.
fn recorded_global_type(c: &crate::infer::Checker<'_>) -> Type {
    c.method_inventory.as_ref().unwrap().completed[0].1.globals[1]
        .1
        .clone()
}

/// Scheme replacement, open fallbacks and provenance-free nested replays must
/// prevent a closed input tuple from being mistaken for a complete certificate.
#[test]
fn shared_dependencies_can_reject_closed_inputs() {
    let p = program("fun string.copy_value(self) -> string { return self }");
    let mut c = checker(&p);
    c.co_checking = true;
    c.method_inventory = Some(Box::new(MethodInventory::default()));
    let symbol = p.functions.keys().next().unwrap();
    let unknown = c.fresh_unknown();
    let active = c.begin_receiver_inventory(symbol, &[Type::Str], None, &unknown);
    let history = EffectHistory::new(&c);
    let before = EffectSnapshot::capture(&c, &[Type::Str], &Type::Str, &history);
    c.schemes.insert("Changed".into(), TypeScheme::default());
    let after = EffectSnapshot::capture(&c, &[Type::Str], &Type::Str, &history);
    assert!(before.compare(&after).unwrap_err().starts_with("schemes"));
    c.observe_scheme_install();
    c.observe_method_replay(Some(&crate::infer::co_replay::GlobalReadProvenance {
        untracked: true,
        ..Default::default()
    }));
    c.finish_method_inventory(active, &Type::Str);
    let (_, deps, reasons) = &c.method_inventory.as_ref().unwrap().completed[0];
    assert_eq!(deps.scheme_revision, 0);
    assert!(reasons.contains(&"changed_scheme"));
    assert!(reasons.contains(&"open_return"));
    assert!(reasons.contains(&"untracked_dependency"));
}

/// Real method walks read same-named globals in their defining modules.
/// Each window retains the defining identity even when reporting names coincide.
#[test]
fn nested_method_global_reads_keep_defining_modules() {
    let modules = [
        ("a", "const value = \"a\"\ntype Item = { n: int32 }\nfun Item.read(self) -> string { return value }\nfun entry() -> string { return Item { n: 0 }.read() }"),
        ("b", "const value = \"b\"\ntype Item = { n: int32 }\nfun Item.read(self) -> string { return value }\nfun entry() -> string { return Item { n: 0 }.read() }"),
    ].map(|(name, source)| brass_hir::LoadedModule { source: None, is_prelude: false, path: vec![name.into()], ast: brass_parser::parse(source).unwrap() });
    let (p, errors) = brass_hir::lower(&modules);
    assert!(errors.is_empty(), "{errors:?}");
    let mut seed = checker(&p);
    seed.co_checking = true;
    for name in ["a", "b"] {
        seed.global_defs.insert(
            vec![name.into()],
            [("value".into(), Type::Str)].into_iter().collect(),
        );
    }
    let mut plain = EffectSnapshot::fork(&seed);
    let mut observed = EffectSnapshot::fork(&seed);
    plain.method_inventory = None;
    observed.method_inventory = Some(Box::new(MethodInventory::default()));
    let mut ah = EffectHistory::new(&seed);
    let mut bh = EffectHistory::new(&seed);
    for module in ["a", "b"] {
        let name = format!("entry@{module}");
        let a = call(&mut plain, &name, &[]);
        let b = call(&mut observed, &name, &[]);
        assert!(observed.errors.is_empty(), "{:?}", observed.errors);
        ah.boundary(&plain);
        bh.boundary(&observed);
        EffectSnapshot::capture(&plain, &[], &plain.resolve(&a), &ah)
            .compare(&EffectSnapshot::capture(
                &observed,
                &[],
                &observed.resolve(&b),
                &bh,
            ))
            .unwrap();
    }
    let records = &observed.method_inventory.as_ref().unwrap().completed;
    assert_eq!(records.len(), 2);
    assert_eq!(records[0].1.globals[0].0.module, ["a"]);
    assert_eq!(records[1].1.globals[0].0.module, ["b"]);
    assert_eq!(records[0].1.globals[0].0.name, "value");
    assert_eq!(records[1].1.globals[0].0.name, "value");
}

/// Name resolution mirrors global scope precedence, including core globals,
/// renamed imports, own-name shadowing and module-qualified reads.
#[test]
fn global_identity_respects_imports_renames_and_shadowing() {
    let mut p = program("fun string.identity(self) -> string { return self }");
    let caller = vec!["caller".into()];
    let origin = vec!["origin".into()];
    p.import_origins.insert(
        caller.clone(),
        [("local".into(), origin.clone())].into_iter().collect(),
    );
    p.import_renames.insert(
        caller.clone(),
        [("local".into(), "remote".into())].into_iter().collect(),
    );
    p.module_aliases.insert(
        caller.clone(),
        [("m".into(), origin.clone())].into_iter().collect(),
    );
    let mut c = checker(&p);
    c.current_module = caller.clone();
    c.global_defs.insert(
        origin.clone(),
        [("remote".into(), Type::Str)].into_iter().collect(),
    );
    c.global_defs.insert(
        vec!["core".into(), "z".into()],
        [("local".into(), Type::Bool)].into_iter().collect(),
    );
    c.global_defs.insert(
        vec!["core".into(), "a".into()],
        [("local".into(), Type::Bool)].into_iter().collect(),
    );
    c.co_checking = true;
    c.method_inventory = Some(Box::new(MethodInventory::default()));
    let symbol = p.functions.keys().next().unwrap();
    let active = c.begin_receiver_inventory(symbol, &[Type::Str], Some(&Type::Str), &Type::Str);
    c.observe_method_global("local", &Type::Str, false);
    c.observe_method_global("m.remote", &Type::Str, true);
    c.global_defs.insert(
        caller.clone(),
        [("local".into(), Type::Str)].into_iter().collect(),
    );
    c.observe_method_global("local", &Type::Str, false);
    c.current_module = vec!["unrelated".into()];
    c.observe_method_global("local", &Type::Bool, false);
    c.finish_method_inventory(active, &Type::Str);
    let reads = &c.method_inventory.as_ref().unwrap().completed[0].1.globals;
    assert_eq!(reads.len(), 3); // Rename and qualifier identify the same read.
    assert_eq!(reads[0].0.module, origin);
    assert_eq!(reads[0].0.name, "remote");
    assert_eq!(reads[1].0.module, caller);
    assert_eq!(reads[2].0.module, ["core", "a"]);
}
