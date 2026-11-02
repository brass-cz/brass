//! Omission probes use real library bodies and independent solver forks.

use super::{Checker, EffectSnapshot, LoadedModule, Program, Rc, TypeKind, check_method_bodies};
use brass_hir::Type;

fn libraries(toml: bool) -> Program {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files: Vec<_> = std::fs::read_dir(root.join("core"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "cz"))
        .collect();
    files.sort();
    files.extend([
        root.join("std/collections.cz"),
        root.join("std/data/json.cz"),
    ]);
    if toml {
        files.push(root.join("std/data/toml.cz"));
    }
    let mut base = 0;
    let mut modules = Vec::new();
    for file in files {
        let relative = file.strip_prefix(&root).unwrap().with_extension("");
        let path: Vec<_> = relative
            .iter()
            .map(|s| s.to_str().unwrap().to_owned())
            .collect();
        let mut source = std::fs::read_to_string(&file).unwrap();
        if path == ["std", "data", "toml"] {
            source.push_str("\nimport std.data.json.{ JsonValue }\n");
            source.push_str(include_str!("toml_conversion.cz"));
        }
        modules.push(LoadedModule {
            source: None,
            is_prelude: path[0] == "core",
            path,
            ast: brass_parser::parse_with_base(&source, base).unwrap(),
        });
        base += source.len() + 1;
    }
    let source = if toml {
        "import std.data.toml.{ TomlValue }\nfun reached() { return TomlValue.parse(\"x = 1\")!.stringify() }"
    } else {
        "import std.data.json.{ JsonValue }\nfun reached() { return JsonValue.parse(\"[1, true, null]\")!.stringify() }"
    };
    modules.push(LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["main".into()],
        ast: brass_parser::parse_with_base(source, base).unwrap(),
    });
    let (program, errors) = brass_hir::lower(&modules);
    assert!(errors.is_empty(), "{errors:?}");
    program
}

fn omit(program: &mut Program, owner: &str, name: &str, variant: Option<i32>) {
    let TypeKind::Sum { variants } = &mut program.types.get_mut(owner).unwrap().kind else {
        panic!("sum expected")
    };
    for v in variants {
        if variant.is_none_or(|tag| tag == v.tag) {
            Rc::make_mut(&mut v.methods.get_mut(name).unwrap().decl).body = None;
        }
    }
}

fn compare_omission(full: &Program, selected: &Program) -> Result<(), String> {
    let mut seed = Checker::new(full, Rc::new(brass_typesys::RowInfo::analyze(full)));
    seed.precompute_global_bindings();
    seed.precompute_returns();
    seed.settle_numeric_globals();
    let mut all = EffectSnapshot::fork(&seed);
    let mut subset = EffectSnapshot::fork(&seed);
    subset.program = selected;
    for schemes_only in [true, false] {
        check_method_bodies(&mut all, full, schemes_only);
        check_method_bodies(&mut subset, selected, schemes_only);
        EffectSnapshot::capture_shared(&all).compare(&EffectSnapshot::capture_shared(&subset))?;
        all.schemes = all.build_schemes();
        subset.schemes = subset.build_schemes();
    }
    let function = &full.functions["reached"];
    let mut results = Vec::new();
    for checker in [&mut all, &mut subset] {
        checker.errors.clear();
        checker.instance_returns.clear();
        let result = checker.instantiate_function_call(
            "reached",
            &function.module,
            &function.signature.params,
            &function.decl.body,
            function.signature.ret_ty.clone(),
            Type::Unknown(0),
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
    assert!(
        results[0].1.is_empty(),
        "reached errors: {:?}",
        results[0].1
    );
    EffectSnapshot::capture_shared(&all).compare(&EffectSnapshot::capture_shared(&subset))
}

#[test]
fn json_converter_omission_probe() {
    let full = libraries(false);
    for variant in [None, Some(0), Some(1), Some(2), Some(3), Some(4), Some(5)] {
        let mut selected = libraries(false);
        omit(&mut selected, "JsonValue", "from", variant);
        compare_omission(&full, &selected).unwrap_or_else(|e| panic!("{variant:?}: {e}"));
    }
}

#[test]
fn toml_converter_omission_probe() {
    let full = libraries(true);
    for variant in [
        None,
        Some(0),
        Some(1),
        Some(2),
        Some(3),
        Some(4),
        Some(5),
        Some(6),
    ] {
        let mut selected = libraries(true);
        omit(&mut selected, "TomlValue", "to_json", variant);
        compare_omission(&full, &selected).unwrap_or_else(|e| panic!("{variant:?}: {e}"));
    }
}

#[test]
fn rootless_local_constraints_do_not_prepare_record_schemes() {
    // Exercise each local category independently; no certificate is consulted
    // when removing these bodies, so this comparison cannot prove itself.
    for source in [
        "fun helper(x: int32) -> int32 { return x }\ntype Choice = | A | B\nfun Choice.unused(self, x) -> int32 { return helper(x) }\nfun reached() -> int32 { return 1 }",
        "type Box = { value }\nfun Box.set(self, x) { self.value = x }\nfun Box.get(self) { return self.value }\ntype Choice = | A | B\nfun Choice.unused(self) { let b: Box { value: int32 } = Box { value: 1 }\nb.set(2)\nreturn b.get() }\nfun reached() { return Box { value: \"ok\" }.get() }",
        "type Choice = | A | B\nfun make(x) { return Choice.A }\nfun Choice.unused(self) { let a: int32[] = []\na.push(1)\nreturn make(a[0]) }\nfun reached() { return Choice.A }",
        "type Choice = | A { value: string } | B { value: string }\nfun Choice.unused(self) { for field in fields(self) { const value = self[field] }\nreturn typeof(self) }\nfun reached() { return Choice.A { value: \"ok\" } }",
        "type Choice = | A | B\nfun Choice.unused(self, callback: () -> int32) -> int32 { return callback() }\nfun reached() -> int32 { return 1 }",
    ] {
        let full = super::program(source);
        let mut selected = super::program(source);
        omit(&mut selected, "Choice", "unused", None);
        compare_omission(&full, &selected).unwrap_or_else(|e| panic!("{source}: {e}"));
    }
}

#[test]
fn rootless_global_read_changes_the_initializer_dependency_set() {
    // Even when an empty array is freshened per read, co_global_reads makes
    // this method depend on initializer settlement. That is shared state.
    let source = "const shared = []\nfun leaf() { shared.push(1) }\nfun middle() { leaf() }\ntype Choice = | A | B\nfun Choice.unused(self) { middle() }\nfun reached() { return shared }";
    let full = super::program(source);
    let mut selected = super::program(source);
    omit(&mut selected, "Choice", "unused", None);
    assert!(
        compare_omission(&full, &selected)
            .unwrap_err()
            .contains("co global reads")
    );
}

#[test]
fn record_owner_return_links_are_not_rootless_effects() {
    let source = "type Box = { value }\nfun Box.get_or(self, fallback) { if false { return fallback }\nreturn self.value }\nfun reached() -> int32 { return 1 }";
    let full = super::program(source);
    let mut selected = super::program(source);
    let TypeKind::Record { methods, .. } = &mut selected.types.get_mut("Box").unwrap().kind else {
        unreachable!()
    };
    Rc::make_mut(&mut methods.get_mut("get_or").unwrap().decl).body = None;
    let difference = compare_omission(&full, &selected).unwrap_err();
    assert!(
        difference.contains("schemes") || difference.contains("record co return links"),
        "{difference}"
    );
}

#[test]
fn an_open_sum_payload_can_retain_a_shared_shape_constraint() {
    let source = "type Choice = | A { value } | B { value }\nfun Choice.unused(self) { return self.value.field }\nfun reached() -> int32 { return 1 }";
    let full = super::program(source);
    let mut selected = super::program(source);
    omit(&mut selected, "Choice", "unused", None);
    let difference = compare_omission(&full, &selected).unwrap_err();
    assert!(difference.contains("shared shapes"), "{difference}");
}

#[test]
fn sum_parameter_with_an_open_nominal_layout_needs_a_certificate() {
    for body in [
        "fun Choice.unused(self, b: Box) { return b.value.field }",
        "fun helper(b: Box) { return b.value.field }\nfun Choice.unused(self, b) { return helper(b) }",
        "fun Choice.unused(self) { let b: Box\nreturn b.value.field }",
    ] {
        let source = format!(
            "type Box = {{ value }}\ntype Choice = | A | B\n{body}\nfun reached() -> int32 {{ return 1 }}"
        );
        let full = super::program(&source);
        let mut selected = super::program(&source);
        omit(&mut selected, "Choice", "unused", None);
        let difference = compare_omission(&full, &selected).unwrap_err();
        assert!(difference.contains("shared shapes"), "{body}: {difference}");
    }
}

#[test]
fn bare_type_test_views_change_shared_shapes() {
    for body in [
        "if b: Box { return b.value.field }",
        "if b: Box { return b.touch() }",
    ] {
        let source = format!(
            "type Box = {{ value }}\nfun Box.touch(self) {{ return self.value.field }}\ntype Choice = | A | B\nfun Choice.unused(self, b) {{ {body}\nreturn 1 }}\nfun reached() -> int32 {{ return 1 }}"
        );
        let full = super::program(&source);
        let mut selected = super::program(&source);
        omit(&mut selected, "Choice", "unused", None);
        assert!(
            compare_omission(&full, &selected)
                .unwrap_err()
                .contains("shared shapes")
        );
    }
}

#[test]
fn open_match_subject_borrows_declared_payloads() {
    let source = "type Open = | A { value } | B\ntype Choice = | A | B\nfun Choice.unused(self, x) { match x { Open.A { value } => { return value.field }, _ => {} }\nreturn 1 }\nfun reached() -> int32 { return 1 }";
    let full = super::program(source);
    let mut selected = super::program(source);
    omit(&mut selected, "Choice", "unused", None);
    assert!(
        compare_omission(&full, &selected)
            .unwrap_err()
            .contains("shared shapes")
    );
}
