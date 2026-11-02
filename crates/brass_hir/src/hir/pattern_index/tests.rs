use super::*;
use crate::{LoadedModule, TypeInfo};

fn program(sources: &[(&str, &str)]) -> Program {
    let modules: Vec<_> = sources
        .iter()
        .map(|(module, source)| LoadedModule {
            source: None,
            path: if module.is_empty() {
                Vec::new()
            } else {
                vec![(*module).into()]
            },
            is_prelude: *module == "prelude",
            ast: brass_parser::parse(source).expect("parse fixture"),
        })
        .collect();
    crate::lower(&modules).0
}

// Keep the unindexed filter/sort as an independent oracle for declaration facts.
fn scan_owners<'a>(program: &'a Program, name: &str) -> Vec<&'a TypeInfo> {
    let mut owners: Vec<_> = program
        .types
        .values()
        .filter(|info| match &info.kind {
            TypeKind::Sum { variants } => variants.iter().any(|variant| variant.name == name),
            TypeKind::Record { .. } => false,
        })
        .collect();
    owners.sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.symbol.cmp(&b.symbol)));
    owners
}

#[test]
fn global_owners_match_scan_including_duplicate_declarations() {
    let mut program = program(&[
        (
            "a",
            "type Shared = | Same | Other\ntype Same = { x: int32 }",
        ),
        ("b", "type Shared = | Same { x: int32 } | Same | End"),
        ("", "type A = | Same | Last"),
    ]);
    for _ in 0..2 {
        for name in ["Same", "Other", "End", "Last", "Missing", "a.Same"] {
            let expected: Vec<_> = scan_owners(&program, name)
                .iter()
                .map(|info| info.id)
                .collect();
            assert_eq!(program.variant_owner_ids(name), expected);
            assert_eq!(
                program
                    .sums_containing_variant(name)
                    .iter()
                    .map(|info| info.id)
                    .collect::<Vec<_>>(),
                expected
            );
        }
        // Insertion order cannot select an owner or change diagnostic ordering.
        let mut entries: Vec<_> = program.types.drain().collect();
        entries.sort_by(|a, b| b.0.cmp(&a.0));
        program.types.extend(entries);
        program.rebuild_resolution_indexes();
    }
}

#[test]
fn rebuild_updates_negative_queries_and_nominal_ids() {
    let mut program = Program::empty();
    assert!(program.variant_owner_ids("Added").is_empty());
    let other = self::program(&[("a", "type S = | Added")]);
    program.types.extend(other.types);
    program.rebuild_resolution_indexes();
    assert_eq!(program.variant_owner_ids("Added").len(), 1);
    assert!(
        program
            .type_by_id(program.variant_owner_ids("Added")[0])
            .is_some()
    );
    assert!(program.type_by_id(-1).is_none());
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "rebuild resolution indexes")]
fn unrouted_variant_addition_is_detected() {
    let mut program = program(&[("a", "type S = | A | B")]);
    let TypeKind::Sum { variants } = &mut program.types.get_mut("S").unwrap().kind else {
        panic!("sum")
    };
    variants.pop();
    program.variant_owner_ids("A");
}

fn braced_key(head: crate::BracedHead<'_>) -> (u8, Option<i32>) {
    match head {
        crate::BracedHead::Record => (0, None),
        crate::BracedHead::Variant => (1, None),
        crate::BracedHead::RecordOrVariant(info) => (2, Some(info.id)),
    }
}

fn scan_braced(program: &Program, module: &[String], name: &str) -> (u8, Option<i32>) {
    if name.contains('.') {
        return (0, None);
    }
    let record = program
        .resolve_type_or_alias(module, name)
        .filter(|info| !info.is_sum());
    let variant = !scan_owners(program, name).is_empty();
    match (record, variant) {
        (Some(info), true) => (2, Some(info.id)),
        (None, true) => (1, None),
        (_, false) => (0, None),
    }
}

#[test]
fn scoped_queries_match_scan_with_imports_aliases_and_collisions() {
    let program = program(&[
        (
            "prelude",
            "type Builtin = | Unit | Common { x: int32 }\ntype Clash = { x: int32 }",
        ),
        (
            "lib",
            "type S = | Unit | Payload { x: int32 } | Clash { x: int32 }\ntype Alias = S\ntype Point = { x: int32 }\ntype RecordAlias = Point\ntype Maybe = S?\ntype Words = string[]",
        ),
        (
            "other",
            "type S = | Unit { x: int32 } | Payload\ntype Point = { y: int32 }",
        ),
        (
            "named",
            "import lib.{ S as Renamed, RecordAlias as Clash, Maybe, Words }",
        ),
        ("aliased", "import lib.{ Alias }"),
        ("whole", "import lib"),
        ("transitive", "import whole"),
        ("local", "type Clash = { y: int32 }"),
        ("", "type Root = | RootUnit"),
    ]);
    for module in [
        "prelude",
        "lib",
        "other",
        "named",
        "aliased",
        "whole",
        "transitive",
        "local",
        "absent",
        "",
    ] {
        let module = if module.is_empty() {
            Vec::new()
        } else {
            vec![module.into()]
        };
        let scope = program.pattern_scope(&module);
        for name in [
            "Unit",
            "Payload",
            "Common",
            "Clash",
            "Renamed",
            "Alias",
            "RecordAlias",
            "Point",
            "Maybe",
            "Words",
            "RootUnit",
            "Missing",
            "lib.Point",
            "lib.RecordAlias",
        ] {
            let all = scan_owners(&program, name);
            let visible: Vec<_> = all
                .iter()
                .copied()
                .filter(|info| program.sum_in_scope(&module, info))
                .collect();
            let ids: Vec<_> = visible.iter().map(|info| info.id).collect();
            assert_eq!(scope.owner_ids(name), ids, "{module:?} {name}");
            assert_eq!(
                scope.first_owner(name, false).map(|info| info.id),
                visible.first().map(|info| info.id)
            );
            assert_eq!(
                scope.first_owner(name, true).map(|info| info.id),
                visible.first().or(all.first()).map(|info| info.id)
            );
            assert_eq!(
                scope.is_unit_variant(name),
                visible.iter().any(|info| info
                    .variant(name)
                    .is_some_and(|variant| variant.fields.is_empty()))
            );
            for _ in 0..2 {
                // Both misses and hits preserve the unresolved collision and
                // distinguish an unknown qualifier from a non-nominal alias.
                assert_eq!(
                    braced_key(scope.braced_head(name)),
                    scan_braced(&program, &module, name)
                );
                let actual = match scope.type_head(name) {
                    crate::PatternTypeHead::Nominal(info) => (0, Some(info.id)),
                    crate::PatternTypeHead::NonNominalAlias => (1, None),
                    crate::PatternTypeHead::Unknown => (2, None),
                };
                let expected = match program.resolve_type_or_alias(&module, name) {
                    Some(info) => (0, Some(info.id)),
                    None if program.resolve_type_alias(&module, name).is_some() => (1, None),
                    None => (2, None),
                };
                assert_eq!(actual, expected, "{module:?} {name}");
            }
        }
    }
}

#[test]
fn rebuilding_invalidates_negative_alias_and_visibility_facts() {
    let mut program = program(&[("lib", "type S = | Unit\ntype Alias = S"), ("client", "")]);
    let module = vec!["client".into()];
    assert!(!program.pattern_scope(&module).is_unit_variant("Unit"));
    assert!(matches!(
        program.pattern_scope(&module).type_head("New"),
        crate::PatternTypeHead::Unknown
    ));
    let mut alias = program.type_aliases["Alias"].clone();
    alias.module = module.clone();
    program.type_aliases.insert("New".into(), alias);
    program
        .module_aliases
        .entry(module.clone())
        .or_default()
        .insert("lib".into(), vec!["lib".into()]);
    program.rebuild_resolution_indexes();
    assert!(program.pattern_scope(&module).is_unit_variant("Unit"));
    assert!(matches!(
        program.pattern_scope(&module).type_head("New"),
        crate::PatternTypeHead::Nominal(_)
    ));
}

#[test]
fn independent_programs_do_not_share_global_collision_facts() {
    let context = program(&[("a", "type Clash = { x: int32 }")]);
    let module = vec!["a".into()];
    assert_eq!(
        braced_key(context.pattern_scope(&module).braced_head("Clash")),
        (0, None)
    );
    let full = program(&[
        ("a", "type Clash = { x: int32 }"),
        ("b", "type S = | Clash { x: int32 }"),
    ]);
    assert!(matches!(
        full.pattern_scope(&module).braced_head("Clash"),
        crate::BracedHead::RecordOrVariant(_)
    ));
    assert!(full.pattern_scope(&module).owner_ids("Clash").is_empty());
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "rebuild resolution indexes")]
fn unrouted_visibility_addition_is_detected() {
    let mut program = program(&[("lib", "type S = | Unit"), ("client", "")]);
    let module = vec!["client".into()];
    program.pattern_scope(&module);
    program
        .module_aliases
        .entry(module.clone())
        .or_default()
        .insert("lib".into(), vec!["lib".into()]);
    program.pattern_scope(&module);
}

#[test]
fn generated_methods_preserve_cached_pattern_facts() {
    let mut program = program(&[(
        "a",
        "type S = | A | B\nfun S.template(self) -> int32 { return 1 }",
    )]);
    let module = vec!["a".into()];
    assert!(program.pattern_scope(&module).is_unit_variant("A"));
    let cached = program.pattern_index.modules.borrow()[&module].clone();
    let ast = brass_parser::parse("fun S.generated(self) -> int32 { return 2 }").unwrap();
    let brass_parser::ast::TopLevel::Fun(decl) = ast.items.into_iter().next().unwrap() else {
        panic!("function")
    };
    let generated = crate::GeneratedDecl {
        module: module.clone(),
        receiver: "S".into(),
        template: "template".into(),
        decl,
        key: crate::Type::Bool,
    };
    assert!(crate::lower_generated_into(&mut program, &[generated]).is_ok());
    assert!(program.pattern_scope(&module).is_unit_variant("A"));
    assert!(std::rc::Rc::ptr_eq(
        &cached,
        &program.pattern_index.modules.borrow()[&module]
    ));
}
