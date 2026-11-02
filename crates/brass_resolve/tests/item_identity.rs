//! Provenance follows resolver routes; item identities survive span relocation.

use brass_hir::{ItemKind, PackageId, SourceOrigin, TypeKind};
use brass_resolve::{SearchPaths, frontend::assemble};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

struct Tree(PathBuf);
impl Tree {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "brass-item-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path)
    }
    fn write(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
}
impl Drop for Tree {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn graph(root: &Path, text: &str, search: &SearchPaths) -> Vec<brass_hir::LoadedModule> {
    let f = assemble(&root.join("main.cz"), text, root, search);
    assert!(f.parse_errors.is_empty(), "{:?}", f.parse_errors);
    assert!(f.load_errors.is_empty(), "{:?}", f.load_errors);
    f.modules
}

#[test]
fn origins_follow_routes_even_for_vendored_and_relative_imports() {
    let t = Tree::new();
    t.write("own/local.cz", "fun own() { return 1 }");
    t.write(
        "own/vendor/dep/a.cz",
        "import b\nimport root_only\nfun exported() { return 1 }",
    );
    t.write("own/vendor/dep/b.cz", "fun helper() { return 1 }");
    t.write("own/root_only.cz", "fun root_helper() { return 1 }");
    t.write(
        "include/shared/a.cz",
        "import b\nfun outside() { return 1 }",
    );
    // A relative dependency import served by the local route stays dependency.
    t.write("own/shared/b.cz", "fun helper() { return 1 }");
    let root = t.0.join("own");
    let search = SearchPaths {
        packages: [("dep".into(), root.join("vendor"))].into_iter().collect(),
        includes: vec![t.0.join("include")],
    };
    let modules = graph(
        &root,
        "import local\nimport dep.a\nimport shared.a",
        &search,
    );
    let origin = |name: &str| {
        &modules
            .iter()
            .find(|m| m.path.join("/") == name)
            .unwrap()
            .source
            .as_ref()
            .unwrap()
            .origin
    };
    assert_eq!(origin("main"), &SourceOrigin::Own(PackageId::new(&root)));
    assert_eq!(origin("local"), origin("main"));
    assert_eq!(origin("root_only"), origin("main"));
    assert_eq!(
        origin("dep/a"),
        &SourceOrigin::Dependency(PackageId::new(&root.join("vendor/dep")))
    );
    assert_eq!(origin("dep/b"), origin("dep/a"));
    assert_eq!(
        origin("shared/a"),
        &SourceOrigin::Dependency(PackageId::new(&t.0.join("include")))
    );
    assert_eq!(origin("shared/b"), origin("shared/a"));
    assert!(
        modules
            .iter()
            .filter(|m| m.is_prelude)
            .all(|m| m.source.as_ref().unwrap().origin == SourceOrigin::Core)
    );
    // Explicitly opening a dependency as an entry always owns that entry.
    let opened = assemble(
        &root.join("vendor/dep/a.cz"),
        "fun local() {}",
        &root,
        &search,
    );
    assert_eq!(
        opened
            .modules
            .last()
            .unwrap()
            .source
            .as_ref()
            .unwrap()
            .origin,
        SourceOrigin::Own(PackageId::new(&root))
    );
}

#[test]
fn item_ids_survive_context_projection_entry_edits_and_symbol_collisions() {
    let t = Tree::new();
    t.write("dep.cz", "fun shared() -> int32 { return 1 }\ntype Choice = A { value: int32 } | B { value: int32 }\nfun Choice.get(self) -> int32 { return self.value }");
    let search = SearchPaths::default();
    let lower = |text: &str, context: bool| {
        let mut modules = graph(&t.0, text, &search);
        if context {
            modules.pop();
        }
        let (p, errors) = brass_hir::lower(&modules);
        assert!(errors.is_empty(), "{errors:?}");
        p
    };
    let a = lower("import dep", true);
    let b = lower(
        "import dep\n// Shift all dependency spans.\nfun shared() -> int32 { return 2 }",
        false,
    );
    let f = |p: &brass_hir::Program| {
        let f = p.functions.values().find(|f| f.module == ["dep"]).unwrap();
        p.item_id(&f.module, f.decl.span, ItemKind::Function)
            .unwrap()
    };
    assert_eq!(f(&a), f(&b));
    assert_ne!(
        a.functions["shared"].symbol,
        b.functions["shared@dep"].symbol
    );
    let ids = |p: &brass_hir::Program| {
        let owner = &p.types["Choice"];
        let TypeKind::Sum { variants } = &owner.kind else {
            panic!()
        };
        variants
            .iter()
            .map(|v| {
                p.method_body_id(owner, &v.methods["get"], Some(v.tag))
                    .unwrap()
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(ids(&a), ids(&b));
    assert_ne!(ids(&a)[0], ids(&a)[1]);
}

/// HIR combines an imported `main` and the entry under one namespace. Their
/// declaration files, ownership and initializer identities must remain distinct.
#[test]
fn imported_main_and_entry_keep_their_own_source_identities() {
    let t = Tree::new();
    let dependency = "type Shared = {}\nfun Shared.from_dep(self) -> int32 { return 1 }\nfun library() -> int32 { return 1 }\n";
    let entry = "import main\n//xx\nfun Shared.from_entry(self) -> int32 { return 2 }\n";
    t.write("vendor/main.cz", dependency);
    t.write("entry.cz", entry);
    let search = SearchPaths {
        packages: [("main".into(), t.0.join("vendor"))].into_iter().collect(),
        includes: vec![],
    };
    let front = assemble(&t.0.join("entry.cz"), entry, &t.0, &search);
    assert!(front.load_errors.is_empty());
    assert!(front.parse_errors.is_empty());
    let (combined, errors) = brass_hir::lower(&front.modules);
    assert!(errors.is_empty(), "{errors:?}");
    let mut modules = front.modules;
    modules.pop();
    let (context, errors) = brass_hir::lower(&modules);
    assert!(errors.is_empty(), "{errors:?}");
    let library = |p: &brass_hir::Program| {
        let f = &p.functions["library"];
        p.item_id(&f.module, f.decl.span, ItemKind::Function)
            .unwrap()
    };
    assert_eq!(library(&context), library(&combined));
    let method = |p: &brass_hir::Program, name: &str| {
        let owner = &p.types["Shared"];
        let TypeKind::Record { methods, .. } = &owner.kind else {
            panic!()
        };
        p.method_body_id(owner, &methods[name], None).unwrap()
    };
    let imported = method(&combined, "from_dep");
    let own = method(&combined, "from_entry");
    assert_eq!(method(&context, "from_dep"), imported);
    assert_eq!(imported.owner, own.owner);
    assert_eq!(imported.offset, own.offset);
    assert_ne!(imported, own);
    assert_eq!(
        own.module,
        brass_hir::ModuleId::new(t.0.join("entry.cz"), &["main".into()])
    );
    let initializers: Vec<_> = combined
        .inits
        .iter()
        .filter(|init| init.path == ["main"])
        .map(|init| {
            let span = init.stmts[0].span();
            let source = combined.module_source(&init.path, span).unwrap();
            let id = combined
                .item_id(&init.path, span, ItemKind::Initializer)
                .unwrap();
            (id, source.origin.clone())
        })
        .collect();
    assert_eq!(initializers.len(), 2);
    assert_ne!(initializers[0].0, initializers[1].0);
    assert_eq!(initializers[0].0.offset, 0);
    assert_eq!(initializers[1].0.offset, 0);
    assert!(matches!(initializers[0].1, SourceOrigin::Dependency(_)));
    assert!(matches!(initializers[1].1, SourceOrigin::Own(_)));
    assert!(
        combined
            .module_source(&["main".into()], brass_hir::Span::new(0, 0))
            .is_none()
    );
}

/// The loader can retain two namespaces for one file. Those HIR definitions
/// remain distinct even though their canonical physical location is identical.
#[cfg(unix)]
#[test]
fn symlinked_namespaces_do_not_merge_declarations() {
    let t = Tree::new();
    t.write("original/a.cz", "fun same() { return true }");
    std::os::unix::fs::symlink(t.0.join("original"), t.0.join("alias")).unwrap();
    let modules = graph(
        &t.0,
        "import original.a\nimport alias.a",
        &SearchPaths::default(),
    );
    let (p, errors) = brass_hir::lower(&modules);
    assert!(errors.is_empty());
    let ids: Vec<_> = p
        .functions
        .values()
        .filter(|f| f.signature.name == "same")
        .map(|f| {
            p.item_id(&f.module, f.decl.span, ItemKind::Function)
                .unwrap()
        })
        .collect();
    assert_eq!(ids.len(), 2);
    assert_ne!(ids[0], ids[1]);
}

/// A path identity must not collapse distinct operating-system byte strings
/// into the same replacement-character display label.
#[cfg(unix)]
#[test]
fn source_identity_keeps_non_utf8_path_bytes() {
    use std::os::unix::ffi::OsStringExt;
    let a = PathBuf::from(std::ffi::OsString::from_vec(vec![b'/', 0xfe]));
    let b = PathBuf::from(std::ffi::OsString::from_vec(vec![b'/', 0xff]));
    assert_eq!(a.display().to_string(), b.display().to_string());
    let namespace = ["same".into()];
    assert_ne!(
        brass_hir::ModuleId::new(a, &namespace),
        brass_hir::ModuleId::new(b, &namespace)
    );
}

#[test]
fn recovered_dependency_ownership_does_not_admit_or_load_the_recovered_graph() {
    use brass_hir::diagnostics::{DiagnosticOwner, DiagnosticOwners};
    use brass_resolve::frontend::assemble_with_recovery;
    for (source, expected) in [
        (
            "import missing\nfun unused() { let x =\nreturn 1\n}\nfun next() {}",
            "function",
        ),
        (
            "type A = { value: int32 }\nfun A.unused(self) { let x =\nreturn 1\n}",
            "method",
        ),
        ("fun unused( {\nfun next() {}", "catalog"),
        ("fun unused() {\nfun hidden() {}", "catalog"),
    ] {
        let tree = Tree::new();
        tree.write("deps/pkg/bad.cz", source);
        let search = SearchPaths {
            packages: [("pkg".into(), tree.0.join("deps"))].into_iter().collect(),
            includes: Vec::new(),
        };
        let entry = tree.0.join("main.cz");
        let input = "import pkg.bad";
        let plain = assemble(&entry, input, &tree.0, &search);
        let mut recovered = Vec::new();
        let observed =
            assemble_with_recovery(&entry, input, &tree.0, &search, &mut |m| recovered.push(m));
        assert_eq!(plain.parse_errors, observed.parse_errors);
        assert_eq!(plain.load_errors, observed.load_errors);
        assert_eq!(
            plain.modules.iter().map(|m| &m.path).collect::<Vec<_>>(),
            observed.modules.iter().map(|m| &m.path).collect::<Vec<_>>()
        );
        assert_eq!(recovered.len(), 1);
        let module = &recovered[0];
        assert_eq!(module.path, ["pkg", "bad"]);
        assert_eq!(
            module.source.as_ref().unwrap().origin,
            SourceOrigin::Dependency(PackageId::new(&tree.0.join("deps/pkg")))
        );
        assert!(!observed.modules.iter().any(|m| m.path == module.path));
        let (program, _) = brass_hir::lower(&recovered);
        let owners = DiagnosticOwners::new(&program);
        assert!(!observed.load_errors.is_empty());
        for (_, span) in observed.load_errors {
            let located = observed.sources.locate(span.lo).unwrap();
            let owner = owners.syntax_owner(span, located.src, span.lo - located.local);
            assert!(
                match expected {
                    "function" => matches!(owner, DiagnosticOwner::Function(_)),
                    "method" => matches!(owner, DiagnosticOwner::Method(_)),
                    _ => owner == DiagnosticOwner::Catalog,
                },
                "{source}: {owner:?}"
            );
        }
    }
}
