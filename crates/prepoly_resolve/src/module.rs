//! Module-level name resolution: validate that every imported name exists and
//! is public. The file-system module graph is resolved by
//! the driver; this checks the resulting program for import errors.

use std::collections::{HashMap, HashSet};

use prepoly_hir::LoadedModule;
use prepoly_parser::Span;
use prepoly_parser::ast::{Stmt, TopLevel};

use crate::qualified::collect_pattern_names;
use crate::visibility::is_public;

#[derive(Clone, Debug)]
pub struct ResolveError {
    pub message: String,
    pub span: Span,
}

/// Check each import against the loaded modules: the name must be public and
/// exported by the named module. A bare prelude path (`io`) is checked against
/// the loaded `std.io` module's exports; importing from any other module that
/// was not loaded is an error.
pub fn check_imports(modules: &[LoadedModule]) -> Vec<ResolveError> {
    let exports = collect_exports(modules);
    let mut errors = Vec::new();
    for m in modules {
        // A rename whose local name is also declared in the importing module
        // is rejected: resolution gives the rename precedence over the bare
        // tables (see `resolve_qualified`), so letting it coexist with a local
        // declaration would silently shadow that declaration.
        let mut declared: HashSet<String> = HashSet::new();
        for item in &m.ast.items {
            match item {
                TopLevel::Fun(f) => {
                    declared.insert(f.name.clone());
                }
                TopLevel::Type(t) => {
                    declared.insert(t.name.clone());
                }
                TopLevel::Stmt(Stmt::Let { pat, .. }) => collect_pattern_names(pat, &mut declared),
                TopLevel::Stmt(_) => {}
            }
        }
        for imp in &m.ast.imports {
            for name in &imp.names {
                if name.local != name.remote && declared.contains(&name.local) {
                    errors.push(ResolveError {
                        message: format!(
                            "the imported name `{}` (renamed from `{}`) collides with a \
                             declaration in this module; rename one of them",
                            name.local, name.remote
                        ),
                        span: name.span,
                    });
                }
            }
        }
        // The same local name imported from two different modules is a local
        // ambiguity in the importing module: neither
        // origin wins, so a bare use cannot be resolved.
        let mut origins: HashMap<&str, Vec<String>> = HashMap::new();
        for imp in &m.ast.imports {
            let key = imp.path.join(".");
            for name in &imp.names {
                let seen = origins.entry(name.local.as_str()).or_default();
                if !seen.contains(&key) {
                    seen.push(key.clone());
                }
            }
        }
        for imp in &m.ast.imports {
            for name in &imp.names {
                if let Some(paths) = origins.get(name.local.as_str())
                    && paths.len() > 1
                    && paths.first() == Some(&imp.path.join("."))
                {
                    errors.push(ResolveError {
                        message: format!(
                            "`{}` is imported from multiple modules (`{}`); \
                                 the import is ambiguous",
                            name.local,
                            paths.join("`, `")
                        ),
                        span: imp.span,
                    });
                }
            }
        }
        for imp in &m.ast.imports {
            let key = imp.path.join(".");
            for name in &imp.names {
                if !is_public(&name.remote) {
                    errors.push(ResolveError {
                        message: format!("cannot import private name `{}`", name.remote),
                        span: imp.span,
                    });
                    continue;
                }
                match exports.get(&key) {
                    Some(names) if !names.contains(&name.remote) => errors.push(ResolveError {
                        message: format!("module `{key}` has no exported name `{}`", name.remote),
                        span: imp.span,
                    }),
                    Some(_) => {}
                    None => {
                        // Not a loaded file module. A bare prelude path (`io`)
                        // aliases the loaded `std.io`, so it is checked against
                        // that module's real exports. Any other unloaded module
                        // is unknown: accepting any program-wide name here (the
                        // old fallback) let a phantom `import std.x.{ name }`
                        // reach private definitions of arbitrary modules.
                        let std_alias = format!("std.{key}");
                        match exports.get(std_alias.as_str()) {
                            Some(names) if !names.contains(&name.remote) => {
                                errors.push(ResolveError {
                                    message: format!(
                                        "module `{key}` has no exported name `{}`",
                                        name.remote
                                    ),
                                    span: imp.span,
                                });
                            }
                            Some(_) => {}
                            None => errors.push(ResolveError {
                                message: format!("cannot import from unknown module `{key}`"),
                                span: imp.span,
                            }),
                        }
                    }
                }
            }
        }
    }
    errors
}

/// Public top-level type and function names exported by each loaded module,
/// keyed by the module's dotted path.
pub(crate) fn collect_exports(modules: &[LoadedModule]) -> HashMap<String, HashSet<String>> {
    let mut exports: HashMap<String, HashSet<String>> = HashMap::new();
    for m in modules {
        let names = exports.entry(m.path.join(".")).or_default();
        for item in &m.ast.items {
            match item {
                TopLevel::Type(t) if is_public(&t.name) => {
                    names.insert(t.name.clone());
                }
                TopLevel::Fun(f) if is_public(&f.name) => {
                    names.insert(f.name.clone());
                }
                // A top-level binding (`const VERSION = ..`) is a module member
                // like any other: the module's own resolution already treats it as
                // a declaration, so it exports too.
                TopLevel::Stmt(Stmt::Let { pat, .. }) => {
                    let mut bound = HashSet::new();
                    collect_pattern_names(pat, &mut bound);
                    names.extend(bound.into_iter().filter(|n| is_public(n)));
                }
                _ => {}
            }
        }
    }
    exports
}

#[cfg(test)]
mod tests {
    use super::*;
    use prepoly_hir::lower;
    use prepoly_parser::parse;

    fn module(path: &[&str], src: &str) -> LoadedModule {
        LoadedModule {
            is_prelude: false,
            path: path.iter().map(|s| s.to_string()).collect(),
            ast: parse(src).expect("parse"),
        }
    }

    fn import_errors(modules: Vec<LoadedModule>) -> Vec<String> {
        let (_program, lerr) = lower(&modules);
        assert!(lerr.is_empty(), "lower errors: {lerr:?}");
        check_imports(&modules)
            .into_iter()
            .map(|e| e.message)
            .collect()
    }

    #[test]
    fn unknown_imported_name_is_reported() {
        let lib = module(&["geometry", "vec"], "type Vec2 = { x: float64 }\n");
        let main = module(&["main"], "import geometry.vec.{ Vec2, missing }\n");
        let errors = import_errors(vec![lib, main]);
        assert!(
            errors
                .iter()
                .any(|m| m.contains("module `geometry.vec` has no exported name `missing`")),
            "{errors:?}"
        );
    }

    #[test]
    fn exported_name_is_accepted() {
        let lib = module(&["geometry", "vec"], "type Vec2 = { x: float64 }\n");
        let main = module(&["main"], "import geometry.vec.{ Vec2 }\n");
        assert!(import_errors(vec![lib, main]).is_empty());
    }

    #[test]
    fn same_name_imported_from_two_modules_is_ambiguous() {
        // Importing `helper` from two different modules into one
        // module is a local ambiguity, reported once and naming both origins.
        // The flat-namespace lower collision is ignored here so the import check
        // is tested in isolation (it is the diagnostic that survives once
        // coexistence lands).
        let a = module(&["a", "util"], "fun helper() -> int32 { return 1 }\n");
        let b = module(&["b", "util"], "fun helper() -> int32 { return 2 }\n");
        let main = module(
            &["main"],
            "import a.util.{ helper }\nimport b.util.{ helper }\n",
        );
        let modules = vec![a, b, main];
        let errors: Vec<String> = check_imports(&modules)
            .into_iter()
            .map(|e| e.message)
            .collect();
        let ambiguous: Vec<_> = errors
            .iter()
            .filter(|m| m.contains("imported from multiple modules"))
            .collect();
        assert_eq!(ambiguous.len(), 1, "reported once: {errors:?}");
        assert!(
            ambiguous[0].contains("`a.util`") && ambiguous[0].contains("`b.util`"),
            "{errors:?}"
        );
    }

    #[test]
    fn private_name_import_is_reported() {
        let lib = module(&["geometry", "vec"], "type _Hidden = { x: float64 }\n");
        let main = module(&["main"], "import geometry.vec.{ _Hidden }\n");
        let errors = import_errors(vec![lib, main]);
        assert!(
            errors
                .iter()
                .any(|m| m.contains("cannot import private name `_Hidden`")),
            "{errors:?}"
        );
    }
}
