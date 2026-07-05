//! Module-graph assembly for analysis.
//!
//! The loading itself (embedded prelude, `SourceMap`, transitive import
//! resolution) is the shared front end in [`prepoly_resolve::loader`] -- one
//! implementation for the driver and the language server. What this module adds
//! is the editor-specific policy: the active document's text comes from the
//! editor (unsaved), load problems become diagnostics instead of aborting, and
//! the parsed prelude is cached once for the life of the process -- it never
//! changes -- so only the edited file is re-parsed per keystroke.

use std::collections::HashSet;
use std::path::Path;
use std::sync::OnceLock;

use prepoly_hir::LoadedModule;
use prepoly_parser::Span;
use prepoly_parser::ast::Module;
use prepoly_parser::parse_recovering;

pub use prepoly_resolve::{SourceMap, prelude_module_names, prelude_source};

/// The parsed prelude shared across analyses: its modules and the `SourceMap`
/// prefix they occupy. Cloned as the starting point of every `World` so the
/// prelude is parsed exactly once for the life of the process.
struct StdlibCache {
    modules: Vec<LoadedModule>,
    sources: SourceMap,
}

fn stdlib_cache() -> &'static StdlibCache {
    static CACHE: OnceLock<StdlibCache> = OnceLock::new();
    CACHE.get_or_init(|| {
        let mut sources = SourceMap::default();
        // The embedded prelude is known-good; a parse failure here is a build
        // bug, so an empty module set is a safe degradation rather than a panic.
        let modules = prepoly_resolve::parse_stdlib(&mut sources).unwrap_or_default();
        StdlibCache { modules, sources }
    })
}

/// The assembled module graph for one analysis of the active document.
pub struct World {
    pub sources: SourceMap,
    /// Byte-offset base of the active document; add it to a document-local
    /// offset to get a global span offset, or subtract to go back.
    pub main_base: usize,
    /// Prelude and dependency modules -- everything except the active document.
    pub context_modules: Vec<LoadedModule>,
    /// The parsed active document, kept separate so the incremental layer can
    /// re-check a subset of its items.
    pub main_ast: Module,
    /// Non-fatal module-graph errors (missing import, dependency syntax
    /// errors, circular import) as `(message, span)`. Graph-level problems
    /// are attributed to the offending import in the main file; a
    /// dependency's syntax errors keep their in-file spans.
    pub load_errors: Vec<(String, Span)>,
    /// The active document's own syntax errors (global spans), in source
    /// order. Non-empty means `main_ast` is the recovered best-effort AST:
    /// good enough for editor features, not for checking.
    pub parse_errors: Vec<(String, Span)>,
}

/// Build the module graph for `main_src` (the active document at `main_path`).
/// Never fails: the active document's syntax errors are collected into
/// `parse_errors` (with the recovered AST in `main_ast`), and dependency
/// problems into `load_errors`, so the rest of the file still checks.
pub fn build(main_path: &Path, main_src: &str) -> World {
    let cache = stdlib_cache();
    let mut sources = cache.sources.clone();
    let mut context_modules = cache.modules.clone();

    let main_base = sources.add(
        Some(main_path.to_path_buf()),
        main_path.display().to_string(),
        main_src.to_string(),
    );
    let (mut main_ast, parse_errors) = parse_recovering(main_src, main_base);
    // The same message the driver renders for this source, so the editor and
    // the command line can never disagree about what is wrong.
    let parse_errors: Vec<(String, Span)> = parse_errors
        .into_iter()
        .map(|e| (format!("syntax error: {}", e.message), e.span))
        .collect();

    let root = main_path.parent().unwrap_or(Path::new(".")).to_path_buf();
    let mut load_errors = Vec::new();
    let mut visited = HashSet::new();
    let mut stack = HashSet::new();
    for (target, span) in prepoly_resolve::canonicalize_imports(&[], &root, &mut main_ast.imports) {
        prepoly_resolve::load_module(
            &target,
            &root,
            &mut sources,
            &mut visited,
            &mut stack,
            &mut context_modules,
            span,
            &mut load_errors,
        );
    }

    // Nested std modules (`std.collections.hashmap`, `std.data.json`) are not in
    // the implicit prelude; load the ones imported by the document or a
    // dependency, transitively.
    let extra: Vec<Vec<String>> = main_ast
        .imports
        .iter()
        .map(|imp| imp.path.clone())
        .collect();
    let nested = prepoly_resolve::load_std_nested(&context_modules, &extra, &mut sources);
    context_modules.extend(nested);

    World {
        sources,
        main_base,
        context_modules,
        main_ast,
        load_errors: load_errors
            .into_iter()
            .map(|e| (e.message, e.span))
            .collect(),
        parse_errors,
    }
}
