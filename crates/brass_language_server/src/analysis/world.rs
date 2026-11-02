//! Module-graph assembly for analysis.
//!
//! The graph itself comes from the shared front end
//! ([`brass_resolve::frontend`]) -- one orchestration for the driver and the
//! language server. What this module adds is the editor-specific policy: the
//! active document's text comes from the editor (unsaved), load and syntax
//! problems become diagnostics instead of aborting, and the active document's
//! AST is kept separate from its context so the incremental layer can re-check
//! a subset of its items.

use std::path::Path;
use std::sync::Arc;

use brass_hir::LoadedModule;
use brass_parser::Span;
use brass_parser::ast::Module;

pub use brass_resolve::{SourceMap, prelude_module_names, prelude_source};

/// The assembled module graph for one analysis of the active document.
pub struct World {
    /// Loader identity retained when the entry AST is split from its context.
    pub main_source: Option<Arc<brass_hir::ModuleSource>>,
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
/// problems into `load_errors`, so the rest of the file still checks. A parse
/// failure in the embedded prelude (a build bug) degrades to an empty prelude
/// rather than dying, so the editor keeps working.
pub fn build(main_path: &Path, main_src: &str) -> World {
    let search = brass_resolve::SearchPaths::from_env();
    let root = main_path.parent().unwrap_or(Path::new("."));
    let mut front = brass_resolve::frontend::assemble_recovered(main_path, main_src, root, &search);
    // The shared front end appends the entry module last; split its AST off
    // so everything remaining is the context.
    let main = front
        .modules
        .pop()
        .expect("the shared front end always appends the entry module");
    // The active buffer is the editor's own root. Merely imported local files
    // have dependency policy until they are opened as a separate document.
    for module in &mut front.modules {
        if let Some(source) = &mut module.source {
            let source = Arc::make_mut(source);
            if let brass_hir::SourceOrigin::Own(package) = &source.origin {
                source.origin = brass_hir::SourceOrigin::Dependency(package.clone());
            }
        }
    }
    World {
        sources: front.sources,
        main_base: front.entry_base,
        context_modules: front.modules,
        main_ast: main.ast,
        main_source: main.source,
        load_errors: front.load_errors,
        parse_errors: front.parse_errors,
    }
}

impl World {
    /// Whether dependency bodies require item selection rather than full core checking.
    pub(super) fn has_dependencies(&self) -> bool {
        self.context_modules.iter().any(|module| !module.is_prelude)
    }
}
