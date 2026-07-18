//! Shared front-end orchestration: the module graph for one entry source.
//!
//! Both front ends -- the CLI driver and the language server -- assemble a
//! program the same way: the embedded core library, then the entry source's
//! transitive file imports, then the entry module last. [`assemble`] is that
//! one sequence. It
//! applies NO error policy: every problem it meets is collected into
//! [`Frontend`], because policy is exactly where the callers differ -- the
//! driver aborts per problem class (syntax errors before graph errors) while
//! the language server converts everything to diagnostics and analyzes the
//! recovered graph anyway.

use fxhash::FxHashSet as HashSet;
use std::path::Path;
use std::sync::OnceLock;

use brass_hir::LoadedModule;
use brass_parser::Span;

use crate::loader::{
    SearchPaths, SourceMap, canonicalize_imports, inject_module_path, load_module, module_location,
    parse_stdlib,
};

/// The parsed embedded core library, shared for the life of the process: it never
/// changes, so it is parsed once and cloned as the starting point of every
/// assembly -- the language server assembles per keystroke and the REPL per
/// entered line. The `SourceMap` holding the prelude sources is cached with
/// the modules, so every assembly hands out the same span bases.
struct StdlibCache {
    sources: SourceMap,
    /// `Err` carries the rendered message of a prelude parse failure -- a
    /// build bug, the embedded sources are known-good. It is kept rather than
    /// panicked on so each front end can pick its severity; `sources` then
    /// holds what was added before the failing module.
    modules: Result<Vec<LoadedModule>, String>,
}

fn stdlib_cache() -> &'static StdlibCache {
    static CACHE: OnceLock<StdlibCache> = OnceLock::new();
    CACHE.get_or_init(|| {
        let mut sources = SourceMap::default();
        let modules = parse_stdlib(&mut sources);
        StdlibCache { sources, modules }
    })
}

/// The assembled module graph for one entry source, with every problem the
/// assembly found. No error policy is applied here: the driver aborts on
/// `parse_errors` before it even looks at `load_errors`, while the language
/// server reports both and keeps analyzing.
pub struct Frontend {
    /// Every module of the program -- the core library, then file
    /// dependencies -- with the entry LAST. Everything before the entry is the
    /// CONTEXT, and keeping the context a prefix gives it the same lowering
    /// ids in a context-only run as in the full one, which is what lets a
    /// cached context seed's tables apply to the full program. It also runs
    /// the entry's top-level statements after every dependency's, the
    /// initialization order they already have with respect to each other.
    pub modules: Vec<LoadedModule>,
    /// Every loaded source and the disjoint span base it was parsed at.
    pub sources: SourceMap,
    /// Byte-offset base the entry source was parsed at: add it to an
    /// entry-local offset for a global span offset, subtract to go back.
    pub entry_base: usize,
    /// The entry source's own syntax errors (`syntax error: ...` with global
    /// spans), in source order. Non-empty means the entry module holds the
    /// recovered best-effort AST: good enough for editor features, not for
    /// checking.
    pub parse_errors: Vec<(String, Span)>,
    /// Non-fatal module-graph problems (missing import, dependency syntax
    /// errors, circular or private import) as `(message, span)`. Graph-level
    /// problems are attributed to the offending import in the entry file; a
    /// dependency's own syntax errors keep their in-file spans.
    pub load_errors: Vec<(String, Span)>,
    /// A parse failure in the embedded prelude, rendered and ready to print.
    /// A build bug; the prelude modules are then absent from `modules`.
    pub stdlib_error: Option<String>,
}

/// Assemble the module graph for `entry_src`, a program identified by
/// `entry_path` (its diagnostic label and its `_PATH`; the file need not
/// exist -- `<repl>` and unsaved editor buffers pass the text they have).
/// File imports resolve relative to `root`, through `search`.
///
/// The sequence both front ends share: the embedded core library (parsed once
/// per process), the entry source parsed with recovery and given its `_PATH`,
/// its imports canonicalized and transitively loaded from disk, and the entry
/// last. Returns everything and decides nothing: syntax errors leave the
/// recovered AST in the graph, graph problems leave the graph partial, and
/// both are reported in the result for the caller to abort on or diagnose.
pub fn assemble(entry_path: &Path, entry_src: &str, root: &Path, search: &SearchPaths) -> Frontend {
    let cache = stdlib_cache();
    let mut sources = cache.sources.clone();
    let (mut modules, stdlib_error) = match &cache.modules {
        Ok(modules) => (modules.clone(), None),
        Err(message) => (Vec::new(), Some(message.clone())),
    };

    let entry_base = sources.add(
        Some(entry_path.to_path_buf()),
        entry_path.display().to_string(),
        entry_src.to_string(),
    );
    let (mut entry_ast, parse_errors) = brass_parser::parse_recovering(entry_src, entry_base);
    // The entry's `_PATH`: its canonical on-disk location, or the label as
    // written when no file exists behind it.
    inject_module_path(
        &mut entry_ast,
        &module_location(entry_path),
        Span::new(entry_base, entry_base),
    );
    let parse_errors: Vec<(String, Span)> = parse_errors
        .into_iter()
        .map(|e| (format!("syntax error: {}", e.message), e.span))
        .collect();

    let mut load_errors = Vec::new();
    let mut visited = HashSet::default();
    let mut stack = HashSet::default();
    for (target, span) in canonicalize_imports(&[], root, &mut entry_ast.imports, search) {
        load_module(
            &target,
            root,
            &mut sources,
            &mut visited,
            &mut stack,
            &mut modules,
            span,
            &mut load_errors,
            search,
        );
    }

    // The entry joins the graph under the fixed module path `main`, LAST (the
    // context-prefix invariant documented on `Frontend::modules`): its file
    // dependencies were all pushed by the loop above.
    modules.push(LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast: entry_ast,
    });

    Frontend {
        modules,
        sources,
        entry_base,
        parse_errors,
        load_errors: load_errors
            .into_iter()
            .map(|e| (e.message, e.span))
            .collect(),
        stdlib_error,
    }
}
