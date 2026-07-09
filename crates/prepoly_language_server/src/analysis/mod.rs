//! Per-document analysis: incremental diagnostics and an on-demand full
//! analysis.
//!
//! Diagnostics are the per-keystroke hot path, so they run incrementally: only
//! the changed items and their users are re-checked (see [`items`]), against a
//! module graph reduced to the affected items plus the definitions they depend
//! on. Hover and go-to-definition need type information for the whole document,
//! so they use a separately cached full analysis, recomputed at most once per
//! document version and only when such a request actually arrives.

pub mod items;
pub mod world;

use std::collections::HashSet;
use std::path::PathBuf;

use prepoly_hir::{LoadedModule, Program, TypedProgram, lower};
use prepoly_parser::Span;
use prepoly_parser::ast::{Module, TopLevel};

use items::{Diag, Item, ItemCache, ItemKind};
use world::SourceMap;

/// A full analysis of one document version, used by hover and go-to-definition.
/// Carries the span map so a definition target in another file can be located.
///
/// This is *not* stored in the persistent server state: the HIR `Program` holds
/// `Rc`-based nodes and so is neither `Send` nor `Sync`. It is computed inside a
/// request handler, used synchronously, and dropped before any await -- which
/// keeps the handler futures `Send` while still giving hover/definition the
/// whole-document type information they need.
pub struct FullAnalysis {
    pub program: Program,
    pub typed: TypedProgram,
    /// Per record-type generalized scheme, keyed by type name; rendered by hover
    /// to show a method's signature over the type's inferred parameters.
    pub schemes: std::collections::HashMap<String, prepoly_hir::TypeScheme>,
    pub sources: SourceMap,
    pub main_base: usize,
    pub main_ast: Module,
}

/// The persistent analysis state for one open document. Holds only `Send`/`Sync`
/// data (the incremental diagnostics cache), so it can live in the shared
/// document map.
pub struct DocAnalyzer {
    path: PathBuf,
    /// Incremental diagnostics bookkeeping carried between versions.
    cache: ItemCache,
}

impl DocAnalyzer {
    pub fn new(path: PathBuf) -> Self {
        DocAnalyzer {
            path,
            cache: ItemCache::default(),
        }
    }

    /// Recompute the document's diagnostics for `text`, reusing cached results
    /// for items whose source is unchanged and that do not use a changed name.
    /// Returns `(message, global span)` pairs; map spans through the active
    /// document to publish them.
    pub fn diagnostics(&mut self, text: &str) -> Vec<(String, Span)> {
        let world = world::build(&self.path, text);
        if !world.parse_errors.is_empty() {
            // The document has syntax errors: report all of them and nothing
            // else -- checking the recovered AST would bury them under
            // cascading name/type errors -- and drop the cache so the next
            // clean parse re-checks from scratch.
            self.cache = ItemCache::default();
            return localize(world.parse_errors, world.main_base, text.len());
        }

        let mut new_items = items::split(&world.main_ast, text, world.main_base);
        let d = items::diff(&self.cache, &new_items);

        // Run the front end on the reduced module graph (the whole document on a
        // from-scratch check). Its diagnostics are authoritative for the
        // affected items and for anything outside the document's items.
        let main_for_run = if d.full {
            world.main_ast.clone()
        } else {
            reduce_main(&world.main_ast, &new_items, &d.reduced)
        };
        let (_program, _typed, _schemes, run_diags) =
            run_pipeline(&world.context_modules, main_for_run);

        // Attribute this run's diagnostics to the items they fall in; the rest
        // (dependency-module errors) become the refreshed global bucket.
        let (per_item, global) = attribute(&run_diags, &new_items);
        for (i, item) in new_items.iter_mut().enumerate() {
            if d.full || d.affected.contains(&i) {
                item.diags = per_item[i].clone();
            }
        }
        // Unaffected items keep their previous diagnostics, shifted to the new
        // byte positions (their source is byte-identical, so all spans move by a
        // constant delta).
        if !d.full {
            for (i, delta, prev_diags) in &d.carry {
                new_items[*i].diags = shift(prev_diags, *delta);
            }
        }

        self.cache = ItemCache { items: new_items };

        // Assemble: every item's diagnostics, the global bucket, and the
        // module-graph load errors (recomputed each run). The cache keeps global
        // span coordinates (so cross-version shifting works); the returned
        // diagnostics are converted to document-local spans and filtered to the
        // active file -- errors located in a dependency are not shown here.
        let mut out: Vec<(String, Span)> = Vec::new();
        for item in &self.cache.items {
            out.extend(item.diags.iter().cloned());
        }
        out.extend(global);
        out.extend(world.load_errors);
        localize(out, world.main_base, text.len())
    }

    /// Compute a full analysis of `text` for hover/definition. Returns an owned
    /// result -- the `Rc`-bearing `Program` is `!Send`, so it must not be stored
    /// in the shared document map; the caller uses it synchronously and drops it.
    /// A document with syntax errors is analyzed from its recovered AST, so
    /// hover/definition keep working on the parts that parse.
    pub fn analyze_full(&self, text: &str) -> Option<FullAnalysis> {
        let world = world::build(&self.path, text);
        let main = world.main_ast.clone();
        let (program, typed, schemes, _diags) = run_pipeline(&world.context_modules, main);
        Some(FullAnalysis {
            program,
            typed,
            schemes,
            sources: world.sources,
            main_base: world.main_base,
            main_ast: world.main_ast,
        })
    }
}

/// Run lex/parse-fed lowering, import resolution, and type checking on
/// `context` (prelude + dependencies) plus `main`. Returns the program, the
/// typed-expression sidecar, and all diagnostics as `(message, global span)`.
#[allow(clippy::type_complexity)]
fn run_pipeline(
    context: &[LoadedModule],
    main: Module,
) -> (
    Program,
    TypedProgram,
    std::collections::HashMap<String, prepoly_hir::TypeScheme>,
    Vec<(String, Span)>,
) {
    let mut modules = context.to_vec();
    modules.push(LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast: main,
    });

    // Resolve qualified uses of module imports (`import a.b` + `b.name`)
    // exactly as the driver does, so the editor reports the same programs
    // valid with the same diagnostics.
    let qualified_errors = prepoly_resolve::resolve_qualified_uses(&mut modules);

    let (program, lower_errors) = lower(&modules);
    let mut diags: Vec<(String, Span)> = Vec::new();
    for e in qualified_errors {
        diags.push((e.message, e.span));
    }
    for e in lower_errors {
        diags.push((e.message, e.span));
    }
    for e in prepoly_resolve::check_imports(&modules) {
        diags.push((e.message, e.span));
    }
    let analysis = prepoly_typeck::analyze(&program);
    for e in &analysis.errors {
        diags.push((e.message.clone(), e.span));
    }
    (program, analysis.typed, analysis.schemes, diags)
}

/// Rebuild the document module keeping only the items whose index is in `keep`.
/// Item indices follow [`items::split`]: functions and types in source order,
/// then the synthetic module-statement bucket last.
fn reduce_main(main: &Module, item_list: &[Item], keep: &HashSet<usize>) -> Module {
    let init_index = item_list.iter().position(|it| it.kind == ItemKind::Init);
    let mut kept = Vec::new();
    let mut idx = 0usize;
    for top in &main.items {
        match top {
            TopLevel::Fun(_) | TopLevel::Type(_) => {
                if keep.contains(&idx) {
                    kept.push(top.clone());
                }
                idx += 1;
            }
            TopLevel::Stmt(_) => {
                if init_index.map(|i| keep.contains(&i)).unwrap_or(false) {
                    kept.push(top.clone());
                }
            }
        }
    }
    Module {
        imports: main.imports.clone(),
        items: kept,
    }
}

/// Partition `diags` by the item their span falls in. Returns per-item
/// diagnostics (indexed like `item_list`) and the leftover that fell outside
/// every item.
fn attribute(diags: &[Diag], item_list: &[Item]) -> (Vec<Vec<Diag>>, Vec<Diag>) {
    let mut per_item = vec![Vec::new(); item_list.len()];
    let mut global = Vec::new();
    for (msg, span) in diags {
        match item_list
            .iter()
            .position(|it| span.lo >= it.span.lo && span.lo <= it.span.hi)
        {
            Some(i) => per_item[i].push((msg.clone(), *span)),
            None => global.push((msg.clone(), *span)),
        }
    }
    (per_item, global)
}

/// Convert global diagnostic spans to document-local spans, keeping only those
/// that fall within the active document `[base, base + len]`. A diagnostic
/// whose span lies in a dependency or the prelude is dropped (it belongs to a
/// different file's diagnostics).
fn localize(diags: Vec<(String, Span)>, base: usize, len: usize) -> Vec<(String, Span)> {
    diags
        .into_iter()
        .filter_map(|(msg, span)| {
            if span.lo < base || span.lo > base + len {
                return None;
            }
            let lo = span.lo - base;
            let hi = span.hi.saturating_sub(base).min(len);
            Some((msg, Span::new(lo, hi.max(lo))))
        })
        .collect()
}

fn shift(diags: &[(String, Span)], delta: i64) -> Vec<(String, Span)> {
    diags
        .iter()
        .map(|(msg, span)| {
            (
                msg.clone(),
                Span::new(
                    (span.lo as i64 + delta).max(0) as usize,
                    (span.hi as i64 + delta).max(0) as usize,
                ),
            )
        })
        .collect()
}
