//! Module-graph assembly for analysis.
//!
//! This mirrors the driver's front-end module loading (`prepoly_driver`'s
//! `analyze`): the embedded standard-library prelude, the active document, and
//! its transitively imported files are parsed into `LoadedModule`s under one
//! `SourceMap` of disjoint byte-offset bases, so every span is globally unique
//! and locates its file. The difference from the driver is that the active
//! document's text comes from the editor (unsaved), and the parsed prelude is
//! cached once -- it never changes -- so only the edited file is re-parsed per
//! keystroke.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use prepoly_hir::LoadedModule;
use prepoly_lexer::Span;
use prepoly_parser::ast::{ImportDecl, Module};
use prepoly_parser::{ParseError, parse_with_base};

/// Embedded standard-library modules (implicit prelude), identical to the
/// driver's `STDLIB`. Paths are relative to this source file. A name with a `/`
/// is a nested module: its segments become the path under `std` (so
/// `collections/hashmap` is the module `std.collections.hashmap`).
const STDLIB: &[(&str, &str)] = &[
    ("io", include_str!("../../../../std/io.pp")),
    ("array", include_str!("../../../../std/array.pp")),
    ("string", include_str!("../../../../std/string.pp")),
    ("math", include_str!("../../../../std/math.pp")),
    ("conv", include_str!("../../../../std/conv.pp")),
    ("assert", include_str!("../../../../std/assert.pp")),
    (
        "collections/hashmap",
        include_str!("../../../../std/collections/hashmap.pp"),
    ),
];

/// Names of the embedded top-level prelude modules (`io`, `array`, ...), used by
/// import-path completion. Nested modules (a name with `/`, e.g.
/// `collections/hashmap`) are excluded: they are not a single importable segment,
/// and their public names (`HashMap`) are already in the implicit prelude.
pub fn prelude_module_names() -> impl Iterator<Item = &'static str> {
    STDLIB
        .iter()
        .map(|(name, _)| *name)
        .filter(|name| !name.contains('/'))
}

/// The source of an embedded prelude module, for listing its public names.
pub fn prelude_source(name: &str) -> Option<&'static str> {
    STDLIB.iter().find(|(n, _)| *n == name).map(|(_, src)| *src)
}

/// Each loaded source with the disjoint byte-offset base its spans were parsed
/// at, so a global span's offset locates its file (ported from the driver). A
/// one-byte gap between files keeps an end-of-file span from colliding with the
/// next file's first byte.
#[derive(Clone, Default)]
pub struct SourceMap {
    next_base: usize,
    entries: Vec<SourceEntry>,
}

#[derive(Clone)]
struct SourceEntry {
    base: usize,
    /// `None` for an embedded prelude module (no file on disk).
    path: Option<PathBuf>,
    src: String,
}

impl SourceMap {
    fn add(&mut self, path: Option<PathBuf>, src: String) -> usize {
        let base = self.next_base;
        self.next_base = base + src.len() + 1;
        self.entries.push(SourceEntry { base, path, src });
        base
    }

    /// Locate the file containing global offset `off`: its path (if it is a real
    /// file), its source text, and the file-local offset.
    pub fn locate(&self, off: usize) -> Option<(Option<&Path>, &str, usize)> {
        self.entries.iter().find_map(|e| {
            (off >= e.base && off <= e.base + e.src.len()).then_some((
                e.path.as_deref(),
                e.src.as_str(),
                off - e.base,
            ))
        })
    }
}

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
        let mut modules = Vec::new();
        for (name, src) in STDLIB {
            let base = sources.add(None, (*src).to_string());
            // The embedded prelude is known-good; a parse failure here is a build
            // bug, so an empty module is a safe degradation rather than a panic.
            if let Ok(ast) = parse_with_base(src, base) {
                // A `/` in the name nests the module under `std` (matching the
                // driver), so `collections/hashmap` becomes `std.collections.hashmap`.
                let mut path = vec!["std".to_string()];
                path.extend(name.split('/').map(str::to_string));
                modules.push(LoadedModule { path, ast });
            }
        }
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
    /// Non-fatal module-graph errors (missing import, dependency parse failure,
    /// circular import), attributed to the offending import's span in the main
    /// file as `(message, span)`.
    pub load_errors: Vec<(String, Span)>,
}

/// Build the module graph for `main_src` (the active document at `main_path`).
/// Returns the active document's parse error (with a global span) when the
/// document itself does not parse; dependency problems are collected as
/// `load_errors` rather than aborting, so the rest of the file still checks.
pub fn build(main_path: &Path, main_src: &str) -> Result<World, (String, Span)> {
    let cache = stdlib_cache();
    let mut sources = cache.sources.clone();
    let mut context_modules = cache.modules.clone();

    let main_base = sources.add(Some(main_path.to_path_buf()), main_src.to_string());
    let mut main_ast = parse_with_base(main_src, main_base).map_err(|e: ParseError| {
        // Place the cursor at the document-local error position for the caller.
        (e.message, e.span)
    })?;

    let root = main_path.parent().unwrap_or(Path::new(".")).to_path_buf();
    let mut load_errors = Vec::new();
    let mut visited = Vec::new();
    let mut stack = Vec::new();
    let imports = main_ast.imports.clone();
    for imp in &imports {
        for target in canonicalize_one(&[], imp, &mut main_ast.imports) {
            load_module(
                &target,
                &root,
                &mut sources,
                &mut visited,
                &mut stack,
                &mut context_modules,
                imp.span,
                &mut load_errors,
            );
        }
    }

    Ok(World {
        sources,
        main_base,
        context_modules,
        main_ast,
        load_errors,
    })
}

/// Resolve an import path written relative to `base` to its canonical
/// (root-relative) path. A `std.*` path or a bare prelude module is global and
/// returns `None` (the prelude is already loaded). Ported from the driver.
fn relativize(base: &[String], imp_path: &[String]) -> Option<Vec<String>> {
    if imp_path.first().map(|s| s == "std").unwrap_or(false) || is_prelude_path(imp_path) {
        return None;
    }
    let mut canonical = base.to_vec();
    canonical.extend_from_slice(imp_path);
    Some(canonical)
}

/// Rewrite one import's path to canonical form in `decls` and return the
/// canonical file targets to load (empty for a prelude import). `decls` is the
/// owning module's import list, matched to `imp` by span.
fn canonicalize_one(
    base: &[String],
    imp: &ImportDecl,
    decls: &mut [ImportDecl],
) -> Vec<Vec<String>> {
    match relativize(base, &imp.path) {
        Some(canonical) => {
            for d in decls.iter_mut() {
                if d.span == imp.span {
                    d.path = canonical.clone();
                }
            }
            vec![canonical]
        }
        None => Vec::new(),
    }
}

fn is_prelude_path(path: &[String]) -> bool {
    matches!(path, [single] if STDLIB.iter().any(|(name, _)| name == single))
}

/// Load the module at canonical `path` and, transitively, the modules it
/// imports, pushing each onto `out`. Errors are recorded against `trigger_span`
/// (the import that asked for this module) rather than aborting.
#[allow(clippy::too_many_arguments)]
fn load_module(
    path: &[String],
    root: &Path,
    sources: &mut SourceMap,
    visited: &mut Vec<String>,
    stack: &mut Vec<String>,
    out: &mut Vec<LoadedModule>,
    trigger_span: Span,
    errors: &mut Vec<(String, Span)>,
) {
    let key = path.join(".");
    if prepoly_resolve::is_private_module(path) {
        errors.push((
            format!("cannot import private module `{key}`"),
            trigger_span,
        ));
        return;
    }
    if visited.contains(&key) {
        return;
    }
    if stack.contains(&key) {
        errors.push((format!("circular import involving `{key}`"), trigger_span));
        return;
    }
    stack.push(key.clone());

    let mut file = root.to_path_buf();
    for seg in path {
        file.push(seg);
    }
    file.set_extension("pp");
    let src = match std::fs::read_to_string(&file) {
        Ok(s) => s,
        Err(_) => {
            errors.push((
                format!("cannot find module `{key}` (expected `{}`)", file.display()),
                trigger_span,
            ));
            stack.retain(|k| k != &key);
            visited.push(key);
            return;
        }
    };
    let base = sources.add(Some(file.clone()), src.clone());
    let mut ast = match parse_with_base(&src, base) {
        Ok(ast) => ast,
        Err(e) => {
            let (line, _) = prepoly_lexer::line_col(&src, e.span.lo - base);
            errors.push((
                format!(
                    "module `{key}` has a parse error at line {line}: {}",
                    e.message
                ),
                trigger_span,
            ));
            stack.retain(|k| k != &key);
            visited.push(key);
            return;
        }
    };
    // This module's imports resolve relative to its own directory.
    let dir = path[..path.len() - 1].to_vec();
    let imports = ast.imports.clone();
    for imp in &imports {
        for target in canonicalize_one(&dir, imp, &mut ast.imports) {
            load_module(
                &target,
                root,
                sources,
                visited,
                stack,
                out,
                trigger_span,
                errors,
            );
        }
    }
    stack.retain(|k| k != &key);
    visited.push(key);
    out.push(LoadedModule {
        path: path.to_vec(),
        ast,
    });
}
