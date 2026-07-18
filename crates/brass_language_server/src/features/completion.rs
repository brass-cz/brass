//! Completion.
//!
//! Three contexts are handled. Inside an `import` statement the cursor is offered
//! module path segments (`import math.|`) and, within the brace list, the public
//! names a module exports (`import math.{ |`); the context is recovered textually
//! from the current line (so it works while the line does not yet parse), and the
//! candidates come from the loader's search roots -- prelude, nested std, files
//! next to the document, include paths, and declared packages -- with the brace
//! names carrying the signatures and docs of the analyzed module.
//! After a `.` (`a.|`) the cursor is offered the members reachable on the
//! receiver -- a record's fields, a record's or a sum's INSTANCE methods, and the
//! built-in and stdlib methods for the receiver's kind -- or, when the receiver is
//! a type name (`Shape.|`), what that name can be qualified with: a sum's variants
//! and, for either kind of nominal, its STATIC methods. The instance/static split
//! is what a call site can actually reach: a value has no static, and a type name
//! has no receiver to bind `self` to. Everywhere else the cursor is offered the
//! types and functions visible from the document.
//!
//! The member case needs the receiver's inferred type, but `a.` does not parse,
//! so the source is re-analyzed with a probe identifier spliced in at the cursor
//! to recover the type. Analysis therefore happens inside this module (via the
//! document's analyzer) rather than being passed in.

use std::collections::HashSet;
use std::path::Path;

use brass_hir::{Type, TypeInfo, TypeKind};
use brass_parser::ast::{TopLevel, TypeBody};
use brass_parser::parse;
use brass_resolve::SearchPaths;
use tower_lsp_server::ls_types::{CompletionItem, CompletionItemKind};

use crate::analysis::world::{prelude_module_names, prelude_source};
use crate::analysis::{DocAnalyzer, FullAnalysis};
use crate::document::Document;
use crate::features::hover::typedef_method_signatures;
use crate::render::{UnknownNamer, is_public_member, render_signature, render_type};

/// Built-in type names that are always in scope.
const BUILTIN_TYPES: &[&str] = &[
    "bool", "int8", "int16", "int32", "int64", "uint8", "uint16", "uint32", "uint64", "float32",
    "float64", "string", "void", "Result",
];

/// Built-in functions that are not part of the prelude module set (compiler
/// intrinsics), so they would not otherwise appear in the program's functions.
const BUILTIN_FUNCTIONS: &[&str] = &["len", "error", "ok"];

/// Compute completion items for `pos`, analyzing the document (and, for the
/// member case, a probe-spliced variant of it) through `analyzer` as needed.
/// Import resolution uses the process environment's search paths.
pub fn completion(
    doc: &Document,
    analyzer: &DocAnalyzer,
    doc_path: &Path,
    pos: tower_lsp_server::ls_types::Position,
) -> Vec<CompletionItem> {
    completion_with(doc, analyzer, doc_path, pos, &SearchPaths::from_env())
}

/// [`completion`] with explicit module search paths, so tests can point the
/// import contexts at their own roots without touching the environment.
pub(crate) fn completion_with(
    doc: &Document,
    analyzer: &DocAnalyzer,
    doc_path: &Path,
    pos: tower_lsp_server::ls_types::Position,
    search: &SearchPaths,
) -> Vec<CompletionItem> {
    let offset = doc.offset_at(pos);
    let line_start = doc.text[..offset].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let prefix = &doc.text[line_start..offset];

    if let Some(ctx) = import_context(prefix) {
        return match ctx {
            ImportContext::Names { module, prefix } => {
                import_name_items(&module, &prefix, analyzer, doc_path, search)
            }
            ImportContext::Path { parents, prefix } => {
                import_path_items(&parents, &prefix, doc_path, search)
            }
        };
    }
    if let Some(items) = member_completion(doc, analyzer, offset) {
        return items;
    }
    symbol_items(analyzer, doc, doc_path)
}

// ===== import completion =====

/// What an import statement's cursor is completing.
enum ImportContext {
    /// A module path segment, e.g. `import math.|` -> parents `["math"]`.
    Path {
        parents: Vec<String>,
        prefix: String,
    },
    /// A name in the brace list, e.g. `import math.{ a, |` -> module `["math"]`.
    Names { module: Vec<String>, prefix: String },
}

/// Recognise an import statement from the line text up to the cursor and decide
/// what is being completed. Returns `None` when the line is not an import.
fn import_context(line_prefix: &str) -> Option<ImportContext> {
    let trimmed = line_prefix.trim_start();
    let rest = trimmed.strip_prefix("import")?;
    // Require whitespace after the keyword, so `important` is not an import.
    if !rest.starts_with(char::is_whitespace) {
        return None;
    }
    let spec = rest.trim_start();

    if let Some((before, after)) = spec.split_once('{') {
        // Inside the brace list: the module path precedes `{`, the current name
        // is the text after the last comma.
        let module = split_path(before.trim().trim_end_matches('.'));
        let prefix = after.rsplit(',').next().unwrap_or("").trim().to_string();
        return Some(ImportContext::Names { module, prefix });
    }

    // A dotted path: the final (possibly empty) segment is what is being typed,
    // the earlier segments are its confirmed parents.
    let mut segments = split_path(spec);
    let prefix = segments.pop().unwrap_or_default();
    Some(ImportContext::Path {
        parents: segments,
        prefix,
    })
}

/// Split a dotted path into segments, dropping empty leading/trailing pieces
/// except a trailing empty segment (which means "completing a fresh segment").
fn split_path(s: &str) -> Vec<String> {
    if s.is_empty() {
        return Vec::new();
    }
    s.split('.').map(|p| p.trim().to_string()).collect()
}

/// Module path segment candidates under `parents`. At the root: the embedded
/// core modules, the `core` namespace, the declared package names, and the
/// modules next to the document or under an include path. Under `core`: the
/// embedded core modules. Anywhere else: the next path segments served by the
/// same roots the loader would search -- a declared package's directory when
/// the first segment names one, otherwise the document's directory and each
/// include path.
fn import_path_items(
    parents: &[String],
    prefix: &str,
    doc_path: &Path,
    search: &SearchPaths,
) -> Vec<CompletionItem> {
    let mut names: Vec<String> = Vec::new();
    if parents.is_empty() {
        names.extend(prelude_module_names().map(String::from));
        names.push("core".to_string());
        names.extend(search.packages.keys().cloned());
        // Exclude the current file so it does not suggest importing itself.
        let self_stem = doc_path.file_stem().and_then(|s| s.to_str());
        names.extend(dir_module_names(&doc_dir(doc_path), self_stem));
        for include in &search.includes {
            names.extend(dir_module_names(include, None));
        }
    } else if parents.first().is_some_and(|s| s == "core") {
        names.extend(core_segments(&parents[1..]));
    } else {
        for root in module_roots(doc_path, search, &parents[0]) {
            let mut dir = root;
            for seg in parents {
                dir.push(seg);
            }
            names.extend(dir_module_names(&dir, None));
        }
    }

    let mut seen = HashSet::new();
    names
        .into_iter()
        .filter(|n| n.starts_with(prefix) && seen.insert(n.clone()))
        .map(|n| item(n, CompletionItemKind::MODULE, None))
        .collect()
}

/// The directories a non-`core` module path is served from, mirroring the
/// loader: a path whose first segment names a declared package resolves only
/// under that package's directory; anything else searches the document's
/// directory first, then each include path.
fn module_roots(
    doc_path: &Path,
    search: &SearchPaths,
    first_segment: &str,
) -> Vec<std::path::PathBuf> {
    if let Some(pkg_root) = search.packages.get(first_segment) {
        return vec![pkg_root.clone()];
    }
    let mut roots = vec![doc_dir(doc_path)];
    roots.extend(search.includes.iter().cloned());
    roots
}

/// The next path segments of the embedded core modules under `parents` (the
/// segments after `core`): `[]` offers every top-level module (`io`,
/// `collections`, ...); a deeper prefix offers what sits below it.
fn core_segments(parents: &[String]) -> Vec<String> {
    let mut names = Vec::new();
    for (key, _) in brass_resolve::STDLIB {
        let segs: Vec<&str> = key.split('/').collect();
        if segs.len() > parents.len() && segs[..parents.len()].iter().eq(parents.iter()) {
            names.push(segs[parents.len()].to_string());
        }
    }
    names
}

/// The public names exported by the module the import path names, for the
/// brace list. The module is analyzed through the document's module graph
/// (a probe source importing it), so the items carry resolved signatures and
/// doc comments; when that finds nothing (e.g. the graph's environment lacks
/// a root the caller supplied), the module's source is located through
/// `search` and its top-level names are listed textually.
fn import_name_items(
    module: &[String],
    prefix: &str,
    analyzer: &DocAnalyzer,
    doc_path: &Path,
    search: &SearchPaths,
) -> Vec<CompletionItem> {
    let mut items = analyzed_module_exports(module, analyzer);
    if items.is_empty() {
        items = module_public_symbols(module, doc_path, search)
            .into_iter()
            .map(|(name, kind)| item(name, kind, None))
            .collect();
    }
    filter_prefix(items, prefix)
}

/// Enumerate a module's public exports from a full analysis of a probe source
/// that imports it -- the same module graph the document's analysis uses, so
/// core, disk, include-path, and plugin modules all resolve.
/// Signatures and docs come from the checked program.
fn analyzed_module_exports(module: &[String], analyzer: &DocAnalyzer) -> Vec<CompletionItem> {
    if module.is_empty() {
        return Vec::new();
    }
    let probe = format!("import {}\n", module.join("."));
    let Some(full) = analyzer.analyze_full(&probe) else {
        return Vec::new();
    };
    // The probe's import path was canonicalized by the loader; a bare core
    // module (`import math`) keeps its written path but is stored under
    // `core.<name>`.
    let Some(imp) = full.main_ast.imports.first() else {
        return Vec::new();
    };
    let target = brass_resolve::qualified_core_path(&imp.path);

    let mut items = Vec::new();
    for f in full.program.functions.values() {
        // A class-qualified name (`fun string.split` stored as `string.split`)
        // is a primitive method, not an importable bare name.
        if f.module == target
            && brass_resolve::is_public(&f.signature.name)
            && !f.signature.name.contains('.')
        {
            items.push(doc_item(
                f.signature.name.clone(),
                CompletionItemKind::FUNCTION,
                Some(render_signature(&f.signature)),
                f.decl.doc.as_deref(),
            ));
        }
    }
    for t in full.program.types.values() {
        if t.module == target && brass_resolve::is_public(&t.name) {
            let kind = match t.kind {
                TypeKind::Record { .. } => CompletionItemKind::STRUCT,
                TypeKind::Sum { .. } => CompletionItemKind::ENUM,
            };
            items.push(doc_item(
                t.name.clone(),
                kind,
                Some(format!("type {}", t.name)),
                t.doc.as_deref(),
            ));
        }
    }
    items
}

/// The public top-level (name, kind) pairs a module exports, parsed from its
/// source text. The textual fallback for [`import_name_items`]: core modules
/// read from the embedded sources, everything else is located through the
/// loader's search roots.
fn module_public_symbols(
    module: &[String],
    doc_path: &Path,
    search: &SearchPaths,
) -> Vec<(String, CompletionItemKind)> {
    let src = match module {
        [single] if prelude_source(single).is_some() => prelude_source(single).map(String::from),
        [s, rest @ ..] if s == "core" => prelude_source(&rest.join("/")).map(String::from),
        _ => brass_resolve::module_source(&doc_dir(doc_path), search, module),
    };
    let Some(src) = src else {
        return Vec::new();
    };
    let Ok(parsed) = parse(&src) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for top in &parsed.items {
        match top {
            TopLevel::Fun(f) if brass_resolve::is_public(&f.name) => {
                out.push((f.name.clone(), CompletionItemKind::FUNCTION));
            }
            TopLevel::Type(t) if brass_resolve::is_public(&t.name) => {
                out.push((t.name.clone(), type_decl_kind(&t.body)));
            }
            _ => {}
        }
    }
    out
}

/// `.cz` file stems and subdirectory names directly under `dir`, as importable
/// module segments, omitting `exclude` (the current file's stem, to avoid a
/// self-import). Errors (missing directory, or no filesystem on wasm) yield
/// nothing.
fn dir_module_names(dir: &Path, exclude: Option<&str>) -> Vec<String> {
    let mut names = Vec::new();
    let Ok(entries) = std::fs::read_dir(dir) else {
        return names;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if let Some(name) = path.file_name().and_then(|s| s.to_str()) {
                names.push(name.to_string());
            }
        } else if path.extension().and_then(|s| s.to_str()) == Some("cz")
            && let Some(stem) = path.file_stem().and_then(|s| s.to_str())
            && Some(stem) != exclude
        {
            names.push(stem.to_string());
        } else if path.extension().and_then(|s| s.to_str()) == Some(std::env::consts::DLL_EXTENSION)
            && let Some(stem) = path.file_stem().and_then(|s| s.to_str())
        {
            // A native plugin library is importable by its module name: the
            // file stem, minus the platform `lib` prefix a cdylib build adds.
            let name = stem
                .strip_prefix(std::env::consts::DLL_PREFIX)
                .filter(|s| !s.is_empty())
                .unwrap_or(stem);
            names.push(name.to_string());
        }
    }
    names
}

// ===== member completion =====

/// Identifier spliced in after a dangling `.` so the source parses and the
/// receiver's type can be recovered. Unlikely to collide with a real name.
const PROBE: &str = "__brass_completion_probe__";

/// Member completion for a cursor right after `recv.` (or `recv.partial`).
/// Returns `None` when the cursor is not in a member-access position, and
/// `Some(items)` (possibly empty) when it is -- so the caller does not fall back
/// to the global symbol list after a `.`.
fn member_completion(
    doc: &Document,
    analyzer: &DocAnalyzer,
    cursor: usize,
) -> Option<Vec<CompletionItem>> {
    let bytes = doc.text.as_bytes();
    // The current partial member name `[word_start, cursor)`.
    let mut word_start = cursor;
    while word_start > 0 && is_ident_byte(bytes[word_start - 1]) {
        word_start -= 1;
    }
    // A `.` must sit immediately before the name, and the receiver before that
    // `.` must look like the end of an expression (not e.g. a float `3.`).
    if word_start == 0 || bytes[word_start - 1] != b'.' {
        return None;
    }
    let dot = word_start - 1;
    match dot.checked_sub(1).map(|i| bytes[i]) {
        Some(b) if is_ident_byte(b) || b == b')' || b == b']' => {}
        _ => return None,
    }
    let partial = &doc.text[word_start..cursor];
    // `_`-prefixed members are implementation details, hidden unless the user
    // is explicitly typing such a name.
    let include_private = partial.starts_with('_');

    // `recv.` does not parse, so splice in a probe identifier; `recv.partial`
    // already parses as a field access.
    let full = if partial.is_empty() {
        let patched = format!("{}{PROBE}{}", &doc.text[..cursor], &doc.text[cursor..]);
        analyzer.analyze_full(&patched)?
    } else {
        analyzer.analyze_full(&doc.text)?
    };

    // A bare type name receiver (`Shape.`) offers that type's variants/methods.
    if let Some(items) = type_qualified_items(&full, &doc.text, dot, include_private) {
        return Some(filter_prefix(items, partial));
    }
    // Otherwise a value receiver: its members come from its inferred type, found
    // as the expression that ends exactly at the `.`.
    let recv_hi = full.main_base + dot;
    let items = match receiver_type_at(&full, recv_hi) {
        Some(ty) => value_member_items(&full, &ty, include_private),
        None => Vec::new(),
    };
    Some(filter_prefix(items, partial))
}

/// The inferred type of the receiver expression ending at global offset `hi`
/// (just before the `.`); the widest such expression, so `foo.bar.|` uses
/// `foo.bar` rather than `bar`.
fn receiver_type_at(full: &FullAnalysis, hi: usize) -> Option<Type> {
    full.typed
        .expressions
        .iter()
        .filter(|e| e.span.hi == hi)
        .min_by_key(|e| e.span.lo)
        .map(|e| e.ty.clone())
}

/// Members reachable on a value of `ty`: a record type's fields and methods,
/// built-in methods for its kind, and the stdlib methods implemented on a
/// primitive/array receiver (`fun string.split`, `fun infer[].map`). There is
/// no UFCS, so a plain free function is not a member. `_`-prefixed members are
/// omitted unless `include_private` (the user typed the `_` themselves).
fn value_member_items(
    full: &FullAnalysis,
    ty: &Type,
    include_private: bool,
) -> Vec<CompletionItem> {
    let base = strip(ty);
    let mut items = Vec::new();

    match &base {
        Type::Slice(_) => {
            for m in ["push", "pop", "insert", "remove", "len"] {
                items.push(item(m.to_string(), CompletionItemKind::METHOD, None));
            }
        }
        Type::Array(_, _) | Type::Str => {
            items.push(item("len".to_string(), CompletionItemKind::METHOD, None));
        }
        _ => {}
    }

    // A nominal receiver -- record OR sum. A record also offers its fields; a
    // sum's payloads are only reachable by matching, so it offers methods alone.
    if let Type::Record(n) | Type::Sum(n) = &base
        && let Some(info) = full.program.type_by_id(n.id)
    {
        if let TypeKind::Record { fields, .. } = &info.kind {
            // Fields, typed for this instance: the receiver's substitution carries
            // the concrete type an open (inferred/slot-dependent) field was pinned
            // to; a still-open slot variable renders as `Self.<slot>`.
            let mut namer = UnknownNamer::default();
            for (slot, var) in &info.slots {
                namer.fix(*var, format!("Self.{slot}"));
            }
            for f in fields {
                if !include_private && !is_public_member(&f.name) {
                    continue;
                }
                let resolved = n.substitution.get(&f.name).or(f.resolved_ty.as_ref());
                let detail =
                    resolved.map(|t| format!("{}: {}", f.name, render_type(t, &mut namer)));
                items.push(item(f.name.clone(), CompletionItemKind::FIELD, detail));
            }
        }
        items.extend(type_method_items(
            full,
            info,
            &n.substitution,
            include_private,
            MethodKind::Instance,
        ));
    }

    // Stdlib methods on this receiver's primitive/array class, dispatched by
    // class through `primitive_methods` (their bodies live under a class-qualified
    // symbol in `functions`).
    if let Some(class) = base.primitive_class() {
        for ((c, name), symbol) in &full.program.primitive_methods {
            if c == class {
                let f = full.program.functions.get(symbol);
                items.push(doc_item(
                    name.clone(),
                    CompletionItemKind::METHOD,
                    f.map(|f| render_signature(&f.signature)),
                    f.and_then(|f| f.decl.doc.as_deref()),
                ));
            }
        }
    }

    dedup_by_label(items)
}

/// Which methods a position can actually call. A value receiver (`v.`) reaches
/// only the methods that take a `self`; a type name (`Shape.`) reaches only the
/// statics, since there is no receiver to bind `self` to.
#[derive(Clone, Copy, PartialEq)]
enum MethodKind {
    Instance,
    Static,
}

impl MethodKind {
    fn matches(self, m: &brass_hir::MethodInfo) -> bool {
        let has_self = m.signature.params.first().is_some_and(|p| p.name == "self");
        match self {
            MethodKind::Instance => has_self,
            MethodKind::Static => !has_self,
        }
    }
}

/// Completion items for a type's methods of the requested kind, with each
/// signature resolved against `substitution` through the type's scheme (see
/// [`typedef_method_signatures`]) -- so a `HashMap<string, int32>` receiver shows
/// `get` returning `int32?` rather than an open variable.
///
/// Both kinds of nominal are served. A SUM's methods are not in a method map of
/// its own: lowering copies each `fun Shape.m` into EVERY variant's table, so
/// they are reached through the variants (any one of them answers -- they hold
/// the same declarations). Looking only at records left a sum value with no
/// members at all.
fn type_method_items(
    full: &FullAnalysis,
    info: &TypeInfo,
    substitution: &brass_hir::Substitution,
    include_private: bool,
    want: MethodKind,
) -> Vec<CompletionItem> {
    let resolved = typedef_method_signatures(full, info, substitution);
    let mut items = Vec::new();
    let mut push = |name: &String, m: &brass_hir::MethodInfo| {
        if !include_private && !is_public_member(name) {
            return;
        }
        if !want.matches(m) {
            return;
        }
        let sig = resolved.get(name).unwrap_or(&m.signature);
        items.push(doc_item(
            name.clone(),
            CompletionItemKind::METHOD,
            Some(render_signature(sig)),
            m.decl.doc.as_deref(),
        ));
    };
    match &info.kind {
        TypeKind::Record { methods, .. } => {
            for (name, m) in methods {
                push(name, m);
            }
        }
        TypeKind::Sum { variants } => {
            for v in variants {
                for (name, m) in &v.methods {
                    push(name, m);
                }
            }
        }
    }
    dedup_by_label(items)
}

/// When the text before the `.` at `dot` is a standalone identifier naming a
/// type, the members are what that name can be qualified with: a sum's variants
/// (`Shape.Circle { .. }`) and, for either kind of nominal, its STATIC methods
/// (`TomlValue.parse(..)`, `Point.origin()`). An instance method is not offered
/// here -- there is no receiver to bind its `self` to, so it is not callable.
fn type_qualified_items(
    full: &FullAnalysis,
    text: &str,
    dot: usize,
    include_private: bool,
) -> Option<Vec<CompletionItem>> {
    let bytes = text.as_bytes();
    let mut start = dot;
    while start > 0 && is_ident_byte(bytes[start - 1]) {
        start -= 1;
    }
    // The receiver must be a lone identifier, not part of a longer chain.
    if start == dot {
        return None;
    }
    if let Some(prev) = start.checked_sub(1) {
        let b = bytes[prev];
        if is_ident_byte(b) || b == b'.' || b == b')' || b == b']' {
            return None;
        }
    }
    let name = &text[start..dot];
    let info = full.program.resolve_type(&["main".to_string()], name)?;
    let mut items = Vec::new();
    if let TypeKind::Sum { variants } = &info.kind {
        for v in variants {
            if !include_private && !is_public_member(&v.name) {
                continue;
            }
            items.push(item(v.name.clone(), CompletionItemKind::ENUM_MEMBER, None));
        }
    }
    // The declaration view: no instance, so an empty substitution shows signatures
    // over the declaration's own slots (`Self.<slot>`).
    let empty = brass_hir::Substitution::empty();
    items.extend(type_method_items(
        full,
        info,
        &empty,
        include_private,
        MethodKind::Static,
    ));
    Some(items)
}

/// Strip transparent wrappers so a nullable/const/mut receiver still resolves to
/// its underlying type for member lookup.
fn strip(ty: &Type) -> Type {
    match ty {
        Type::Nullable(inner) | Type::ConstOf(inner) | Type::Mut(inner) | Type::Ref(inner) => {
            strip(inner)
        }
        other => other.clone(),
    }
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn filter_prefix(items: Vec<CompletionItem>, prefix: &str) -> Vec<CompletionItem> {
    if prefix.is_empty() {
        return items;
    }
    items
        .into_iter()
        .filter(|i| i.label.starts_with(prefix))
        .collect()
}

fn dedup_by_label(mut items: Vec<CompletionItem>) -> Vec<CompletionItem> {
    let mut seen = HashSet::new();
    items.retain(|i| seen.insert(i.label.clone()));
    items
}

// ===== type / function completion =====

/// Types and functions visible from the document, plus the built-in types and
/// intrinsic functions. From the analyzed program when available, else a
/// best-effort set parsed from the document and prelude.
fn symbol_items(analyzer: &DocAnalyzer, doc: &Document, doc_path: &Path) -> Vec<CompletionItem> {
    let mut items = match analyzer.analyze_full(&doc.text) {
        Some(f) => program_symbols(&f),
        None => fallback_symbols(doc, doc_path),
    };
    for ty in BUILTIN_TYPES {
        items.push(item((*ty).to_string(), CompletionItemKind::STRUCT, None));
    }
    for f in BUILTIN_FUNCTIONS {
        items.push(item((*f).to_string(), CompletionItemKind::FUNCTION, None));
    }

    let mut seen = HashSet::new();
    items.retain(|i| seen.insert(i.label.clone()));
    items
}

/// Visible symbols taken from the analyzed program: every function and type
/// whose defining module is reachable from `main` (its own module, the empty
/// built-in module, the `core` prelude, or an imported name).
fn program_symbols(full: &FullAnalysis) -> Vec<CompletionItem> {
    let main_module = vec!["main".to_string()];
    let imported = full
        .program
        .module_imports
        .get(&main_module)
        .cloned()
        .unwrap_or_default();
    let visible = |module: &[String], name: &str| {
        module.is_empty()
            || module == main_module.as_slice()
            || full.program.prelude_modules.contains(module)
            || imported.iter().any(|n| n == name)
    };

    let mut items = Vec::new();
    for f in full.program.functions.values() {
        if visible(&f.module, &f.signature.name) {
            items.push(doc_item(
                f.signature.name.clone(),
                CompletionItemKind::FUNCTION,
                Some(render_signature(&f.signature)),
                f.decl.doc.as_deref(),
            ));
        }
    }
    for t in full.program.types.values() {
        if visible(&t.module, &t.name) {
            let kind = match t.kind {
                TypeKind::Record { .. } => CompletionItemKind::STRUCT,
                TypeKind::Sum { .. } => CompletionItemKind::ENUM,
            };
            items.push(doc_item(
                t.name.clone(),
                kind,
                Some(format!("type {}", t.name)),
                t.doc.as_deref(),
            ));
        }
    }
    items
}

/// Best-effort symbols when the document does not parse: its own top-level
/// declarations (if it parses) and every prelude module's public names.
fn fallback_symbols(doc: &Document, _doc_path: &Path) -> Vec<CompletionItem> {
    let mut items = Vec::new();
    if let Ok(parsed) = parse(&doc.text) {
        for top in &parsed.items {
            match top {
                TopLevel::Fun(f) => {
                    items.push(item(f.name.clone(), CompletionItemKind::FUNCTION, None));
                }
                TopLevel::Type(t) => {
                    items.push(item(t.name.clone(), type_decl_kind(&t.body), None));
                }
                _ => {}
            }
        }
    }
    for name in prelude_module_names() {
        if let Some(src) = prelude_source(name) {
            for (n, kind) in module_public_symbols_from_src(src) {
                items.push(item(n, kind, None));
            }
        }
    }
    items
}

fn module_public_symbols_from_src(src: &str) -> Vec<(String, CompletionItemKind)> {
    let Ok(parsed) = parse(src) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for top in &parsed.items {
        match top {
            TopLevel::Fun(f) if brass_resolve::is_public(&f.name) => {
                out.push((f.name.clone(), CompletionItemKind::FUNCTION));
            }
            TopLevel::Type(t) if brass_resolve::is_public(&t.name) => {
                out.push((t.name.clone(), type_decl_kind(&t.body)));
            }
            _ => {}
        }
    }
    out
}

fn type_decl_kind(body: &TypeBody) -> CompletionItemKind {
    match body {
        TypeBody::Record(_) => CompletionItemKind::STRUCT,
        TypeBody::Sum(_) => CompletionItemKind::ENUM,
        // An alias resolves to a refined record; present it as a struct.
        TypeBody::Alias(_) => CompletionItemKind::STRUCT,
    }
}

// ===== helpers =====

fn doc_dir(doc_path: &Path) -> std::path::PathBuf {
    doc_path
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| std::path::PathBuf::from("."))
}

fn item(label: String, kind: CompletionItemKind, detail: Option<String>) -> CompletionItem {
    CompletionItem {
        label,
        kind: Some(kind),
        detail,
        ..Default::default()
    }
}

/// [`item`] plus the declaration's doc comment, rendered as markdown in the
/// completion detail popup.
fn doc_item(
    label: String,
    kind: CompletionItemKind,
    detail: Option<String>,
    doc: Option<&str>,
) -> CompletionItem {
    use tower_lsp_server::ls_types::{Documentation, MarkupContent, MarkupKind};
    let mut it = item(label, kind, detail);
    it.documentation = doc.map(|d| {
        Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: d.to_string(),
        })
    });
    it
}
