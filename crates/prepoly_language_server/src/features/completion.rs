//! Completion.
//!
//! Three contexts are handled. Inside an `import` statement the cursor is offered
//! module path segments (`import math.|`) and, within the brace list, the public
//! names a module exports (`import math.{ |`); these are recovered textually
//! from the current line, so they work even while the line does not yet parse.
//! After a `.` (`a.|`) the cursor is offered the members reachable on the
//! receiver -- built-in methods, the receiver type's record methods, and the
//! free functions callable on it through UFCS -- or, when the receiver is a type
//! name (`Shape.|`), that type's variants and methods. Everywhere else the
//! cursor is offered the types and functions visible from the document.
//!
//! The member case needs the receiver's inferred type, but `a.` does not parse,
//! so the source is re-analyzed with a probe identifier spliced in at the cursor
//! to recover the type. Analysis therefore happens inside this module (via the
//! document's analyzer) rather than being passed in.

use std::collections::HashSet;
use std::path::Path;

use prepoly_hir::{Type, TypeKind};
use prepoly_parser::ast::{TopLevel, TypeBody};
use prepoly_parser::parse;
use tower_lsp_server::ls_types::{CompletionItem, CompletionItemKind};

use crate::analysis::world::{prelude_module_names, prelude_source};
use crate::analysis::{DocAnalyzer, FullAnalysis};
use crate::document::Document;
use crate::render::render_signature;

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
pub fn completion(
    doc: &Document,
    analyzer: &DocAnalyzer,
    doc_path: &Path,
    pos: tower_lsp_server::ls_types::Position,
) -> Vec<CompletionItem> {
    let offset = doc.offset_at(pos);
    let line_start = doc.text[..offset].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let prefix = &doc.text[line_start..offset];

    if let Some(ctx) = import_context(prefix) {
        return match ctx {
            ImportContext::Names { module, prefix } => {
                import_name_items(&module, &prefix, doc_path)
            }
            ImportContext::Path { parents, prefix } => {
                import_path_items(&parents, &prefix, doc_path)
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

/// Module path segment candidates under `parents`: the prelude modules and the
/// `std` namespace at the root, plus `.pp` files and directories on disk.
fn import_path_items(parents: &[String], prefix: &str, doc_path: &Path) -> Vec<CompletionItem> {
    let mut names: Vec<String> = Vec::new();
    if parents.is_empty() {
        names.extend(prelude_module_names().map(String::from));
        names.push("std".to_string());
        // Exclude the current file so it does not suggest importing itself.
        let self_stem = doc_path.file_stem().and_then(|s| s.to_str());
        names.extend(dir_module_names(&doc_dir(doc_path), self_stem));
    } else if parents == ["std"] {
        names.extend(prelude_module_names().map(String::from));
    } else {
        let mut dir = doc_dir(doc_path);
        for seg in parents {
            dir.push(seg);
        }
        names.extend(dir_module_names(&dir, None));
    }

    let mut seen = HashSet::new();
    names
        .into_iter()
        .filter(|n| n.starts_with(prefix) && seen.insert(n.clone()))
        .map(|n| item(n, CompletionItemKind::MODULE, None))
        .collect()
}

/// The public names exported by the module the import path names, for the brace
/// list. Prelude modules read from the embedded source; others from disk.
fn import_name_items(module: &[String], prefix: &str, doc_path: &Path) -> Vec<CompletionItem> {
    module_public_symbols(module, doc_path)
        .into_iter()
        .filter(|(name, _)| name.starts_with(prefix))
        .map(|(name, kind)| item(name, kind, None))
        .collect()
}

/// The public top-level (name, kind) pairs a module exports.
fn module_public_symbols(module: &[String], doc_path: &Path) -> Vec<(String, CompletionItemKind)> {
    let src = match module {
        [single] if prelude_source(single).is_some() => prelude_source(single).map(String::from),
        [s, name] if s == "std" => prelude_source(name).map(String::from),
        _ => {
            let mut file = doc_dir(doc_path);
            for seg in module {
                file.push(seg);
            }
            file.set_extension("pp");
            std::fs::read_to_string(file).ok()
        }
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
            TopLevel::Fun(f) if prepoly_resolve::is_public(&f.name) => {
                out.push((f.name.clone(), CompletionItemKind::FUNCTION));
            }
            TopLevel::Type(t) if prepoly_resolve::is_public(&t.name) => {
                out.push((t.name.clone(), type_decl_kind(&t.body)));
            }
            _ => {}
        }
    }
    out
}

/// `.pp` file stems and subdirectory names directly under `dir`, as importable
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
        } else if path.extension().and_then(|s| s.to_str()) == Some("pp")
            && let Some(stem) = path.file_stem().and_then(|s| s.to_str())
            && Some(stem) != exclude
        {
            names.push(stem.to_string());
        }
    }
    names
}

// ===== member completion =====

/// Identifier spliced in after a dangling `.` so the source parses and the
/// receiver's type can be recovered. Unlikely to collide with a real name.
const PROBE: &str = "__prepoly_completion_probe__";

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

    // `recv.` does not parse, so splice in a probe identifier; `recv.partial`
    // already parses as a field access.
    let full = if partial.is_empty() {
        let patched = format!("{}{PROBE}{}", &doc.text[..cursor], &doc.text[cursor..]);
        analyzer.analyze_full(&patched)?
    } else {
        analyzer.analyze_full(&doc.text)?
    };

    // A bare type name receiver (`Shape.`) offers that type's variants/methods.
    if let Some(items) = type_qualified_items(&full, &doc.text, dot) {
        return Some(filter_prefix(items, partial));
    }
    // Otherwise a value receiver: its members come from its inferred type, found
    // as the expression that ends exactly at the `.`.
    let recv_hi = full.main_base + dot;
    let items = match receiver_type_at(&full, recv_hi) {
        Some(ty) => value_member_items(&full, &ty),
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

/// Members reachable on a value of `ty`: built-in methods for its kind, a record
/// type's own methods, and the stdlib methods implemented on a primitive/array
/// receiver (`fun string.split`, `fun infer[].map`). There is no UFCS, so a plain
/// free function is not a member.
fn value_member_items(full: &FullAnalysis, ty: &Type) -> Vec<CompletionItem> {
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

    if let Some(id) = nominal_id(&base)
        && let Some(info) = full.program.type_by_id(id)
        && let TypeKind::Record { methods, .. } = &info.kind
    {
        for (name, m) in methods {
            items.push(doc_item(
                name.clone(),
                CompletionItemKind::METHOD,
                Some(render_signature(&m.signature)),
                m.decl.doc.as_deref(),
            ));
        }
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

/// When the text before the `.` at `dot` is a standalone identifier naming a
/// type, the members are that type's variants (sum) or methods (record).
fn type_qualified_items(
    full: &FullAnalysis,
    text: &str,
    dot: usize,
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
    match &info.kind {
        TypeKind::Sum { variants } => {
            for v in variants {
                items.push(item(v.name.clone(), CompletionItemKind::ENUM_MEMBER, None));
            }
        }
        TypeKind::Record { methods, .. } => {
            for (n, m) in methods {
                items.push(doc_item(
                    n.clone(),
                    CompletionItemKind::METHOD,
                    Some(render_signature(&m.signature)),
                    m.decl.doc.as_deref(),
                ));
            }
        }
    }
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

fn nominal_id(ty: &Type) -> Option<i32> {
    match ty {
        Type::Record(n) | Type::Sum(n) => Some(n.id),
        _ => None,
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
/// built-in module, the `std` prelude, or an imported name).
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
            TopLevel::Fun(f) if prepoly_resolve::is_public(&f.name) => {
                out.push((f.name.clone(), CompletionItemKind::FUNCTION));
            }
            TopLevel::Type(t) if prepoly_resolve::is_public(&t.name) => {
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
