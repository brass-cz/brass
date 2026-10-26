//! Source positions needed by implicit locations and lifted Result errors.

use brass_hir::LoadedModule;
use brass_parser::Span;
use brass_parser::ast::{Member, Stmt, TypeBody};
use fxhash::FxHashMap as HashMap;

#[cfg(test)]
mod tests;

/// Whether the checked result will supply source positions to execution.
#[derive(Clone, Copy)]
pub(super) enum LocationTables {
    /// Preserve all location metadata consumed by MIR and the interpreter.
    Execution,
    /// Skip execution metadata when only checking or streaming channels.
    Omit,
}

/// Map calls, constructions, propagations, and returned expressions to source
/// positions (diagnostic label, 1-based line and column). MIR uses these for
/// implicit `Location` arguments and newly lifted errors; collecting them here
/// keeps source access out of lowering.
pub(super) fn call_site_locations(
    modules: &[LoadedModule],
    sources: &brass_resolve::SourceMap,
    search: &brass_resolve::SearchPaths,
) -> HashMap<Span, (String, u32, u32)> {
    let started = std::time::Instant::now();
    let mut spans: Vec<Span> = Vec::new();
    for m in modules {
        for item in &m.ast.items {
            match item {
                brass_parser::ast::TopLevel::Fun(f) => {
                    collect_spans_block(&f.body, &mut spans, true)
                }
                brass_parser::ast::TopLevel::Stmt(st) => collect_spans_stmt(st, &mut spans, true),
                brass_parser::ast::TopLevel::Type(t) => {
                    let collect_member = |member: &Member, spans: &mut Vec<Span>| {
                        if let Member::Method(method) = member
                            && let Some(body) = &method.body
                        {
                            collect_spans_block(body, spans, true);
                        }
                    };
                    match &t.body {
                        TypeBody::Record(members) => {
                            members.iter().for_each(|m| collect_member(m, &mut spans))
                        }
                        TypeBody::Sum(variants) => variants
                            .iter()
                            .flat_map(|v| &v.members)
                            .for_each(|m| collect_member(m, &mut spans)),
                        TypeBody::Alias(_) => {}
                    }
                }
            }
        }
    }
    // Labels are relativized against the working directory and the include
    // roots' parents, so a baked expectation (an e2e `.out`) does not embed a
    // machine-specific absolute path.
    let mut prefixes: Vec<String> = Vec::new();
    if let Ok(cwd) = std::env::current_dir()
        && let Ok(c) = cwd.canonicalize()
    {
        prefixes.push(format!("{}/", c.display()));
    }
    for root in &search.includes {
        if let Ok(c) = root.canonicalize()
            && let Some(parent) = c.parent()
        {
            prefixes.push(format!("{}/", parent.display()));
        }
    }
    // A package root serves modules under `<root>/<name>/...`, so the root
    // itself is the prefix to strip (`std=/toolchain` renders the standard
    // library as `std/fs.cz`).
    for root in search.packages.values() {
        if let Ok(c) = root.canonicalize() {
            prefixes.push(format!("{}/", c.display()));
        }
    }
    let plugin_labels: Vec<(String, String)> = sources
        .plugins()
        .map(|(module, library)| {
            let library = library
                .canonicalize()
                .unwrap_or_else(|_| library.to_path_buf())
                .display()
                .to_string();
            (library, format!("<plugin:{}>", module.join(".")))
        })
        .collect();
    let relativize = |label: &str| -> String {
        // Canonicalize the label's path first (a plugin label wraps one), so
        // the caller's spelling (`../../x.cz`) does not leak into the
        // recorded position.
        let mut label = if let Some(inner) = label
            .strip_prefix("<plugin:")
            .and_then(|r| r.strip_suffix('>'))
        {
            match std::fs::canonicalize(inner) {
                Ok(c) => {
                    let path = c.display().to_string();
                    plugin_labels
                        .iter()
                        .find_map(|(library, label)| (library == &path).then(|| label.clone()))
                        .unwrap_or_else(|| format!("<plugin:{path}>"))
                }
                Err(_) => label.to_string(),
            }
        } else {
            match std::fs::canonicalize(label) {
                Ok(c) => c.display().to_string(),
                Err(_) => label.to_string(),
            }
        };
        for p in &prefixes {
            label = label.replace(p.as_str(), "");
        }
        label
    };
    let mut labels = HashMap::default();
    let mut out = HashMap::default();
    for span in spans {
        if let Some(loc) = sources.locate(span.lo) {
            let (line, col) = loc.line_col();
            // Each source's first resolution is the label snapshot for this
            // table build. Raw diagnostic labels remain in the source map.
            let label = labels
                .entry(span.lo - loc.local)
                .or_insert_with(|| relativize(loc.label));
            out.insert(span, (label.clone(), line as u32, col as u32));
        }
    }
    brass_utils::perf_phase("front/source-locations", started.elapsed());
    out
}

/// Collect call-related spans for provisional keyed diagnostics. Returned values
/// contribute only their nested call-related spans, not their own extent.
pub(super) fn collect_call_spans_stmt(stmt: &Stmt, out: &mut Vec<Span>) {
    collect_spans_stmt(stmt, out, false);
}

fn collect_spans_block(b: &brass_parser::ast::Block, out: &mut Vec<Span>, include_returns: bool) {
    for s in &b.stmts {
        collect_spans_stmt(s, out, include_returns);
    }
}

fn collect_spans_stmt(s: &Stmt, out: &mut Vec<Span>, include_returns: bool) {
    match s {
        Stmt::Let { value: Some(v), .. } => collect_spans_expr(v, out, include_returns),
        Stmt::Assign { target, value, .. } => {
            collect_spans_expr(target, out, include_returns);
            collect_spans_expr(value, out, include_returns);
        }
        Stmt::Return(Some(e), _) => {
            if include_returns {
                out.push(e.span());
            }
            collect_spans_expr(e, out, include_returns);
        }
        Stmt::Expr(e) => collect_spans_expr(e, out, include_returns),
        Stmt::While { cond, body, .. } => {
            collect_spans_expr(cond, out, include_returns);
            collect_spans_block(body, out, include_returns);
        }
        Stmt::For { iter, body, .. } => {
            collect_spans_expr(iter, out, include_returns);
            collect_spans_block(body, out, include_returns);
        }
        _ => {}
    }
}

fn collect_spans_expr(e: &brass_parser::ast::Expr, out: &mut Vec<Span>, include_returns: bool) {
    use brass_parser::ast::{Expr, StrSeg};
    match e {
        Expr::Call(callee, args, span) => {
            out.push(*span);
            collect_spans_expr(callee, out, include_returns);
            for a in args {
                collect_spans_expr(&a.expr, out, include_returns);
            }
        }
        Expr::Field(b, _, _) | Expr::Unary(_, b, _) => collect_spans_expr(b, out, include_returns),
        // `!` sites need positions too: a lifted propagation stamps its own.
        Expr::ErrorProp(b, span) => {
            out.push(*span);
            collect_spans_expr(b, out, include_returns);
        }
        Expr::Binary(_, l, r, _) | Expr::Index(l, r, _) | Expr::Range(l, r, _) => {
            collect_spans_expr(l, out, include_returns);
            collect_spans_expr(r, out, include_returns);
        }
        Expr::Array(es, _) => es
            .iter()
            .for_each(|e| collect_spans_expr(e, out, include_returns)),
        // Construction spans are collected too: a lifted forwarded return
        // stamps the construction's own position into the wrapped Error.
        Expr::TypeLit(_, fs, span) | Expr::VariantLit(_, _, fs, span) => {
            out.push(*span);
            fs.iter()
                .for_each(|(_, e)| collect_spans_expr(e, out, include_returns))
        }
        Expr::Str(segs, _) => segs.iter().for_each(|seg| {
            if let StrSeg::Expr(e) = seg {
                collect_spans_expr(e, out, include_returns);
            }
        }),
        Expr::If(c, t, els, _) => {
            collect_spans_expr(c, out, include_returns);
            collect_spans_block(t, out, include_returns);
            if let Some(e) = els {
                collect_spans_expr(e, out, include_returns);
            }
        }
        Expr::IfLet(_, scrut, t, els, _) => {
            collect_spans_expr(scrut, out, include_returns);
            collect_spans_block(t, out, include_returns);
            if let Some(e) = els {
                collect_spans_expr(e, out, include_returns);
            }
        }
        Expr::Match(scrut, arms, _) => {
            collect_spans_expr(scrut, out, include_returns);
            for arm in arms {
                collect_spans_expr(&arm.body, out, include_returns);
            }
        }
        Expr::Block(b, _) => collect_spans_block(b, out, include_returns),
        Expr::Closure(_, b, _) => collect_spans_expr(b, out, include_returns),
        Expr::TypeTest(subject, _, _, _) if include_returns => {
            collect_spans_expr(subject, out, include_returns)
        }
        _ => {}
    }
}
