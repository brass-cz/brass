//! Spawn shapes the ownership pass cannot make race-free, rejected over the
//! pristine tree before the rewrite: spawns in closures that are not themselves
//! spawned, spawned tasks touching written module globals, reassigned captures,
//! and spawns in module-level code.

use fxhash::FxHashSet as HashSet;

use brass_parser::Span;
use brass_parser::ast::*;

use super::SpawnError;
use super::analysis::{capture_scan, param_names};
use super::scopes::{LexicalScopes, lexical_scopes, nested_block_stmts};
use super::sites::{
    SpawnArg, closure_bindings_at, closure_bound_in, spawn_arg, spawn_closure_body,
    spawn_stmt_span, spawned_binding_spans, stmt_span,
};

/// Reject spawn shapes the ownership pass cannot make race-free, checked over
/// the PRISTINE tree before `auto_acquire` rewrites it:
///
/// - a `spawn` inside a closure literal that is not itself spawned: the pass
///   analyzes function bodies and spawned closures only, so such a spawn's
///   captures would get no promotion and no guarding at all;
/// - a spawned task touching a module global that is written anywhere in the
///   program: module storage has no binding to promote to a cown, so the task
///   and any writer would race unguarded. Never-written globals stay shareable;
/// - a spawned task assigning a captured variable as a whole (`n = 5`): the
///   task works on its own copy of the binding, so nothing would observe it.
pub fn pre_spawn_errors(
    stmts: &[Stmt],
    params: &HashSet<String>,
    mutated_globals: &HashSet<String>,
) -> Vec<SpawnError> {
    let mut errors = Vec::new();
    pre_scan_scope(stmts, params, mutated_globals, &mut errors);
    errors
}

fn pre_scan_scope(
    stmts: &[Stmt],
    in_scope: &HashSet<String>,
    mutated_globals: &HashSet<String>,
    errors: &mut Vec<SpawnError>,
) {
    let lexical = lexical_scopes(stmts, in_scope);
    let spawned = spawned_binding_spans(stmts);
    pre_scan_scope_stmts(stmts, stmts, &lexical, &spawned, mutated_globals, errors);
}

fn pre_scan_scope_stmts(
    stmts: &[Stmt],
    all: &[Stmt],
    lexical: &LexicalScopes,
    spawned: &HashSet<Span>,
    mutated_globals: &HashSet<String>,
    errors: &mut Vec<SpawnError>,
) {
    for stmt in stmts {
        match spawn_arg(stmt) {
            Some(SpawnArg::Literal) => {
                if let Some(body) = spawn_closure_body(stmt) {
                    let mut visible = lexical
                        .spawn_sites
                        .get(&spawn_stmt_span(stmt))
                        .cloned()
                        .unwrap_or_default();
                    visible.extend(closure_bound_in(stmt));
                    pre_check_spawn_body(&body, stmt.span(), &visible, mutated_globals, errors);
                }
                continue;
            }
            Some(SpawnArg::Var(name, _)) => {
                for binding in closure_bindings_at(all, spawn_stmt_span(stmt), name) {
                    let mut visible = lexical
                        .closure_bindings
                        .get(&binding.span)
                        .cloned()
                        .unwrap_or_default();
                    visible.extend(param_names(&binding.params));
                    pre_check_spawn_body(
                        &binding.body,
                        binding.span,
                        &visible,
                        mutated_globals,
                        errors,
                    );
                }
                continue;
            }
            // An opaque argument is reported by `auto_acquire` itself.
            Some(SpawnArg::Opaque(..)) => continue,
            None => {}
        }
        // A closure selected by an actual `spawn(name)` site is checked as a
        // spawn body, not as an ordinary closure.
        if spawned.contains(&stmt_span(stmt)) {
            continue;
        }
        nested_block_stmts(stmt, &mut |inner| {
            pre_scan_scope_stmts(inner, all, lexical, spawned, mutated_globals, errors)
        });
        each_stmt_expr(stmt, &mut |e| pre_check_plain_expr(e, errors));
    }
}

/// Check one spawned closure body: no writable-global captures and no
/// reassignment of a captured variable, then recurse into it as its own scope
/// (it may host nested spawns and plain closures).
fn pre_check_spawn_body(
    body: &Block,
    span: Span,
    enclosing_bound: &HashSet<String>,
    mutated_globals: &HashSet<String>,
    errors: &mut Vec<SpawnError>,
) {
    let cbound = HashSet::default();
    let scan = capture_scan(body, &cbound);
    let mut frees: Vec<String> = scan
        .free
        .into_iter()
        .filter(|n| !enclosing_bound.contains(n) && mutated_globals.contains(n))
        .collect();
    frees.sort();
    for name in frees {
        errors.push(SpawnError {
            message: format!(
                "spawned task accesses module global `{name}`, which is written \
                 elsewhere; share it through a local value captured by the task"
            ),
            span,
        });
    }
    // The task works on its own copy of a captured primitive and on the shared
    // object a captured heap binding refers to; assigning the captured
    // variable itself would only rebind the task's copy, which nothing reads.
    for (name, at) in scan.rebound {
        if enclosing_bound.contains(&name) {
            errors.push(SpawnError {
                message: format!(
                    "cannot reassign captured `{name}` inside `spawn`: the task works \
                     on a copy; mutate a shared object instead"
                ),
                span: at,
            });
        }
    }
    pre_scan_scope(&body.stmts, enclosing_bound, mutated_globals, errors);
}

/// A closure literal in a plain expression position (not a spawn argument or a
/// spawned variable's binding) must not contain a `spawn`: the pass never
/// analyzes such a body, so the spawn's captures would be entirely unguarded.
fn pre_check_plain_expr(e: &Expr, errors: &mut Vec<SpawnError>) {
    if let Expr::Closure(_, body, _) = e {
        let mut spans = Vec::new();
        collect_spawn_spans_expr(body, &mut spans);
        for span in spans {
            errors.push(SpawnError {
                message: "`spawn` inside a closure that is not itself spawned is not \
                          analyzable; spawn from the enclosing body or a named function"
                    .to_string(),
                span,
            });
        }
    }
}

/// Every direct subexpression of `stmt` (not descending into nested statement
/// blocks, which `nested_block_stmts` covers).
fn each_stmt_expr(stmt: &Stmt, f: &mut dyn FnMut(&Expr)) {
    match stmt {
        Stmt::Let {
            value: Some(value), ..
        } => each_expr(value, f),
        Stmt::Let { value: None, .. } => {}
        Stmt::Assign { target, value, .. } => {
            each_expr(target, f);
            each_expr(value, f);
        }
        Stmt::Expr(e) => each_expr(e, f),
        Stmt::While { cond, .. } => each_expr(cond, f),
        Stmt::For { iter, .. } => each_expr(iter, f),
        Stmt::Return(Some(e), _) => each_expr(e, f),
        _ => {}
    }
}

/// Apply `f` to `e` and every nested expression, without crossing into
/// statement blocks of control-flow expressions (covered by the statement
/// walk) but including closure literals themselves (`f` decides whether to
/// look inside).
fn each_expr(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    match e {
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) | Expr::Field(inner, _, _) => {
            each_expr(inner, f)
        }
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
            each_expr(a, f);
            each_expr(b, f);
        }
        Expr::Call(callee, args, _) => {
            each_expr(callee, f);
            for a in args {
                each_expr(&a.expr, f);
            }
        }
        Expr::Array(items, _) => {
            for i in items {
                each_expr(i, f);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, fe) in fields {
                each_expr(fe, f);
            }
        }
        Expr::Str(segs, _) => {
            for seg in segs {
                if let brass_parser::ast::StrSeg::Expr(inner) = seg {
                    each_expr(inner, f);
                }
            }
        }
        _ => {}
    }
}

/// Spans of every `spawn(..)` call reachable in `e`, including inside nested
/// closures and control-flow blocks.
fn collect_spawn_spans_expr(e: &Expr, out: &mut Vec<Span>) {
    if let Expr::Call(callee, _, span) = e
        && matches!(&**callee, Expr::Ident(n, _) if n == "spawn")
    {
        out.push(*span);
    }
    match e {
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) | Expr::Field(inner, _, _) => {
            collect_spawn_spans_expr(inner, out)
        }
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
            collect_spawn_spans_expr(a, out);
            collect_spawn_spans_expr(b, out);
        }
        Expr::Call(callee, args, _) => {
            collect_spawn_spans_expr(callee, out);
            for a in args {
                collect_spawn_spans_expr(&a.expr, out);
            }
        }
        Expr::Array(items, _) => {
            for i in items {
                collect_spawn_spans_expr(i, out);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, fe) in fields {
                collect_spawn_spans_expr(fe, out);
            }
        }
        Expr::Str(segs, _) => {
            for seg in segs {
                if let brass_parser::ast::StrSeg::Expr(inner) = seg {
                    collect_spawn_spans_expr(inner, out);
                }
            }
        }
        Expr::Closure(_, body, _) => collect_spawn_spans_expr(body, out),
        Expr::Block(b, _) => {
            for s in &b.stmts {
                collect_spawn_spans_stmt(s, out);
            }
        }
        Expr::If(c, t, els, _) => {
            collect_spawn_spans_expr(c, out);
            for s in &t.stmts {
                collect_spawn_spans_stmt(s, out);
            }
            if let Some(e) = els {
                collect_spawn_spans_expr(e, out);
            }
        }
        Expr::IfLet(_, scrut, t, els, _) => {
            collect_spawn_spans_expr(scrut, out);
            for s in &t.stmts {
                collect_spawn_spans_stmt(s, out);
            }
            if let Some(e) = els {
                collect_spawn_spans_expr(e, out);
            }
        }
        Expr::Match(scrut, arms, _) => {
            collect_spawn_spans_expr(scrut, out);
            for arm in arms {
                collect_spawn_spans_expr(&arm.body, out);
            }
        }
        _ => {}
    }
}

/// Spans of every `spawn` in `stmts`, at any nesting depth (closures included).
/// The driver uses this to reject module-top-level spawns: init code never runs
/// through the ownership pass, so nothing would promote or guard their captures.
pub fn all_spawn_spans(stmts: &[Stmt]) -> Vec<Span> {
    let mut out = Vec::new();
    for s in stmts {
        collect_spawn_spans_stmt(s, &mut out);
    }
    out
}

fn collect_spawn_spans_stmt(stmt: &Stmt, out: &mut Vec<Span>) {
    each_stmt_expr(stmt, &mut |e| {
        if let Expr::Call(callee, _, span) = e
            && matches!(&**callee, Expr::Ident(n, _) if n == "spawn")
        {
            out.push(*span);
        }
        if let Expr::Closure(_, body, _) = e {
            collect_spawn_spans_expr(body, out);
        }
    });
    nested_block_stmts(stmt, &mut |inner| {
        for s in inner {
            collect_spawn_spans_stmt(s, out);
        }
    });
}
