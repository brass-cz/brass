//! Interprocedural summaries: which parameters of each function a `spawn`
//! reachable inside it captures, iterated to a fixpoint over the call graph.

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use brass_parser::ast::*;

use super::SpawnSummaries;
use super::analysis::{captured, param_names, root_ident, stmts_block};
use super::sites::{
    SpawnArg, closure_bindings_at, closure_bound_in, each_spawn_site, spawn_arg,
    spawn_closure_body, spawn_stmt_span,
};

/// Compute [`SpawnSummaries`] for a program's functions and methods, given each
/// as `(name, parameter names, body)`. Two steps:
///
/// 1. Direct: a spawn site inside `f` (literal, or a closure variable bound in
///    `f`) captures one of `f`'s parameters.
/// 2. Transitive fixpoint: `f` passes a place rooted at one of its parameters
///    into a call position already known to be spawn-captured (`fun f(p) {
///    start(p) }` where `start` spawns a task capturing its first parameter
///    makes `p` spawn-captured in `f` too), like the write-through-parameter
///    analysis in `brass_hir::mutation`.
pub fn spawn_capture_summaries(fns: &[(String, Vec<String>, &Block)]) -> SpawnSummaries {
    let mut summaries: SpawnSummaries = HashMap::default();

    // Step 1: direct captures of a parameter by a spawn site in the body.
    for (name, params, body) in fns {
        let mut captured_params: HashSet<usize> = HashSet::default();
        each_scope_spawn_body(&body.stmts, &body.stmts, &mut |cbody, bound| {
            for cap in captured(cbody, bound) {
                if let Some(i) = params.iter().position(|p| *p == cap) {
                    captured_params.insert(i);
                }
            }
        });
        if !captured_params.is_empty() {
            summaries
                .entry(name.clone())
                .or_default()
                .extend(captured_params);
        }
    }

    // Step 2: propagate through call sites until nothing changes.
    loop {
        let mut changed = false;
        for (name, params, body) in fns {
            let mut found: HashSet<usize> = HashSet::default();
            each_call(&stmts_block(&body.stmts), &mut |callee, recv, args| {
                let Some(indices) = summaries.get(callee) else {
                    return;
                };
                for &j in indices {
                    let arg = match recv {
                        // Method call: position 0 is the receiver.
                        Some(r) if j == 0 => Some(r),
                        Some(_) => args.get(j - 1).map(|a| &a.expr),
                        None => args.get(j).map(|a| &a.expr),
                    };
                    if let Some(root) = arg.and_then(root_ident)
                        && let Some(i) = params.iter().position(|p| *p == root)
                    {
                        found.insert(i);
                    }
                }
            });
            if !found.is_empty() {
                let entry = summaries.entry(name.clone()).or_default();
                for i in found {
                    changed |= entry.insert(i);
                }
            }
        }
        if !changed {
            break;
        }
    }
    summaries
}

/// Visit every spawn-closure body reachable in the scope tree rooted at `stmts`
/// (through control flow and through nested spawn closures): literal spawn
/// arguments and closures bound to a spawned local. `all` is the full scope for
/// resolving closure-variable bindings. Used for summary computation, where
/// unresolvable spawn arguments are simply skipped (the transform reports them).
fn each_scope_spawn_body(
    stmts: &[Stmt],
    all: &[Stmt],
    f: &mut impl FnMut(&Block, &HashSet<String>),
) {
    each_spawn_site(stmts, &mut |stmt| match spawn_arg(stmt) {
        Some(SpawnArg::Literal) => {
            if let Some(body) = spawn_closure_body(stmt) {
                let bound = closure_bound_in(stmt);
                f(&body, &bound);
                each_scope_spawn_body(&body.stmts, &body.stmts, f);
            }
        }
        Some(SpawnArg::Var(name, _)) => {
            for binding in closure_bindings_at(all, spawn_stmt_span(stmt), name) {
                let bound = param_names(&binding.params);
                f(&binding.body, &bound);
                each_scope_spawn_body(&binding.body.stmts, &binding.body.stmts, f);
            }
        }
        Some(SpawnArg::Opaque(_)) | None => {}
    });
}

/// Visit every call expression in `block` (descending everything, closures
/// included) as `(callee name, method receiver, args)`. A free call `g(a, b)`
/// yields `("g", None, args)`; a method call `r.m(a)` yields `("m", Some(r),
/// args)`.
pub(super) fn each_call<'a>(
    block: &'a Block,
    f: &mut impl FnMut(&'a str, Option<&'a Expr>, &'a [Arg]),
) {
    fn walk_stmt<'a>(s: &'a Stmt, f: &mut impl FnMut(&'a str, Option<&'a Expr>, &'a [Arg])) {
        match s {
            Stmt::Let {
                value: Some(value), ..
            }
            | Stmt::Expr(value)
            | Stmt::Return(Some(value), _) => walk_expr(value, f),
            Stmt::Let { value: None, .. } => {}
            Stmt::Assign { target, value, .. } => {
                walk_expr(target, f);
                walk_expr(value, f);
            }
            Stmt::While { cond, body, .. } => {
                walk_expr(cond, f);
                body.stmts.iter().for_each(|s| walk_stmt(s, f));
            }
            Stmt::For { iter, body, .. } => {
                walk_expr(iter, f);
                body.stmts.iter().for_each(|s| walk_stmt(s, f));
            }
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }
    fn walk_expr<'a>(e: &'a Expr, f: &mut impl FnMut(&'a str, Option<&'a Expr>, &'a [Arg])) {
        match e {
            Expr::Call(callee, args, _) => {
                match callee.as_ref() {
                    Expr::Ident(name, _) => f(name, None, args),
                    Expr::Field(base, method, _) if !callee.span().is_parenthesized() => {
                        f(method, Some(base), args)
                    }
                    _ => {}
                }
                walk_expr(callee, f);
                args.iter().for_each(|a| walk_expr(&a.expr, f));
            }
            Expr::Field(b, _, _)
            | Expr::Unary(_, b, _)
            | Expr::ErrorProp(b, _)
            | Expr::TypeTest(b, _, _, _) => walk_expr(b, f),
            Expr::Index(b, i, _) | Expr::Range(b, i, _) | Expr::Binary(_, b, i, _) => {
                walk_expr(b, f);
                walk_expr(i, f);
            }
            Expr::Closure(_, body, _) => walk_expr(body, f),
            Expr::Array(elems, _) => elems.iter().for_each(|el| walk_expr(el, f)),
            Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
                fields.iter().for_each(|(_, v)| walk_expr(v, f))
            }
            Expr::Str(segs, _) => segs.iter().for_each(|seg| {
                if let StrSeg::Expr(e) = seg {
                    walk_expr(e, f);
                }
            }),
            Expr::Block(b, _) => b.stmts.iter().for_each(|s| walk_stmt(s, f)),
            Expr::If(c, t, e, _) => {
                walk_expr(c, f);
                t.stmts.iter().for_each(|s| walk_stmt(s, f));
                if let Some(e) = e {
                    walk_expr(e, f);
                }
            }
            Expr::IfLet(_, scrut, t, e, _) => {
                walk_expr(scrut, f);
                t.stmts.iter().for_each(|s| walk_stmt(s, f));
                if let Some(e) = e {
                    walk_expr(e, f);
                }
            }
            Expr::Match(scrut, arms, _) => {
                walk_expr(scrut, f);
                arms.iter().for_each(|arm| walk_expr(&arm.body, f));
            }
            Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(_)
            | Expr::Ident(..)
            | Expr::SelfExpr(_) => {}
        }
    }
    block.stmts.iter().for_each(|s| walk_stmt(s, f));
}
