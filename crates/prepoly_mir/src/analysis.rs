//! Free-variable analysis over the AST, used to decide a closure's captures.
//!
//! This duplicates the small AST walk also used by codegen's closure conversion
//! (it cannot depend on `prepoly_jit_llvm`, which will in turn depend on this
//! crate). Given a closure's parameters and body, [`free_vars_of`] returns the
//! identifiers it references but does not itself bind; lowering keeps those that
//! are bound in the enclosing scope as the closure's captured operands.

use std::collections::HashSet;

use prepoly_parser::Span;
use prepoly_parser::ast::*;

/// Locals that must be heap-promoted to a shared cell: those a
/// closure captures *and* that are assigned (mutated) somewhere -- in the closure or
/// the enclosing body -- so the mutation is observed through the shared capture, not
/// made on a per-closure copy. Read-only captures stay by-value. The cell is modeled
/// as a one-element array, reusing the array machinery (alloc, indexed get/set, RC).
pub fn cell_promotions(body: &Block) -> HashSet<String> {
    let mut captured = HashSet::new();
    let mut mutated = HashSet::new();
    promo_block(body, &mut captured, &mut mutated);
    captured.intersection(&mutated).cloned().collect()
}

fn promo_block(b: &Block, cap: &mut HashSet<String>, mutd: &mut HashSet<String>) {
    for s in &b.stmts {
        match s {
            Stmt::Let {
                value: Some(value), ..
            } => promo_expr(value, cap, mutd),
            Stmt::Let { value: None, .. } => {}
            Stmt::Assign { target, value, .. } => {
                if let Expr::Ident(n, _) = target {
                    mutd.insert(n.clone());
                }
                promo_expr(target, cap, mutd);
                promo_expr(value, cap, mutd);
            }
            Stmt::Expr(e) => promo_expr(e, cap, mutd),
            Stmt::While { cond, body, .. } => {
                promo_expr(cond, cap, mutd);
                promo_block(body, cap, mutd);
            }
            Stmt::For { iter, body, .. } => {
                promo_expr(iter, cap, mutd);
                promo_block(body, cap, mutd);
            }
            Stmt::Return(Some(e), _) => promo_expr(e, cap, mutd),
            _ => {}
        }
    }
}

fn promo_expr(e: &Expr, cap: &mut HashSet<String>, mutd: &mut HashSet<String>) {
    match e {
        Expr::Closure(params, cbody, _) => {
            let cb = closure_as_block(cbody);
            for v in free_vars_of(params, &cb) {
                cap.insert(v);
            }
            promo_block(&cb, cap, mutd);
        }
        Expr::Block(b, _) => promo_block(b, cap, mutd),
        Expr::If(c, t, els, _) => {
            promo_expr(c, cap, mutd);
            promo_block(t, cap, mutd);
            if let Some(e) = els {
                promo_expr(e, cap, mutd);
            }
        }
        Expr::IfLet(_, s, t, els, _) => {
            promo_expr(s, cap, mutd);
            promo_block(t, cap, mutd);
            if let Some(e) = els {
                promo_expr(e, cap, mutd);
            }
        }
        Expr::Match(s, arms, _) => {
            promo_expr(s, cap, mutd);
            for a in arms {
                promo_expr(&a.body, cap, mutd);
            }
        }
        _ => walk_subexprs(e, &mut |sub| promo_expr(sub, cap, mutd)),
    }
}

/// A closure body viewed as a block (an expression body becomes a one-statement
/// block). Mirrors `lower::closure_block`.
fn closure_as_block(body: &Expr) -> Block {
    match body {
        Expr::Block(b, _) => b.clone(),
        other => Block {
            stmts: vec![Stmt::Expr(other.clone())],
            span: other.span(),
        },
    }
}

/// Free variables of a closure body relative to its own parameters and locals,
/// sorted for deterministic capture order. The walk is ordered and scoped: a
/// read *before* a same-named later `let` is free (it refers to the outer
/// binding the closure must capture), and a binding introduced inside a nested
/// block, loop body, or match/if-let arm goes out of scope with it.
pub fn free_vars_of(params: &[Param], body: &Block) -> Vec<String> {
    let mut bound: HashSet<String> = params.iter().map(|p| p.name.clone()).collect();
    let mut free = HashSet::new();
    free_block(body, &mut bound, &mut free);
    let mut out: Vec<String> = free.into_iter().collect();
    out.sort();
    out
}

/// Walk a block in statement order, adding reads of names not currently bound
/// to `free`. `bound` is restored on exit, so the block's `let`s do not leak
/// into the enclosing scope.
fn free_block(b: &Block, bound: &mut HashSet<String>, free: &mut HashSet<String>) {
    let saved = bound.clone();
    for s in &b.stmts {
        match s {
            Stmt::Let { pat, value, .. } => {
                // The initializer is evaluated before the pattern binds, so a
                // self-named reference in it (`let y = y + 1`) is a free read.
                if let Some(value) = value {
                    free_expr(value, bound, free);
                }
                bound_pat(pat, bound);
            }
            Stmt::Assign { target, value, .. } => {
                free_expr(target, bound, free);
                free_expr(value, bound, free);
            }
            Stmt::Expr(e) => free_expr(e, bound, free),
            Stmt::While { cond, body, .. } => {
                free_expr(cond, bound, free);
                free_block(body, bound, free);
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                free_expr(iter, bound, free);
                let mut inner = bound.clone();
                for n in pat.bound_names() {
                    inner.insert(n.to_string());
                }
                free_block(body, &mut inner, free);
            }
            Stmt::Return(Some(e), _) => free_expr(e, bound, free),
            _ => {}
        }
    }
    *bound = saved;
}

fn free_expr(e: &Expr, bound: &mut HashSet<String>, free: &mut HashSet<String>) {
    match e {
        Expr::Ident(n, _) => {
            if !bound.contains(n) {
                free.insert(n.clone());
            }
        }
        // `self` is a read like any other: a method binds it as an ordinary
        // parameter named `self`, and the expression form lowers through
        // `lower_ident("self")`. Left out of this walk, a closure in a method
        // body never CAPTURED it -- the body's `self` then resolved to nothing,
        // and the value it stood for was one the back ends could not type.
        Expr::SelfExpr(_) => {
            if !bound.contains("self") {
                free.insert("self".to_string());
            }
        }
        // A nested closure binds its own parameters; whatever else it reads and
        // we have not bound is transitively free here.
        Expr::Closure(params, body, _) => {
            let mut inner = bound.clone();
            for p in params {
                inner.insert(p.name.clone());
            }
            free_block(&closure_as_block(body), &mut inner, free);
        }
        Expr::Block(b, _) => free_block(b, bound, free),
        Expr::If(c, t, els, _) => {
            free_expr(c, bound, free);
            free_block(t, bound, free);
            if let Some(e) = els {
                free_expr(e, bound, free);
            }
        }
        // Pattern bindings are visible only in the arm they guard.
        Expr::IfLet(pat, s, t, els, _) => {
            free_expr(s, bound, free);
            let mut inner = bound.clone();
            bound_pat(pat, &mut inner);
            free_block(t, &mut inner, free);
            if let Some(e) = els {
                free_expr(e, bound, free);
            }
        }
        Expr::Match(s, arms, _) => {
            free_expr(s, bound, free);
            for a in arms {
                let mut inner = bound.clone();
                bound_pat(&a.pattern, &mut inner);
                free_expr(&a.body, &mut inner, free);
            }
        }
        _ => walk_subexprs(e, &mut |sub| free_expr(sub, bound, free)),
    }
}

fn bound_pat(p: &Pattern, out: &mut HashSet<String>) {
    match p {
        Pattern::Binding(n, _) => {
            out.insert(n.clone());
        }
        Pattern::Array(ps, _) => ps.iter().for_each(|p| bound_pat(p, out)),
        Pattern::Record(_, fps, _) => {
            for fp in fps {
                match &fp.pat {
                    Some(sub) => bound_pat(sub, out),
                    None => {
                        out.insert(fp.name.clone());
                    }
                }
            }
        }
        _ => {}
    }
}

/// Apply `f` to the immediate value sub-expressions of `e`. Nested closures are
/// walked through their body so transitively captured names are still seen.
fn walk_subexprs(e: &Expr, f: &mut impl FnMut(&Expr)) {
    match e {
        Expr::Unary(_, a, _) | Expr::Field(a, _, _) | Expr::ErrorProp(a, _) => f(a),
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
            f(a);
            f(b);
        }
        Expr::Call(c, args, _) => {
            f(c);
            for a in args {
                f(&a.expr);
            }
        }
        Expr::Closure(_, body, _) => f(body),
        Expr::Array(es, _) => es.iter().for_each(f),
        Expr::TypeLit(_, fs, _) | Expr::VariantLit(_, _, fs, _) => {
            fs.iter().for_each(|(_, e)| f(e))
        }
        Expr::Str(segs, _) => {
            for s in segs {
                if let StrSeg::Expr(e) = s {
                    f(e);
                }
            }
        }
        Expr::If(c, t, els, _) => {
            f(c);
            block_exprs(t, f);
            if let Some(e) = els {
                f(e);
            }
        }
        Expr::IfLet(_, s, t, els, _) => {
            f(s);
            block_exprs(t, f);
            if let Some(e) = els {
                f(e);
            }
        }
        Expr::Match(s, arms, _) => {
            f(s);
            for a in arms {
                f(&a.body);
            }
        }
        Expr::Block(b, _) => block_exprs(b, f),
        _ => {}
    }
}

fn block_exprs(b: &Block, f: &mut impl FnMut(&Expr)) {
    for s in &b.stmts {
        match s {
            Stmt::Let {
                value: Some(value), ..
            } => f(value),
            Stmt::Let { value: None, .. } => {}
            Stmt::Assign { target, value, .. } => {
                f(target);
                f(value);
            }
            Stmt::Expr(e) => f(e),
            Stmt::While { cond, body, .. } => {
                f(cond);
                block_exprs(body, f);
            }
            Stmt::For { iter, body, .. } => {
                f(iter);
                block_exprs(body, f);
            }
            Stmt::Return(Some(e), _) => f(e),
            _ => {}
        }
    }
}

/// Whether a body auto-wraps plain returns in `Result.Ok`, i.e. it uses
/// `error(...)` or the `expr!` propagation operator. Mirrors codegen's
/// `fallible_block` so MIR records the same fallibility bit.
pub fn fallible_block(b: &Block) -> bool {
    scan_block(b, Props::Count(&HashSet::new()))
}

/// Like [`fallible_block`], but an `expr!` whose span is in `null_props` (a
/// nullable-operand propagation, per the checker) does not count: its failure
/// arm returns `null`, not an error `Result`, so a body whose only `!`s are
/// nullable is not fallible -- its return type is nullable instead.
pub fn fallible_block_except(b: &Block, null_props: &HashSet<Span>) -> bool {
    scan_block(b, Props::Count(null_props))
}

/// Whether a body constructs an error `Result` with `error(...)`. Unlike
/// [`fallible_block`], `expr!` does not count: in the entry `main` a failed
/// propagation aborts the program instead of returning an error Result, so
/// only an explicit `error(...)` makes such a body fallible.
pub fn constructs_error_block(b: &Block) -> bool {
    scan_block(b, Props::Ignore)
}

/// How `expr!` sites count while scanning for fallibility: as error sources
/// (except the given nullable-operand spans), or not at all.
#[derive(Clone, Copy)]
enum Props<'a> {
    Count(&'a HashSet<Span>),
    Ignore,
}

impl Props<'_> {
    fn counts(&self, span: Span) -> bool {
        match self {
            Props::Count(null_props) => !null_props.contains(&span),
            Props::Ignore => false,
        }
    }
}

fn scan_block(b: &Block, props: Props) -> bool {
    b.stmts.iter().any(|s| scan_stmt(s, props))
}

fn scan_stmt(s: &Stmt, props: Props) -> bool {
    match s {
        Stmt::Let { value, .. } => value.as_ref().is_some_and(|e| scan_expr(e, props)),
        Stmt::Assign { target, value, .. } => scan_expr(target, props) || scan_expr(value, props),
        Stmt::Expr(e) => scan_expr(e, props),
        Stmt::While { cond, body, .. } => scan_expr(cond, props) || scan_block(body, props),
        Stmt::For { iter, body, .. } => scan_expr(iter, props) || scan_block(body, props),
        Stmt::Return(Some(e), _) => scan_expr(e, props),
        _ => false,
    }
}

fn scan_expr(e: &Expr, props: Props) -> bool {
    match e {
        // `error(..)!` immediately unwraps (aborts at an entry, propagates
        // elsewhere -- and the propagation is counted via `props`); the
        // construction never escapes as this body's own Result, so it alone
        // does not make the body fallible. Its arguments are still scanned.
        Expr::ErrorProp(inner, span) => {
            if let Expr::Call(c, args, _) = &**inner
                && matches!(&**c, Expr::Ident(n, _) if n == "error")
            {
                return props.counts(*span) || args.iter().any(|a| scan_expr(&a.expr, props));
            }
            props.counts(*span) || scan_expr(inner, props)
        }
        Expr::Call(c, args, _) => {
            matches!(&**c, Expr::Ident(n, _) if n == "error")
                || scan_expr(c, props)
                || args.iter().any(|a| scan_expr(&a.expr, props))
        }
        Expr::Unary(_, a, _) | Expr::Field(a, _, _) => scan_expr(a, props),
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) => {
            scan_expr(a, props) || scan_expr(b, props)
        }
        Expr::Array(es, _) => es.iter().any(|e| scan_expr(e, props)),
        Expr::TypeLit(_, fs, _) | Expr::VariantLit(_, _, fs, _) => {
            fs.iter().any(|(_, v)| scan_expr(v, props))
        }
        Expr::Str(segs, _) => segs
            .iter()
            .any(|s| matches!(s, StrSeg::Expr(e) if scan_expr(e, props))),
        Expr::If(c, t, e, _) => {
            scan_expr(c, props)
                || scan_block(t, props)
                || e.as_ref().is_some_and(|e| scan_expr(e, props))
        }
        Expr::IfLet(_, s, t, e, _) => {
            scan_expr(s, props)
                || scan_block(t, props)
                || e.as_ref().is_some_and(|e| scan_expr(e, props))
        }
        Expr::Match(s, arms, _) => {
            scan_expr(s, props) || arms.iter().any(|a| scan_expr(&a.body, props))
        }
        Expr::Block(b, _) => scan_block(b, props),
        _ => false,
    }
}
