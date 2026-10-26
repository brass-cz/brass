//! Scoped free-name analysis shared by checking and closure lowering.

use brass_parser::ast::*;
use fxhash::FxHashSet as HashSet;

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
    let mut free = HashSet::default();
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
        Pattern::Binding(n, _, _) => {
            out.insert(n.clone());
        }
        Pattern::Array(ps, _) => ps.iter().for_each(|p| bound_pat(p, out)),
        Pattern::Record(_, _, fps, _) => {
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
pub fn walk_subexprs(e: &Expr, f: &mut impl FnMut(&Expr)) {
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
        Expr::TypeTest(subject, _, _, _) => f(subject),
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
