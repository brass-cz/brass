//! Closure conversion support: free-variable analysis to decide
//! which of a function's locals are captured by a nested closure. Captured
//! locals are boxed in heap cells so that writes through the closure and
//! through the enclosing scope share state (the accumulator/counter examples).

use std::collections::HashSet;

use prepoly_parser::ast::*;

/// Names bound (as params or `let`) anywhere in a function body.
pub fn bound_names(params: &[Param], body: &Block) -> HashSet<String> {
    let mut s: HashSet<String> = params.iter().map(|p| p.name.clone()).collect();
    collect_bound_block(body, &mut s);
    s
}

fn collect_bound_block(b: &Block, out: &mut HashSet<String>) {
    for s in &b.stmts {
        collect_bound_stmt(s, out);
    }
}

fn collect_bound_stmt(s: &Stmt, out: &mut HashSet<String>) {
    match s {
        Stmt::Let { pat, .. } => collect_pat_names(pat, out),
        Stmt::While { body, .. } => collect_bound_block(body, out),
        Stmt::For { pat, body, .. } => {
            collect_pat_names(pat, out);
            collect_bound_block(body, out);
        }
        _ => {}
    }
}

pub fn collect_pat_names(p: &Pattern, out: &mut HashSet<String>) {
    match p {
        Pattern::Binding(n, _) => {
            out.insert(n.clone());
        }
        Pattern::Array(ps, _) => ps.iter().for_each(|p| collect_pat_names(p, out)),
        Pattern::Record(_, fps, _) => {
            for fp in fps {
                match &fp.pat {
                    Some(sub) => collect_pat_names(sub, out),
                    None => {
                        out.insert(fp.name.clone());
                    }
                }
            }
        }
        _ => {}
    }
}

/// The set of identifiers referenced free in any closure inside `body`
/// (excluding each closure's own params/locals).
pub fn closure_free_vars(body: &Block) -> HashSet<String> {
    let mut out = HashSet::new();
    each_closure_block(body, &mut |params, cbody| {
        let mut bound: HashSet<String> = params.iter().map(|p| p.name.clone()).collect();
        collect_bound_block(cbody, &mut bound);
        let mut refs = HashSet::new();
        idents_block(cbody, &mut refs);
        for r in refs {
            if !bound.contains(&r) {
                out.insert(r);
            }
        }
    });
    out
}

/// Free variables of a single closure body relative to its own params/locals.
pub fn free_vars_of(params: &[Param], body: &Block) -> Vec<String> {
    let mut bound: HashSet<String> = params.iter().map(|p| p.name.clone()).collect();
    collect_bound_block(body, &mut bound);
    let mut refs = HashSet::new();
    idents_block(body, &mut refs);
    let mut v: Vec<String> = refs.into_iter().filter(|r| !bound.contains(r)).collect();
    v.sort();
    v
}

/// Apply `f` to every closure (its params and block body) nested anywhere in
/// `body`. Used by the ownership analysis to find the bindings an inner closure
/// introduces, which are not captures of an enclosing one.
pub fn each_nested_closure(body: &Block, mut f: impl FnMut(&[Param], &Block)) {
    each_closure_block(body, &mut f);
}

fn each_closure_block(b: &Block, f: &mut impl FnMut(&[Param], &Block)) {
    for s in &b.stmts {
        each_closure_stmt(s, f);
    }
}

fn each_closure_stmt(s: &Stmt, f: &mut impl FnMut(&[Param], &Block)) {
    match s {
        Stmt::Let {
            value: Some(value), ..
        } => each_closure_expr(value, f),
        Stmt::Let { value: None, .. } => {}
        Stmt::Assign { target, value, .. } => {
            each_closure_expr(target, f);
            each_closure_expr(value, f);
        }
        Stmt::Expr(e) => each_closure_expr(e, f),
        Stmt::While { cond, body, .. } => {
            each_closure_expr(cond, f);
            each_closure_block(body, f);
        }
        Stmt::For { iter, body, .. } => {
            each_closure_expr(iter, f);
            each_closure_block(body, f);
        }
        Stmt::Return(Some(e), _) => each_closure_expr(e, f),
        _ => {}
    }
}

fn each_closure_expr(e: &Expr, f: &mut impl FnMut(&[Param], &Block)) {
    if let Expr::Closure(params, body, _) = e {
        if let Expr::Block(b, _) = &**body {
            f(params, b);
        } else {
            // Expression-bodied closure: wrap as a single-return block view.
            let mut refs = Block {
                stmts: vec![],
                span: e.span(),
            };
            let _ = &mut refs;
            f(
                params,
                &Block {
                    stmts: vec![Stmt::Expr((**body).clone())],
                    span: e.span(),
                },
            );
        }
    }
    walk_subexprs(e, &mut |s| each_closure_expr(s, f));
}

/// Collect identifier names referenced as values in a block.
pub fn idents_block(b: &Block, out: &mut HashSet<String>) {
    idents_stmts(&b.stmts, out);
}

/// Collect identifiers referenced across a statement slice. Used by ownership
/// analysis to test whether a captured variable stays live after a `spawn`.
pub fn idents_stmts(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        idents_stmt(s, out);
    }
}

fn idents_stmt(s: &Stmt, out: &mut HashSet<String>) {
    match s {
        Stmt::Let {
            value: Some(value), ..
        } => idents_expr(value, out),
        Stmt::Let { value: None, .. } => {}
        Stmt::Assign { target, value, .. } => {
            idents_expr(target, out);
            idents_expr(value, out);
        }
        Stmt::Expr(e) => idents_expr(e, out),
        Stmt::While { cond, body, .. } => {
            idents_expr(cond, out);
            idents_block(body, out);
        }
        Stmt::For { iter, body, .. } => {
            idents_expr(iter, out);
            idents_block(body, out);
        }
        Stmt::Return(Some(e), _) => idents_expr(e, out),
        _ => {}
    }
}

fn idents_expr(e: &Expr, out: &mut HashSet<String>) {
    if let Expr::Ident(n, _) = e {
        out.insert(n.clone());
    }
    walk_subexprs(e, &mut |s| idents_expr(s, out));
}

/// Apply `f` to the immediate sub-expressions of `e`.
fn walk_subexprs(e: &Expr, f: &mut impl FnMut(&Expr)) {
    match e {
        Expr::Unary(_, a, _) | Expr::Field(a, _, _) | Expr::ErrorProp(a, _) => f(a),
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) => {
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
