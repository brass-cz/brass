//! Syntactic identifier analysis over the AST for the spawn ownership pass.
//! Closure capture and shared-cell decisions belong to MIR lowering
//! (`brass_mir::analysis`).

use fxhash::FxHashSet as HashSet;

use brass_parser::ast::*;

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
