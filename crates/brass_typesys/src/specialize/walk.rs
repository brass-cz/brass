//! Structural recognition of a decoder template's record walk: the
//! `for f in fields(x)` loops and the bindings they iterate. The walk is found
//! by its shape -- the binding a `fields(..)` loop iterates -- never by the
//! binding's name.

use brass_parser::ast::{Arg, Block, Expr, Stmt};

/// The binding a `fields(x)` loop iterates (`x`), when `iter` is one.
pub(super) fn fields_loop_binding(iter: &Expr) -> Option<&str> {
    let call = match iter {
        Expr::ErrorProp(inner, _) => inner,
        other => other,
    };
    match call {
        Expr::Call(c, args, _) if matches!(&**c, Expr::Ident(n, _) if n == "fields") => {
            match args.as_slice() {
                [
                    Arg {
                        expr: Expr::Ident(x, _),
                    },
                ] => Some(x),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Every binding name a `fields(..)` loop in `body` iterates, at any depth.
pub(super) fn fields_walked_bindings(body: &Block) -> fxhash::FxHashSet<String> {
    fn block(b: &Block, out: &mut fxhash::FxHashSet<String>) {
        for st in &b.stmts {
            match st {
                Stmt::For { iter, body, .. } => {
                    if let Some(x) = fields_loop_binding(iter) {
                        out.insert(x.to_string());
                    }
                    expr(iter, out);
                    block(body, out);
                }
                Stmt::While { cond, body, .. } => {
                    expr(cond, out);
                    block(body, out);
                }
                Stmt::Let { value: Some(e), .. } | Stmt::Expr(e) | Stmt::Return(Some(e), _) => {
                    expr(e, out)
                }
                Stmt::Assign { target, value, .. } => {
                    expr(target, out);
                    expr(value, out);
                }
                Stmt::Let { value: None, .. }
                | Stmt::Return(None, _)
                | Stmt::Break(_)
                | Stmt::Continue(_) => {}
            }
        }
    }
    // Loops sit in statement blocks; only the expressions that carry blocks
    // need descending.
    fn expr(e: &Expr, out: &mut fxhash::FxHashSet<String>) {
        match e {
            Expr::Block(b, _) => block(b, out),
            Expr::If(_, then, els, _) | Expr::IfLet(_, _, then, els, _) => {
                block(then, out);
                if let Some(els) = els {
                    expr(els, out);
                }
            }
            Expr::Match(_, arms, _) => arms.iter().for_each(|arm| expr(&arm.body, out)),
            Expr::Closure(_, body, _) => expr(body, out),
            _ => {}
        }
    }
    let mut out = fxhash::FxHashSet::default();
    block(body, &mut out);
    out
}
