//! Nullable narrowing. `if v { ... }` and
//! `if v != null { ... }` narrow `v` from `T?` to `T` in the truthy branch;
//! `if !v { return }` and `if v == null { return }` narrow it after the guard.

use prepoly_parser::ast::{BinOp, Expr, UnaryOp};

/// Variable narrowed to non-null in the truthy branch of `if cond`.
pub fn truthy_narrows(cond: &Expr) -> Option<&str> {
    match cond {
        Expr::Ident(n, _) => Some(n),
        Expr::Binary(BinOp::Ne, a, b, _) => null_compare_name(a, b),
        _ => None,
    }
}

/// Variable narrowed to non-null after `if cond { return }` style guards when
/// the guard exits on the null case.
pub fn falsy_narrows(cond: &Expr) -> Option<&str> {
    match cond {
        Expr::Unary(UnaryOp::Not, inner, _) => match &**inner {
            Expr::Ident(n, _) => Some(n),
            _ => None,
        },
        Expr::Binary(BinOp::Eq, a, b, _) => null_compare_name(a, b),
        _ => None,
    }
}

fn null_compare_name<'a>(a: &'a Expr, b: &'a Expr) -> Option<&'a str> {
    match (a, b) {
        (Expr::Ident(n, _), Expr::Null(_)) | (Expr::Null(_), Expr::Ident(n, _)) => Some(n),
        _ => None,
    }
}
