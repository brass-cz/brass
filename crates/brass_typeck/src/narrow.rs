//! The conditions that narrow a nullable variable, recognized syntactically
//! (the infer pass applies them). `if v { ... }` and `if v != null { ... }`
//! narrow `v` from `T?` to `T` in the truthy branch; a diverging guard
//! `if !v { return }` or `if v == null { return }` narrows it for the rest of
//! the block. Only a variable narrows: a tested field path is recognized only
//! to explain a later unchecked read of the same field.

use brass_parser::ast::{BinOp, Expr, UnaryOp};

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

/// The field path a condition tests for presence (`if p.n`, `if p.n != null`),
/// spelled as written. Testing a field does not narrow it -- a field can be
/// reassigned through any alias of its record -- so the path is kept only to
/// explain a later unchecked read of the same field.
pub(crate) fn truthy_field_path(cond: &Expr) -> Option<String> {
    match cond {
        Expr::Field(..) => field_path(cond),
        Expr::Binary(BinOp::Ne, a, b, _) => null_compare_field(a, b),
        _ => None,
    }
}

/// The field path a diverging guard tests for absence (`if !p.n { return }`,
/// `if p.n == null { return }`); see [`truthy_field_path`].
pub(crate) fn falsy_field_path(cond: &Expr) -> Option<String> {
    match cond {
        Expr::Unary(UnaryOp::Not, inner, _) if matches!(**inner, Expr::Field(..)) => {
            field_path(inner)
        }
        Expr::Binary(BinOp::Eq, a, b, _) => null_compare_field(a, b),
        _ => None,
    }
}

/// `x.a.b` (rooted at a binding or `self`) spelled as a dotted path.
pub(crate) fn field_path(e: &Expr) -> Option<String> {
    match e {
        Expr::Ident(n, _) => Some(n.clone()),
        Expr::SelfExpr(_) => Some("self".to_string()),
        Expr::Field(base, name, _) => Some(format!("{}.{name}", field_path(base)?)),
        _ => None,
    }
}

fn null_compare_field(a: &Expr, b: &Expr) -> Option<String> {
    match (a, b) {
        (field @ Expr::Field(..), Expr::Null(_)) | (Expr::Null(_), field @ Expr::Field(..)) => {
            field_path(field)
        }
        _ => None,
    }
}
