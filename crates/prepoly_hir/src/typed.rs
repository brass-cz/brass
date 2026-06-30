//! Typed HIR sidecar data produced by type checking.
//!
//! The current executable HIR still keeps parsed AST nodes for code generation.
//! This module is the migration surface toward a fully typed HIR: every checked
//! expression can be represented by its source span, inferred type, and
//! constness until expression kinds are fully lowered into HIR-owned nodes.

use prepoly_lexer::Span;
use prepoly_parser::ast::{BinOp, Expr, UnaryOp};

use crate::Type;

/// Constness attached to a typed expression.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Constness {
    Mutable,
    Const,
    Unknown,
}

/// A region identifier: the unit of mutable-object ownership a
/// `with` scope establishes. Matches the runtime's 1-based region ids.
pub type RegionId = u32;

/// The ownership class of a checked expression's value. Most
/// values are `Local` (the thread's implicit region); `Immutable`/`Cown`/`InRegion`
/// are established by freeze/cown/region operations. Several of these are only
/// settled once concrete types are known at JIT time, so an
/// expression whose ownership the front end has not resolved carries `Unknown`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ownership {
    /// The thread's local region (the default for newly created values).
    Local,
    /// Deeply frozen and shareable across threads.
    Immutable,
    /// Held in a cown, reached only under its lock.
    Cown,
    /// Inside an explicit region.
    InRegion(RegionId),
    /// Not yet determined (settled at JIT time once types are concrete).
    Unknown,
}

/// The HIR-owned shape of a checked expression.
///
/// This intentionally stores only stable expression identity, not child nodes.
/// It lets the typed sidecar move toward a fully typed HIR while the executable
/// HIR still keeps parser AST nodes for code generation.
#[derive(Clone, Debug, PartialEq)]
pub enum TypedExprKind {
    Int,
    Float,
    String,
    Bool,
    Null,
    Ident(String),
    SelfExpr,
    Unary(UnaryOp),
    Binary(BinOp),
    Call,
    Field(String),
    Index,
    ErrorPropagate,
    Closure,
    Array,
    TypeLiteral(String),
    VariantLiteral { ty: String, variant: String },
    If,
    IfLet,
    Match,
    Block,
    Unknown,
}

impl TypedExprKind {
    pub fn from_expr(expr: &Expr) -> Self {
        match expr {
            Expr::Int(..) => Self::Int,
            Expr::Float(..) => Self::Float,
            Expr::Str(..) => Self::String,
            Expr::Bool(..) => Self::Bool,
            Expr::Null(_) => Self::Null,
            Expr::Ident(name, _) => Self::Ident(name.clone()),
            Expr::SelfExpr(_) => Self::SelfExpr,
            Expr::Unary(op, _, _) => Self::Unary(*op),
            Expr::Binary(op, _, _, _) => Self::Binary(*op),
            Expr::Call(..) => Self::Call,
            Expr::Field(_, name, _) => Self::Field(name.clone()),
            Expr::Index(..) => Self::Index,
            Expr::ErrorProp(..) => Self::ErrorPropagate,
            Expr::Closure(..) => Self::Closure,
            Expr::Array(..) | Expr::Range(..) => Self::Array,
            Expr::TypeLit(name, ..) => Self::TypeLiteral(name.clone()),
            Expr::VariantLit(ty, variant, ..) => Self::VariantLiteral {
                ty: ty.clone(),
                variant: variant.clone(),
            },
            Expr::If(..) => Self::If,
            Expr::IfLet(..) => Self::IfLet,
            Expr::Match(..) => Self::Match,
            Expr::Block(..) => Self::Block,
        }
    }
}

/// Type information for one expression node in the lowered program. Pairs the
/// expression's inferred type with its `ownership` class.
#[derive(Clone, Debug, PartialEq)]
pub struct TypedExpr {
    pub kind: TypedExprKind,
    pub span: Span,
    pub ty: Type,
    pub constness: Constness,
    pub ownership: Ownership,
}

/// Typed expression data collected for a program.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TypedProgram {
    pub expressions: Vec<TypedExpr>,
}

impl TypedProgram {
    pub fn push(&mut self, span: Span, ty: Type, constness: Constness) {
        self.push_kind(TypedExprKind::Unknown, span, ty, constness);
    }

    pub fn push_expr(&mut self, expr: &Expr, ty: Type, constness: Constness) {
        self.push_kind(TypedExprKind::from_expr(expr), expr.span(), ty, constness);
    }

    pub fn push_kind(&mut self, kind: TypedExprKind, span: Span, ty: Type, constness: Constness) {
        // The front end records the default ownership: a literal value is born in
        // the local region; anything else is settled at JIT time once concrete
        // types are known, so it stays `Unknown` here.
        let ownership = match kind {
            TypedExprKind::Int
            | TypedExprKind::Float
            | TypedExprKind::String
            | TypedExprKind::Bool
            | TypedExprKind::Array
            | TypedExprKind::TypeLiteral(_)
            | TypedExprKind::VariantLiteral { .. } => Ownership::Local,
            _ => Ownership::Unknown,
        };
        self.expressions.push(TypedExpr {
            kind,
            span,
            ty,
            constness,
            ownership,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A literal value is born in the local region; a non-literal expression's
    /// ownership is settled at JIT time, so the front end records `Unknown`.
    #[test]
    fn literals_are_local_others_unknown() {
        let mut prog = TypedProgram::default();
        let span = Span::new(0, 0);
        prog.push_kind(TypedExprKind::Int, span, Type::Unknown(0), Constness::Const);
        prog.push_kind(
            TypedExprKind::Ident("x".into()),
            span,
            Type::Unknown(1),
            Constness::Mutable,
        );
        assert_eq!(prog.expressions[0].ownership, Ownership::Local);
        assert_eq!(prog.expressions[1].ownership, Ownership::Unknown);
    }
}
