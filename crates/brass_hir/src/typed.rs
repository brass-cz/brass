//! Typed sidecar data produced by type checking.
//!
//! The HIR keeps function bodies as parsed AST nodes, so the checker records
//! what it decides about each checked expression beside them: its source
//! span, a node kind, its inferred type and constness ([`TypedProgram`]). The
//! checker derives the span-keyed channels MIR lowering and monomorphization
//! read from these records; editor tooling reads them directly.

use brass_parser::Span;
use brass_parser::ast::{BinOp, Expr, UnaryOp};

use crate::Type;

/// Constness attached to a typed expression.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Constness {
    Mutable,
    Const,
    Unknown,
}

/// The HIR-owned shape of a checked expression: its node kind and the
/// identity a consumer needs (an identifier's name, an operator), never child
/// nodes -- the expression itself is the AST node at the record's span.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
    /// Checker-only evidence for the receiver selected by a method call, keyed
    /// by the enclosing call span. MIR consumes it to complete that call's
    /// omitted arguments without aggregating unrelated same-named methods.
    MethodReceiver,
    /// The resolved type of a local annotation containing `typeof`, keyed by
    /// the annotation span. Slot seeds retain the enclosing callable instance.
    TypeOfAnnotation,
    /// The numeric storage type of an unannotated binding, keyed by its
    /// declaration's binding span. Captured cells use this as their element type.
    /// Non-numeric instances also record their type to prevent a shared numeric seed.
    NumericBinding,
    /// The effective numeric type supplied to an unannotated parameter,
    /// keyed by the argument expression's span in the enclosing instance.
    /// Other argument types invalidate numeric seeds shared across instances.
    NumericArgument,
    /// Numeric storage valid only in the recorded callable instance.
    InstanceNumericBinding,
    /// Numeric argument storage valid only in the recorded callable instance.
    InstanceNumericArgument,
    Field(String),
    Index,
    ErrorPropagate,
    Closure,
    Array {
        /// Whether the literal has no elements. An empty literal's element
        /// representation cannot be re-derived from element values, so its
        /// checked type is the back end's only source (the seeding channel).
        empty: bool,
    },
    /// A range `[lo..hi]`: an array-valued expression whose element type (the
    /// type its counter runs at) the checker decides from both bounds.
    Range,
    TypeLiteral(String),
    VariantLiteral {
        ty: String,
        variant: String,
    },
    If,
    IfLet,
    Match,
    Block,
    /// Checker evidence keyed by an `if`/`if let`/`match` span: the numeric
    /// type its value joins at because its literal branches adapted to the
    /// requirement the value flows into (`let b: uint8 = if c { 200 } else
    /// { 7 }`). The back end types the join with it; the bare literal values
    /// would join at their default type.
    LiteralBranchJoin,
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
            Expr::Array(es, _) => Self::Array {
                empty: es.is_empty(),
            },
            Expr::Range(..) => Self::Range,
            Expr::TypeLit(name, ..) => Self::TypeLiteral(name.clone()),
            Expr::VariantLit(ty, variant, ..) => Self::VariantLiteral {
                ty: ty.clone(),
                variant: variant.clone(),
            },
            Expr::If(..) => Self::If,
            Expr::IfLet(..) => Self::IfLet,
            // A type test is decided at compile time; its value is a constant
            // bool for the deciding instance.
            Expr::TypeTest(..) => Self::Bool,
            Expr::Match(..) => Self::Match,
            Expr::Block(..) => Self::Block,
        }
    }
}

/// The inferred type, node kind, source extent, and constness of an expression.
#[derive(Clone, Debug, PartialEq)]
pub struct TypedExpr {
    pub kind: TypedExprKind,
    pub span: Span,
    pub ty: Type,
    pub constness: Constness,
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
        self.expressions.push(TypedExpr {
            kind,
            span,
            ty,
            constness,
        });
    }
}
