//! Abstract syntax tree for Prepoly.
//!
//! A `Module` is one source file: a list of imports followed by top-level
//! items (type/function declarations and statements). Records and sum types
//! share the single `TypeDecl` node.

use prepoly_lexer::Span;

/// One parsed source file.
#[derive(Clone, Debug)]
pub struct Module {
    pub imports: Vec<ImportDecl>,
    pub items: Vec<TopLevel>,
}

#[derive(Clone, Debug)]
pub struct ImportDecl {
    /// Dotted module path, e.g. `math.vector` -> ["math", "vector"].
    pub path: Vec<String>,
    /// Names brought into scope from that module.
    pub names: Vec<String>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TopLevel {
    Type(TypeDecl),
    Fun(FunDecl),
    Stmt(Stmt),
}

/// A `type` declaration. `interfaces` holds the enforced interface names from
/// `type B: A, C = ...`; the body is either a record or a sum type.
#[derive(Clone, Debug)]
pub struct TypeDecl {
    pub name: String,
    pub interfaces: Vec<String>,
    pub body: TypeBody,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TypeBody {
    Record(Vec<Member>),
    Sum(Vec<Variant>),
}

#[derive(Clone, Debug)]
pub struct Variant {
    pub name: String,
    pub members: Vec<Member>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Member {
    Field(Field),
    Method(Method),
}

#[derive(Clone, Debug)]
pub struct Field {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Method {
    pub name: String,
    pub params: Vec<Param>,
    pub ret: Option<TypeExpr>,
    /// `None` for an interface method declaration (signature only, no body).
    pub body: Option<Block>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct FunDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub ret: Option<TypeExpr>,
    pub body: Block,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Let {
        pat: Pattern,
        ty: Option<TypeExpr>,
        value: Expr,
        is_const: bool,
        span: Span,
    },
    Assign {
        target: Expr,
        op: AssignOp,
        value: Expr,
        span: Span,
    },
    Expr(Expr),
    While {
        cond: Expr,
        body: Block,
        span: Span,
    },
    For {
        var: String,
        iter: Expr,
        body: Block,
        span: Span,
    },
    Return(Option<Expr>, Span),
    Break(Span),
    Continue(Span),
}

impl Stmt {
    pub fn span(&self) -> Span {
        match self {
            Stmt::Let { span, .. }
            | Stmt::Assign { span, .. }
            | Stmt::While { span, .. }
            | Stmt::For { span, .. }
            | Stmt::Return(_, span)
            | Stmt::Break(span)
            | Stmt::Continue(span) => *span,
            Stmt::Expr(e) => e.span(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssignOp {
    Eq,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
    BitNot,
}

/// A segment of a string literal: literal text or an interpolated expression.
#[derive(Clone, Debug)]
pub enum StrSeg {
    Lit(String),
    Expr(Box<Expr>),
}

/// A call argument.
#[derive(Clone, Debug)]
pub struct Arg {
    pub expr: Expr,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Int(i64, Span),
    Float(f64, Span),
    Str(Vec<StrSeg>, Span),
    Bool(bool, Span),
    Null(Span),
    Ident(String, Span),
    SelfExpr(Span),
    /// `Self` used as a value (e.g. `Self { ... }` is parsed as TypeLit "Self").
    Unary(UnaryOp, Box<Expr>, Span),
    Binary(BinOp, Box<Expr>, Box<Expr>, Span),
    Call(Box<Expr>, Vec<Arg>, Span),
    Field(Box<Expr>, String, Span),
    Index(Box<Expr>, Box<Expr>, Span),
    /// `expr!` error-propagation operator.
    ErrorProp(Box<Expr>, Span),
    /// Closure `(params) -> body`; the body is any expression (a block is one).
    Closure(Vec<Param>, Box<Expr>, Span),
    Array(Vec<Expr>, Span),
    /// `[lo..hi]` -- a half-open integer range built into the array
    /// `[lo, lo+1, ..., hi-1]` (empty when `lo >= hi`).
    Range(Box<Expr>, Box<Expr>, Span),
    /// `Type { field: value, ... }` record/struct literal (also `Self { ... }`).
    TypeLit(String, Vec<(String, Expr)>, Span),
    /// `Type.Variant { field: value, ... }` sum-type variant construction.
    VariantLit(String, String, Vec<(String, Expr)>, Span),
    If(Box<Expr>, Block, Option<Box<Expr>>, Span),
    /// `if let pattern = expr { ... } else { ... }`.
    IfLet(Pattern, Box<Expr>, Block, Option<Box<Expr>>, Span),
    Match(Box<Expr>, Vec<MatchArm>, Span),
    Block(Block, Span),
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Int(_, s)
            | Expr::Float(_, s)
            | Expr::Str(_, s)
            | Expr::Bool(_, s)
            | Expr::Null(s)
            | Expr::Ident(_, s)
            | Expr::SelfExpr(s)
            | Expr::Unary(_, _, s)
            | Expr::Binary(_, _, _, s)
            | Expr::Call(_, _, s)
            | Expr::Field(_, _, s)
            | Expr::Index(_, _, s)
            | Expr::ErrorProp(_, s)
            | Expr::Closure(_, _, s)
            | Expr::Array(_, s)
            | Expr::Range(_, _, s)
            | Expr::TypeLit(_, _, s)
            | Expr::VariantLit(_, _, _, s)
            | Expr::If(_, _, _, s)
            | Expr::IfLet(_, _, _, _, s)
            | Expr::Match(_, _, s)
            | Expr::Block(_, s) => *s,
        }
    }
}

#[derive(Clone, Debug)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Wildcard(Span),
    /// A bare name: a binding, or a unit variant when it names one (resolved
    /// during type/exhaustiveness checking).
    Binding(String, Span),
    Literal(Box<Expr>, Span),
    /// `Name { field, field: subpat, ... }` record/variant destructuring.
    Record(String, Vec<FieldPat>, Span),
    Array(Vec<Pattern>, Span),
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Pattern::Wildcard(s)
            | Pattern::Binding(_, s)
            | Pattern::Literal(_, s)
            | Pattern::Record(_, _, s)
            | Pattern::Array(_, s) => *s,
        }
    }
}

#[derive(Clone, Debug)]
pub struct FieldPat {
    pub name: String,
    /// `None` means shorthand `{ name }` binding the field to its own name.
    pub pat: Option<Pattern>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TypeExpr {
    /// Primitive or user-defined type name.
    Named(String, Span),
    /// `T[n]` fixed-length array or `T[]` slice (`len == None`).
    Array(Box<TypeExpr>, Option<usize>, Span),
    /// `(T1, T2) -> U` function type.
    Fun(Vec<TypeExpr>, Box<TypeExpr>, Span),
    /// `T?` nullable.
    Nullable(Box<TypeExpr>, Span),
    /// `T!` fallible: the built-in `Result` with success payload `T` and an
    /// inferred error payload (`Result.Ok { value: T } | Result.Err`).
    Fallible(Box<TypeExpr>, Span),
    /// `[T0, T1, ...]` fixed-length heterogeneous tuple.
    Tuple(Vec<TypeExpr>, Span),
    /// `anonymous { field: T, ... }` -- an inline anonymous structure type
    /// (a structural record with the given fields, no nominal name).
    Anonymous(Vec<(String, TypeExpr)>, Span),
    /// `mut(T)` -- a mutable `T`: a place of this type may be mutated (assigned
    /// to, or have a mutating method called on it). Plain `T` is immutable.
    Mut(Box<TypeExpr>, Span),
    /// `ref(T)` an immutable reference, or `ref(mut(T))` a mutable reference (the
    /// inner is then a `mut(...)`). A reference parameter borrows the argument
    /// instead of deep-copying it; a non-reference parameter is passed by copy.
    Ref(Box<TypeExpr>, Span),
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Named(_, s)
            | TypeExpr::Array(_, _, s)
            | TypeExpr::Fun(_, _, s)
            | TypeExpr::Nullable(_, s)
            | TypeExpr::Fallible(_, s)
            | TypeExpr::Tuple(_, s)
            | TypeExpr::Anonymous(_, s)
            | TypeExpr::Mut(_, s)
            | TypeExpr::Ref(_, s) => *s,
        }
    }
}
