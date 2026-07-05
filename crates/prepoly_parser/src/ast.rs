//! Abstract syntax tree for Prepoly.
//!
//! A `Module` is one source file: a list of imports followed by top-level
//! items (type/function declarations and statements). Records and sum types
//! share the single `TypeDecl` node.

use crate::lexer::Span;

/// One parsed source file.
#[derive(Clone, Debug)]
pub struct Module {
    pub imports: Vec<ImportDecl>,
    pub items: Vec<TopLevel>,
}

/// One name in an import's braced list; `local` differs from `remote` when an
/// `as` rename is present (`import m.{ X as Y }` -> remote "X", local "Y").
#[derive(Clone, Debug)]
pub struct ImportedName {
    /// The name as it exists in the target module.
    pub remote: String,
    /// The name as it appears in the importing module's scope.
    pub local: String,
    pub span: Span,
}

impl ImportedName {
    pub fn plain(name: String, span: Span) -> Self {
        Self {
            local: name.clone(),
            remote: name,
            span,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ImportDecl {
    /// Dotted module path, e.g. `math.vector` -> ["math", "vector"].
    pub path: Vec<String>,
    /// Names brought into scope from that module.
    pub names: Vec<ImportedName>,
    /// A brace-less `import a.b`: whether the path names a module (qualified
    /// use via `alias`) or a module plus one trailing name is decided by the
    /// loader, which knows which modules exist. `false` for `import a.{ .. }`.
    pub bare: bool,
    /// For a bare import resolved as a MODULE import: the qualifier the
    /// program uses (`import geometry.vec` -> `vec.dot(..)`), the path's last
    /// segment. Filled by the loader, or by the parser when `as` is present.
    pub alias: Option<String>,
    /// True when the user wrote `import ... as name` — the alias comes from
    /// the source, not from the loader's last-segment default.
    pub explicit_alias: bool,
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
    /// `type Alias = <type expression>` -- an alias whose right-hand side is a
    /// type expression, typically a refinement (`type JsonObject = HashMap {
    /// key: string, value: JsonValue }`). The alias name resolves to the
    /// right-hand side's type; it is not a new nominal.
    Alias(TypeExpr),
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
    /// `Some(T)` when this is a method implementation `fun T.m(...)`: `T` is the
    /// receiver type (a named type, or an array `T[]` for primitive-array
    /// methods). `None` for a plain free function `fun m(...)`.
    pub recv: Option<TypeExpr>,
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
        /// `None` for a declaration without an initializer (`let p: Point`).
        /// Only an annotated `let` (not `const`) may omit it; the binding must
        /// then be definitely assigned -- whole or field by field -- before any
        /// read, which the checker's definite-assignment pass enforces.
        value: Option<Expr>,
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
    /// `typeof(e)` in type position: the static type of the value expression
    /// `e`. The checker resolves it by tying the annotation to `e`'s inferred
    /// type; `e` is type-checked but never evaluated at runtime.
    TypeOf(Box<Expr>, Span),
    /// The `type` keyword as a field's declared type: a TYPE SLOT, a
    /// type-parameter of the enclosing record with no runtime storage. It is
    /// filled by a refinement (`Base { slot: T }`) or inferred from use; it
    /// cannot be read or written as a value.
    TypeSlot(Span),
    /// `Self.field` in type position: the type of the enclosing type's field
    /// named `field` (usually a `type` slot). Lets one field's type be expressed
    /// over another's, e.g. `entries: _Entry { key: Self.key }?[]`.
    SelfField(String, Span),
    /// `Base { field: T, ... }` -- a REFINEMENT of nominal record `Base` that
    /// pins the named fields/slots to the given types. Omitted fields keep
    /// `Base`'s declared type (an unpinned slot is left open). A refinement of a
    /// field whose base type is concrete and does not match is an error.
    Refine(Box<TypeExpr>, Vec<(String, TypeExpr)>, Span),
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
            | TypeExpr::Ref(_, s)
            | TypeExpr::TypeOf(_, s)
            | TypeExpr::TypeSlot(s)
            | TypeExpr::SelfField(_, s)
            | TypeExpr::Refine(_, _, s) => *s,
        }
    }
}
