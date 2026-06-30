//! Operands and right-hand-side values.
//!
//! Expressions are flattened to three-address form during lowering: every
//! computed value is named by a local, and an [`Operand`] is either such a local
//! or an inline constant. An [`Rvalue`] is the one computation a [`MirStmt`]
//! performs. None of these nodes carry concrete types; operator/operand types
//! are recovered later from the locals' [`crate::TypeRef`]s, which keeps the IR
//! type-independent.

use std::fmt;

use prepoly_parser::ast::{BinOp, UnaryOp};

use crate::ids::{ClosureId, LocalId};

/// A constant operand. String interpolation and `error(x)` are *not* literals;
/// they desugar into calls/constructors during lowering, so a `Str` here is
/// always fully constant text.
#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
    Str(String),
    Bool(bool),
    /// The `null` literal (`Never?`).
    Null,
    /// The unit/`void` value, used for empty returns and discarded results.
    Void,
}

/// A read-only value supplied to an rvalue or terminator.
#[derive(Clone, Debug, PartialEq)]
pub enum Operand {
    /// Read the current value of a local slot.
    Local(LocalId),
    /// An inline constant.
    Const(Literal),
}

impl Operand {
    pub fn void() -> Self {
        Operand::Const(Literal::Void)
    }

    pub fn as_local(&self) -> Option<LocalId> {
        match self {
            Operand::Local(id) => Some(*id),
            Operand::Const(_) => None,
        }
    }
}

/// One step of a place projection: into a record/variant field or an array
/// element. The base of a projection is always a local; reading or storing a
/// global goes through [`Rvalue::Global`] / [`crate::MirStmt::SetGlobal`].
#[derive(Clone, Debug, PartialEq)]
pub enum Projection {
    Field(String),
    Index(Operand),
}

/// A storage location derived from a local by zero or more projections.
/// `local` with an empty `proj` denotes the local itself; with projections it
/// denotes a field/element reachable through the heap object the local holds.
#[derive(Clone, Debug, PartialEq)]
pub struct Place {
    pub local: LocalId,
    pub proj: Vec<Projection>,
}

impl Place {
    pub fn local(local: LocalId) -> Self {
        Place {
            local,
            proj: Vec::new(),
        }
    }

    pub fn projected(local: LocalId, proj: Vec<Projection>) -> Self {
        Place { local, proj }
    }

    /// Whether this place is a bare local with no projections.
    pub fn is_local(&self) -> bool {
        self.proj.is_empty()
    }
}

/// What a [`Rvalue::Call`] dispatches to.
///
/// The split is purely *syntactic / name-resolution* based, never type based:
/// which concrete monomorphic instance a `Free`/`Method`/`Static` call selects
/// is decided later from the argument types. This mirrors how the current
/// AST-walking codegen routes calls (`codegen::gen_call`), so a later MIR-driven
/// codegen is a faithful refactor.
#[derive(Clone, Debug, PartialEq)]
pub enum Callee {
    /// A free function, named by its resolved module-qualified storage symbol.
    Free(String),
    /// An instance method `recv.method(args)`; the receiver is the first call
    /// operand. The receiving type is recovered from that operand's type.
    Method(String),
    /// A static / UFCS call `Type.method(args)`. `ty` is the dispatch key: a
    /// user type's unique symbol, or a primitive type word (`int32`, ...).
    Static { ty: String, method: String },
    /// A runtime builtin or intrinsic with no user-level definition (`print`,
    /// `len`, the `pp_*` primitives, ...).
    Builtin(String),
    /// An indirect call through a closure/function value operand.
    Indirect(Operand),
}

/// The single computation performed by an assignment statement.
#[derive(Clone, Debug, PartialEq)]
pub enum Rvalue {
    /// Copy an operand.
    Use(Operand),
    /// A non-short-circuiting binary operator. `&&`/`||` never appear here; they
    /// lower to control flow.
    Bin(BinOp, Operand, Operand),
    /// A unary operator.
    Un(UnaryOp, Operand),
    /// A call. Argument evaluation order is the operand order.
    Call(Callee, Vec<Operand>),
    /// Read through a place projection (a field or array element).
    Load(Place),
    /// Read a module-level global by source name.
    Global(String),
    /// A fixed/slice array literal.
    Array(Vec<Operand>),
    /// A record literal. Fields are kept in source order under their names;
    /// positional layout ordering is a codegen concern, not a MIR one.
    Record {
        ty: String,
        fields: Vec<(String, Operand)>,
    },
    /// A sum-type variant construction. `error(x)` lowers to the built-in
    /// `Result.Err { error: x }` form of this node.
    Variant {
        ty: String,
        variant: String,
        fields: Vec<(String, Operand)>,
    },
    /// `T.from(v)`: a fallible structural conversion to record type `T`. The result
    /// is `T?` -- the record built by reading every field of `T` from `source` when
    /// the (monomorphized) source type has them all, otherwise null. The
    /// field-presence decision is made per instance by the back ends, so a `source`
    /// missing a field becomes a runtime null rather than a static error.
    RecordFrom { ty: String, source: Operand },
    /// A closure value: the lowered body plus the captured operands, in the same
    /// order as the body's capture locals.
    Closure {
        id: ClosureId,
        captures: Vec<Operand>,
    },
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Int(v) => write!(f, "{v}"),
            Literal::Float(v) => write!(f, "{v:?}"),
            Literal::Str(s) => write!(f, "{s:?}"),
            Literal::Bool(b) => write!(f, "{b}"),
            Literal::Null => f.write_str("null"),
            Literal::Void => f.write_str("void"),
        }
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Local(id) => write!(f, "{id}"),
            Operand::Const(lit) => write!(f, "{lit}"),
        }
    }
}

impl fmt::Display for Projection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Projection::Field(name) => write!(f, ".{name}"),
            Projection::Index(op) => write!(f, "[{op}]"),
        }
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.local)?;
        for p in &self.proj {
            write!(f, "{p}")?;
        }
        Ok(())
    }
}

impl fmt::Display for Callee {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Callee::Free(sym) => write!(f, "fn {sym}"),
            Callee::Method(m) => write!(f, "method .{m}"),
            Callee::Static { ty, method } => write!(f, "static {ty}.{method}"),
            Callee::Builtin(name) => write!(f, "builtin {name}"),
            Callee::Indirect(op) => write!(f, "indirect {op}"),
        }
    }
}

fn join_operands(ops: &[Operand]) -> String {
    ops.iter()
        .map(|o| o.to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

fn join_fields(fields: &[(String, Operand)]) -> String {
    fields
        .iter()
        .map(|(n, o)| format!("{n}: {o}"))
        .collect::<Vec<_>>()
        .join(", ")
}

impl fmt::Display for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rvalue::Use(op) => write!(f, "{op}"),
            Rvalue::Bin(op, a, b) => write!(f, "{a} {op:?} {b}"),
            Rvalue::Un(op, a) => write!(f, "{op:?} {a}"),
            Rvalue::Call(callee, args) => write!(f, "{callee}({})", join_operands(args)),
            Rvalue::Load(place) => write!(f, "load {place}"),
            Rvalue::Global(name) => write!(f, "global {name}"),
            Rvalue::Array(es) => write!(f, "[{}]", join_operands(es)),
            Rvalue::Record { ty, fields } => write!(f, "{ty} {{ {} }}", join_fields(fields)),
            Rvalue::RecordFrom { ty, source } => write!(f, "{ty}.from({source})"),
            Rvalue::Variant {
                ty,
                variant,
                fields,
            } => {
                write!(f, "{ty}.{variant} {{ {} }}", join_fields(fields))
            }
            Rvalue::Closure { id, captures } => {
                write!(f, "{id}[{}]", join_operands(captures))
            }
        }
    }
}
