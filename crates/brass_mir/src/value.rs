//! Operands and right-hand-side values.
//!
//! Expressions are flattened to three-address form during lowering: every
//! computed value is named by a local, and an [`Operand`] is either such a local
//! or an inline constant. An [`Rvalue`] is the one computation a [`MirStmt`]
//! performs. None of these nodes carry concrete types; operator/operand types
//! are recovered later from the locals' [`crate::TypeRef`]s, which keeps the IR
//! type-independent.

use std::fmt;

use brass_hir::Type;
use brass_parser::ast::{BinOp, UnaryOp};

use crate::ids::{ClosureId, LocalId};

/// A constant operand. String interpolation and `error(x)` are *not* literals;
/// they desugar into calls/constructors during lowering, so a `Str` here is
/// always fully constant text.
#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    /// An integer constant, sign included. Its range covers every Brass
    /// integer type (`int64` through `uint64`); the type it takes is decided
    /// by monomorphization from the value and the operand context.
    Int(i128),
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
/// is decided later, by monomorphization, from the argument types.
#[derive(Clone, Debug, PartialEq)]
pub enum Callee {
    /// A free function, named by its resolved module-qualified storage symbol.
    Free(String),
    /// A free call with a return-origin contract selected per enclosing instance.
    NumericFree {
        base: String,
        site: brass_parser::Span,
    },
    /// A method or static call with a negotiated body contract.
    Numeric {
        inner: Box<Callee>,
        site: brass_parser::Span,
    },
    /// An instance method `recv.method(args)`; the receiver is the first call
    /// operand. The receiving type is recovered from that operand's type.
    Method(String),
    /// A static method call `Type.method(args)`. `ty` is the dispatch key: a
    /// user type's unique symbol, or a primitive type word (`int32`, ...).
    Static { ty: String, method: String },
    /// A runtime builtin or intrinsic with no user-level definition (`print`,
    /// `len`, the `pp_*` primitives, ...).
    Builtin(String),
    /// An indirect call through a closure/function value operand.
    Indirect(Operand),
    /// A reflective (`-> infer!`) method call that the instances of the
    /// enclosing body key differently, so each dispatches to a different
    /// generated specialization. `site` (the call's source span) keys the
    /// checker's per-instance dispatch ([`crate::MirProgram::instance_dispatch`]);
    /// monomorphization resolves it for the instance it types, and the call
    /// then dispatches exactly like [`Callee::Method`] naming that
    /// specialization (the receiver is the first operand). `method` is the
    /// reflective template's name, for diagnostics.
    Keyed {
        method: String,
        site: brass_parser::Span,
    },
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
    /// A sum-type variant construction.
    Variant {
        ty: String,
        variant: String,
        fields: Vec<(String, Operand)>,
    },
    /// `T.from(v)`: a fallible structural conversion to record type `T`. The result
    /// is `T?` -- the record built by reading every field of `T` from `source` when
    /// the (monomorphized) source type has them all, each flowing into its field
    /// type by a flow conversion, otherwise null. The
    /// field-presence decision is made per instance by the back ends, so a `source`
    /// missing a field becomes a runtime null rather than a static error.
    RecordFrom { ty: String, source: Operand },
    /// Convert an anonymous structural argument into the VIEW of a callee
    /// parameter's row: a fresh structural record holding exactly the fields
    /// `callee`'s parameter `param` requires (per the program-wide row table,
    /// re-derived by the monomorphizer), with a guarded field that is absent or
    /// type-mismatched materialized as null. Emitted only at call sites the
    /// checker recorded as view-convertible; like `RecordFrom`, the node itself
    /// is type-free -- presence decisions happen per monomorphized instance.
    RecordView {
        callee: String,
        param: usize,
        source: Operand,
    },
    /// A closure value: the lowered body plus the captured operands, in the same
    /// order as the body's capture locals.
    Closure {
        id: ClosureId,
        captures: Vec<Operand>,
    },
    /// `typeof(x)`: the source name of the operand's static type, as a string.
    /// The name is NOT baked into the (instance-shared) body: each back end
    /// derives it from the operand's monomorphized type, so every instance of a
    /// generic body reports its own type. The operand's value is never read at
    /// runtime -- only its type -- but the operand expression is still
    /// evaluated for its effects like any other argument.
    TypeName(Operand),
    /// A type test (`if v: T`): whether the operand's monomorphized type
    /// matches the checker-resolved pattern (`brass_typesys::type_test_accepts`;
    /// `Unknown` positions are `infer` wildcards). Like `TypeName`, nothing is
    /// baked per instance: each back end folds it to a constant bool from the
    /// operand's own type, and branch folding prunes the untaken arm, so the
    /// test never exists at runtime.
    TypeTest(Operand, Type),
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
            Callee::Numeric { inner, site } => {
                write!(f, "numeric {inner}@{}..{}", site.lo, site.hi)
            }
            Callee::NumericFree { base, site } => {
                write!(f, "numeric fn {base}@{}..{}", site.lo, site.hi)
            }
            Callee::Method(m) => write!(f, "method .{m}"),
            Callee::Static { ty, method } => write!(f, "static {ty}.{method}"),
            Callee::Builtin(name) => write!(f, "builtin {name}"),
            Callee::Indirect(op) => write!(f, "indirect {op}"),
            Callee::Keyed { method, site } => {
                write!(f, "keyed .{method}@{}..{}", site.lo, site.hi)
            }
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
            Rvalue::RecordView {
                callee,
                param,
                source,
            } => write!(f, "view({callee}#{param}, {source})"),
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
            Rvalue::TypeName(op) => write!(f, "typename {op}"),
            Rvalue::TypeTest(op, pattern) => write!(f, "typetest {op}: {}", pattern.display()),
        }
    }
}
