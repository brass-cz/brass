//! The one definition of `==` / `!=` that every back end implements.
//!
//! Equality is structural and decided per concrete (monomorphized) type:
//!
//! - integers and bools compare their values, floats by IEEE equality (so
//!   `NaN != NaN` and `0.0 == -0.0`), strings byte for byte;
//! - a nullable is equal when both sides are absent, unequal when exactly one
//!   is, and otherwise compares the present values by the inner type's rule;
//! - a record compares every field (in declaration order);
//! - a sum compares the variant tags, then the active variant's payload
//!   fields;
//! - an array (fixed or growable) compares the lengths, then the elements in
//!   order; a tuple compares its elements in position;
//! - a function value has no structure to compare and is equal only to the
//!   same closure object (identity);
//! - `void` / `never` values are always equal (they carry no value).
//!
//! Two values of the same aggregate object are equal without inspecting them,
//! which also ends the comparison of a value with itself through a cycle.
//!
//! The LLVM JIT emits one comparison helper per aggregate type from
//! [`equality_kind`] and the shared field lists
//! ([`crate::render_record_fields`] / [`crate::render_variant_fields`]); the
//! REPL interpreter walks its runtime values by the same kinds and lists. The
//! monomorphizer accepts `==` exactly when [`equality_defined`] holds, and the
//! prelude `HashMap` compares keys with this `==`.

use brass_hir::{Program, Type};

/// How two values of one concrete type compare under `==`. See the module
/// documentation for the semantics of each kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EqualityKind {
    /// An integer or bool: compare the values.
    Scalar,
    /// A float: IEEE equality.
    Float,
    /// A string: byte equality.
    Str,
    /// A nullable: null-safe comparison of the present values.
    Nullable,
    /// A record: every field, in declaration order.
    Record,
    /// A sum: the variant tag, then the active variant's payload fields.
    Sum,
    /// An array or slice: the lengths, then the elements in order.
    Sequence,
    /// A tuple: the elements in position.
    Tuple,
    /// A function value: the same closure object.
    Identity,
    /// `void` / `never`: no value, always equal.
    Unit,
}

/// The [`EqualityKind`] of a concrete type. Reference, mutability and const
/// wrappers (erased before the back ends) are seen through. An unresolved type
/// (`Unknown`, `Self`) never reaches a back end; it is classified as
/// [`EqualityKind::Identity`] so the decision stays total.
pub fn equality_kind(ty: &Type) -> EqualityKind {
    match ty {
        Type::Bool | Type::Int(_) => EqualityKind::Scalar,
        Type::Float(_) => EqualityKind::Float,
        Type::Str => EqualityKind::Str,
        Type::Nullable(_) => EqualityKind::Nullable,
        Type::Record(_) => EqualityKind::Record,
        Type::Sum(_) => EqualityKind::Sum,
        Type::Array(..) | Type::Slice(_) => EqualityKind::Sequence,
        Type::Tuple(_) => EqualityKind::Tuple,
        Type::Void | Type::Never => EqualityKind::Unit,
        Type::ConstOf(inner) | Type::Mut(inner) | Type::Ref(inner) => equality_kind(inner),
        Type::Fun(..) | Type::Unknown(_) | Type::SelfType => EqualityKind::Identity,
    }
}

/// Whether `==` / `!=` is defined between operands of the concrete types `a`
/// and `b` beyond the numeric case (two numbers convert to their common type
/// first, which the caller decides): both operands have the same type -- the
/// same record or sum declaration with invariant payloads, arrays/tuples of the
/// same element types, two bools, two strings, or two function values of one
/// signature. An array literal and a fixed array of the same element type
/// compare too: both are arrays at run time.
pub fn equality_defined(program: &Program, a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Bool, Type::Bool) | (Type::Str, Type::Str) => true,
        (Type::Record(x), Type::Record(y)) | (Type::Sum(x), Type::Sum(y)) => {
            x.id == y.id && brass_typesys::types_invariant(program, a, b)
        }
        (Type::Slice(x) | Type::Array(x, _), Type::Slice(y) | Type::Array(y, _)) => {
            brass_typesys::types_invariant(program, x, y)
        }
        (Type::Tuple(_), Type::Tuple(_)) | (Type::Fun(..), Type::Fun(..)) => {
            brass_typesys::types_invariant(program, a, b)
        }
        _ => false,
    }
}
