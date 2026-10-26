//! Deferred structural constraints on inference variables.
//!
//! A closure literal is typed at its definition with its unannotated
//! parameters bound to fresh inference variables; that check fixes the
//! closure value's function type. Its body may use a parameter in a way that
//! constrains it (arithmetic, a method/field access, indexing) even though the
//! concrete argument type is only known later, at a call site.
//!
//! Each such use records a `ShapeConstraint` keyed by the parameter's inference
//! variable id. When the closure value is applied (`apply_callable`), every
//! recorded constraint is verified against the argument's type before the open
//! parameter is committed to it. This makes a closure such as `(x) -> x + 1`
//! reject a `string` argument even where the application's re-check of the
//! body (`check_callable_body`, which needs fully-known argument types) does
//! not run, matching the soundness a named function gets from per-call body
//! re-checking. The constraints also travel to each instance of a generalized
//! closure binding ([`ShapeConstraint::substitute`]).

use brass_hir::Type;
use brass_parser::ast::BinOp;

/// A structural requirement on an inference variable, discovered while checking
/// a body that used the variable before its concrete type was known. Verified
/// when the variable is solved at a call site.
#[derive(Clone, Debug)]
pub enum ShapeConstraint {
    /// The variable must equal a concrete non-convertible type: the operand of
    /// a string concatenation next to a `string`.
    Equals(Type),
    /// The variable is an operand of the numeric operator `op` whose other
    /// operand has type `other` (with the value `literal` when it is written
    /// as an integer literal). The variable's concrete type must type the
    /// operator by the shared rule (`brass_typesys::numeric_binary`), so an
    /// `int32` next to an `int64` is accepted (they meet at `int64`). When
    /// the body was typed with the operation yielding `result`, the concrete
    /// operation must yield exactly that: the closure's type records the
    /// result its definition was typed with, so it cannot follow the
    /// argument.
    Operand {
        op: BinOp,
        other: Type,
        literal: Option<brass_typesys::NumericLiteral>,
        result: Option<Type>,
    },
    /// The variable must be a value exposing the named method (`x.speak()`).
    HasMethod(String),
    /// The variable must be a record exposing the named field (`x.name`).
    HasField(String),
    /// The variable must be indexable: an array, slice, or string (`x[0]`).
    Indexable,
}

impl ShapeConstraint {
    /// The constraint with each inference variable that `map` names replaced
    /// by its mapped type: a constraint copied onto an instance of a
    /// generalized closure refers to the instance's variables, not the
    /// scheme's.
    pub fn substitute(&self, map: &std::collections::BTreeMap<u32, Type>) -> Self {
        let subst = |t: &Type| brass_hir::substitute_vars(t, map);
        match self {
            ShapeConstraint::Equals(t) => ShapeConstraint::Equals(subst(t)),
            ShapeConstraint::Operand {
                op,
                other,
                literal,
                result,
            } => ShapeConstraint::Operand {
                op: *op,
                other: subst(other),
                literal: *literal,
                result: result.as_ref().map(subst),
            },
            other => other.clone(),
        }
    }
}
