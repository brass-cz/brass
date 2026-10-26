//! Numeric flow: which implicit conversions exist between numeric types, and
//! the common type two numeric types meet at -- the lattice the operator rule
//! (`crate::operators`) and the value join (`crate::join`) build on.
//!
//! The rule is value preservation: a conversion is implicit only when EVERY
//! value of the source type is exactly representable in the target type.
//! Anything lossy (a narrower integer, a sign change, a narrower float, an
//! integer wider than the float's mantissa) requires the explicit `T.from(x)`
//! conversion, whose `T!` result makes the failure mode visible.

use brass_hir::{FloatKind, IntKind, Type};

/// How a value of one type may flow into a position of another numeric type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Flow {
    /// Same type; nothing to do.
    Identity,
    /// A value-preserving widening; the back ends emit the matching
    /// conversion for the concrete kinds.
    Widen,
    /// Not implicit. The payload names the explicit conversion to suggest.
    Forbidden(&'static str),
}

/// The flow from `from` into a position of type `to`. Non-numeric operands
/// yield `Forbidden` with an empty hint (callers fall back to their general
/// type error).
pub fn numeric_flow(from: &Type, to: &Type) -> Flow {
    match (from, to) {
        (Type::Int(a), Type::Int(b)) if a == b => Flow::Identity,
        (Type::Float(a), Type::Float(b)) if a == b => Flow::Identity,
        (Type::Int(a), Type::Int(b)) => int_to_int(*a, *b),
        (Type::Float(a), Type::Float(b)) => {
            if float_bits(*a) < float_bits(*b) {
                Flow::Widen
            } else {
                Flow::Forbidden("a narrower float would lose precision; convert explicitly")
            }
        }
        (Type::Int(a), Type::Float(b)) => int_to_float(*a, *b),
        (Type::Float(_), Type::Int(_)) => {
            Flow::Forbidden("float to int drops the fraction; convert explicitly")
        }
        _ => Flow::Forbidden(""),
    }
}

/// Whether `from` flows into `to` implicitly (identity or widening), for
/// callers that need no hint.
pub fn numeric_flows_into(from: &Type, to: &Type) -> bool {
    matches!(numeric_flow(from, to), Flow::Identity | Flow::Widen)
}

fn int_to_int(a: IntKind, b: IntKind) -> Flow {
    let (ab, bb) = (a.bits(), b.bits());
    match (a.is_signed(), b.is_signed()) {
        // Same signedness: strictly wider is preserving.
        (true, true) | (false, false) if ab < bb => Flow::Widen,
        // Unsigned into a STRICTLY wider signed integer is preserving.
        (false, true) if ab < bb => Flow::Widen,
        (true, false) => {
            Flow::Forbidden("a signed value does not fit an unsigned type; convert explicitly")
        }
        _ => Flow::Forbidden("implicit narrowing would be lossy; convert explicitly"),
    }
}

/// An integer flows into a float only when the float's mantissa holds every
/// value of the integer type exactly: 24 bits for float32, 53 for float64.
fn int_to_float(a: IntKind, b: FloatKind) -> Flow {
    let mantissa = match b {
        FloatKind::F32 => 24,
        FloatKind::F64 => 53,
    };
    // An unsigned type uses all its bits for magnitude; a signed one all but
    // the sign bit (which the float sign covers).
    let needed = if a.is_signed() {
        a.bits() - 1
    } else {
        a.bits()
    };
    if needed <= mantissa {
        Flow::Widen
    } else {
        Flow::Forbidden(
            "the integer exceeds the float's exact range; convert explicitly if the \
             precision loss is intended",
        )
    }
}

fn float_bits(f: FloatKind) -> u32 {
    match f {
        FloatKind::F32 => 32,
        FloatKind::F64 => 64,
    }
}

/// The smallest numeric type BOTH `a` and `b` flow into implicitly: the type
/// two non-literal numeric operands meet at (the full rule, literals
/// included, is [`crate::common_operand_type`]). `None` when either type is
/// not numeric or no value-preserving common type exists (e.g. `int64` with
/// `uint64`, or `int64` with `float64`) -- the operands must then be
/// converted explicitly.
pub fn common_numeric_type(a: &Type, b: &Type) -> Option<Type> {
    if !is_numeric(a) || !is_numeric(b) {
        return None;
    }
    if a == b {
        return Some(a.clone());
    }
    if numeric_flows_into(a, b) {
        return Some(b.clone());
    }
    if numeric_flows_into(b, a) {
        return Some(a.clone());
    }
    // Neither side reaches the other directly; try the candidates both could
    // widen into, smallest first.
    let candidates = [
        Type::Int(IntKind::I16),
        Type::Int(IntKind::I32),
        Type::Int(IntKind::I64),
        Type::Float(FloatKind::F32),
        Type::Float(FloatKind::F64),
    ];
    candidates
        .into_iter()
        .find(|c| numeric_flows_into(a, c) && numeric_flows_into(b, c))
}

fn is_numeric(t: &Type) -> bool {
    matches!(t, Type::Int(_) | Type::Float(_))
}
