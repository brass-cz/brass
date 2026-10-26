//! Numeric literal and operator typing: the default type of an integer
//! literal, which types a literal value fits, the common type two numeric
//! operands meet at, and the typing of a binary operator over numbers.
//!
//! This is the ONE rule every pass applies -- the checker (`infer` and its
//! light pre-pass) on source operands and monomorphization on MIR operands --
//! so the type an operation is checked at is the type it is compiled and
//! executed at. An operand is described by its type plus, when it is written
//! as a numeric literal, the literal's value: the rule is value-based, so the
//! passes agree whenever they see the same literal.
//!
//! The rule, as the language reference states it:
//!
//! - An integer literal's default type is `int32` when its value fits, else
//!   `int64`, else `uint64` ([`int_literal_kind`]); a float literal's is
//!   `float64`.
//! - A literal operand ADAPTS to the other operand's numeric type when its
//!   value fits that type ([`NumericLiteral::fits`]: an integer type whose
//!   range holds an integer literal, a float type representing an integer
//!   literal exactly, a float type at which a float literal stays finite):
//!   `b & 15` with `b: uint8` is `uint8`, `f * 2` and `f * 0.5` with
//!   `f: float32` are `float32`.
//! - Otherwise both operands take their common type, the smallest type both
//!   convert to value-preservingly ([`crate::common_numeric_type`]): `b + 300`
//!   is `int32`. Two literals meet at their default types' common type.
//! - The operation is computed at that operand type (integer arithmetic wraps
//!   at its width); a comparison yields `bool`, every other operator the
//!   operand type. `%`, the bitwise operators and the shifts need an integer
//!   operand type.

use brass_hir::{FloatKind, IntKind, Type};
use brass_parser::ast::{BinOp, Expr, UnaryOp};

/// The default type of an integer literal written without context: `int32`
/// when the value fits, otherwise `int64`, otherwise `uint64` (so
/// `18446744073709551615` is writable). `None` for a value no integer type
/// holds -- a negated literal below `INT64_MIN` -- which the checker rejects.
pub fn int_literal_kind(value: i128) -> Option<IntKind> {
    [IntKind::I32, IntKind::I64, IntKind::U64]
        .into_iter()
        .find(|kind| int_fits(value, *kind))
}

/// Whether an integer literal with this value can take type `ty` without
/// changing its value: an integer type whose range holds it, or a float type
/// that represents it exactly (`16777217` does not fit `float32`). This is
/// what "the literal fits" means at every flow site and in the operator rule.
/// Passing-mode and nullable wrappers are not seen through; callers peel the
/// position they check against.
pub fn literal_fits(value: i128, ty: &Type) -> bool {
    match ty {
        Type::Int(kind) => int_fits(value, *kind),
        // A round trip through the float is exact exactly when the float
        // holds the value; every literal value is far inside both float
        // ranges, so the casts never saturate.
        Type::Float(FloatKind::F32) => (value as f32) as i128 == value,
        Type::Float(FloatKind::F64) => (value as f64) as i128 == value,
        _ => false,
    }
}

fn int_fits(value: i128, kind: IntKind) -> bool {
    let bits = kind.bits();
    let (min, max) = if kind.is_signed() {
        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    } else {
        (0, (1i128 << bits) - 1)
    };
    (min..=max).contains(&value)
}

/// The value of an operand written as a numeric literal, sign included: the
/// one description of a literal every literal rule reads (operator operands,
/// flow positions, the value join of branches and returns). A literal has no
/// fixed type of its own; it takes [`Self::default_type`] unless it adapts
/// to a type it [fits](Self::fits).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum NumericLiteral {
    /// An integer literal, including a negated one (`-1`).
    Int(i128),
    /// A float literal, including a negated one.
    Float(f64),
}

impl NumericLiteral {
    /// The literal an expression is written as: an integer or float literal,
    /// or a negated one (`-1`, `-0.5`, which parse as a unary minus applied
    /// to the literal). `None` for any other expression, including a named
    /// constant or a computation.
    pub fn of_expr(expr: &Expr) -> Option<Self> {
        if let Some(value) = expr.int_literal_value() {
            return Some(NumericLiteral::Int(value));
        }
        match expr {
            Expr::Float(value, _) => Some(NumericLiteral::Float(*value)),
            Expr::Unary(UnaryOp::Neg, inner, _) => match &**inner {
                Expr::Float(value, _) => Some(NumericLiteral::Float(-*value)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The type the literal takes when nothing else decides it: an integer's
    /// [`int_literal_kind`] (`int32`, `int64`, then `uint64`; a value no
    /// integer type holds, which the checker rejects, reads as `int64`), and
    /// `float64` for a float.
    pub fn default_type(self) -> Type {
        match self {
            NumericLiteral::Int(value) => {
                Type::Int(int_literal_kind(value).unwrap_or(IntKind::I64))
            }
            NumericLiteral::Float(_) => Type::Float(FloatKind::F64),
        }
    }

    /// Whether the literal can take type `ty`: an integer literal per
    /// [`literal_fits`]; a float literal a float type at which it stays
    /// finite (rounding is accepted, as in every float context). A float
    /// literal never takes an integer type.
    pub fn fits(self, ty: &Type) -> bool {
        match (self, ty) {
            (NumericLiteral::Int(value), _) => literal_fits(value, ty),
            (NumericLiteral::Float(value), Type::Float(FloatKind::F32)) => {
                (value as f32).is_finite()
            }
            (NumericLiteral::Float(value), Type::Float(FloatKind::F64)) => value.is_finite(),
            (NumericLiteral::Float(_), _) => false,
        }
    }
}

/// One operand of a numeric operator or join, as the rule sees it.
#[derive(Clone, Copy, Debug)]
pub struct NumericOperand<'a> {
    /// The operand's type. For a literal this is the type it was typed at on
    /// its own (normally its default type).
    pub ty: &'a Type,
    /// The value, when the operand is written as a numeric literal. Any other
    /// operand -- a named constant, a parenthesized computation -- is `None`
    /// and never adapts.
    pub literal: Option<NumericLiteral>,
}

impl<'a> NumericOperand<'a> {
    pub fn new(ty: &'a Type, literal: Option<NumericLiteral>) -> Self {
        NumericOperand { ty, literal }
    }

    /// An operand that is not a literal.
    pub fn value(ty: &'a Type) -> Self {
        NumericOperand { ty, literal: None }
    }
}

/// The type two numeric operands meet at: the other operand's type when
/// exactly one of them is a literal that fits it, otherwise their common type
/// (the smallest both flow into value-preservingly). `None` when either type
/// is not numeric or the pair has no value-preserving common type. This is a
/// binary operator's operand type, and it is the value join
/// ([`crate::join_values`]) of the two operands: the branches of an `if`, a
/// function's returns and an operator's operands meet by the same rule.
pub fn common_operand_type(a: NumericOperand<'_>, b: NumericOperand<'_>) -> Option<Type> {
    if !is_numeric(a.ty) || !is_numeric(b.ty) {
        return None;
    }
    crate::join::join_numeric(&[(0, a.ty.clone(), a.literal), (1, b.ty.clone(), b.literal)])
        .ok()
        .flatten()
        .map(|(joined, _)| joined)
}

/// Why a binary operator has no numeric typing for its operands.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperatorError {
    /// The operator is a logical connective (`&&`, `||`) or an operand is not
    /// a number. The caller's non-numeric rules apply (string concatenation,
    /// equality of strings, bools and records, logical connectives), or the
    /// pair is an error.
    NotNumeric,
    /// Two numbers with no value-preserving common type (`int64` with
    /// `uint64`, `int64` with `float64`): one side must be converted
    /// explicitly.
    NoCommonType,
    /// `%`, a bitwise operator or a shift whose operands meet at a float type.
    IntegerOnly,
}

/// The typing of a binary operator over two numeric operands.
#[derive(Clone, Debug, PartialEq)]
pub struct NumericBinary {
    /// The type both operands convert to before the operation; the operation
    /// is computed (and an integer one wraps) at this type.
    pub operand: Type,
    /// The value the operator yields: `bool` for a comparison, otherwise
    /// `operand`.
    pub result: Type,
}

/// Type the binary operator `op` over two numeric operands -- the authority
/// every checker pass and monomorphization consult for arithmetic,
/// comparison, bitwise and shift operators (see the module documentation for
/// the rule). Compound assignment `x op= e` is typed by this same call with
/// `x` as the left operand; the result then flows into `x`.
pub fn numeric_binary(
    op: BinOp,
    a: NumericOperand<'_>,
    b: NumericOperand<'_>,
) -> Result<NumericBinary, OperatorError> {
    if matches!(op, BinOp::And | BinOp::Or) || !is_numeric(a.ty) || !is_numeric(b.ty) {
        return Err(OperatorError::NotNumeric);
    }
    let operand = common_operand_type(a, b).ok_or(OperatorError::NoCommonType)?;
    let integer_only = matches!(
        op,
        BinOp::Rem | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr
    );
    if integer_only && !matches!(operand, Type::Int(_)) {
        return Err(OperatorError::IntegerOnly);
    }
    let comparison = matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge
    );
    let result = if comparison {
        Type::Bool
    } else {
        operand.clone()
    };
    Ok(NumericBinary { operand, result })
}

fn is_numeric(ty: &Type) -> bool {
    matches!(ty, Type::Int(_) | Type::Float(_))
}

#[cfg(test)]
mod tests {
    use super::*;

    const U8: Type = Type::Int(IntKind::U8);
    const I16: Type = Type::Int(IntKind::I16);
    const I32: Type = Type::Int(IntKind::I32);
    const I64: Type = Type::Int(IntKind::I64);
    const U64: Type = Type::Int(IntKind::U64);
    const F32: Type = Type::Float(FloatKind::F32);
    const F64: Type = Type::Float(FloatKind::F64);

    fn lit(ty: &Type, value: i128) -> NumericOperand<'_> {
        NumericOperand::new(ty, Some(NumericLiteral::Int(value)))
    }

    /// Defaults widen by magnitude through `uint64`; the sign is part of the
    /// value, so `-2147483648` is still an `int32`.
    #[test]
    fn literal_defaults_follow_the_value() {
        assert_eq!(int_literal_kind(5), Some(IntKind::I32));
        assert_eq!(int_literal_kind(-2_147_483_648), Some(IntKind::I32));
        assert_eq!(int_literal_kind(3_000_000_000), Some(IntKind::I64));
        assert_eq!(int_literal_kind(i128::from(i64::MIN)), Some(IntKind::I64));
        assert_eq!(int_literal_kind(i128::from(u64::MAX)), Some(IntKind::U64));
        assert_eq!(int_literal_kind(i128::from(i64::MIN) - 1), None);
    }

    /// Fitting a float means exact representation, not merely range.
    #[test]
    fn float_fit_is_exact_representation() {
        assert!(literal_fits(16_777_216, &F32));
        assert!(!literal_fits(16_777_217, &F32));
        assert!(literal_fits(16_777_217, &F64));
        assert!(!literal_fits((1 << 53) + 1, &F64));
    }

    /// A literal adapts to a narrow operand it fits (arithmetic, bitwise and
    /// shifts alike), and otherwise keeps its default so both meet at the
    /// common type.
    #[test]
    fn literal_adapts_only_when_it_fits() {
        let narrow = numeric_binary(BinOp::Add, NumericOperand::value(&U8), lit(&I32, 100));
        assert_eq!(narrow.map(|t| t.result), Ok(U8));
        let mask = numeric_binary(BinOp::BitAnd, NumericOperand::value(&U8), lit(&I32, 15));
        assert_eq!(mask.map(|t| t.result), Ok(U8));
        let shift = numeric_binary(BinOp::Shr, NumericOperand::value(&I16), lit(&I32, 4));
        assert_eq!(shift.map(|t| t.result), Ok(I16));
        let wide = numeric_binary(BinOp::Add, NumericOperand::value(&U8), lit(&I32, 300));
        assert_eq!(wide.map(|t| t.result), Ok(I32));
        let cmp = numeric_binary(BinOp::Lt, lit(&I32, 300), NumericOperand::value(&U8));
        assert_eq!(
            cmp,
            Ok(NumericBinary {
                operand: I32,
                result: Type::Bool
            })
        );
    }

    /// An integer literal next to a float becomes that float, and so does a
    /// float literal that stays finite there; a negative literal never adapts
    /// to an unsigned type.
    #[test]
    fn literal_adapts_to_floats_and_respects_sign() {
        let f = numeric_binary(BinOp::Mul, NumericOperand::value(&F32), lit(&I32, 2));
        assert_eq!(f.map(|t| t.result), Ok(F32));
        let half = NumericOperand::new(&F64, Some(NumericLiteral::Float(0.5)));
        let f = numeric_binary(BinOp::Mul, NumericOperand::value(&F32), half);
        assert_eq!(f.map(|t| t.result), Ok(F32));
        let huge = NumericOperand::new(&F64, Some(NumericLiteral::Float(1e39)));
        let f = numeric_binary(BinOp::Mul, NumericOperand::value(&F32), huge);
        assert_eq!(f.map(|t| t.result), Ok(F64));
        let f = numeric_binary(BinOp::Mul, NumericOperand::value(&I32), half);
        assert_eq!(f.map(|t| t.result), Ok(F64));
        let u = numeric_binary(BinOp::Add, NumericOperand::value(&U64), lit(&I32, -1));
        assert_eq!(u, Err(OperatorError::NoCommonType));
        let u = numeric_binary(BinOp::Add, NumericOperand::value(&U64), lit(&I32, 1));
        assert_eq!(u.map(|t| t.result), Ok(U64));
    }

    /// An operator's operand type is the value join of its two operands: the
    /// operator rule and the join of branches and returns are one rule.
    #[test]
    fn operand_type_is_the_value_join() {
        use crate::join::{JoinOperand, join_values};
        let program = brass_hir::Program::empty();
        let int = |v: i128| Some(NumericLiteral::Int(v));
        let cases = [
            (I64, None, I32, int(0)),
            (U8, None, I32, int(300)),
            (U8, None, I32, int(200)),
            (I32, int(1), I64, int(3_000_000_000)),
            (U64, None, I32, int(-1)),
            (F32, None, F64, Some(NumericLiteral::Float(0.5))),
            (I16, None, U8, None),
        ];
        for (ta, la, tb, lb) in cases {
            let operand =
                common_operand_type(NumericOperand::new(&ta, la), NumericOperand::new(&tb, lb));
            let joined = join_values(
                &program,
                &[
                    JoinOperand {
                        ty: ta.clone(),
                        literal: la,
                    },
                    JoinOperand {
                        ty: tb.clone(),
                        literal: lb,
                    },
                ],
            )
            .ok()
            .flatten();
            assert_eq!(operand, joined, "{ta:?} {la:?} / {tb:?} {lb:?}");
        }
    }

    /// Two literals, or two typed operands, meet at their common type; the
    /// integer-only operators reject a float meeting point.
    #[test]
    fn non_literal_pairs_use_the_common_type() {
        assert_eq!(
            common_operand_type(lit(&I32, 1), lit(&I64, 3_000_000_000)),
            Some(I64)
        );
        assert_eq!(
            common_operand_type(NumericOperand::value(&I32), NumericOperand::value(&F64)),
            Some(F64)
        );
        assert_eq!(
            numeric_binary(BinOp::Rem, NumericOperand::value(&F64), lit(&I32, 2)),
            Err(OperatorError::IntegerOnly)
        );
        assert_eq!(
            numeric_binary(BinOp::And, NumericOperand::value(&I32), lit(&I32, 2)),
            Err(OperatorError::NotNumeric)
        );
    }
}
