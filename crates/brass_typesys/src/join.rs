//! The value join: the single type several values reaching one place are
//! read back at -- the `return`s of one callable instance, the error payloads
//! of one fallible body, the branch values of a value-producing `if`/`match`,
//! the values pushed into an empty array, the elements of a numeric bracket
//! literal, the arguments of a `let` closure's direct calls. A binary
//! operator's two operands meet by the same rule
//! ([`crate::common_operand_type`]).
//!
//! Every pass that reconciles such a set (the checker's definitional pass and
//! its per-instance re-elaboration, monomorphization) asks [`join_values`],
//! so the type is decided by one rule everywhere and never by which value
//! happened to be visited first.

use brass_hir::{FloatKind, IntKind, Program, Type};
use brass_solver::unify::Subst;

use crate::flow::numeric_flows_into;
use crate::operators::NumericLiteral;
use crate::structural::types_compatible;

/// One value taking part in a join: its type, and its literal value when the
/// value is written as a numeric literal.
#[derive(Clone, Debug, PartialEq)]
pub struct JoinOperand {
    pub ty: Type,
    pub literal: Option<NumericLiteral>,
}

impl JoinOperand {
    /// An operand that is not a literal.
    pub fn value(ty: Type) -> Self {
        Self { ty, literal: None }
    }
}

/// Two operands of a join with no common type, as indices into the operand
/// slice (`first < second`), so the caller can point at both values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JoinConflict {
    pub first: usize,
    pub second: usize,
}

impl JoinConflict {
    fn new(a: usize, b: usize) -> Self {
        Self {
            first: a.min(b),
            second: a.max(b),
        }
    }
}

/// The type every operand flows into: the join of one value set (see the
/// module documentation). The result does not depend on the order of
/// `operands`. `Ok(None)` for an empty set.
///
/// The rules, applied to resolved types:
///
/// - A `never` operand (a path that diverged) constrains nothing.
/// - A bare `null` (`never?`) or a nullable operand makes the join nullable:
///   `T` and `null` join to `T?`. A bare `null` joined only with `void` (a
///   nullable `!` used as a statement in a value-less body) is `void`: the
///   null carries nothing a caller could observe.
/// - Numeric operands join to the smallest type every one of them flows into
///   value-preservingly ([`numeric_flows_into`]): `int32` and `int64` join to
///   `int64`, `int8` and `uint8` to `int16`, `int32` and `float64` to
///   `float64`. A numeric literal first ADAPTS: when its value fits the join
///   of the non-literal numeric operands it takes that type; otherwise it
///   keeps its default type ([`NumericLiteral::default_type`]) and takes part
///   in the join like a typed value. So `small_int8` with `100` is `int8`,
///   while `small_int8` with `300` is `int32`, in either order.
/// - Other operands must unify (an open inference variable unifies with
///   anything, including the numeric join) or be related by declared sum
///   subtyping, in which case the join is the parent sum (the subtype value
///   is rebuilt as the parent where it flows out). Records of different
///   declarations never join: they have different layouts.
///
/// A set with no join is reported as the first pair found that has none.
pub fn join_values(
    program: &Program,
    operands: &[JoinOperand],
) -> Result<Option<Type>, JoinConflict> {
    let mut nullable = false;
    let mut saw_null = false;
    // (operand index, value type with one nullable layer peeled, literal)
    let mut items: Vec<(usize, Type, Option<NumericLiteral>)> = Vec::new();
    for (i, op) in operands.iter().enumerate() {
        match &op.ty {
            Type::Never => {}
            Type::Nullable(inner) if matches!(**inner, Type::Never) => {
                nullable = true;
                saw_null = true;
            }
            Type::Nullable(inner) => {
                nullable = true;
                items.push((i, (**inner).clone(), op.literal));
            }
            other => items.push((i, other.clone(), op.literal)),
        }
    }
    if items.is_empty() {
        return Ok(match (operands.is_empty(), nullable) {
            (true, _) => None,
            (false, true) => Some(Type::null()),
            (false, false) => Some(Type::Never),
        });
    }
    if saw_null && items.iter().all(|(_, ty, _)| matches!(ty, Type::Void)) {
        return Ok(Some(Type::Void));
    }
    let (numeric, others): (Vec<_>, Vec<_>) = items
        .into_iter()
        .partition(|(_, ty, _)| matches!(ty, Type::Int(_) | Type::Float(_)));
    let numeric_join = join_numeric(&numeric)?;
    let joined = match (numeric_join, others.is_empty()) {
        (Some((ty, _)), true) => ty,
        (numeric_join, false) => join_others(program, &others, numeric_join)?,
        (None, true) => unreachable!("a non-empty item set is numeric or not"),
    };
    Ok(Some(if nullable {
        Type::nullable(joined)
    } else {
        joined
    }))
}

/// The element type a bracket literal's elements share when they are all
/// numbers: their value join ([`join_values`]), so a literal element adapts
/// to the others (`[big, 1]` with `big: int64` is an `int64` sequence) and
/// typed elements meet at the smallest type they all widen to (`int32` and
/// `int64` make `int64`). `None` when some element is not a number (a
/// nullable number counts as its number; `null` elements are the caller's
/// to exclude) or the numbers have no common type (`int64` with `uint64`):
/// the literal is then classified by unification, a tuple when the elements
/// do not unify.
///
/// The checker's passes and monomorphization classify bracket literals by
/// this one rule, so a literal is an array or a tuple identically for all of
/// them.
pub fn numeric_element_join(program: &Program, elements: &[JoinOperand]) -> Option<Type> {
    let numeric = |ty: &Type| matches!(ty, Type::Int(_) | Type::Float(_));
    let all_numeric = !elements.is_empty()
        && elements.iter().all(|op| match &op.ty {
            Type::Nullable(inner) => numeric(inner),
            other => numeric(other),
        });
    if !all_numeric {
        return None;
    }
    join_values(program, elements).ok().flatten()
}

/// The join of the numeric operands, with the index of one of them (for a
/// conflict against a non-numeric operand). `Ok(None)` when there are none.
/// A binary operator's operand type is this join of its two operands
/// (`crate::operators::common_operand_type`).
pub(crate) fn join_numeric(
    numeric: &[(usize, Type, Option<NumericLiteral>)],
) -> Result<Option<(Type, usize)>, JoinConflict> {
    let Some((first_idx, _, _)) = numeric.first() else {
        return Ok(None);
    };
    let typed: Vec<(usize, Type)> = numeric
        .iter()
        .filter(|(_, _, lit)| lit.is_none())
        .map(|(i, ty, _)| (*i, ty.clone()))
        .collect();
    let base = least_numeric_upper_bound(&typed)?;
    // A literal that fits the typed operands' join adapts to it; any other
    // literal joins at its default type.
    let mut all = typed;
    for (i, _, lit) in numeric {
        if let Some(lit) = lit
            && !base.as_ref().is_some_and(|b| lit.fits(b))
        {
            all.push((*i, lit.default_type()));
        }
    }
    let joined = least_numeric_upper_bound(&all)?
        .expect("a non-empty numeric operand set joins to some type or conflicts");
    Ok(Some((joined, *first_idx)))
}

/// The smallest numeric type every type in `types` flows into
/// value-preservingly: one of the types itself when it absorbs all the
/// others, else the narrowest common candidate. `Ok(None)` for an empty set.
fn least_numeric_upper_bound(types: &[(usize, Type)]) -> Result<Option<Type>, JoinConflict> {
    if types.is_empty() {
        return Ok(None);
    }
    let absorbs = |target: &Type| types.iter().all(|(_, t)| numeric_flows_into(t, target));
    if let Some((_, own)) = types.iter().find(|(_, t)| absorbs(t)) {
        return Ok(Some(own.clone()));
    }
    let candidates = [
        Type::Int(IntKind::I16),
        Type::Int(IntKind::I32),
        Type::Int(IntKind::I64),
        Type::Float(FloatKind::F32),
        Type::Float(FloatKind::F64),
    ];
    if let Some(found) = candidates.into_iter().find(|c| absorbs(c)) {
        return Ok(Some(found));
    }
    // No common type: name a pair that has none (one exists for the numeric
    // kinds; fall back to the extremes of the set otherwise).
    for (x, (i, a)) in types.iter().enumerate() {
        for (j, b) in &types[x + 1..] {
            if crate::flow::common_numeric_type(a, b).is_none() {
                return Err(JoinConflict::new(*i, *j));
            }
        }
    }
    Err(JoinConflict::new(types[0].0, types[types.len() - 1].0))
}

/// The join of the non-numeric operands (plus the numeric join, which open
/// variables among them unify with).
fn join_others(
    program: &Program,
    others: &[(usize, Type, Option<NumericLiteral>)],
    numeric_join: Option<(Type, usize)>,
) -> Result<Type, JoinConflict> {
    let mut subst = Subst::new();
    let (mut top_idx, mut top) = (others[0].0, others[0].1.clone());
    for (idx, ty, _) in &others[1..] {
        let snapshot = subst.snapshot();
        if subst.unify(&top, ty).is_ok() {
            // Two instances of one declaration unify on their shared slots;
            // the join carries the slots either one pins (an `A { x }` and a
            // `B { y }` of one sum are one value type with both payloads).
            top = union_slots(&top, ty);
            continue;
        }
        subst.rollback(snapshot);
        if flows_to(program, ty, &top) {
            continue;
        }
        if flows_to(program, &top, ty) {
            (top_idx, top) = (*idx, ty.clone());
            continue;
        }
        return Err(JoinConflict::new(top_idx, *idx));
    }
    // Every operand must reach the chosen top (a sibling seen before a wider
    // top was chosen included).
    for (idx, ty, _) in others {
        let snapshot = subst.snapshot();
        if subst.unify(&top, ty).is_ok() || flows_to(program, ty, &top) {
            continue;
        }
        subst.rollback(snapshot);
        return Err(JoinConflict::new(top_idx, *idx));
    }
    if let Some((numeric, numeric_idx)) = numeric_join {
        let snapshot = subst.snapshot();
        if subst.unify(&top, &numeric).is_err() {
            subst.rollback(snapshot);
            return Err(JoinConflict::new(numeric_idx, top_idx));
        }
    }
    Ok(subst.resolve_deep(&top))
}

/// `a` with every slot of `b` it does not pin itself added, when both are
/// instances of the same declaration (their shared slots have already
/// unified); otherwise `a` unchanged.
fn union_slots(a: &Type, b: &Type) -> Type {
    match (a, b) {
        (Type::Record(x), Type::Record(y)) | (Type::Sum(x), Type::Sum(y)) if x.id == y.id => {
            let mut joined = x.clone();
            for (key, ty) in y.substitution.iter() {
                if joined.substitution.get(key).is_none() {
                    joined.substitution.insert(key, ty.clone());
                }
            }
            match a {
                Type::Record(_) => Type::Record(joined),
                _ => Type::Sum(joined),
            }
        }
        _ => a.clone(),
    }
}

/// The only join between types that do not unify: a declared sum subtype
/// reaches its parent through a rebuild at the flow site. Structural record
/// satisfaction and function subtyping do not establish a shared value type.
fn flows_to(program: &Program, have: &Type, want: &Type) -> bool {
    matches!((have, want), (Type::Sum(h), Type::Sum(w)) if h.id != w.id)
        && types_compatible(program, have, want)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(kind: IntKind) -> Type {
        Type::Int(kind)
    }

    fn join(ops: &[JoinOperand]) -> Result<Option<Type>, JoinConflict> {
        join_values(&Program::empty(), ops)
    }

    fn lit(v: i128) -> JoinOperand {
        JoinOperand {
            ty: NumericLiteral::Int(v).default_type(),
            literal: Some(NumericLiteral::Int(v)),
        }
    }

    /// A literal adapts to the typed operands' join when it fits; one that
    /// does not keeps its default type and widens the join -- in either order.
    #[test]
    fn literals_adapt_or_widen_independent_of_order() {
        let small = JoinOperand::value(int(IntKind::I8));
        assert_eq!(join(&[small.clone(), lit(100)]), Ok(Some(int(IntKind::I8))));
        assert_eq!(join(&[lit(100), small.clone()]), Ok(Some(int(IntKind::I8))));
        assert_eq!(
            join(&[small.clone(), lit(300)]),
            Ok(Some(int(IntKind::I32)))
        );
        assert_eq!(join(&[lit(300), small]), Ok(Some(int(IntKind::I32))));
        let big = JoinOperand::value(int(IntKind::I64));
        assert_eq!(join(&[lit(1), big]), Ok(Some(int(IntKind::I64))));
        let float = JoinOperand::value(Type::Float(FloatKind::F64));
        assert_eq!(
            join(&[lit(0), float]),
            Ok(Some(Type::Float(FloatKind::F64)))
        );
    }

    /// Typed numeric values widen value-preservingly; a pair with no common
    /// type is a conflict naming both operands.
    #[test]
    fn typed_numerics_widen_or_conflict() {
        let ops = [
            JoinOperand::value(int(IntKind::I32)),
            JoinOperand::value(int(IntKind::I64)),
        ];
        assert_eq!(join(&ops), Ok(Some(int(IntKind::I64))));
        let ops = [
            JoinOperand::value(int(IntKind::I8)),
            JoinOperand::value(int(IntKind::U8)),
        ];
        assert_eq!(join(&ops), Ok(Some(int(IntKind::I16))));
        let ops = [
            JoinOperand::value(int(IntKind::I64)),
            JoinOperand::value(Type::Float(FloatKind::F64)),
        ];
        assert_eq!(join(&ops), Err(JoinConflict::new(0, 1)));
        // The set's own bound, not a pairwise fold: uint32 + int8 alone would
        // pick int64, which float32 cannot reach.
        let ops = [
            JoinOperand::value(int(IntKind::U32)),
            JoinOperand::value(int(IntKind::I8)),
            JoinOperand::value(Type::Float(FloatKind::F32)),
        ];
        assert_eq!(join(&ops), Ok(Some(Type::Float(FloatKind::F64))));
    }

    /// `null` makes the join nullable; a value and a string never join.
    #[test]
    fn null_wraps_and_kinds_conflict() {
        let ops = [
            JoinOperand::value(Type::null()),
            JoinOperand::value(int(IntKind::I32)),
        ];
        assert_eq!(join(&ops), Ok(Some(Type::nullable(int(IntKind::I32)))));
        let ops = [
            JoinOperand::value(Type::Str),
            JoinOperand::value(Type::Never),
            lit(1),
        ];
        assert_eq!(join(&ops), Err(JoinConflict::new(0, 2)));
        let ops = [
            JoinOperand::value(Type::null()),
            JoinOperand::value(Type::Void),
        ];
        assert_eq!(join(&ops), Ok(Some(Type::Void)));
    }

    /// Instances of one sum built from different variants join to the one
    /// instance carrying both variants' payload slots, in either order.
    #[test]
    fn variant_instances_join_their_slots() {
        let with = |key: &str, ty: Type| {
            let mut n = brass_hir::NominalType::new(3, "T");
            n.substitution.insert(key, ty);
            Type::Sum(n)
        };
        let a = with("A.x", int(IntKind::I32));
        let b = with("B.y", Type::Str);
        let mut both = brass_hir::NominalType::new(3, "T");
        both.substitution.insert("A.x", int(IntKind::I32));
        both.substitution.insert("B.y", Type::Str);
        let expected = Ok(Some(Type::Sum(both)));
        let ops = [JoinOperand::value(a.clone()), JoinOperand::value(b.clone())];
        assert_eq!(join(&ops), expected);
        let ops = [JoinOperand::value(b), JoinOperand::value(a)];
        assert_eq!(join(&ops), expected);
    }

    /// Function variance and structural width do not define a value join,
    /// even inside a container or when the return order is reversed.
    #[test]
    fn structural_and_function_subtyping_do_not_join() {
        let narrow = brass_hir::structural_record(vec![("a".into(), int(IntKind::I32))]);
        let wide = brass_hir::structural_record(vec![
            ("a".into(), int(IntKind::I32)),
            ("b".into(), Type::Str),
        ]);
        let pairs = [
            (narrow.clone(), wide.clone()),
            (
                Type::Fun(vec![narrow.clone()], Box::new(Type::Str)),
                Type::Fun(vec![wide.clone()], Box::new(Type::Str)),
            ),
            (Type::Slice(Box::new(narrow)), Type::Slice(Box::new(wide))),
        ];
        for (a, b) in pairs {
            for (left, right) in [(a.clone(), b.clone()), (b, a)] {
                assert_eq!(
                    join(&[JoinOperand::value(left.clone()), JoinOperand::value(right)]),
                    Err(JoinConflict::new(0, 1))
                );
                assert_eq!(
                    join(&[
                        JoinOperand::value(left.clone()),
                        JoinOperand::value(left.clone())
                    ]),
                    Ok(Some(left))
                );
            }
        }
    }

    /// An open variable unifies with the rest of the set, numeric included.
    #[test]
    fn open_variables_take_the_join() {
        let ops = [JoinOperand::value(Type::Unknown(7)), lit(1)];
        assert_eq!(join(&ops), Ok(Some(int(IntKind::I32))));
        let ops = [
            JoinOperand::value(Type::Slice(Box::new(Type::Unknown(3)))),
            JoinOperand::value(Type::Slice(Box::new(Type::Str))),
        ];
        assert_eq!(join(&ops), Ok(Some(Type::Slice(Box::new(Type::Str)))));
    }
}
