//! Joining an instance's return values into its return type, and the
//! consistency rule for re-typing a local.
//!
//! The checker reconciles an instantiation's returns with
//! [`brass_typesys::join_values`] and rejects the instantiations whose returns
//! have no join; monomorphization joins the same values with the same rule,
//! so the two agree on every accepted instance. A pair with no join reaching
//! this pass means the checker accepted something it should not have, so it
//! is an internal error -- never a silently chosen side, which the back ends
//! would then read at the wrong representation.

use super::*;
use brass_typesys::{JoinOperand, join_values};

/// The message for a pair of values the checker should have kept apart.
pub(super) fn join_conflict_error(what: &str, sym: &str, a: &Type, b: &Type) -> String {
    format!(
        "internal error: the {what} of `{sym}` have no common type (`{}` and `{}`); the type \
         checker should have rejected this instantiation",
        a.display(),
        b.display()
    )
}

impl Monomorphizer<'_, '_> {
    /// The join of the return operands of the blocks `mask` selects (the
    /// instance's live, reachable blocks) whose types are already known:
    /// `Ok(None)` until one is. A pair with no join is returned as `Err` for
    /// the caller to report once the fixpoint has settled (an operand typed
    /// from a still-provisional assumption may change before then).
    ///
    /// A `return` of the unit constant -- the MIR builder's synthesized
    /// fall-through of a body whose real returns all sit inside loops or
    /// after a diverging `!`, or a bare `return` -- yields to any value
    /// return, the way the checker never collects the fall-through: the body
    /// is `void` only when nothing else returns.
    pub(super) fn join_block_returns(
        &self,
        body: &MirBody,
        local_types: &[Option<Type>],
        mask: &[bool],
    ) -> Result<Option<Type>, Box<(Type, Type)>> {
        let mut operands = Vec::new();
        let mut unit_return = false;
        for (block, _) in body.blocks.iter().zip(mask).filter(|(_, live)| **live) {
            let Terminator::Return(op) = &block.term else {
                continue;
            };
            if matches!(op, Operand::Const(Literal::Void)) {
                unit_return = true;
                continue;
            }
            let ty = match op {
                Operand::Local(local) => local_types[local.index()].clone(),
                Operand::Const(lit) => const_type(lit).ok(),
            };
            if let Some(ty) = ty {
                operands.push(JoinOperand {
                    ty,
                    literal: operand_literal(op),
                });
            }
        }
        if operands.is_empty() && unit_return {
            return Ok(Some(Type::Void));
        }
        join_values(self.program, &operands).map_err(|conflict| {
            Box::new((
                operands[conflict.first].ty.clone(),
                operands[conflict.second].ty.clone(),
            ))
        })
    }
}

/// Whether `rv` hands over a value that already exists at its own type (a
/// copied local, a call result, a load, a global), as opposed to a literal or
/// a construction, which the back ends build directly at the destination's
/// type (so an `int32` literal element of a `float64[]` local is built as a
/// float). Only the former can disagree with the destination's
/// representation.
pub(super) fn reads_existing_value(rv: &Rvalue) -> bool {
    matches!(
        rv,
        Rvalue::Use(Operand::Local(_)) | Rvalue::Call(..) | Rvalue::Load(_) | Rvalue::Global(_)
    )
}

/// Whether a local already typed `cur` may receive a value of type `new`: the
/// two describe one representation up to a conversion the back ends perform
/// at the store (a numeric conversion, a nullable wrap or a narrowed unwrap,
/// a declared sum subtype rebuilt as its parent, or a refinement of the same
/// declaration). Anything else -- a string into an integer slot, a `Result`
/// into a plain value, records of different declarations, arrays of
/// differently sized elements -- would be read back at the wrong
/// representation.
pub(super) fn retype_flows(program: &Program, cur: &Type, new: &Type) -> bool {
    flows(program, cur, new, false)
}

fn flows(program: &Program, cur: &Type, new: &Type, nested: bool) -> bool {
    if cur == new {
        return true;
    }
    match (cur, new) {
        (Type::Never | Type::Unknown(_), _) | (_, Type::Never | Type::Unknown(_)) => true,
        // A scalar slot converts at the store; an element of shared storage
        // cannot (its neighbours keep the slot's width).
        (Type::Int(_) | Type::Float(_), Type::Int(_) | Type::Float(_)) => !nested,
        (Type::Nullable(c), Type::Nullable(n)) => flows(program, c, n, nested),
        (Type::Nullable(c), n) => !nested && flows(program, c, n, nested),
        (c, Type::Nullable(n)) => !nested && flows(program, c, n, nested),
        // One declaration: the slots both instances pin must agree (a bare
        // instance against a refined one is fine; two records whose shared
        // field types differ are two layouts). For a `Result` two payload
        // differences are one value shape: a payload the value's
        // construction left unpinned (`void`, `never`, open -- an
        // `error(..)` result's Ok side) belongs to the variant the value
        // does not hold, and an error payload may still be the raw value on
        // one side and the prelude `Error` it is lifted into on the other
        // (the lift rebuilds it where it propagates).
        (Type::Record(c), Type::Record(n)) | (Type::Sum(c), Type::Sum(n))
            if c.id == n.id && (c.id >= 0 || c.name() == n.name()) =>
        {
            c.substitution.iter().all(|(key, ct)| {
                n.substitution.get(key).is_none_or(|nt| {
                    flows(program, ct, nt, true)
                        || (c.is_result_type()
                            && (unpinned_payload(nt)
                                || (key == brass_hir::types::RESULT_ERR_ERROR
                                    && lift_pair(program, ct, nt))))
                })
            })
        }
        (Type::Record(_), Type::Record(_)) | (Type::Sum(_), Type::Sum(_)) => {
            !nested && brass_typesys::types_compatible(program, new, cur)
        }
        (Type::Slice(c), Type::Slice(n))
        | (Type::Array(c, _), Type::Array(n, _))
        | (Type::Slice(c), Type::Array(n, _))
        | (Type::Array(c, _), Type::Slice(n)) => flows(program, c, n, true),
        (Type::Tuple(c), Type::Tuple(n)) => {
            c.len() == n.len() && c.iter().zip(n).all(|(c, n)| flows(program, c, n, true))
        }
        (Type::Fun(..), Type::Fun(..)) => true,
        _ => false,
    }
}

/// The type a `Result` local typed `cur` takes when it is also assigned a
/// `Result` of type `new`, when the two are one value shape seen from two
/// constructions; `None` when they are not (a payload both sides pin
/// differently), or when either is not a `Result`.
///
/// Payload by payload: a side one of them leaves unpinned (`void`, `never`
/// or open -- an `Err` construction says nothing about the Ok payload, which
/// is uninhabited for that value) yields to the other, and a raw error
/// payload yields to the prelude `Error` it is lifted into.
pub(super) fn result_merge(program: &Program, cur: &Type, new: &Type) -> Option<Type> {
    let (Type::Sum(c), Type::Sum(n)) = (cur, new) else {
        return None;
    };
    if !c.is_result_type() || c.id != n.id {
        return None;
    }
    let error_id = program.prelude_type("Error").map(|info| info.id);
    let is_error = |t: &Type| matches!(t, Type::Record(r) if Some(r.id) == error_id);
    let mut merged = Substitution::empty();
    for key in [
        brass_hir::types::RESULT_OK_VALUE,
        brass_hir::types::RESULT_ERR_ERROR,
    ] {
        let payload = match (c.substitution.get(key), n.substitution.get(key)) {
            (Some(a), Some(b)) if a == b => a.clone(),
            (None, Some(t)) | (Some(t), None) => t.clone(),
            (Some(a), Some(b)) if unpinned_payload(a) => b.clone(),
            (Some(a), Some(b)) if unpinned_payload(b) => a.clone(),
            (Some(a), Some(b))
                if key == brass_hir::types::RESULT_ERR_ERROR && is_error(b) && !is_error(a) =>
            {
                b.clone()
            }
            (Some(a), Some(b))
                if key == brass_hir::types::RESULT_ERR_ERROR && is_error(a) && !is_error(b) =>
            {
                a.clone()
            }
            (None, None) => continue,
            _ => return None,
        };
        merged.insert(key, payload);
    }
    Some(Type::Sum(NominalType::with_substitution(
        c.id,
        c.name.clone(),
        merged,
    )))
}

/// Whether a `Result` payload type is the unpinned side of a construction:
/// `void` (the default a construction gives the variant it does not build),
/// `never`, or still open.
fn unpinned_payload(ty: &Type) -> bool {
    matches!(ty, Type::Void | Type::Never | Type::Unknown(_))
}

/// Whether exactly one of two error payloads is the prelude `Error`: a raw
/// payload and the `Error` it is lifted into.
fn lift_pair(program: &Program, a: &Type, b: &Type) -> bool {
    let error_id = program.prelude_type("Error").map(|info| info.id);
    let is_error = |t: &Type| matches!(t, Type::Record(r) if Some(r.id) == error_id);
    is_error(a) != is_error(b)
}
