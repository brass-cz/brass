//! Typing of join locals ([`brass_mir::TypeRef::Join`]): the result of a
//! value-producing `if`/`if let`/`match`, which each arm writes.
//!
//! The checker types such an expression as the join of its arm values
//! (`brass_typesys::join_values` for numbers: `if c { an_int64 } else { 0 }`
//! is `int64`). An ordinary local takes the type of whichever assignment the
//! fixpoint types first, which would make the result `int32` when the literal
//! arm comes first and narrow the other arm's value into it. A join local
//! instead waits until every arm value is typed and takes their join, so the
//! instance computes at the checked type.

use super::*;

/// The values each join local is assigned in this instance's live blocks. A
/// join local written by anything but a plain value copy is left out and
/// types as an ordinary local.
pub(super) type JoinSources = HashMap<LocalId, Vec<Operand>>;

pub(super) fn collect_join_sources(body: &MirBody, live: &[bool]) -> JoinSources {
    let mut sources = JoinSources::default();
    let mut other_writes: HashSet<LocalId> = HashSet::default();
    for (block, _) in body.blocks.iter().zip(live).filter(|(_, live)| **live) {
        for stmt in &block.stmts {
            let MirStmt::Assign(local, rv) = stmt else {
                continue;
            };
            if !body.local(*local).ty.is_join() {
                continue;
            }
            match rv {
                Rvalue::Use(op) => sources.entry(*local).or_default().push(op.clone()),
                _ => {
                    other_writes.insert(*local);
                }
            }
        }
    }
    sources.retain(|local, _| !other_writes.contains(local));
    sources
}

/// How far a join local's type is settled.
pub(super) enum JoinTyping {
    /// The arm values are numbers (or `null`) and their join is this type.
    Joined(Type),
    /// An arm value is not typed yet; the local waits for it.
    Pending,
    /// Not a numeric join: the local types like an ordinary one.
    Ordinary,
}

impl Monomorphizer<'_, '_> {
    /// The type of a join local whose arm values are `sources`. Numeric arm
    /// values (with `null` or nullable numbers among them) meet by the
    /// checker's join rule, an integer-literal value adapting like a literal
    /// arm; anything else is [`JoinTyping::Ordinary`]. While an arm value is
    /// untyped the local is [`JoinTyping::Pending`] -- unless `settle` is set
    /// (the fixpoint stalled: an arm typed only through this very local, or
    /// one that never types in this instance), in which case the typed values
    /// decide.
    pub(super) fn join_typing(
        &self,
        sources: &[Operand],
        local_types: &[Option<Type>],
        settle: bool,
    ) -> Result<JoinTyping, String> {
        let mut nullable = false;
        let mut pending = false;
        let mut values: Vec<(Type, Option<brass_typesys::NumericLiteral>)> =
            Vec::with_capacity(sources.len());
        for op in sources {
            match self.operand_type(op, local_types)? {
                None => pending = true,
                Some(Type::Never) => {}
                Some(t) if t.is_null() => nullable = true,
                Some(Type::Nullable(inner)) if matches!(*inner, Type::Int(_) | Type::Float(_)) => {
                    nullable = true;
                    values.push((*inner, None));
                }
                Some(t @ (Type::Int(_) | Type::Float(_))) => values.push((t, operand_literal(op))),
                Some(_) => return Ok(JoinTyping::Ordinary),
            }
        }
        if pending && !settle {
            return Ok(JoinTyping::Pending);
        }
        if values.is_empty() {
            return Ok(JoinTyping::Ordinary);
        }
        let operands: Vec<brass_typesys::JoinOperand> = values
            .into_iter()
            .map(|(ty, literal)| brass_typesys::JoinOperand { ty, literal })
            .collect();
        Ok(match brass_typesys::join_values(self.program, &operands) {
            Ok(Some(joined)) if nullable => JoinTyping::Joined(Type::Nullable(Box::new(joined))),
            Ok(Some(joined)) => JoinTyping::Joined(joined),
            _ => JoinTyping::Ordinary,
        })
    }
}
