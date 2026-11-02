//! The typing fixpoint of one instance body: resolving every local and the
//! return type until nothing changes.

use super::*;

/// What the fixpoint consults about a body's structure, scanned once per
/// instance: where each closure local gets its parameter types from, and the
/// pushes that type an empty `[]` literal.
pub(super) struct BodyScans {
    pub(super) indirect_args: HashMap<LocalId, Vec<Vec<Operand>>>,
    pub(super) closure_passes: HashMap<LocalId, Vec<ClosurePass>>,
    pub(super) record_field_closures: HashMap<LocalId, (LocalId, String, String)>,
    pub(super) array_pushes: HashMap<LocalId, Vec<Operand>>,
}

impl BodyScans {
    /// Closure parameter sources -- a direct in-body call, being passed to a
    /// higher-order function (probed from the callee), or initializing a
    /// record field with a declared function type -- and the array pushes
    /// that give an empty `[]` literal its element type.
    pub(super) fn of(body: &MirBody) -> Self {
        Self {
            indirect_args: collect_indirect_args(body),
            closure_passes: collect_closure_passes(body),
            record_field_closures: collect_record_field_closures(body),
            array_pushes: collect_array_pushes(body),
        }
    }
}

/// The blocks of `live` that are also reachable once the statically known
/// conditions fold against the types resolved so far (an untyped local
/// stands in as `Never`, whose truthiness is unknown, so a block is called
/// dead only on a condition that really did resolve).
pub(super) fn live_reachable(
    program: &Program,
    body: &MirBody,
    local_types: &[Option<Type>],
    live: &[bool],
) -> Vec<bool> {
    let probe: Vec<Type> = local_types
        .iter()
        .map(|t| t.clone().unwrap_or(Type::Never))
        .collect();
    reachable_blocks(program, body, &probe, &HashMap::default())
        .into_iter()
        .zip(live)
        .map(|(r, l)| r && *l)
        .collect()
}

/// The fixpoint's answer: the return type (`None` when nothing typed it) and
/// each block's held type error, or the pair of return types that had no
/// join when the fixpoint settled.
pub(super) type FixpointOutcome = Result<(Option<Type>, Vec<Option<String>>), Box<(Type, Type)>>;

impl<'m> Monomorphizer<'m, '_> {
    /// Type the `live` blocks of an instance body until stable. Calls are
    /// instantiated as they become resolvable; self-recursion reads the return
    /// type computed so far (`initial_ret` seeds it: the annotation, or a lower
    /// bound learned from an earlier attempt).
    ///
    /// A statement's type error is held against its block rather than raised:
    /// a block a statically-known `if` makes unreachable never runs, so an arm
    /// that cannot type for this instantiation (`s.split(..)` where `s` is an
    /// array) must not reject the program. Only the last round's errors stand
    /// -- earlier rounds fail merely because types are still filling in -- and
    /// the caller reports only those in blocks that stay reachable.
    ///
    /// A non-fallible callable's return type is the join of its return
    /// operands ([`brass_typesys::join_values`], the checker's rule), taken
    /// afresh each round over the blocks that are live and reachable under the
    /// types known so far: a `return null` path (`never?`) combines with a
    /// value path to that value's nullable type, an integer literal adapts to
    /// a wider sibling, and a path a folded condition kills contributes
    /// nothing. A fallible one's is `Result<ok, err>` ([`Self::infer_result_ret`]).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn type_body_fixpoint(
        &mut self,
        sym: &str,
        body: &'m MirBody,
        module: &[String],
        scans: &BodyScans,
        local_types: &mut [Option<Type>],
        live: &[bool],
        initial_ret: Option<Type>,
        annotated: bool,
        fallible: bool,
        declared_ok: Option<&Type>,
    ) -> Result<FixpointOutcome, String> {
        // A lower bound learned from an earlier attempt joins every round's
        // result, so the return can only grow from it.
        let floor = if annotated { None } else { initial_ret.clone() };
        let mut ret = initial_ret;
        let mut block_errors: Vec<Option<String>> = vec![None; body.blocks.len()];
        let mut conflict = None;
        // Every local types at most a handful of times (unknown, typed, then
        // only upgraded), so a body that keeps changing past this bound is a
        // defect, reported rather than spun on.
        let round_limit = 4 * (body.locals.len() + body.blocks.len()) + 64;
        let mut rounds = 0usize;
        let joins = super::join::collect_join_sources(body, live);
        // Set once the rounds stall with a join local still waiting on an arm
        // value: the typed arms then decide (see `join_typing`).
        let mut settle_joins = false;
        loop {
            rounds += 1;
            if rounds > round_limit {
                return Err(format!(
                    "internal error: the types of `{sym}` did not settle while typing its body"
                ));
            }
            let mut changed = false;
            block_errors.iter_mut().for_each(|e| *e = None);
            for (i, block) in body.blocks.iter().enumerate() {
                if !live[i] {
                    continue;
                }
                for stmt in &block.stmts {
                    if let Err(e) = self.type_stmt(
                        stmt,
                        body,
                        sym,
                        module,
                        &scans.indirect_args,
                        &scans.closure_passes,
                        &scans.record_field_closures,
                        &scans.array_pushes,
                        (&joins, settle_joins),
                        local_types,
                        &ret,
                        fallible,
                        &mut changed,
                    ) && block_errors[i].is_none()
                    {
                        block_errors[i] = Some(e);
                    }
                }
            }
            let mask = live_reachable(self.program, body, local_types, live);
            if !fallible && !annotated {
                match self.join_block_returns(body, local_types, &mask) {
                    Ok(joined) => {
                        conflict = None;
                        let joined = match (joined, &floor) {
                            (Some(t), Some(floor)) => self.join_pair(&t, floor),
                            (joined, _) => joined.or_else(|| floor.clone()),
                        };
                        if joined.is_some() && joined != ret {
                            ret = joined;
                            changed = true;
                        }
                    }
                    Err(pair) => conflict = Some(pair),
                }
            }
            if fallible
                && let Some(t) =
                    self.infer_result_ret(sym, body, local_types, declared_ok, &mask)?
                && ret.as_ref() != Some(&t)
            {
                ret = Some(t);
                changed = true;
            }
            if !changed {
                let waiting = joins
                    .keys()
                    .any(|local| local_types[local.index()].is_none());
                if settle_joins || !waiting {
                    break;
                }
                settle_joins = true;
            }
        }
        Ok(match conflict {
            Some(pair) => Err(pair),
            None => Ok((ret, block_errors)),
        })
    }

    /// The value join of two types, or the first when they have none (the
    /// conflict itself is reported by the caller's own join).
    fn join_pair(&self, a: &Type, b: &Type) -> Option<Type> {
        brass_typesys::join_values(
            self.program,
            &[
                brass_typesys::JoinOperand::value(a.clone()),
                brass_typesys::JoinOperand::value(b.clone()),
            ],
        )
        .unwrap_or_else(|_| Some(a.clone()))
    }
}
