//! Typing one MIR statement inside an instance body's fixpoint: an
//! assignment types its destination local (join locals, closures, empty
//! array literals, and the rules for re-typing an already-typed local), a
//! discarded call is typed for its effect, and stores and global
//! initializations are checked or recorded.

use super::*;

impl Monomorphizer<'_, '_> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn type_stmt(
        &mut self,
        stmt: &MirStmt,
        body: &MirBody,
        cur_sym: &str,
        module: &[String],
        indirect_args: &HashMap<LocalId, Vec<Vec<Operand>>>,
        closure_passes: &HashMap<LocalId, Vec<ClosurePass>>,
        record_field_closures: &HashMap<LocalId, (LocalId, String, String)>,
        array_pushes: &HashMap<LocalId, Vec<Operand>>,
        (joins, settle_joins): (&join::JoinSources, bool),
        local_types: &mut [Option<Type>],
        cur_ret: &Option<Type>,
        fallible: bool,
        changed: &mut bool,
    ) -> Result<(), String> {
        match stmt {
            // An empty array literal `[]` gets its element type from a later
            // `push` (it is filled before use).
            MirStmt::Assign(local, Rvalue::Array(es)) if es.is_empty() => {
                if local_types[local.index()].is_none() {
                    // A literal copied straight into an annotated binding
                    // (`let frames: Frame[] = []` lowers through a temp) takes
                    // the binding's seeded type.
                    for block in &body.blocks {
                        for stmt in &block.stmts {
                            if let MirStmt::Assign(dst, Rvalue::Use(Operand::Local(src))) = stmt
                                && src == local
                                && let Some(t @ (Type::Slice(_) | Type::Array(..))) =
                                    &local_types[dst.index()]
                            {
                                local_types[local.index()] = Some(t.clone());
                                *changed = true;
                                return Ok(());
                            }
                        }
                    }
                    let Some(elem_ops) = array_pushes.get(local) else {
                        let binding = match binding_name_of(body, *local) {
                            Some(n) => format!(" bound to `{n}`"),
                            None => String::new(),
                        };
                        // A synthetic symbol (an init body) means top-level
                        // code; the wrapper already says so, and the mangled
                        // name would only confuse.
                        let context = if cur_sym.starts_with(SYNTH_SIGIL) {
                            String::new()
                        } else {
                            format!(" (in `{cur_sym}`)")
                        };
                        return Err(format!(
                            "the element type of the empty array literal{binding} is unknown: \
                             annotate the binding (e.g. `let x: T[] = []`) or push a value into \
                             it first{context}"
                        ));
                    };
                    // The pushed values join like returns: a literal adapts
                    // to a wider sibling, `null` makes the element nullable.
                    let mut pushed = Vec::with_capacity(elem_ops.len());
                    for op in elem_ops {
                        let Some(ty) = self.operand_type(op, local_types)? else {
                            return Ok(());
                        };
                        pushed.push(brass_typesys::JoinOperand {
                            ty,
                            literal: operand_literal(op),
                        });
                    }
                    let elem = brass_typesys::join_values(self.program, &pushed).map_err(|c| {
                        returns::join_conflict_error(
                            "pushed elements",
                            cur_sym,
                            &pushed[c.first].ty,
                            &pushed[c.second].ty,
                        )
                    })?;
                    if let Some(elem) = elem {
                        local_types[local.index()] = Some(Type::Slice(Box::new(elem)));
                        *changed = true;
                    }
                }
                Ok(())
            }
            // A closure local is typed from the function type the checker fixed
            // for it (the local's declared type), else from how it is used -- an
            // in-body call or being passed to a higher-order function; this also
            // instantiates the closure body. A checked local is seeded with its
            // type before the walk, so it is (re)typed here until its body is
            // instantiated and its return settled.
            MirStmt::Assign(local, Rvalue::Closure { id, captures }) => {
                // A returned closure's local may have been seeded with the
                // instance's return instead (`seed_returned_closure`).
                let seeded = match &local_types[local.index()] {
                    Some(t @ Type::Fun(..)) => Some(t.clone()),
                    _ => None,
                };
                let declared = self.local_seed(body.local(*local));
                let checked = declared.as_ref().or(seeded.as_ref());
                if (checked.is_some() || local_types[local.index()].is_none())
                    && let Some(t) = self.closure_local_type(
                        *id,
                        captures,
                        *local,
                        checked,
                        module,
                        indirect_args,
                        closure_passes,
                        record_field_closures,
                        local_types,
                    )?
                    && local_types[local.index()].as_ref() != Some(&t)
                {
                    local_types[local.index()] = Some(t);
                    *changed = true;
                }
                Ok(())
            }
            MirStmt::Assign(local, rv) => {
                // The result of a value-producing `if`/`match` is the join of
                // its arm values, not its first-typed arm.
                if let Some(sources) = joins.get(local) {
                    match self.join_typing(sources, local_types, settle_joins)? {
                        join::JoinTyping::Joined(t) => {
                            if local_types[local.index()].as_ref() != Some(&t) {
                                local_types[local.index()] = Some(t);
                                *changed = true;
                            }
                            return Ok(());
                        }
                        join::JoinTyping::Pending => return Ok(()),
                        join::JoinTyping::Ordinary => {}
                    }
                }
                // The destination's already-known type (a `let x: T` annotation, or
                // a call result seeded from the checker via a `Known` local) is the
                // expected type for the rvalue -- in particular a static call's
                // return-polymorphic result.
                let expected = local_types[local.index()].clone();
                let t = self.rvalue_type(
                    rv,
                    cur_sym,
                    module,
                    local_types,
                    cur_ret,
                    fallible,
                    expected.as_ref(),
                )?;
                match (expected, t) {
                    (None, Some(t)) => {
                        local_types[local.index()] = Some(t);
                        *changed = true;
                    }
                    // A Result local assigned Results of one shape seen from
                    // different constructions takes their payload-wise merge:
                    // an Err construction leaves the Ok payload unpinned (and
                    // vice versa), and an Err payload upgrades to the lifted
                    // (prelude `Error`) shape -- the pre-lift typing was
                    // provisional (see `infer_result_ret`).
                    (Some(cur), Some(t))
                        if let Some(merged) = returns::result_merge(self.program, &cur, &t)
                            && merged != cur =>
                    {
                        local_types[local.index()] = Some(merged);
                        *changed = true;
                    }
                    // A destination seeded with a BARE nominal (the checker's
                    // seed of a call whose callee declares a bare `-> T`)
                    // upgrades to the rvalue's REFINEMENT of it: the nominal
                    // is unchanged, the slots only the callee's body could
                    // type (unannotated fields) fill in. Refinement strictly
                    // adds information, so the fixpoint stays monotone.
                    (Some(cur), Some(t)) if cur != t && is_refinement_of(&cur, &t) => {
                        local_types[local.index()] = Some(t);
                        *changed = true;
                    }
                    // A local first assigned `null` types as bare `never?`; a
                    // later concrete assignment upgrades it to that type's
                    // nullable (`let a: A? = null` then `a = A { .. }` makes
                    // the local `A?`). Without the upgrade the stale `never`
                    // element reaches codegen, where a nullable wrap of a
                    // "never" payload skips the retain and double-frees.
                    (Some(cur), Some(t)) if cur.is_null() && !t.is_null() => {
                        local_types[local.index()] = Some(match t {
                            t @ Type::Nullable(_) => t,
                            other => Type::Nullable(Box::new(other)),
                        });
                        *changed = true;
                    }
                    // Symmetrically, assigning `null` into a local first typed
                    // concrete makes it nullable, so the null representation
                    // (a null cell pointer) matches the local's element type.
                    (Some(cur), Some(t))
                        if t.is_null() && !cur.is_null() && !matches!(cur, Type::Nullable(_)) =>
                    {
                        local_types[local.index()] = Some(Type::Nullable(Box::new(cur)));
                        *changed = true;
                    }
                    // Any other value must reach the local's representation
                    // through a conversion the back ends perform at the store;
                    // keeping the old type would read the new value at the
                    // wrong representation.
                    (Some(cur), Some(t))
                        if returns::reads_existing_value(rv)
                            && !returns::retype_flows(self.program, &cur, &t) =>
                    {
                        let name = binding_name_of(body, *local).map_or_else(
                            || format!("local _{}", local.index()),
                            |n| format!("`{n}`"),
                        );
                        return Err(format!(
                            "internal error: {name} in `{cur_sym}` has type `{}` but is assigned \
                             a `{}` value",
                            cur.display(),
                            t.display()
                        ));
                    }
                    _ => {}
                }
                Ok(())
            }
            // A call run for its side effect (the result is discarded).
            MirStmt::Eval(rv @ Rvalue::Call(..)) => {
                self.rvalue_type(rv, cur_sym, module, local_types, cur_ret, fallible, None)?;
                Ok(())
            }
            MirStmt::Eval(_) => {
                Err("unsupported statement (non-call eval) on the typed backend".into())
            }
            MirStmt::Store(place, value) => {
                if !matches!(
                    place.proj.as_slice(),
                    [Projection::Field(_)] | [Projection::Index(_)]
                ) {
                    return Err(
                        "nested projection stores are unsupported on the typed backend".into(),
                    );
                }
                // A record literal stored into a generic field or element is
                // constructed at that slot's instance, including nullable fields.
                // Existing values keep their own type; only a fresh literal adapts.
                if let Operand::Local(local) = value
                    && let Some(actual_ty @ Type::Record(actual)) = &local_types[local.index()]
                    && let Some(slot) = self.rvalue_type(
                        &Rvalue::Load(place.clone()), cur_sym, module, local_types,
                        cur_ret, fallible, None,
                    )?
                    && let Type::Record(want) = unwrap_nullable(&slot)
                    && actual.id == want.id
                    && actual != want
                    // Preserve a literal's more complete nested substitution.
                    // Narrowing it to the slot would discard information its
                    // assignment restores on the next fixpoint round.
                    && !is_refinement_of(unwrap_nullable(&slot), actual_ty)
                    && body.blocks.iter().flat_map(|block| &block.stmts).any(|stmt| {
                        matches!(stmt, MirStmt::Assign(dest, Rvalue::Record { .. }) if dest == local)
                    })
                {
                    local_types[local.index()] = Some(Type::Record(want.clone()));
                    *changed = true;
                }
                Ok(())
            }
            // A top-level `let g = v`: record the global's concrete type (from
            // its initializer) for reads elsewhere.
            MirStmt::SetGlobal(name, op) => {
                if !self.global_types.contains_key(name)
                    && let Some(t) = self.operand_type(op, local_types)?
                {
                    if !is_supported(&t) {
                        return Err(format!(
                            "internal error: global `{name}` has unsupported type `{}`",
                            t.display()
                        ));
                    }
                    self.global_types.insert(name.clone(), t);
                    *changed = true;
                }
                Ok(())
            }
        }
    }
}
