//! The generic `Result` on the typed path: the concrete `Result<ok, err>`
//! type, a fallible callable's return inferred from its body, the error
//! payload mutual recursion assumes before that inference completes, and
//! the type of a `Result` construction typed in context.

use super::*;

/// The concrete `Result<ok, err>` type with its payloads recorded in the nominal
/// substitution (the keys the back end and HIR agree on).
pub(super) fn result_type(ok: Type, err: Type) -> Type {
    let mut subst = Substitution::empty();
    subst.insert(brass_hir::types::RESULT_OK_VALUE, ok);
    subst.insert(brass_hir::types::RESULT_ERR_ERROR, err);
    Type::Sum(NominalType::with_substitution(
        RESULT_TYPE_ID,
        "Result",
        subst,
    ))
}

/// Whether a `Result` payload of type `have` flows into a payload slot typed
/// `want`: the same type, a value-preserving numeric widening, a structural or
/// declared-subtype flow, a refinement of the same nominal, a value or `null`
/// into a nullable slot, or a type with no value (`never`, unresolved).
fn payload_flows(program: &Program, have: &Type, want: &Type) -> bool {
    match (have, want) {
        (Type::Never | Type::Unknown(_), _) | (_, Type::Unknown(_)) => true,
        _ if have == want => true,
        (Type::Nullable(h), Type::Nullable(_)) if matches!(**h, Type::Never) => true,
        (_, Type::Nullable(inner)) if !matches!(have, Type::Nullable(_)) => {
            payload_flows(program, have, inner)
        }
        _ => {
            brass_typesys::field_satisfies(have, want)
                || brass_typesys::types_compatible(program, have, want)
                || is_refinement_of(want, have)
                || is_refinement_of(have, want)
        }
    }
}

impl Monomorphizer<'_, '_> {
    /// Infer a fallible callable's `Result<ok, err>` return type: the `ok`
    /// payload from bare (non-`Result`) returns or explicit `Ok` constructions,
    /// the `err` payload from `error(...)` / `Err` constructions, and either from
    /// a directly-returned `Result`. `None` until both payloads are resolvable.
    ///
    /// `declared_ok` is the Ok payload fixed by a `T!` return annotation; when
    /// present it is authoritative (the body's own bare returns do not override it),
    /// so a then-branch returning a wrong type does not redefine the Ok payload --
    /// essential for the structural fold, which folds that branch away by comparing
    /// the return against the *declared* Ok type.
    ///
    /// Only the blocks `mask` selects (live and reachable for this instance)
    /// contribute. Without an annotation the Ok payload is the value join
    /// ([`brass_typesys::join_values`]) of the bare returns and Ok payloads,
    /// as in the checker; a pair with no join is an internal error.
    pub(super) fn infer_result_ret(
        &self,
        sym: &str,
        body: &MirBody,
        local_types: &[Option<Type>],
        declared_ok: Option<&Type>,
        mask: &[bool],
    ) -> Result<Option<Type>, String> {
        let mut ok_t: Option<Type> = declared_ok.cloned();
        // Without an annotation: the Ok values to join, and whether a
        // returned Result carried an uninhabited (`void`) Ok payload -- an
        // `error(...)` result, which yields to any real value.
        let mut ok_values: Vec<brass_typesys::JoinOperand> = Vec::new();
        let mut uninhabited_ok = false;
        let mut err_e: Option<Type> = None;
        // Whether some nullable-operand `expr!` returns `null` from this body:
        // the fallible return type is then wrapped in an outer `?`. A `T!?`
        // annotation declares that layer whatever the body does.
        let mut saw_null_prop = body.declared_nullable_result;
        // Ok-slot notes merge instead of freezing on the first sighting: a
        // directly-returned `error(...)` Result carries an UNINHABITED Ok
        // payload (`void`), which must yield to the real payload of a bare
        // return elsewhere in the body -- freezing `ok` on the first sighting
        // would type it void and read the real value back as 0. A later
        // sighting that merely REFINES the current one (same nominal, more
        // slots pinned) also upgrades it, mirroring the bare-annotation
        // promotion.
        let note = |slot: &mut Option<Type>, t: Option<Type>| {
            let Some(t) = t else {
                return;
            };
            match slot {
                None => *slot = Some(t),
                Some(existing)
                    if matches!(existing, Type::Void | Type::Never)
                        && !matches!(t, Type::Void | Type::Never) =>
                {
                    *slot = Some(t)
                }
                Some(existing) if *existing != t && is_refinement_of(existing, &t) => {
                    *slot = Some(t)
                }
                _ => {}
            }
        };
        // The Err slot prefers the LIFTED payload (the prelude `Error`): a
        // body whose propagation/return rebuilds its Err arm contains both
        // the pre-lift construction and the lifted one, and the lifted one is
        // what the body hands back.
        let error_id = self.program.prelude_type("Error").map(|i| i.id);
        let note_err = |slot: &mut Option<Type>, t: Option<Type>| {
            let Some(t) = t else {
                return;
            };
            let is_error = |t: &Type| matches!(t, Type::Record(n) if Some(n.id) == error_id);
            match slot {
                None => *slot = Some(t),
                Some(existing) if !is_error(existing) && is_error(&t) => *slot = Some(t),
                _ => {}
            }
        };
        let propagated_returns = propagated_result_returns(body);
        let null_prop_blocks = null_prop_returns(body);
        let err_constructions = scan::err_construction_locals(body);
        // A construction defines this callable's payloads only when its value
        // can actually be RETURNED as the callable's result: seeds are the
        // return operands outside the propagate/null arms (whose payloads the
        // return scan below notes), expanded backward through `Use` copies.
        // Without the gate, the `!`-on-declared-subtype REBUILD -- an Ok/Err
        // reconstruction of the OPERAND, consumed by the propagation test --
        // would note the operand's Ok payload as this callable's.
        let mut returned: HashSet<LocalId> = HashSet::default();
        for (idx, block) in body.blocks.iter().enumerate() {
            if null_prop_blocks.contains(&idx) || !mask[idx] {
                continue;
            }
            if let Terminator::Return(Operand::Local(l)) = &block.term
                && !propagated_returns.contains(&(idx, *l))
            {
                returned.insert(*l);
            }
        }
        loop {
            let mut grew = false;
            for block in &body.blocks {
                for stmt in &block.stmts {
                    if let MirStmt::Assign(dest, Rvalue::Use(Operand::Local(src))) = stmt
                        && returned.contains(dest)
                        && returned.insert(*src)
                    {
                        grew = true;
                    }
                }
            }
            if !grew {
                break;
            }
        }
        for (block_idx, block) in body.blocks.iter().enumerate() {
            if !mask[block_idx] {
                continue;
            }
            for stmt in &block.stmts {
                // Every `error(..)` the body evaluates is an error source,
                // returned or not: its Err payload is this callable's, as the
                // checker counts it.
                if let MirStmt::Assign(dest, Rvalue::Call(Callee::Free(callee), _)) = stmt
                    && callee == "error"
                    && let Some(Some(made)) = local_types.get(dest.index())
                    && let Some((_, err)) = made.result_payloads()
                {
                    note_err(&mut err_e, Some(err.clone()));
                }
                if let MirStmt::Assign(
                    dest,
                    Rvalue::Variant {
                        ty,
                        variant,
                        fields,
                    },
                ) = stmt
                    && ty == "Result"
                    && returned.contains(dest)
                {
                    for (fname, op) in fields {
                        let t = self.operand_type(op, local_types)?;
                        match (variant.as_str(), fname.as_str()) {
                            ("Ok", "value") if declared_ok.is_none() => {
                                if let Some(t) = t {
                                    ok_values.push(brass_typesys::JoinOperand {
                                        ty: t,
                                        literal: operand_literal(op),
                                    });
                                }
                            }
                            ("Ok", "value") => note(&mut ok_t, t),
                            ("Err", "error") => note_err(&mut err_e, t),
                            _ => {}
                        }
                    }
                }
            }
            if let Terminator::Return(op) = &block.term {
                // The null arm of a nullable `expr!` returns `null` itself; it
                // carries no Ok/Err payload, only the outer nullability.
                if null_prop_blocks.contains(&block_idx) {
                    saw_null_prop = true;
                    continue;
                }
                match self.operand_type(op, local_types)? {
                    // `expr!` lowers its error arm to `return <the original Result>`.
                    // That return can only execute for the `Err` variant, so it must
                    // not define this callable's `Ok` payload. The previous
                    // implementation treated the propagated `Result<File, string>`
                    // from `open(...)!` as evidence that the surrounding function
                    // returned `File!`, which made helpers such as `read_file`
                    // return a `Result<File, string>` at the typed back end even
                    // though their successful bare return was a `string`.
                    Some(Type::Sum(n))
                        if n.id == RESULT_TYPE_ID
                            && matches!(
                                op,
                                Operand::Local(local)
                                    if propagated_returns.contains(&(block_idx, *local))
                            ) =>
                    {
                        if let Some((_, err)) = n.result_payloads() {
                            note_err(&mut err_e, Some(err.clone()));
                        }
                    }
                    // A directly-returned Result carries both payloads -- unless
                    // the returned local is an `Err { .. }` construction (the `!`
                    // lift arm's rebuild): that return only executes an error
                    // path, and its Ok slot (seeded from the propagated operand)
                    // must not define this callable's Ok payload.
                    Some(Type::Sum(n)) if n.id == RESULT_TYPE_ID => {
                        if let Some((ok, err)) = n.result_payloads() {
                            if !matches!(op, Operand::Local(l) if err_constructions.contains(l)) {
                                if declared_ok.is_some() {
                                    note(&mut ok_t, Some(ok.clone()));
                                } else if matches!(ok, Type::Void | Type::Never) {
                                    uninhabited_ok = true;
                                } else {
                                    ok_values.push(brass_typesys::JoinOperand::value(ok.clone()));
                                }
                            }
                            note_err(&mut err_e, Some(err.clone()));
                        }
                    }
                    // The unit constant (a bare `return`, or the synthesized
                    // fall-through after a diverging `error(..)!`) yields to
                    // any real Ok value, like an error result's void payload.
                    Some(Type::Void)
                        if declared_ok.is_none() && matches!(op, Operand::Const(Literal::Void)) =>
                    {
                        uninhabited_ok = true;
                    }
                    // Under a `T!?` annotation a bare `null` is the declared
                    // outer null (the checker admits it only there): it
                    // carries no Ok payload.
                    Some(Type::Nullable(inner))
                        if body.declared_nullable_result && matches!(*inner, Type::Never) => {}
                    // A bare value is the implicit Ok payload.
                    Some(other) if declared_ok.is_none() => {
                        ok_values.push(brass_typesys::JoinOperand {
                            ty: other,
                            literal: operand_literal(op),
                        });
                    }
                    Some(other) => note(&mut ok_t, Some(other)),
                    None => {}
                }
            }
        }
        if declared_ok.is_none() {
            ok_t = match brass_typesys::join_values(self.program, &ok_values) {
                Ok(Some(joined)) => Some(joined),
                Ok(None) => uninhabited_ok.then_some(Type::Void),
                Err(conflict) => {
                    return Err(returns::join_conflict_error(
                        "Ok payloads",
                        sym,
                        &ok_values[conflict.first].ty,
                        &ok_values[conflict.second].ty,
                    ));
                }
            };
        }
        // A body that also returns `null` (a nullable `expr!`'s failure arm)
        // has a NULLABLE fallible return: `Result<ok, err>?`.
        let wrap = |t: Type| {
            if saw_null_prop {
                Type::Nullable(Box::new(t))
            } else {
                t
            }
        };
        match (ok_t, err_e) {
            (Some(ok), Some(err)) => Ok(Some(wrap(result_type(ok, err)))),
            // A body whose error sites all sit in code this instance never
            // runs (a statically dead arm) produces no `Err` value at all:
            // its error payload is uninhabited, the mirror of an Err-only
            // body's Ok payload, and is `void` like that one -- the unpinned
            // payload any slot's error type accepts.
            (Some(ok), None)
                if !fold::live_fallible_site(body, mask)
                    && fold::live_fallible_site(body, &vec![true; body.blocks.len()]) =>
            {
                Ok(Some(wrap(result_type(ok, Type::Void))))
            }
            // A callable made fallible only by a `T!` return annotation never
            // produces an error, so its error payload is unconstrained: default it
            // to `string` (the conventional error type) once the Ok payload is
            // known. Guarded by the absence of any error source -- an
            // `error(..)`, an `Err` construction, a `!` propagation -- so a
            // fallible body that does raise errors still waits for the real
            // error type.
            (Some(ok), None) if !fold::live_fallible_site(body, &vec![true; body.blocks.len()]) => {
                Ok(Some(wrap(result_type(ok, Type::Str))))
            }
            // The mirror: a body whose every non-propagated return is an `Err`
            // construction produces no Ok value at all, so its Ok payload is
            // uninhabited for this instance and defaults to void. Guarded
            // conservatively -- any other return operand (a call the fixpoint
            // has not resolved yet) keeps the payload open.
            (None, Some(err))
                if returns_only_err_constructions(body, &propagated_returns, &null_prop_blocks) =>
            {
                Ok(Some(wrap(result_type(Type::Void, err))))
            }
            _ => Ok(None),
        }
    }

    /// The error payload a fallible body is assumed to produce before its
    /// own inference completes: the prelude `Error` record wrapping a string,
    /// instantiated the way record construction types it (deep field
    /// substitution), so a mutual-recursion guess equals the final instance.
    /// Bare `string` in a program without the prelude.
    pub(super) fn guessed_error_payload(&self) -> Type {
        let Some(info) = self.program.prelude_type("Error") else {
            return Type::Str;
        };
        let TypeKind::Record { fields, .. } = &info.kind else {
            return Type::Str;
        };
        let mut subst = brass_hir::Substitution::empty();
        for f in fields {
            if f.name == "value" {
                subst.insert("value", Type::Str);
            } else if let Some(t) = &f.resolved_ty {
                subst.insert(f.name.clone(), resolve_nominal(self.program, t));
            }
        }
        Type::Record(brass_hir::NominalType::with_substitution(
            info.id,
            info.name.clone(),
            subst,
        ))
    }

    /// The type of a `Result` construction typed in context `ctx` (its
    /// destination's or the enclosing callable's `Result` type): `ctx`, unless
    /// the payload operand's type cannot flow into `ctx`'s slot for it. Such a
    /// construction is not the value the context describes -- the pre-lift
    /// `Err` a propagation rebuilds into the prelude `Error`, or an `Ok` wrap
    /// that feeds a nested expression -- so it keeps its own payload type
    /// (the other slot still comes from `ctx`); typing it by the context would
    /// store the payload in a slot of another representation.
    pub(super) fn result_construction_type(
        &self,
        ctx: Type,
        variant: &str,
        fields: &[(String, Operand)],
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        let Some((ok, err)) = (match &ctx {
            Type::Sum(n) => n.result_payloads(),
            _ => None,
        }) else {
            return Ok(Some(ctx));
        };
        let (key, want) = match variant {
            "Ok" => ("value", ok),
            "Err" => ("error", err),
            _ => return Ok(Some(ctx)),
        };
        let Some((_, op)) = fields.iter().find(|(name, _)| name == key) else {
            return Ok(Some(ctx));
        };
        let Some(have) = self.operand_type(op, local_types)? else {
            return Ok(Some(ctx));
        };
        if payload_flows(self.program, &have, want) {
            return Ok(Some(ctx));
        }
        Ok(Some(if variant == "Ok" {
            result_type(have, err.clone())
        } else {
            result_type(ok.clone(), have)
        }))
    }
}
