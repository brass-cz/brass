//! Instantiating a callable: typing one instance of a function, method, or
//! closure body until its type tests, recursive calls, and returns settle,
//! checking the typed body, and storing it under its instance symbol -- or
//! rolling back every instance a failed frame stored.

use super::*;

impl<'m> Monomorphizer<'m, '_> {
    /// Instantiate a free function `base` for `type_args` (memoized).
    pub(super) fn instantiate_fn(
        &mut self,
        base: &str,
        type_args: Vec<Type>,
    ) -> Result<String, String> {
        self.instantiate_numeric_fn(base, type_args, None)
    }

    /// Instantiate a free body with its negotiated local return-origin storage.
    pub(super) fn instantiate_numeric_fn(
        &mut self,
        base: &str,
        type_args: Vec<Type>,
        numeric_layout: Option<brass_hir::NumericLayout>,
    ) -> Result<String, String> {
        let effective_base = instance::numeric_base(base, numeric_layout.as_ref());
        let sym = instance_symbol(&effective_base, &type_args);
        if self.instances.contains_key(&sym) {
            return Ok(sym);
        }
        let Some(&func) = self.by_fn.get(base) else {
            // Record what a demand-driven caller (the lazy pipeline, which
            // lowers function bodies into the MIR program on demand) would
            // need to make this call instantiable.
            self.note_missing(base, &type_args, true);
            return Err(format!("internal error: unknown function `{base}`"));
        };
        // The instance is keyed by the caller's argument types (both the
        // checker's instance and the call sites' symbol); its parameters
        // start from the declared-nullable rule over them.
        let instance = self.function_instance(base, &type_args).map(|mut key| {
            key.numeric_layout = numeric_layout;
            key
        });
        let type_args = match self.program.functions.get(base) {
            Some(info) => {
                params::check_record_params(
                    self.program,
                    base,
                    &info.signature.params,
                    &type_args,
                )?;
                self.instance_param_types(&info.signature.params, &type_args)
            }
            None => type_args,
        };
        let sig_ret = self
            .program
            .functions
            .get(base)
            .and_then(|info| info.signature.ret_ty.clone());
        // A `T!` return fixes the Ok payload `T` (even if the inferred error type
        // is left open); keep it so the body cannot redefine it.
        let declared_ok = sig_ret.as_ref().and_then(result_concrete_ok);
        // An unannotated instance returning a function value: the checker's
        // settled return for this instance types the returned closure.
        let returned_fun = match &sig_ret {
            None => self
                .instance_return(effective_base.as_ref(), &type_args)
                .map(|ret| resolve_nominal(self.program, ret))
                .filter(|ret| matches!(ret, Type::Fun(..)) && is_supported(ret)),
            Some(_) => None,
        };
        let ret_ann = sig_ret.filter(is_supported);
        self.type_and_store(
            sym,
            &func.body,
            &func.module,
            type_args,
            ret_ann,
            declared_ok,
            returned_fun,
            &[],
            Vec::new(),
            false,
            func.fallible,
            instance,
        )
    }

    /// Type a callable body for one instance and store it. Shared by functions,
    /// methods, and closures. `capture_seed` pre-types a closure's captured
    /// locals (read from its environment); `captures` records them for the back
    /// end.
    ///
    /// On failure every instance stored during this frame is rolled back:
    /// mutual recursion types a callee against this frame's provisional return
    /// and stores it first, so letting it survive a failed frame would leave an
    /// instance calling a symbol that never materializes.
    ///
    /// `instance` is the checker instance the body is typed as (see
    /// [`instance`]); a closure body ignores it and stays in the instance
    /// that creates it.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn type_and_store(
        &mut self,
        sym: String,
        body: &'m MirBody,
        module: &[String],
        type_args: Vec<Type>,
        ret_ann: Option<Type>,
        declared_ok: Option<Type>,
        seed_ret: Option<Type>,
        capture_seed: &[(LocalId, Type)],
        captures: Vec<LocalId>,
        is_closure: bool,
        fallible: bool,
        instance: Option<brass_hir::InstanceKey>,
    ) -> Result<String, String> {
        if let Some(failure) = self.missing_failures.get(&sym) {
            let error = failure.error.clone();
            let demands = failure.demands.clone();
            for (base, type_args, needs_body) in demands {
                self.note_missing(&base, &type_args, needs_body);
            }
            return Err(error);
        }
        let missing_before = self.missing_observations.get();
        let demands_before = self.missing_demands.borrow().len();
        let watermark = self.instance_log.len();
        let cleanup_sym = sym.clone();
        // Instances are typed depth-first, each nested inside the frame of
        // the body that first calls it, so a chain of distinct callables
        // nests as deep as the program's static call chain does. The checker
        // rejects the recursion that would nest forever (a callable calling
        // itself at an ever-larger type); this bound -- on the instances of
        // ONE callable in the nesting, which only such recursion piles up --
        // turns any chain it missed into an error instead of exhausting the
        // stack. The failure is sticky: the frames it unwinds through would
        // otherwise retry the call on every fixpoint round, and the retries
        // multiply with the depth.
        if let Some(error) = &self.nesting_overflow {
            return Err(error.clone());
        }
        // The callable's own name: the instance symbol spells out the
        // (possibly enormous) argument types.
        let callable = sym.split("$$").next().unwrap_or(&sym).to_string();
        let nested = self.callable_nesting.entry(callable.clone()).or_default();
        if *nested >= instance::MAX_INSTANCE_NESTING {
            let error = format!(
                "internal error: instantiating `{callable}` nests more than {} instances \
                 of it deep; it may be calling itself at an ever-larger type",
                instance::MAX_INSTANCE_NESTING
            );
            self.nesting_overflow = Some(error.clone());
            return Err(error);
        }
        *nested += 1;
        let instance = if is_closure && instance.is_none() {
            self.current_instance().cloned()
        } else {
            instance
        };
        self.instance_stack.push(instance);
        let res = self.type_and_store_inner(
            sym,
            body,
            module,
            type_args,
            ret_ann,
            declared_ok,
            seed_ret,
            capture_seed,
            captures,
            is_closure,
            fallible,
        );
        self.instance_stack.pop();
        if let Some(nested) = self.callable_nesting.get_mut(&callable) {
            *nested -= 1;
        }
        if res.is_err() {
            for stored in self.instance_log.drain(watermark..) {
                self.instances.remove(&stored);
            }
            self.in_progress.remove(&cleanup_sym);
            self.assumed_rets.remove(&cleanup_sym);
            self.self_call_rets.remove(&cleanup_sym);
        }
        if self.missing_observations.get() != missing_before
            && let Err(error) = &res
        {
            let demands = self.missing_demands.borrow()[demands_before..].to_vec();
            self.missing_failures.insert(
                cleanup_sym,
                MissingFailure {
                    error: error.clone(),
                    demands,
                },
            );
        }
        res
    }

    #[allow(clippy::too_many_arguments)]
    fn type_and_store_inner(
        &mut self,
        sym: String,
        body: &'m MirBody,
        module: &[String],
        type_args: Vec<Type>,
        ret_ann: Option<Type>,
        declared_ok: Option<Type>,
        seed_ret: Option<Type>,
        capture_seed: &[(LocalId, Type)],
        captures: Vec<LocalId>,
        is_closure: bool,
        fallible: bool,
    ) -> Result<String, String> {
        if self.instances.contains_key(&sym) {
            return Ok(sym);
        }
        if body.params.len() != type_args.len() {
            return Err(format!(
                "internal error: `{sym}` expects {} argument(s), got {}",
                body.params.len(),
                type_args.len()
            ));
        }
        let mut local_types: Vec<Option<Type>> = vec![None; body.locals.len()];
        for (i, p) in body.params.iter().enumerate() {
            local_types[p.index()] = Some(type_args[i].clone());
        }
        for (local, ty) in capture_seed {
            local_types[local.index()] = Some(ty.clone());
        }
        // A `let x: T = ...` binding fixed its local's type during lowering; seed it
        // so monomorphization preserves an annotation the initializer alone cannot
        // express (e.g. `let x: int32? = null`). A nominal annotation (an
        // uninitialized `let x: Point`) is a bare reference; resolve its field
        // substitution from the declaration so the seed is self-describing.
        for (i, decl) in body.locals.iter().enumerate() {
            if let Some(t) = self.local_seed(decl) {
                local_types[i] = Some(resolve_nominal(self.program, &t));
            }
        }
        let annotated = ret_ann.is_some();
        // Seed the locals that flow into the returned record/variant from a known
        // aggregate's field types: a declared aggregate return, or the caller's
        // expected result (a witness-free constructor). An empty array field built
        // without a later `push` (`items = []` returned by `new()`) then takes its
        // element type from the result the caller fixed. Seeding leaves the return
        // type to be inferred from the now-concrete body, so the constructed record
        // keeps its full field substitution -- the return type is not forced to the
        // (possibly sparser) expected type.
        if let Some(seed) = ret_ann.clone().or(seed_ret.clone())
            && is_return_polymorphic_result(&seed)
        {
            seed_returned_aggregate(body, &seed, self.program, &mut local_types);
        }
        // A declared tuple return makes a returned bracket literal that tuple:
        // its elements alone (`[a, b]` at one type) would build an array.
        if let Some(tuple @ Type::Tuple(_)) = &ret_ann {
            seed_returned_tuple(body, tuple, &mut local_types);
        }
        // A returned closure is typed by the function type the instance
        // returns -- declared, or settled by the checker for this instance
        // (the closure is neither called nor passed in the body, and its
        // literal may have another type in another instance).
        if let Some(fun @ Type::Fun(..)) = ret_ann.as_ref().or(seed_ret.as_ref()) {
            seed_returned_closure(body, fun, &mut local_types);
        }
        let scans = self.body_scans(body);
        let fields = self.field_selections(body);

        // The blocks this instance actually owns, once its type tests fold. A
        // type-test-dead block is never typed or compiled here and contributes
        // NO evidence: its returns do not join the instance's return type and
        // its error sites do not make the instance fallible -- that code
        // belongs to other instantiations. A test is decided as soon as its
        // subject's type is known in this instance -- a parameter or an
        // annotated local before typing, any other local (a copy of a
        // parameter, a field read, ...) once the fixpoint has typed it -- so
        // the body is typed again whenever typing decided more tests, from the
        // seeds and with the smaller live set, until the decisions are stable
        // (each round only shrinks the set).
        let seeds = local_types;
        let mut live = fold::type_test_live_blocks(self.program, body, &seeds, &fields);
        // A self-recursive call reads the return type computed so far. When
        // the finished return is wider (a `return 0` joined with the float a
        // recursive sum produces), the body is typed again with the call
        // reading at least that type, until the call and the return agree.
        let mut ret_floor: Option<Type> = None;
        // Set once the typed body shows every error source sits in code a
        // folded condition makes unreachable for this instance.
        let mut errors_unreachable = false;
        let mut attempts = 0usize;
        let (local_types, mut ret, block_errors, fallible) = loop {
            attempts += 1;
            if attempts > body.blocks.len() + 8 {
                return Err(format!(
                    "internal error: the types of `{sym}` did not settle while folding its type \
                     tests and recursive calls"
                ));
            }
            // Fallibility is per instance: a declared `T!` annotation is always a
            // Result (its body may only forward), while a body-inferred fallible
            // callable is one only when a live block still carries an error
            // source.
            let fallible = fallible
                && (body.declared_fallible
                    || (!errors_unreachable && fold::live_fallible_site(body, &live)));
            // The provisional return type mutual recursion may type against: the
            // authoritative annotation when there is one. A fallible callable's
            // annotation (`T!`) leaves the error payload open, so it is guessed as
            // the payload `error(...)`/a lifted `!` produces (the prelude `Error`
            // wrapping a string); the guess is validated against the final
            // inferred type when this frame completes.
            let provisional = ret_ann.clone().or_else(|| {
                if fallible {
                    let err = self.guessed_error_payload();
                    declared_ok.clone().map(|ok| {
                        let result = result_type(ok, err);
                        if body.declared_nullable_result {
                            Type::Nullable(Box::new(result))
                        } else {
                            result
                        }
                    })
                } else {
                    None
                }
            });
            self.in_progress.insert(sym.clone(), provisional);
            self.self_call_rets.remove(&sym);
            let mut local_types = seeds.clone();
            let typed = self.type_body_fixpoint(
                &sym,
                body,
                module,
                &scans,
                &mut local_types,
                &live,
                ret_ann.clone().or_else(|| ret_floor.clone()),
                annotated,
                fallible,
                declared_ok.as_ref(),
            )?;
            let (ret, block_errors) = match typed {
                Ok(done) => done,
                Err(pair) => {
                    return Err(returns::join_conflict_error(
                        "returns", &sym, &pair.0, &pair.1,
                    ));
                }
            };
            let decided = fold::type_test_live_blocks(self.program, body, &local_types, &fields);
            let narrowed: Vec<bool> = decided.iter().zip(&live).map(|(d, l)| *d && *l).collect();
            if narrowed != live {
                live = narrowed;
                continue;
            }
            // A condition only the typed body decides -- a member-presence
            // test (`if v.chars`), a presence `if let` over an absent member
            // -- may leave every error source unreachable: the instance then
            // never fails and is typed again with a plain return, as the
            // checker's per-instance walk (which prunes the same arm) types it.
            if fallible && !body.declared_fallible && !errors_unreachable {
                let reachable = fixpoint::live_reachable(self.program, body, &local_types, &live);
                if !fold::live_fallible_site(body, &reachable) {
                    errors_unreachable = true;
                    continue;
                }
            }
            if !annotated
                && let Some(assumed) = self.self_call_rets.remove(&sym)
                && Some(&assumed) != ret.as_ref()
                && let Some(current) = &ret
            {
                let floor = brass_typesys::join_values(
                    self.program,
                    &[
                        brass_typesys::JoinOperand::value(assumed.clone()),
                        brass_typesys::JoinOperand::value(current.clone()),
                    ],
                )
                .map_err(|_| returns::join_conflict_error("returns", &sym, &assumed, current))?;
                if floor != ret_floor {
                    ret_floor = floor;
                    continue;
                }
            }
            break (local_types, ret, block_errors, fallible);
        };

        // Which blocks actually run, judged against the types resolved so far.
        let reachable = fixpoint::live_reachable(self.program, body, &local_types, &live);
        if let Some(e) = reachable
            .iter()
            .zip(&block_errors)
            .find_map(|(live, e)| live.then_some(e.as_ref()).flatten())
        {
            return Err(e.clone());
        }

        // A return annotation is authoritative for the nominal it names, but a
        // BARE nominal annotation carries no substitution for the slots only
        // the body's constructions can type (an unannotated closure field).
        // Freezing the bare annotation washes those types out: the caller's
        // local goes bare, `resolve_nominal` cannot supply an unannotated
        // field, and reading it yields `?`. So join the reachable returns the
        // way the unannotated path does and promote to the joined instance
        // when it merely REFINES the annotation -- the nominal identity the
        // annotation states is preserved, its open slots are filled. Anything
        // else keeps the annotation, exactly the pre-existing behavior.
        if annotated && !fallible {
            // Returns that merely each flow into the annotation need not join
            // one another; without a join there is nothing to promote to.
            let merged = self
                .join_block_returns(body, &local_types, &reachable)
                .ok()
                .flatten();
            if let (Some(ann), Some(m)) = (&ret, merged)
                && &m != ann
                && is_refinement_of(ann, &m)
            {
                ret = Some(m);
            }
        } else if fallible
            && declared_ok.is_some()
            && let Some(t) = self.infer_result_ret(&sym, body, &local_types, None, &reachable)?
            && ret
                .as_ref()
                .is_some_and(|cur| cur != &t && is_refinement_of(cur, &t))
        {
            // The fallible mirror: `-> T!` fixes the Ok payload, but a bare
            // nominal `T` needs the body's inferred Ok instance the same way.
            // Gated on `declared_ok` (not `annotated`): a `T!` annotation with
            // an open error payload is filtered from `ret_ann` as unsupported
            // while its Ok side still froze the payload via `declared_ok`.
            ret = Some(t);
        }

        let dead_locals = locals_only_in_dead_blocks(body, &reachable);
        let local_types = local_types
            .into_iter()
            .enumerate()
            .map(|(i, t)| match t {
                // A local no reachable block writes has no runtime slot, so its
                // type never matters: an unreachable arm's temporaries stay
                // untyped once that arm's statements were allowed to fail, or
                // keep a type the typed back end has no layout for (the
                // payload of a variant no value of this instance holds).
                Some(t) if dead_locals[i] && !is_supported(&t) => Ok(Type::Void),
                Some(t) => Ok(t),
                None if dead_locals[i] => Ok(Type::Void),
                None => Err({
                    // Name the binding whose type stayed unknown; a bare local
                    // index means nothing to the programmer.
                    match binding_name_of(body, LocalId(i as u32)) {
                        Some(n) => format!("cannot infer the type of `{n}` in `{sym}`"),
                        None => format!(
                            "cannot infer the type of an expression temporary (local _{i}) in `{sym}`"
                        ),
                    }
                }),
            })
            .collect::<Result<Vec<_>, _>>()?;

        // A non-fallible callable with a non-null declared return cannot return an
        // always-null value (`never?` -- a `null` literal or an absent structural
        // field). The checker rejects such a return, so one reaching this
        // backstop is an internal error rather than a null read back at the
        // declared type. Only *reachable* returns count: an `if` on a
        // statically-false condition (an absent field reads as `never?`) makes its
        // then-branch unreachable, so a `return absent.field` there is pruned, not
        // an error. (A declared `T?` return may hold null and is not checked.)
        if !fallible
            && let Some(declared) = &ret
            && !matches!(declared, Type::Nullable(_))
        {
            let reachable = reachable_blocks(self.program, body, &local_types, &fields);
            for (i, block) in body.blocks.iter().enumerate() {
                if reachable[i]
                    && let Terminator::Return(op) = &block.term
                    && matches!(operand_type_of(op, &local_types), Type::Nullable(inner) if matches!(*inner, Type::Never))
                {
                    return Err(format!(
                        "internal error: returns a null value where `{}` is required (in `{sym}`)",
                        declared.display()
                    ));
                }
            }
        }
        // The instance's parameter types are the parameters' resolved types, not the
        // raw argument types. An annotated parameter keeps its declared type -- a
        // nullable `int32?` stays nullable even when a value or an omitted-null
        // argument is passed -- so callers coerce each argument to it (a value is
        // wrapped into the nullable cell, `null` stays null) and the body sees a
        // consistent nullable, not a bare value.
        let type_args: Vec<Type> = body
            .params
            .iter()
            .map(|p| local_types[p.index()].clone())
            .collect();
        let ret =
            ret.ok_or_else(|| format!("internal error: cannot infer return type of `{sym}`"))?;
        for t in local_types.iter().chain(std::iter::once(&ret)) {
            if !is_supported(t) {
                return Err(format!(
                    "internal error: type `{}` is not supported by the typed backend (in `{sym}`)",
                    t.display()
                ));
            }
        }
        for (block, live) in
            body.blocks
                .iter()
                .zip(reachable_blocks(self.program, body, &local_types, &fields))
        {
            if live {
                for stmt in &block.stmts {
                    if let MirStmt::Assign(_, Rvalue::FieldsTest { site, .. }) = stmt
                        && !fields.contains_key(site)
                    {
                        return Err(format!(
                            "internal error: field loop has no checked expansion for `{sym}`"
                        ));
                    }
                }
            }
        }
        self.validate(
            body,
            &sym,
            &local_types,
            &reachable_blocks(self.program, body, &local_types, &fields),
        )?;

        // Validate what mutual recursion assumed about this instance while it
        // was in progress: a mismatch (e.g. a fallible body whose error payload
        // is not the guessed `string`) must fail the frame -- the consumer was
        // already typed against the assumption. An assumption taken from a
        // bare annotation that the final return merely refines is compatible:
        // the consumer typed against the same nominal, just with fewer slots
        // pinned (the reverse -- a concrete assumption, bare final -- stays an
        // error).
        if let Some(assumed) = self.assumed_rets.remove(&sym)
            && assumed != ret
            && !is_refinement_of(&assumed, &ret)
        {
            return Err(format!(
                "internal error: mutual recursion typed `{sym}` as returning `{}`, but its body returns `{}`",
                assumed.display(),
                ret.display()
            ));
        }
        let keyed = self.keyed_targets(body, &reachable)?;
        let mut closure_targets = HashMap::default();
        if !self.numeric_calls.is_empty() {
            for block in &body.blocks {
                for stmt in &block.stmts {
                    if let MirStmt::Assign(dest, Rvalue::Closure { id, captures }) = stmt
                        && let Type::Fun(params, _) = &local_types[dest.index()]
                    {
                        let types: Vec<_> = captures
                            .iter()
                            .map(|op| operand_type_of(op, &local_types))
                            .collect();
                        let (target, _) = self.closure_contract(*id, &types, params)?;
                        closure_targets.insert(*id, target);
                    }
                }
            }
        }
        self.in_progress.remove(&sym);
        self.instance_log.push(sym.clone());
        self.instances.insert(
            sym.clone(),
            MonoFunction {
                body,
                symbol: sym.clone(),
                type_args,
                ret,
                local_types,
                captures,
                is_closure,
                fallible,
                keyed,
                fields,
                closure_targets,
            },
        );
        Ok(sym)
    }

    /// Check operator/type constraints over a fully-typed body (the static
    /// checking half of monomorphization). Only blocks this instance can reach
    /// are checked: an arm a statically-known `if` folds away is not emitted, and
    /// its operators may well be ill-typed for *this* instantiation.
    fn validate(
        &self,
        body: &MirBody,
        sym: &str,
        local_types: &[Type],
        reachable: &[bool],
    ) -> Result<(), String> {
        let ty = |op: &Operand| -> Type {
            match op {
                Operand::Local(id) => local_types[id.index()].clone(),
                Operand::Const(lit) => const_type(lit).unwrap_or(Type::Void),
            }
        };
        for (block, _) in body.blocks.iter().zip(reachable).filter(|(_, r)| **r) {
            for stmt in &block.stmts {
                let (MirStmt::Assign(_, Rvalue::Bin(op, a, b))
                | MirStmt::Eval(Rvalue::Bin(op, a, b))) = stmt
                else {
                    continue;
                };
                check_bin(self.program, *op, (&ty(a), a), (&ty(b), b))
                    .map_err(|e| format!("{e} (in `{sym}`)"))?;
            }
        }
        Ok(())
    }
}
