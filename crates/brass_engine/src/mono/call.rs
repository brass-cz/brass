//! Resolving a call to its callee instance: instance-method dispatch (on a
//! nominal, a structural, or a primitive receiver), static methods and
//! constructors, and free functions -- including the recursion,
//! postponement, deferral, and missing-body handling a call goes through
//! before its callee is instantiated.

use super::*;

impl<'m> Monomorphizer<'m, '_> {
    /// Type an instance-method call `recv.name(args)`.
    pub(super) fn method_call_type(
        &mut self,
        name: &str,
        args: &[Operand],
        cur_sym: &str,
        cur_ret: &Option<Type>,
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        let Some(mut arg_types) = self.arg_types(args, local_types)? else {
            return Ok(None);
        };
        // A narrowed `T?` receiver dispatches as `T`: the checker only lets a
        // method call through when a guard proved the receiver non-null, and
        // the call boundary unwraps the cell, so the instance is created for
        // the inner type (matching `method_symbol`'s keying).
        if let Type::Nullable(inner) = &arg_types[0] {
            arg_types[0] = (**inner).clone();
        }
        // A genuine record or whole-sum method takes priority.
        if let Type::Record(n) | Type::Sum(n) = &arg_types[0]
            && let Some(info) = self.program.type_by_id(n.id)
        {
            let type_symbol = info.symbol.clone();
            if let Some(&method) = self.by_method.get(&(type_symbol.as_str(), name)) {
                if let TypeKind::Record { methods, .. } = &info.kind
                    && let Some(declared) = methods.get(name)
                {
                    params::check_record_params(
                        self.program,
                        name,
                        &declared.signature.params,
                        &arg_types,
                    )?;
                }
                let ret_ann = method_ret_annotation(self.program, &type_symbol, name);
                let target = method_symbol(name, &arg_types);
                let body = &method.body;
                let module = method.module.clone();
                let fallible = method.fallible;
                let instance = self.method_instance(&type_symbol, name, &arg_types);
                let arg_types = match params::method_params(info, name) {
                    Some(declared) => self.instance_param_types(declared, &arg_types),
                    None => arg_types,
                };
                return self.resolve_callable(
                    cur_sym, cur_ret, target, body, &module, arg_types, ret_ann, None, fallible,
                    instance,
                );
            }
        }
        // A STRUCTURAL (anonymous) receiver resolves a method by satisfaction:
        // the record type declaring `name` whose declared fields the value
        // provides. The checker has already enforced that exactly one
        // module-visible candidate exists; candidates are scanned in sorted
        // symbol order so the pick is deterministic here too.
        if let Type::Record(n) = &arg_types[0]
            && n.id == brass_hir::STRUCTURAL_RECORD_ID
        {
            let mut symbols: Vec<&String> = self
                .program
                .types
                .values()
                .filter_map(|info| {
                    let TypeKind::Record { fields, methods } = &info.kind else {
                        return None;
                    };
                    if !methods.contains_key(name) {
                        return None;
                    }
                    let satisfied = fields.iter().all(|f| match n.substitution.get(&f.name) {
                        None => false,
                        Some(have) => match &f.resolved_ty {
                            Some(decl) if brass_hir::is_fully_known(decl) => have == decl,
                            _ => true,
                        },
                    });
                    satisfied.then_some(&info.symbol)
                })
                .collect();
            symbols.sort();
            if let Some(&symbol) = symbols.first()
                && let Some(&method) = self.by_method.get(&(symbol.as_str(), name))
            {
                let ret_ann = method_ret_annotation(self.program, symbol, name);
                let target = method_symbol(name, &arg_types);
                let body = &method.body;
                let module = method.module.clone();
                let fallible = method.fallible;
                let instance = self.method_instance(symbol, name, &arg_types);
                let arg_types = match self
                    .program
                    .types
                    .get(symbol)
                    .and_then(|info| params::method_params(info, name))
                {
                    Some(declared) => self.instance_param_types(declared, &arg_types),
                    None => arg_types,
                };
                return self.resolve_callable(
                    cur_sym, cur_ret, target, body, &module, arg_types, ret_ann, None, fallible,
                    instance,
                );
            }
        }
        // A stdlib method on a primitive/array receiver (`fun string.split`,
        // `fun infer[].map`), dispatched by the receiver's class. Its body is an
        // ordinary function stored under a class-qualified symbol; instantiate it
        // for the call's argument tuple.
        if let Some(class) = arg_types[0].primitive_class()
            && let Some(sym) = self
                .program
                .primitive_methods
                .get(&(class.to_string(), name.to_string()))
        {
            let sym = sym.clone();
            return self.resolve_free(cur_sym, cur_ret, &sym, arg_types);
        }
        // Builtin structural debug prepares the effective debug methods of
        // its children. Core primitive methods and a declared nominal debug
        // were consulted above and own their rendering.
        if name == "debug" && arg_types.len() == 1 {
            return if is_printable(&arg_types[0]) {
                Ok(self
                    .prepare_rendering(
                        &arg_types[0],
                        crate::render::RenderForm::Debug,
                        cur_sym,
                        cur_ret,
                    )?
                    .then_some(Type::Str))
            } else {
                Err(format!(
                    "debug of `{}` is unsupported on the typed backend",
                    arg_types[0].display()
                ))
            };
        }
        Err(format!(
            "internal error: no method `{name}` for `{}`",
            arg_types[0].display()
        ))
    }

    /// Type a static call `Type.method(args)`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn static_call_type(
        &mut self,
        ty: &str,
        method_name: &str,
        args: &[Operand],
        cur_sym: &str,
        cur_ret: &Option<Type>,
        module: &[String],
        local_types: &[Option<Type>],
        expected: Option<&Type>,
    ) -> Result<Option<Type>, String> {
        let Some(arg_types) = self.arg_types(args, local_types)? else {
            return Ok(None);
        };
        // Numeric/string conversions (`Type.from`/`Type.parse`) are runtime-
        // recognized, not user static methods.
        if let Some(ret) = numeric_conv_ret(ty, method_name) {
            return Ok(Some(ret));
        }
        // `File.stdin/stdout/stderr` are runtime standard streams.
        let info = self
            .program
            .resolve_type(module, ty)
            // MIR may carry the canonical storage symbol of a generated,
            // already-validated type whose source module differs from the
            // specialization template. Scoped lookup stays first so a local
            // shadow still wins.
            .or_else(|| self.program.types.get(ty))
            .ok_or_else(|| format!("internal error: unknown type `{ty}`"))?;
        let type_symbol = info.symbol.clone();
        let method = *self
            .by_method
            .get(&(type_symbol.as_str(), method_name))
            .ok_or_else(|| {
                format!("internal error: type `{ty}` has no static method `{method_name}`")
            })?;
        if let TypeKind::Record { methods, .. } = &info.kind
            && let Some(declared) = methods.get(method_name)
        {
            params::check_record_params(
                self.program,
                method_name,
                &declared.signature.params,
                &arg_types,
            )?;
        }
        let ret_ann = method_ret_annotation(self.program, &type_symbol, method_name);
        // The caller's expected result type (the destination local's resolved type,
        // seeded from the checker) seeds a witness-free constructor's empty array
        // fields and keys a return-polymorphic, no-argument constructor by its
        // result. It does *not* override the body-inferred return: seeding makes the
        // body's own return concrete, and the constructed record carries the full
        // field substitution the back end lays out from.
        let seed = expected
            .filter(|t| is_return_polymorphic_result(t))
            .cloned();
        let target = static_symbol(ty, method_name, &arg_types, seed.as_ref());
        let body = &method.body;
        let mmodule = method.module.clone();
        let fallible = method.fallible;
        let instance = self.method_instance(&type_symbol, method_name, &arg_types);
        let arg_types = match params::method_params(info, method_name) {
            Some(declared) => self.instance_param_types(declared, &arg_types),
            None => arg_types,
        };
        self.resolve_callable(
            cur_sym, cur_ret, target, body, &mmodule, arg_types, ret_ann, seed, fallible, instance,
        )
    }

    /// Resolve a call to an already-located method/static body: handle
    /// self-recursion and mutual recursion, instantiate, and return the instance
    /// return type.
    #[allow(clippy::too_many_arguments)]
    fn resolve_callable(
        &mut self,
        cur_sym: &str,
        cur_ret: &Option<Type>,
        target: String,
        body: &'m MirBody,
        module: &[String],
        type_args: Vec<Type>,
        ret_ann: Option<Type>,
        seed_ret: Option<Type>,
        fallible: bool,
        instance: Option<brass_hir::InstanceKey>,
    ) -> Result<Option<Type>, String> {
        let mut target = target;
        let mut instance = instance;
        if !self.numeric_calls.is_empty() {
            let active = self.active_numeric_call.take();
            let layout = instance
                .as_ref()
                .and_then(|key| self.recursive_numeric_layout(key))
                .unwrap_or_else(|| active.as_ref().and_then(|(_, layout)| layout.clone()));
            target = brass_hir::numeric_instance_base(&target, layout.as_ref());
            if let Some(key) = &mut instance {
                key.numeric_layout = layout;
            }
            if let Some((site, _)) = active {
                self.numeric_targets
                    .insert((site, self.current_instance().cloned()), target.clone());
            }
        }
        if target == cur_sym {
            // The FIRST type a self call read in this attempt is the one its
            // result local was typed at (a local is not re-typed later in the
            // same attempt), so that is what the finished return is compared
            // against (see `self_call_rets`).
            if let Some(ret) = cur_ret {
                self.self_call_rets
                    .entry(target)
                    .or_insert_with(|| ret.clone());
            }
            return Ok(cur_ret.clone());
        }
        // The target is an ancestor on the instantiation stack (mutual
        // recursion). With an authoritative return annotation the instance type
        // is already fixed, so this call types against it and the ancestor frame
        // completes the instance itself; without one nothing sound is known.
        if let Some(provisional) = self.in_progress.get(&target) {
            return match provisional.clone() {
                Some(t) => {
                    self.assumed_rets.insert(target, t.clone());
                    Ok(Some(t))
                }
                None => Err(format!(
                    "mutual recursion (`{cur_sym}` <-> `{target}`) needs an explicit return type annotation on `{target}`"
                )),
            };
        }
        // The Ok payload of a `T!` return is authoritative even when the full
        // annotation is unsupported (open error payload); compute it from the
        // raw annotation, then filter for the provisional/return type.
        let declared_ok = ret_ann.as_ref().and_then(result_concrete_ok);
        let ret_ann = ret_ann.filter(is_supported);
        let sym = self.type_and_store(
            target,
            body,
            module,
            type_args,
            ret_ann,
            declared_ok,
            seed_ret,
            &[],
            Vec::new(),
            false,
            fallible,
            instance,
        )?;
        Ok(self.instances.get(&sym).map(|i| i.ret.clone()))
    }

    /// Resolve a free-function call, returning its instance return type (or
    /// `None` when an argument type is not yet known and the caller should retry).
    pub(super) fn resolve_free(
        &mut self,
        cur_sym: &str,
        cur_ret: &Option<Type>,
        base: &str,
        arg_types: Vec<Type>,
    ) -> Result<Option<Type>, String> {
        self.resolve_numeric_free(cur_sym, cur_ret, base, arg_types, None)
    }

    /// Resolve a free call including a concrete return-origin storage contract.
    pub(super) fn resolve_numeric_free(
        &mut self,
        cur_sym: &str,
        cur_ret: &Option<Type>,
        base: &str,
        arg_types: Vec<Type>,
        numeric_layout: Option<brass_hir::NumericLayout>,
    ) -> Result<Option<Type>, String> {
        let active = self.active_numeric_call.take();
        let numeric_layout = if self.numeric_calls.is_empty() {
            numeric_layout
        } else {
            self.function_instance(base, &arg_types)
                .and_then(|key| self.recursive_numeric_layout(&key))
                .unwrap_or_else(|| {
                    numeric_layout
                        .or_else(|| active.as_ref().and_then(|(_, layout)| layout.clone()))
                })
        };
        let effective_base = instance::numeric_base(base, numeric_layout.as_ref());
        let target = instance_symbol(&effective_base, &arg_types);
        if let Some((site, _)) = active {
            self.numeric_targets
                .insert((site, self.current_instance().cloned()), target.clone());
        }
        if target == cur_sym {
            // The FIRST type a self call read in this attempt is the one its
            // result local was typed at (a local is not re-typed later in the
            // same attempt), so that is what the finished return is compared
            // against (see `self_call_rets`).
            if let Some(ret) = cur_ret {
                self.self_call_rets
                    .entry(target)
                    .or_insert_with(|| ret.clone());
            }
            return Ok(cur_ret.clone());
        }
        // Mutual recursion; see resolve_callable for the provisional contract.
        // An unannotated function in the cycle has no annotation to type
        // against, but the checker may have settled this very instance's
        // return; that is the provisional type then, validated like any other
        // assumption when the instance completes.
        if let Some(provisional) = self.in_progress.get(&target) {
            let provisional = provisional.clone().or_else(|| {
                self.instance_return(&effective_base, &arg_types)
                    .map(|ret| resolve_nominal(self.program, ret))
                    .filter(|ret| brass_hir::is_fully_known(ret) && is_supported(ret))
            });
            return match provisional {
                Some(t) => {
                    self.assumed_rets.insert(target, t.clone());
                    Ok(Some(t))
                }
                None => Err(format!(
                    "mutual recursion (`{cur_sym}` <-> `{target}`) needs an explicit return type annotation on `{target}`"
                )),
            };
        }
        if numeric_layout.is_none()
            && let Some(ret) = self.postpone_call(base, &arg_types)
        {
            return Ok(Some(ret));
        }
        if numeric_layout.is_none()
            && let Some(sig) = self.deferrable(base, &arg_types)
        {
            let ret = sig.ret.clone();
            let symbol = instance_symbol(base, &arg_types);
            if let Some(targets) = self.defer.as_mut() {
                targets.insert(symbol, sig);
            }
            return Ok(Some(ret));
        }
        // A missing body in a demand-driven run: record the demand and fail
        // the STATEMENT (a held block error) rather than the frame, so this
        // same pass keeps walking and collects every other missing body it
        // can see -- the retry count becomes the call graph's depth, not its
        // node count. The existing block-error rules keep this sound: a
        // reachable block's held error fails the frame after the walk (so
        // nothing typed under a live miss is ever emitted -- an annotated
        // destination local would otherwise satisfy the unresolved-temporary
        // validation), while a statically dead block's is dropped, and the
        // clean root then rolls the dead demand back at its watermark.
        if self.defer.is_some()
            && !self.by_fn.contains_key(base)
            && self.program.functions.contains_key(base)
        {
            let candidate = self.unannotated_deferral_candidate(base, &arg_types);
            // A candidate is body-free only while its checker contract is
            // still outstanding. If that contract is already present,
            // `deferrable` rejected its concrete return shape above, so only
            // supplying the MIR body can change the next pass.
            let contract_present = self.instance_return(&effective_base, &arg_types).is_some();
            let needs_body = numeric_layout.is_some() || !candidate || contract_present;
            self.note_missing(base, &arg_types, needs_body);
            return Err(format!("internal error: missing body `{base}` (demanded)"));
        }
        let sym = self.instantiate_numeric_fn(base, arg_types, numeric_layout)?;
        Ok(self.instances.get(&sym).map(|i| i.ret.clone()))
    }
}
