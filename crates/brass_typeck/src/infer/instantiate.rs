//! Per-call instantiation of function and method signatures: building
//! the argument frame, specializing annotated/scheme types with the
//! actual argument types, and re-inferring returns from the frame.

use super::*;

/// How deep the re-elaboration of callee bodies at call sites may nest. Each
/// level is a distinct callable (a repeat is already caught as recursion), so a
/// real program's chain is short; this only bounds a pathological one.
const MAX_ELABORATION_DEPTH: usize = 64;

/// How many callee bodies may be re-elaborated across one analysis. Generous
/// enough that no converging program comes near it -- the heaviest case in the
/// e2e suite and examples (the http library) settles at ~34k, some sixty times
/// under -- and low enough that a chain which expands instead of converging is
/// reported rather than left to run forever.
const ELABORATION_BUDGET: u64 = 2_000_000;

impl<'a> Checker<'a> {
    /// Whether another callee body may be re-elaborated: recursion is guarded per
    /// callable by `instantiating`, but a call graph can still expand faster than
    /// it converges. Rather than hang, stop re-elaborating (call sites fall back
    /// to declared/precomputed returns) and report it once.
    ///
    /// The depth check is separate from the budget so a runaway *nesting* is cut
    /// immediately instead of only once the total is spent.
    fn elaboration_allowed(&mut self, what: &str, span: brass_parser::Span) -> bool {
        if self.instantiating.len() >= MAX_ELABORATION_DEPTH {
            tracing::debug!(callee = %what, "elaboration depth limit, using fallback return type");
            return false;
        }
        self.elaborations += 1;
        if self.elaborations <= ELABORATION_BUDGET {
            return true;
        }
        if !self.elaboration_budget_reported {
            self.elaboration_budget_reported = true;
            self.errors.push(TypeError {
                message: format!(
                    "type inference gave up while re-elaborating `{what}`: the calls it \
                     expands into keep growing instead of settling. Annotate the return \
                     types of the callables in this chain so each call can be typed from \
                     its signature instead of its body"
                ),
                span,
            });
        }
        false
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn instantiate_function_call(
        &mut self,
        symbol: &str,
        module: &[String],
        params: &[ParamInfo],
        body: &Block,
        declared_ret: Option<Type>,
        fallback_ret: Type,
        arg_types: &[Type],
        span: brass_parser::Span,
    ) -> Type {
        if params.len() != arg_types.len() {
            return fallback_ret;
        }
        let unannotated = declared_ret.is_none();
        // A previous elaboration of this callee at the same fully-resolved
        // argument types already recorded the body's channel entries and
        // settled its return; reuse it (see `Checker::elaboration_memo`).
        let memo_key = self.elaboration_memo_key("fn", symbol, arg_types);
        if let Some(memo_key) = &memo_key
            && let Some(ret) = self.elaboration_memo.get(memo_key)
        {
            return ret.clone();
        }
        let errors_before = self.errors.len();
        let key = format!("fn:{symbol}");
        if !self.instantiating.insert(key.clone()) {
            // Recursive call: re-checking the body again would not terminate, so
            // fall back to the declared/precomputed return type. Remember that it
            // happened -- the fallback is the SHARED table entry, and only a body
            // that read it needs its variables tied to the real return.
            tracing::debug!(symbol = %symbol, "recursive call, using fallback return type");
            self.recursed.insert(key);
            return fallback_ret;
        }
        if !self.elaboration_allowed(symbol, span) {
            self.instantiating.remove(&key);
            return fallback_ret;
        }
        tracing::debug!(
            symbol = %symbol,
            args = ?arg_types.iter().map(|t| self.resolve(t).display()).collect::<Vec<_>>(),
            "re-elaborating function body at call site"
        );
        // Re-check the callee body in its own module so its internal names
        // resolve under that module's visibility, not the caller's.
        let saved_module = std::mem::replace(&mut self.current_module, module.to_vec());
        // A free function has no receiver instance, so no scheme parameters.
        let frame = self.signature_call_frame(params, arg_types, &[], None);
        let mut scopes = vec![frame.clone()];
        let full_ret = self.check_block_root(body, &mut scopes, declared_ret.as_ref());
        let ret = match declared_ret {
            Some(ret) => ret,
            None => {
                let ret = self.prefer_full_return(full_ret, body, frame);
                // A RECURSIVE call inside this body could only read the PRECOMPUTED
                // return -- the full one is what we just computed -- and it shares
                // that entry's variables. Tie the two together, so a container the
                // body pins (a `HashMap.new()` filled by `set`) is no longer OPEN
                // where the recursion hands it back: a method called on it
                // (`collect(..)!.pairs()`) would otherwise monomorphize at an open
                // type, which the typed back end refuses -- a program the checker
                // accepted. Only a body that actually recursed: the entry is shared
                // by every call site, so pinning it for a function that never reads
                // it back would fix a generic callee at its first call.
                if self.recursed.remove(&key) {
                    self.link_inferred_return(&fallback_ret, &ret);
                }
                ret
            }
        };
        self.current_module = saved_module;
        self.instantiating.remove(&key);
        if let Some(memo_key) = memo_key
            && self.errors.len() == errors_before
        {
            let resolved = self.resolve(&ret);
            if brass_hir::is_fully_known(&resolved) {
                if unannotated {
                    self.instance_returns
                        .insert((symbol.to_string(), memo_key.1.clone()), resolved.clone());
                }
                self.elaboration_memo.insert(memo_key, resolved);
            }
        }
        ret
    }

    /// The memo key for re-elaborating a callable at these argument types, or
    /// `None` when any argument is not fully resolved (elaborating at an open
    /// argument constrains the caller's variables, which a memo hit must not
    /// skip). The resolved argument types are kept structurally -- hashing
    /// them directly is much cheaper than rendering them to a string, and the
    /// structural comparison distinguishes two instantiations of one nominal
    /// the way a full `Debug` rendering would (ids and substitutions
    /// included).
    fn elaboration_memo_key(
        &self,
        kind: &str,
        callable: &str,
        arg_types: &[Type],
    ) -> Option<(String, Vec<Type>)> {
        let mut resolved_args = Vec::with_capacity(arg_types.len());
        for arg in arg_types {
            let resolved = self.resolve(arg);
            if !brass_hir::is_fully_known(&resolved) {
                return None;
            }
            resolved_args.push(resolved);
        }
        Some((format!("{kind}:{callable}"), resolved_args))
    }

    /// Choose an inferred-return body's return type: the full check's
    /// reconciliation when it produced one and the body raises no propagation
    /// (the full check observes the stores/pushes the light pass misses),
    /// otherwise the light assembly -- a fallible body's `Result` from its
    /// error sites, wrapped in `?` when a nullable `expr!` can return null --
    /// which the normal-return reconciliation does not build.
    fn prefer_full_return(
        &mut self,
        full_ret: Option<Type>,
        body: &Block,
        frame: HashMap<String, Type>,
    ) -> Type {
        let mut env = frame;
        let mut normal = Vec::new();
        let mut props = LightProps::default();
        self.infer_returns_block(body, &mut env, &mut normal, &mut props);
        let has_props = !props.errors.is_empty() || !props.nulls.is_empty();
        // Call-site re-inference does not report conflicts; the definition
        // site already did.
        let normal_ty = self.reconcile_return_types(&normal, false);
        let err_ty = self.reconcile_error_payloads(&props.errors, false);
        let base = self.result_from_payloads(normal_ty, err_ty);
        let light = super::precompute::wrap_null_propagated_return(base, &props.nulls);
        let collected = std::mem::take(&mut self.last_returns);
        if let Some(t) = full_ret
            && !has_props
        {
            return t;
        }
        // A propagating body's `Result`/`?` WRAPPING is the light assembly's -- the
        // full check's reconciliation does not rebuild it -- but its Ok PAYLOAD is
        // the full check's. The light pass cannot re-elaborate a method's body, so a
        // container the body fills (`HashMap.new()` then `set`) keeps OPEN element
        // types there while the full check pins them. Take the light shape and fill
        // it from what the body really returns, or the map reaches the back end with
        // its element types unset.
        //
        // Reconciled HERE rather than taken from `full_ret`: an `error(..)` return
        // carries no Ok value (its payload is a variable no path produces), and
        // reconciled in it wins and leaves the payload open.
        let mut values = Vec::with_capacity(collected.len());
        for (ty, span) in collected {
            let resolved = self.resolve(&ty);
            if resolved
                .result_payloads()
                .is_some_and(|(ok, _)| ok.is_unknown())
            {
                continue;
            }
            values.push((ty, span));
        }
        if let Some(ok) = self.reconcile_return_types(&values, false) {
            self.link_inferred_return(&light, &ok);
        }
        light
    }

    /// Type a method call's result by instantiating the method's scheme against
    /// the receiver instance: the scheme expresses the return over the type's
    /// inferred parameters, and matching the scheme's field types to the
    /// receiver's resolved field substitution fixes them (`get`'s `-> V?` becomes
    /// `-> string?` for a `string`-valued map). Returns `None` when the receiver
    /// is not a scheme'd record, the method is not in the scheme, or the return
    /// still has an open parameter the instance did not pin (a parameter that only
    /// flows through `==`, never a store or field read) -- the caller then keeps
    /// the re-elaborated return.
    /// For a method call on a scheme'd record receiver, the type each non-`self`
    /// parameter instantiates to for this receiver instance -- the map's `set`
    /// value parameter becomes `int64` for a `string -> int64` map. `Some(t)`
    /// only when the receiver pins the parameter to a fully-known type; a
    /// parameter the instance leaves open (or a non-record/non-scheme receiver)
    /// yields `None`, so the caller falls back to the argument's own type. The
    /// result is aligned with the call's arguments (the receiver's `self` is not
    /// included).
    pub(super) fn scheme_method_param_types(
        &self,
        recv_ty: &Type,
        method: &str,
    ) -> Vec<Option<Type>> {
        let mut t = self.resolve(recv_ty);
        while let Type::Ref(i) | Type::Mut(i) | Type::ConstOf(i) | Type::Nullable(i) = t {
            t = *i;
        }
        let Type::Record(nominal) = t else {
            return Vec::new();
        };
        let Some(info) = self.program.type_by_id(nominal.id) else {
            return Vec::new();
        };
        let Some(scheme) = self.schemes.get(&info.name) else {
            return Vec::new();
        };
        let Some(scheme_method) = scheme.methods.get(method) else {
            return Vec::new();
        };
        let map = scheme_instance_map(scheme, &nominal);
        scheme_method
            .params
            .iter()
            .filter(|(name, _)| name != "self")
            .map(|(_, ty)| {
                let inst = apply_scheme_param_map(ty, &map);
                self.solver.free_vars(&inst).is_empty().then_some(inst)
            })
            .collect()
    }

    pub(super) fn scheme_method_return(&self, recv_ty: &Type, method: &str) -> Option<Type> {
        let mut t = self.resolve(recv_ty);
        while let Type::Ref(i) | Type::Mut(i) | Type::ConstOf(i) | Type::Nullable(i) = t {
            t = *i;
        }
        let Type::Record(nominal) = t else {
            return None;
        };
        let info = self.program.type_by_id(nominal.id)?;
        let scheme = self.schemes.get(&info.name)?;
        let scheme_method = scheme.methods.get(method)?;
        let map = scheme_instance_map(scheme, &nominal);
        // Instantiating a `?`-wrapped scheme return with a nullable value type
        // nests the nullable; collapse it (there is one `null`).
        let ret = brass_hir::collapse_nullable(&apply_scheme_param_map(&scheme_method.ret, &map));
        // Only adopt the instantiated return when it is fully resolved; an open
        // variable means the instance did not constrain it, so the re-elaborated
        // return (which can still defer) is the safer choice.
        self.solver.free_vars(&ret).is_empty().then_some(ret)
    }

    pub(super) fn instantiate_method_call(&mut self, call: MethodCall<'_>) -> Type {
        let MethodCall {
            owner,
            self_type,
            name: method_name,
            method,
            signature_params,
            receiver_ty,
            declared_ret,
            fallback_ret,
            arg_types,
            scheme_params,
            span,
        } = call;
        let has_self = signature_params.first().is_some_and(|p| p.name == "self");
        if signature_params.len().saturating_sub(usize::from(has_self)) != arg_types.len() {
            return fallback_ret;
        }
        // Keyed by the receiver TYPE, not by `owner` (the `Sum.Variant` qualifier
        // this call resolved through): a sum's method lives in every variant's
        // table, so one call resolves to one candidate per variant, all sharing
        // the same body. Per-qualifier keys let a recursive call re-enter through
        // a variant not yet on the stack, and the work grew factorially in the
        // variant count -- see `Checker::instantiating`.
        let key = format!("method:{self_type}.{method_name}");
        if !self.instantiating.insert(key.clone()) {
            return fallback_ret;
        }
        if !self.elaboration_allowed(&format!("{owner}.{method_name}"), span) {
            self.instantiating.remove(&key);
            return fallback_ret;
        }
        let saved = self.self_type.replace(self_type.to_string());
        let saved_variant = self.self_variant.clone();
        self.self_variant = owner
            .split_once('.')
            .map(|(_, variant)| (self_type.to_string(), variant.to_string()));
        // Re-check the method body in its defining type's module.
        let owner_type = self_type.to_string();
        let saved_module =
            self.swap_module_for(|p| p.types.get(&owner_type).map(|t| t.module.clone()));
        let frame =
            self.signature_call_frame(signature_params, arg_types, scheme_params, receiver_ty);
        let full_ret = if let Some(body) = &method.body {
            let mut scopes = vec![frame.clone()];
            self.check_block_root(body, &mut scopes, declared_ret.as_ref())
        } else {
            None
        };
        let ret = match (&method.body, declared_ret) {
            (_, Some(ret)) => ret,
            (Some(body), None) => self.prefer_full_return(full_ret, body, frame),
            (None, None) => Type::Void,
        };
        self.self_type = saved;
        self.self_variant = saved_variant;
        self.current_module = saved_module;
        self.instantiating.remove(&key);
        ret
    }

    pub(super) fn signature_call_frame(
        &mut self,
        params: &[ParamInfo],
        arg_types: &[Type],
        scheme_params: &[Option<Type>],
        receiver_ty: Option<Type>,
    ) -> HashMap<String, Type> {
        // Re-checking a callee body sees the globals visible from ITS module
        // (`current_module` is the callee's here); signature parameters layer on
        // top so they shadow same-named globals.
        let mut frame = self.global_scope();
        let mut arg_idx = 0;
        for param in params {
            // A method called with the receiver passed separately (`receiver_ty`)
            // binds `self` to it and does not consume an argument slot. A
            // primitive/array method (`fun infer[].slice`) is instead instantiated
            // like a function: its receiver is `arg_types[0]`, aligned with the
            // `self` parameter, so `self` is handled by the ordinary positional
            // branch below (instantiating its `infer[]` annotation against the
            // receiver and advancing `arg_idx`).
            let ty = if param.name == "self" && receiver_ty.is_some() {
                receiver_ty
                    .clone()
                    .or_else(|| param.resolved_ty.clone())
                    .unwrap_or_else(|| self.fresh_unknown())
            } else if let Some(annotated) = param_expected_type(param).cloned() {
                let ty = arg_types
                    .get(arg_idx)
                    .map(|arg| self.instantiate_annotated_type(&annotated, arg))
                    .unwrap_or(annotated);
                arg_idx += 1;
                ty
            } else {
                // An unannotated parameter takes the receiver-instantiated type
                // (from the scheme) when the instance pins it, so the body sees
                // the map's actual value type rather than an argument's default;
                // otherwise it takes the argument's own type.
                let ty = scheme_params
                    .get(arg_idx)
                    .and_then(|o| o.clone())
                    .or_else(|| arg_types.get(arg_idx).cloned())
                    .or_else(|| param.resolved_ty.clone())
                    .unwrap_or_else(|| self.fresh_unknown());
                arg_idx += 1;
                ty
            };
            frame.insert(param.name.clone(), ty);
        }
        frame
    }

    pub(super) fn instantiate_annotated_type(&self, annotated: &Type, actual: &Type) -> Type {
        // Match against the actual value type, looking through `const`/`mut`/`ref`
        // wrappers (an argument's mutability/reference does not change which
        // element type a generic parameter is instantiated with).
        let actual = peel_value_wrappers(&self.resolve(actual)).clone();
        match (self.resolve(annotated), actual) {
            // A bare `infer` parameter takes the argument's type.
            (Type::Unknown(_), have) => have,
            // Passing wrappers belong to the annotated signature, while the
            // actual argument is matched by its underlying value type. Recurse
            // under every wrapper so a generic record does not lose its field
            // substitution merely because it is borrowed or copied.
            (Type::ConstOf(want), have) => {
                Type::ConstOf(Box::new(self.instantiate_annotated_type(&want, &have)))
            }
            (Type::Mut(want), have) => {
                Type::Mut(Box::new(self.instantiate_annotated_type(&want, &have)))
            }
            (Type::Ref(want), have) => {
                Type::Ref(Box::new(self.instantiate_annotated_type(&want, &have)))
            }
            // A generic container parameter (`infer[]`, `infer[]?`, ...) is
            // instantiated element-wise, so e.g. `slice(arr: infer[])` applied to
            // an `int32[]` returns an `int32[]` rather than an unconstrained `?[]`.
            (Type::Slice(want), Type::Slice(have) | Type::Array(have, _)) => {
                Type::Slice(Box::new(self.instantiate_annotated_type(&want, &have)))
            }
            (Type::Array(want, n), Type::Array(have, _) | Type::Slice(have)) => {
                Type::Array(Box::new(self.instantiate_annotated_type(&want, &have)), n)
            }
            (Type::Nullable(want), Type::Nullable(have)) => {
                Type::Nullable(Box::new(self.instantiate_annotated_type(&want, &have)))
            }
            // A non-null actual is promoted to the annotated nullable after its
            // inner generic positions have been instantiated.
            (Type::Nullable(want), have) => {
                Type::Nullable(Box::new(self.instantiate_annotated_type(&want, &have)))
            }
            (Type::Tuple(want), Type::Tuple(have)) if want.len() == have.len() => Type::Tuple(
                want.iter()
                    .zip(&have)
                    .map(|(want, have)| self.instantiate_annotated_type(want, have))
                    .collect(),
            ),
            (Type::Fun(want_params, want_ret), Type::Fun(have_params, have_ret))
                if want_params.len() == have_params.len() =>
            {
                Type::Fun(
                    want_params
                        .iter()
                        .zip(&have_params)
                        .map(|(want, have)| self.instantiate_annotated_type(want, have))
                        .collect(),
                    Box::new(self.instantiate_annotated_type(&want_ret, &have_ret)),
                )
            }
            (Type::Record(want), Type::Record(have)) => {
                let mut substitution = want.substitution.clone();
                for (key, _) in want.substitution.iter() {
                    if let Some(have_ty) = have.substitution.get(key) {
                        substitution.insert(key, have_ty.clone());
                    }
                }
                if let Some(TypeKind::Record { fields, .. }) =
                    self.program.type_by_id(want.id).map(|info| &info.kind)
                {
                    for field in fields {
                        if field
                            .resolved_ty
                            .as_ref()
                            .is_some_and(|ty| !brass_hir::is_fully_known(ty))
                            && let Some(have_ty) = self.record_field_type(&have, &field.name)
                        {
                            substitution.insert(field.name.clone(), have_ty);
                        }
                    }
                }
                if let Some(TypeKind::Record { methods, .. }) =
                    self.program.type_by_id(want.id).map(|info| &info.kind)
                {
                    for (method_name, want_method) in methods {
                        let Some(have_method) =
                            self.program
                                .type_by_id(have.id)
                                .and_then(|info| match &info.kind {
                                    TypeKind::Record { methods, .. } => methods.get(method_name),
                                    TypeKind::Sum { .. } => None,
                                })
                        else {
                            continue;
                        };
                        for (want_param, have_param) in want_method
                            .signature
                            .params
                            .iter()
                            .zip(&have_method.signature.params)
                        {
                            if want_param.name == "self" {
                                continue;
                            }
                            if want_param
                                .resolved_ty
                                .as_ref()
                                .is_some_and(|ty| !brass_hir::is_fully_known(ty))
                            {
                                let key =
                                    method_param_substitution_key(method_name, &want_param.name);
                                if let Some(have_ty) = have
                                    .substitution
                                    .get(&key)
                                    .cloned()
                                    .or_else(|| have_param.resolved_ty.clone())
                                {
                                    substitution.insert(key, have_ty);
                                }
                            }
                        }
                        if want_method
                            .signature
                            .ret_ty
                            .as_ref()
                            .is_some_and(|ty| !brass_hir::is_fully_known(ty))
                        {
                            let key = method_return_substitution_key(method_name);
                            let have_ret = have
                                .substitution
                                .get(&key)
                                .cloned()
                                .or_else(|| have_method.signature.ret_ty.clone())
                                .or_else(|| {
                                    self.method_returns
                                        .get(&(have.name().to_string(), method_name.clone()))
                                        .cloned()
                                });
                            if let Some(have_ret) = have_ret {
                                substitution.insert(key, have_ret);
                            }
                        }
                    }
                }
                apply_nominal_substitution(Type::Record(want), substitution)
            }
            (Type::Sum(want), Type::Sum(have)) => {
                let mut substitution = want.substitution.clone();
                for (key, _) in want.substitution.iter() {
                    if let Some(have_ty) = have.substitution.get(key) {
                        substitution.insert(key, have_ty.clone());
                    }
                }
                if let Some(TypeKind::Sum { variants }) =
                    self.program.type_by_id(want.id).map(|info| &info.kind)
                {
                    for variant in variants {
                        for field in &variant.fields {
                            let Some(want_ty) = field.resolved_ty.as_ref() else {
                                continue;
                            };
                            if brass_hir::is_fully_known(want_ty) {
                                continue;
                            }
                            let key = field_substitution_key(Some(&variant.name), &field.name);
                            if let Some(have_ty) = have.substitution.get(&key) {
                                substitution.insert(key, have_ty.clone());
                            }
                        }
                    }
                }
                apply_nominal_substitution(Type::Sum(want), substitution)
            }
            _ => annotated.clone(),
        }
    }

    fn record_field_type(&self, record: &NominalType, field: &str) -> Option<Type> {
        record.substitution.get(field).cloned().or_else(|| {
            self.program
                .type_by_id(record.id)
                .and_then(|info| match &info.kind {
                    TypeKind::Record { fields, .. } => fields
                        .iter()
                        .find(|candidate| candidate.name == field)
                        .and_then(|candidate| candidate.resolved_ty.clone()),
                    TypeKind::Sum { .. } => None,
                })
        })
    }
}

/// Map each scheme parameter to the receiver instance's concrete type by matching
/// the scheme's field types against the receiver's resolved field substitution
/// (`entries : _Entry<K, V>[]` vs `entries : _Entry<string, string>[]` gives `K
/// -> string`, `V -> string`). Used to instantiate a method's scheme at a call.
pub(super) fn scheme_instance_map(scheme: &TypeScheme, recv: &NominalType) -> HashMap<u32, Type> {
    let mut map = HashMap::default();
    for (fname, fty) in &scheme.fields {
        if let Some(actual) = recv.substitution.get(fname) {
            match_scheme_param(fty, actual, &scheme.params, &mut map);
        }
    }
    map
}

/// Record `param -> actual` where a scheme parameter variable aligns with a
/// concrete position in the receiver's field type, recursing structurally.
fn match_scheme_param(
    scheme_ty: &Type,
    actual: &Type,
    params: &[u32],
    map: &mut HashMap<u32, Type>,
) {
    match (scheme_ty, actual) {
        (Type::Unknown(id), a) if params.contains(id) => {
            map.entry(*id).or_insert_with(|| a.clone());
        }
        (Type::Slice(s), Type::Slice(a))
        | (Type::Slice(s), Type::Array(a, _))
        | (Type::Array(s, _), Type::Slice(a))
        | (Type::Array(s, _), Type::Array(a, _))
        | (Type::Nullable(s), Type::Nullable(a))
        | (Type::Ref(s), Type::Ref(a))
        | (Type::Mut(s), Type::Mut(a))
        | (Type::ConstOf(s), Type::ConstOf(a)) => match_scheme_param(s, a, params, map),
        (Type::Record(sn), Type::Record(an)) | (Type::Sum(sn), Type::Sum(an)) => {
            for (k, sv) in sn.substitution.iter() {
                if let Some(av) = an.substitution.get(k) {
                    match_scheme_param(sv, av, params, map);
                }
            }
        }
        _ => {}
    }
}

/// Substitute scheme parameters with their concrete types throughout a type.
pub(super) fn apply_scheme_param_map(ty: &Type, map: &HashMap<u32, Type>) -> Type {
    match ty {
        Type::Unknown(id) => map.get(id).cloned().unwrap_or_else(|| ty.clone()),
        Type::Slice(e) => Type::Slice(Box::new(apply_scheme_param_map(e, map))),
        Type::Array(e, n) => Type::Array(Box::new(apply_scheme_param_map(e, map)), *n),
        Type::Nullable(e) => Type::Nullable(Box::new(apply_scheme_param_map(e, map))),
        Type::Ref(e) => Type::Ref(Box::new(apply_scheme_param_map(e, map))),
        Type::Mut(e) => Type::Mut(Box::new(apply_scheme_param_map(e, map))),
        Type::ConstOf(e) => Type::ConstOf(Box::new(apply_scheme_param_map(e, map))),
        Type::Fun(ps, r) => Type::Fun(
            ps.iter().map(|p| apply_scheme_param_map(p, map)).collect(),
            Box::new(apply_scheme_param_map(r, map)),
        ),
        Type::Tuple(es) => Type::Tuple(es.iter().map(|e| apply_scheme_param_map(e, map)).collect()),
        Type::Record(n) => Type::Record(map_scheme_nominal(n, map)),
        Type::Sum(n) => Type::Sum(map_scheme_nominal(n, map)),
        other => other.clone(),
    }
}

fn map_scheme_nominal(n: &NominalType, map: &HashMap<u32, Type>) -> NominalType {
    let mut subst = Substitution::empty();
    for (k, v) in n.substitution.iter() {
        subst.insert(k, apply_scheme_param_map(v, map));
    }
    NominalType::with_substitution(n.id, n.name().to_string(), subst)
}
