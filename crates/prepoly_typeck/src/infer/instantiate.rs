//! Per-call instantiation of function and method signatures: building
//! the argument frame, specializing annotated/scheme types with the
//! actual argument types, and re-inferring returns from the frame.

use super::*;

impl<'a> Checker<'a> {
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
    ) -> Type {
        if params.len() != arg_types.len() {
            return fallback_ret;
        }
        let key = format!("fn:{symbol}");
        if !self.instantiating.insert(key.clone()) {
            // Recursive call: re-checking the body again would not terminate, so
            // fall back to the declared/precomputed return type.
            tracing::debug!(symbol = %symbol, "recursive call, using fallback return type");
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
            None => self.prefer_full_return(full_ret, body, frame),
        };
        self.current_module = saved_module;
        self.instantiating.remove(&key);
        ret
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
        match full_ret {
            Some(t) if !has_props => t,
            _ => light,
        }
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
        let ret = prepoly_hir::collapse_nullable(&apply_scheme_param_map(&scheme_method.ret, &map));
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
        } = call;
        let has_self = signature_params.first().is_some_and(|p| p.name == "self");
        if signature_params.len().saturating_sub(usize::from(has_self)) != arg_types.len() {
            return fallback_ret;
        }
        let key = format!("method:{owner}.{method_name}");
        if !self.instantiating.insert(key.clone()) {
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

    fn signature_call_frame(
        &mut self,
        params: &[ParamInfo],
        arg_types: &[Type],
        scheme_params: &[Option<Type>],
        receiver_ty: Option<Type>,
    ) -> HashMap<String, Type> {
        // Re-checking a callee body sees top-level globals; signature
        // parameters layer on top so they shadow same-named globals.
        let mut frame = self.global_scope.clone();
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
            (Type::Record(want), Type::Record(have)) => {
                let mut substitution = want.substitution.clone();
                if let Some(TypeKind::Record { fields, .. }) =
                    self.program.type_by_id(want.id).map(|info| &info.kind)
                {
                    for field in fields {
                        if field.resolved_ty.as_ref().is_some_and(Type::is_unknown)
                            && let Some(actual_ty) = self.record_field_type(&have, &field.name)
                        {
                            substitution.insert(field.name.clone(), actual_ty);
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
                                .is_some_and(Type::is_unknown)
                            {
                                let key =
                                    method_param_substitution_key(method_name, &want_param.name);
                                if let Some(actual_ty) = have
                                    .substitution
                                    .get(&key)
                                    .cloned()
                                    .or_else(|| have_param.resolved_ty.clone())
                                {
                                    substitution.insert(key, actual_ty);
                                }
                            }
                        }
                        if want_method
                            .signature
                            .ret_ty
                            .as_ref()
                            .is_some_and(Type::is_unknown)
                        {
                            let key = method_return_substitution_key(method_name);
                            let actual_ret = have
                                .substitution
                                .get(&key)
                                .cloned()
                                .or_else(|| have_method.signature.ret_ty.clone())
                                .or_else(|| {
                                    self.method_returns
                                        .get(&(have.name().to_string(), method_name.clone()))
                                        .cloned()
                                });
                            if let Some(actual_ret) = actual_ret {
                                substitution.insert(key, actual_ret);
                            }
                        }
                    }
                }
                apply_nominal_substitution(Type::Record(want), substitution)
            }
            _ => annotated.clone(),
        }
    }

    fn record_field_type(&self, record: &NominalType, field: &str) -> Option<Type> {
        record.substitution.get(field).cloned().or_else(|| {
            self.program
                .types
                .get(record.name())
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
fn scheme_instance_map(scheme: &TypeScheme, recv: &NominalType) -> HashMap<u32, Type> {
    let mut map = HashMap::new();
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
fn apply_scheme_param_map(ty: &Type, map: &HashMap<u32, Type>) -> Type {
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
