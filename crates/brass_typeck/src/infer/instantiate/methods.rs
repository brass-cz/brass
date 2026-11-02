//! Call-site method body elaboration and exact memo replay.

use super::memo_check_enabled;
use crate::infer::{Checker, MethodCall};
use brass_hir::{Type, TypeInfo};
use std::rc::Rc;

impl Checker<'_> {
    /// The method counterpart of [`Self::instantiate_function_call`]: type one
    /// resolved method candidate's call by re-elaborating its body at the
    /// receiver and arguments, in the declaring type's module with `Self`
    /// (and the variant, for a sum method) bound. A recursive call or one past
    /// the elaboration limits gets `call.fallback_ret`.
    pub(in crate::infer) fn instantiate_method_call(&mut self, call: MethodCall<'_>) -> Type {
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
        let numeric_layout = (self.numeric_enabled && declared_ret.is_none())
            .then(|| {
                method.body.as_ref().and_then(|body| {
                    self.numeric_callable_layout(
                        &brass_hir::InstanceCallable::Method {
                            owner: self_type.to_owned(),
                            method: method_name.to_owned(),
                        },
                        &receiver_ty
                            .iter()
                            .chain(arg_types.iter())
                            .cloned()
                            .collect::<Vec<_>>(),
                        body.span,
                    )
                })
            })
            .flatten();
        if self.numeric_enabled && declared_ret.is_none() && method.body.is_some() {
            self.record_numeric_call(span, numeric_layout.clone(), self.current_instance());
        }
        let has_self = signature_params.first().is_some_and(|p| p.name == "self");
        if signature_params.len().saturating_sub(usize::from(has_self)) != arg_types.len() {
            return fallback_ret;
        }
        // Keyed by the receiver TYPE, not by `owner` (the `Sum.Variant` qualifier
        // this call resolved through): a sum's method lives in every variant's
        // table, so one call resolves to one candidate per variant, all sharing
        // the same body. Per-qualifier keys would let a recursive call re-enter
        // through a variant not yet on the stack, growing the work factorially
        // in the variant count -- see `Checker::instantiating`.
        let key = format!("method:{self_type}.{method_name}");
        let key = if self.instantiating.contains(&key)
            && let Some(body) = &method.body
        {
            let inputs: Vec<_> = receiver_ty.iter().chain(arg_types).cloned().collect();
            let Some(key) = self.fields_recursion_key(
                key,
                &brass_hir::InstanceCallable::Method {
                    owner: self_type.to_owned(),
                    method: method_name.to_owned(),
                },
                body.span,
                &inputs,
            ) else {
                return fallback_ret;
            };
            key
        } else {
            key
        };
        // A co-check records return links and an active type-test probe commits
        // bindings for its holes. Recursive calls must take the fallback path.
        let method_rejection = self
            .co_checking
            .then(|| {
                self.method_co_precheck(
                    receiver_ty.as_ref(),
                    arg_types,
                    scheme_params,
                    declared_ret.as_ref(),
                    &fallback_ret,
                )
            })
            .flatten();
        if let Some(reason) = method_rejection {
            tracing::trace!(target: "brass::perf", callable = key, reason, "check: method memo bypass");
        }
        let memo_enabled = !self.numeric.probing
            && (!self.co_checking || method_rejection.is_none())
            && self.type_test_holes.is_empty()
            && !self.instantiating.contains(&key);
        let memo_key = memo_enabled.then(|| {
            receiver_ty
                .clone()
                // Static methods have no value receiver; their declaring nominal
                // is the fixed receiver identity that supplies `Self`.
                .or_else(|| self.program.types.get(self_type).map(TypeInfo::type_ref))
        });
        let mut memo_key = memo_key.flatten().and_then(|resolved_receiver| {
            let variant = owner.split_once('.').map_or("", |(_, variant)| variant);
            let callable = format!("{self_type}:{variant}:{method_name}");
            // Receiver-scheme parameters are derived from the resolved receiver;
            // an unpinned scheme parameter falls back to its argument type. The
            // receiver and arguments therefore cover every frame binding. An
            // ordinary method is not expectation-directed: expected returns only
            // select reflective methods, whose template bodies do not reach here.
            self.elaboration_memo_key(
                "m",
                &callable,
                Some(&resolved_receiver),
                arg_types,
                scheme_params,
            )
        });
        memo_key = self.co_memo_context(memo_key);
        if let (Some(layout), Some(context)) = (&numeric_layout, &mut memo_key) {
            context
                .key
                .callable
                .push_str(&format!(":numeric-layout={layout:?}"));
        }
        let method_dependencies = (self.co_checking && memo_key.is_some())
            .then(|| self.method_memo_dependencies(declared_ret.as_ref(), &fallback_ret));
        let mut co_replayed = None;
        let mut method_validation = None;
        let mut memo_validation = None;
        if let Some(memo_key) = &memo_key
            && let Some(entry) =
                self.lookup_elaboration_entry(memo_key, method_dependencies.as_ref())
        {
            if memo_check_enabled() && method_dependencies.is_some() {
                method_validation = entry.method_dependencies.clone();
            }
            self.stats.memo_hits += 1;
            self.observe_co_lookup(&memo_key.key, true);
            tracing::debug!(callable = %memo_key.key.callable, "elaboration memo hit");
            if self.co_checking && memo_check_enabled() {
                self.begin_co_validation(true);
            }
            let replay_errors_before = self.errors.len();
            let replayed = self.replay_elaboration_memo_entry(&entry, memo_key);
            let replay_errors = self.errors.len() - replay_errors_before;
            if self.co_checking && memo_check_enabled() {
                co_replayed = Some(self.finish_co_validation());
            }
            if !memo_check_enabled() {
                return replayed;
            }
            memo_validation = Some((replayed, replay_errors));
        } else if let Some(memo_key) = &memo_key {
            self.stats.memo_misses += 1;
            self.observe_co_lookup(&memo_key.key, false);
            tracing::debug!(callable = %memo_key.key.callable, "elaboration memo miss");
        }
        let first_touch = memo_validation.is_none()
            && method_dependencies.is_some()
            && memo_key
                .as_ref()
                .is_some_and(|context| !self.method_co_storage_ready(&context.key));
        if first_touch {
            memo_key = None;
        }
        let errors_before = self.errors.len();
        let warnings_before = self.warnings.len();
        if !self.instantiating.insert(key.clone()) {
            self.record_untracked_method_dependency();
            let inputs: Vec<Type> = receiver_ty.iter().chain(arg_types).cloned().collect();
            let names: Vec<&str> = receiver_ty
                .iter()
                .map(|_| "self")
                .chain(
                    signature_params
                        .iter()
                        .filter(|p| p.name != "self")
                        .map(|p| p.name.as_str()),
                )
                .collect();
            self.check_polymorphic_recursion(
                &brass_hir::InstanceCallable::Method {
                    owner: self_type.to_string(),
                    method: method_name.to_string(),
                },
                &format!("{owner}.{method_name}"),
                &names,
                &inputs,
                span,
            );
            return fallback_ret;
        }
        if !self.elaboration_allowed(&format!("{owner}.{method_name}"), span) {
            if let Some(body) = &method.body {
                self.report_incomplete_fields(body.span);
            }
            self.instantiating.remove(&key);
            return fallback_ret;
        }
        if co_replayed.is_some() {
            self.begin_co_validation(false);
        }
        let method_observation = self.method_inventory.is_some()
            && self.begin_method_inventory(&MethodCall {
                owner,
                self_type,
                name: method_name,
                method,
                signature_params,
                receiver_ty: receiver_ty.clone(),
                declared_ret: declared_ret.clone(),
                fallback_ret: fallback_ret.clone(),
                arg_types,
                scheme_params,
                span,
            });
        if self.co_checking {
            tracing::trace!(target: "brass::perf", callable = key,
                reason = method_rejection.unwrap_or(if first_touch { "first_touch" } else if memo_key.is_some() { "memo_miss" } else { "ineligible_key" }),
                "check: method body walk");
        }
        self.observe_body_walk(&key, memo_key.is_some() || first_touch);
        let capped_before = self.depth_capped;
        self.elaboration_stack.push(key.clone());
        if memo_key.is_some() {
            self.begin_elaboration_journal();
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
        let site_inputs: Vec<Type> = receiver_ty.iter().chain(arg_types).cloned().collect();
        self.enter_instance(
            brass_hir::InstanceCallable::Method {
                owner: self_type.to_string(),
                method: method_name.to_string(),
            },
            &site_inputs,
        );
        self.settle_numeric_instance(numeric_layout);
        let frame =
            self.signature_call_frame(signature_params, arg_types, scheme_params, receiver_ty);
        let full_ret = if let Some(body) = &method.body {
            let mut scopes = frame.clone();
            let ret = self.check_block_root(body, &mut scopes, declared_ret.as_ref());
            // The concrete receiver and arguments can reveal a sum that the
            // open method pass could not identify. Publish its coverage errors
            // in this call's delta, before a lazy consumer compiles the method.
            if self.lazy_profile {
                let module = self.current_module.clone();
                self.errors.extend(crate::exhaustive::check_block(
                    self.program,
                    &self.typed,
                    &module,
                    body,
                ));
            }
            ret
        } else {
            None
        };
        let numeric_result = self.numeric.result.clone();
        let ret = match (&method.body, declared_ret) {
            (_, Some(ret)) => ret,
            (Some(body), None) => {
                let site = self.instance_site(
                    format!("{owner}.{method_name}"),
                    span,
                    key.clone(),
                    site_inputs,
                );
                self.prefer_full_return(full_ret, body, frame, site)
            }
            (None, None) => Type::Void,
        };
        self.numeric.result = numeric_result;
        self.leave_instance();
        self.self_type = saved;
        self.self_variant = saved_variant;
        self.current_module = saved_module;
        self.elaboration_stack.pop();
        self.instantiating.remove(&key);
        let co_validation = co_replayed.map(|replay| (replay, self.finish_co_validation()));
        // A replay recorded where the nesting was shallow is exact; this
        // re-elaboration may have fallen back past the depth limit instead.
        if let Some((replayed, replay_errors)) = memo_validation
            && self.depth_capped == capped_before
        {
            debug_assert_eq!(
                self.canonical_memo_check_return(&replayed),
                self.canonical_memo_check_return(&ret)
            );
            debug_assert_eq!(replay_errors, self.errors.len() - errors_before);
            if let (Some(stored), Some(initial)) = (&method_validation, &method_dependencies) {
                self.assert_method_dependencies(&key, stored, initial);
            }
            if let Some((replay, walk)) = co_validation {
                self.assert_co_validation(&key, replay, walk, &replayed, &ret);
            }
        }
        if let Some(memo_key) = memo_key {
            let resolved = self.resolve(&ret);
            let memoizable =
                self.errors.len() == errors_before && self.depth_capped == capped_before;
            let frame = self.finish_elaboration_journal();
            let nested_replay = frame.memo_replayed;
            if memoizable
                && (!self.co_checking || self.warnings.len() == warnings_before)
                && !frame.has_closure_bodies
                && self.speculation_depth == 0
                && self.method_storage_precheck(
                    &memo_key.key.callable,
                    method_dependencies.is_some(),
                    &frame,
                )
                && let Some(mut entry) =
                    self.build_elaboration_memo_entry(&resolved, frame, &memo_key)
                && self.certify_method_entry(
                    &memo_key.key.callable,
                    nested_replay,
                    &mut entry,
                    method_dependencies,
                )
            {
                self.elaboration_memo.insert(memo_key.key, Rc::new(entry));
            }
        }
        self.finish_method_inventory(method_observation, &ret);
        ret
    }
}
