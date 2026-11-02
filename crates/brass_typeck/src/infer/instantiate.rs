//! Call-site elaboration of function and method bodies: a call re-checks its
//! callee's body at the call's argument types (memoized per canonical
//! instantiation, bounded in depth and in total), and the call's result is
//! the return that instantiation produces. This module builds the callee's
//! argument frame (annotations and receiver schemes instantiated at the
//! arguments), types a recursive call against the elaboration in progress,
//! and settles an unannotated body's return from its full and light walks.

use super::*;
use std::sync::OnceLock;

mod canonical;
mod methods;
mod observed;

/// How deep the re-elaboration of callee bodies at call sites may nest. Each
/// level is a distinct callable or reflected instance, so a
/// real program's chain is short; this only bounds a pathological one.
const MAX_ELABORATION_DEPTH: usize = 64;

/// How many callee bodies may be re-elaborated across one analysis. Generous
/// enough that no converging program comes near it -- the heaviest case in the
/// e2e suite and examples (the http library) settles at ~34k, some sixty times
/// under -- and low enough that a chain which expands instead of converging is
/// reported rather than left to run forever.
pub(super) const ELABORATION_BUDGET: u64 = 2_000_000;

fn memo_check_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("BRASS_MEMO_CHECK").is_ok_and(|value| value == "1"))
}

struct FunctionCall<'a> {
    symbol: &'a str,
    module: &'a [String],
    params: &'a [ParamInfo],
    body: &'a Block,
    declared_ret: Option<Type>,
    fallback_ret: Type,
    arg_types: &'a [Type],
    span: brass_parser::Span,
}

impl<'a> Checker<'a> {
    /// Whether another callee body may be re-elaborated: recursion is guarded per
    /// callable (or reflected instance) by `instantiating`, but calls can expand faster than
    /// it converges. Rather than hang, stop re-elaborating (call sites fall back
    /// to declared/precomputed returns) and report it once.
    ///
    /// The depth check is separate from the budget so a runaway *nesting* is cut
    /// immediately instead of only once the total is spent.
    fn elaboration_allowed(&mut self, what: &str, span: brass_parser::Span) -> bool {
        if self.instantiating.len() >= MAX_ELABORATION_DEPTH {
            tracing::debug!(callee = %what, "elaboration depth limit, using fallback return type");
            self.depth_capped += 1;
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

    fn instantiate_function_call_inner(&mut self, call: FunctionCall<'_>) -> Type {
        let FunctionCall {
            symbol,
            module,
            params,
            body,
            declared_ret,
            fallback_ret,
            arg_types,
            span,
        } = call;
        if params.len() != arg_types.len() {
            return fallback_ret;
        }
        // An annotated result ends origin flow. A structurally zero-growth
        // body has no storage negotiation to retain, so its ordinary memo is
        // valid even inside its caller's private numeric walk.
        if self.numeric.probing
            && declared_ret.is_some()
            && self.numeric_eligibility().transitive(body.span)
        {
            let mut numeric = std::mem::take(&mut self.numeric);
            let enabled = std::mem::replace(&mut self.numeric_enabled, false);
            let depth = self.speculation_depth;
            if depth == 1 {
                self.speculation_depth = 0;
            }
            let co_suspended = self.co_memo_suspended;
            self.co_memo_suspended |= self.co_checking;
            let result = self.instantiate_function_call(
                symbol,
                module,
                params,
                body,
                declared_ret,
                fallback_ret,
                arg_types,
                span,
            );
            self.speculation_depth = depth;
            self.co_memo_suspended = co_suspended;
            self.numeric_enabled = enabled;
            numeric.result = None;
            self.numeric = numeric;
            return result;
        }
        let unannotated = declared_ret.is_none();
        let numeric_layout = (unannotated && self.numeric_enabled)
            .then(|| {
                self.numeric_callable_layout(
                    &brass_hir::InstanceCallable::Function(symbol.to_owned()),
                    arg_types,
                    body.span,
                )
            })
            .flatten();
        if unannotated && self.numeric_enabled {
            self.record_numeric_call(span, numeric_layout.clone(), self.current_instance());
        }
        let key = format!("fn:{symbol}");
        let key = if self.instantiating.contains(&key) {
            let Some(key) = self.fields_recursion_key(
                key,
                &brass_hir::InstanceCallable::Function(symbol.to_owned()),
                body.span,
                arg_types,
            ) else {
                return fallback_ret;
            };
            key
        } else {
            key
        };
        // Co-check effects share the ordinary journal under a distinct flavor.
        // Type-test probes commit hole bindings, and recursion must read the
        // shared fallback instead of consulting or populating the body memo.
        let co_method = self.co_checking && !self.co_free_function(symbol);
        let method_rejection = co_method
            .then(|| {
                self.method_co_precheck(None, arg_types, &[], declared_ret.as_ref(), &fallback_ret)
            })
            .flatten();
        if let Some(reason) = method_rejection {
            tracing::trace!(target: "brass::perf", callable = symbol, reason, "check: method memo bypass");
        }
        let numeric_replay = self.numeric.probing && self.numeric_pure_body(symbol);
        let memo_enabled = (!self.numeric.probing || numeric_replay)
            && (!self.co_checking
                || self.co_memo_eligible(symbol)
                || (co_method && method_rejection.is_none()))
            && self.type_test_holes.is_empty()
            && !self.instantiating.contains(&key);
        let mut memo_key = memo_enabled
            .then(|| self.elaboration_memo_key("fn", symbol, None, arg_types, &[]))
            .flatten();
        memo_key = self.co_memo_context(memo_key);
        if numeric_replay && let Some(context) = &mut memo_key {
            self.numeric_memo_flavor(context);
        }
        if unannotated
            && let Some(layout) = numeric_layout.clone()
            && let Some(context) = &mut memo_key
        {
            context
                .key
                .callable
                .push_str(&format!(":numeric-layout={layout:?}"));
        }
        let method_dependencies = (co_method && memo_key.is_some())
            .then(|| self.method_memo_dependencies(declared_ret.as_ref(), &fallback_ret));
        let mut method_validation = None;
        let mut memo_validation = None;
        let mut co_replayed = None;
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
            let validate_co = self.co_checking && memo_check_enabled();
            if validate_co {
                self.begin_co_validation(true);
            }
            let replay_errors_before = self.errors.len();
            let replayed = self.replay_elaboration_memo_entry(&entry, memo_key);
            let replay_errors = self.errors.len() - replay_errors_before;
            if validate_co {
                co_replayed = Some(self.finish_co_validation());
            }
            if !memo_check_enabled() {
                if numeric_replay {
                    self.replay_numeric_origin(memo_key, body.span);
                }
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
            // Recursive call: re-checking the body again would not terminate, so
            // the call is typed against what the elaboration in progress
            // assumes it returns: the settled return while a recursive
            // instantiation is re-elaborated (see `settle_recursive_return`),
            // else its PROVISIONAL return (see `recursion_provisional`), else
            // the declared/precomputed one. Remember that it happened: the
            // assumed type is tied to what the body really returns once the
            // body is done.
            tracing::debug!(symbol = %symbol, "recursive call, using provisional return type");
            let name = self
                .program
                .functions
                .get(symbol)
                .map_or(symbol, |f| f.signature.name.as_str());
            let names: Vec<&str> = params.iter().map(|p| p.name.as_str()).collect();
            self.check_polymorphic_recursion(
                &brass_hir::InstanceCallable::Function(symbol.to_string()),
                name,
                &names,
                arg_types,
                span,
            );
            self.recursed.insert(key.clone());
            if self.elaboration_stack.last() != Some(&key) {
                self.mutually_recursed.insert(key.clone());
            }
            if let Some(assumed) = self.recursion_assumption(&key, arg_types) {
                return assumed;
            }
            let in_progress = self
                .recursion_provisional
                .get(&key)
                .map(|(args, provisional)| {
                    let same_args = args.len() == arg_types.len()
                        && args
                            .iter()
                            .zip(arg_types)
                            .all(|(arg, now)| *arg == self.resolve(now));
                    (same_args, provisional.clone())
                });
            return match in_progress {
                Some((true, provisional)) => provisional,
                // A recursive call at other argument types (polymorphic
                // recursion) gets a provisional type of its own.
                Some((false, _)) => {
                    self.instance_provisional_return(&fallback_ret, params, arg_types)
                }
                None => fallback_ret,
            };
        }
        if !self.elaboration_allowed(symbol, span) {
            self.report_incomplete_fields(body.span);
            self.instantiating.remove(&key);
            return fallback_ret;
        }
        if co_replayed.is_some() {
            self.begin_co_validation(false);
        }
        let method_observation =
            self.begin_receiver_inventory(symbol, arg_types, declared_ret.as_ref(), &fallback_ret);
        if co_method {
            tracing::trace!(target: "brass::perf", callable = key,
                reason = method_rejection.unwrap_or(if first_touch { "first_touch" } else if memo_key.is_some() { "memo_miss" } else { "ineligible_key" }),
                "check: method body walk");
        }
        self.observe_body_walk(&key, memo_key.is_some() || first_touch);
        let capped_before = self.depth_capped;
        if unannotated {
            let provisional = self.instance_provisional_return(&fallback_ret, params, arg_types);
            let args = arg_types.iter().map(|arg| self.resolve(arg)).collect();
            self.recursion_provisional
                .insert(key.clone(), (args, provisional));
        }
        self.elaboration_stack.push(key.clone());
        self.enter_instance(
            brass_hir::InstanceCallable::Function(symbol.to_string()),
            arg_types,
        );
        self.settle_numeric_instance(unannotated.then(|| numeric_layout.clone()).flatten());
        if memo_key.is_some() {
            self.begin_elaboration_journal();
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
        let mut scopes = frame.clone();
        let full_ret = self.check_block_root(body, &mut scopes, declared_ret.as_ref());
        let numeric_result = self.numeric.result.clone();
        let ret = match declared_ret {
            Some(ret) => ret,
            None => {
                let site = self.instance_site(
                    symbol.to_string(),
                    span,
                    key.clone(),
                    arg_types.iter().cloned(),
                );
                let mut ret = self.prefer_full_return(full_ret, body, frame.clone(), site);
                // What this body's recursive calls were typed against: the
                // instance's provisional return, or -- when that is a concrete
                // type the real return contradicts (a `return 0` default against
                // a float instantiation) -- the return the body is elaborated
                // again with, until the two agree.
                let mut read = self
                    .recursion_provisional
                    .get(&key)
                    .map(|(_, provisional)| provisional.clone());
                if self.recursed.contains(&key) {
                    let first = read.clone().unwrap_or_else(|| fallback_ret.clone());
                    let (settled, assumed) =
                        self.settle_recursive_return(&key, arg_types, &first, ret, |this| {
                            let mut scopes = frame.clone();
                            let full_ret = this.check_block_root(body, &mut scopes, None);
                            let site = this.instance_site(
                                symbol.to_string(),
                                span,
                                key.clone(),
                                arg_types.iter().cloned(),
                            );
                            this.prefer_full_return(full_ret, body, frame.clone(), site)
                        });
                    ret = settled;
                    if assumed.is_some() {
                        read = assumed;
                    }
                }
                self.recursion_provisional.remove(&key);
                // Tie what the recursive calls read to what the body really
                // returns, so a container the body pins (a `HashMap.new()`
                // filled by `set`) is not left OPEN where the recursion hands
                // it back: a method called on it (`collect(..)!.pairs()`) would
                // otherwise monomorphize at an open type, which the typed back
                // end refuses. The provisional type belongs to THIS instance
                // alone, so pinning it never fixes the generic callee for its
                // other call sites.
                let mutual = self.mutually_recursed.remove(&key);
                if self.recursed.remove(&key) {
                    if let Some(read) = read {
                        self.link_inferred_return(&read, &ret, symbol, span);
                    }
                    self.report_unsettled_recursive_return(symbol, arg_types, &ret, mutual, span);
                }
                ret
            }
        };
        // A closure this instance returns is compiled with the instance:
        // fix its parameter types from its body before the return settles.
        if arg_types
            .iter()
            .all(|arg| brass_hir::is_fully_known(&self.resolve(arg)))
        {
            self.settle_escaping_closures(&ret);
        }
        self.leave_instance();
        self.elaboration_stack.pop();
        self.current_module = saved_module;
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
                self.assert_co_validation(symbol, replay, walk, &replayed, &ret);
            }
        }
        self.numeric.result = numeric_result;
        if let Some(memo_key) = memo_key {
            let resolved = self.resolve(&ret);
            // A nested call typed from a depth-capped fallback leaves the
            // return an approximation: it is neither replayed nor reported.
            let memoizable =
                self.errors.len() == errors_before && self.depth_capped == capped_before;
            if memoizable && unannotated && !self.co_checking {
                self.record_instance_return(
                    brass_hir::numeric_instance_base(symbol, numeric_layout.clone().as_ref()),
                    arg_types.iter().map(|arg| self.resolve(arg)).collect(),
                    resolved.clone(),
                );
            }
            let frame = self.finish_elaboration_journal();
            let nested_replay = frame.memo_replayed;
            let rejected = if !memoizable {
                Some(if self.depth_capped != capped_before {
                    "depth_cap"
                } else {
                    "error_walk"
                })
            } else if self.co_checking && self.warnings.len() != warnings_before {
                Some("warning_walk")
            } else if frame.has_closure_bodies {
                Some("closure_body")
            } else if self.speculation_depth != 0 && !numeric_replay {
                Some("speculative")
            } else {
                None
            };
            if rejected.is_none()
                && (!numeric_replay || self.save_numeric_origin(&memo_key))
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
            } else if self.co_checking
                && let Some(reason) = rejected
            {
                tracing::trace!(target: "brass::perf", callable = memo_key.key.callable,
                    reason, "check: co memo storage");
            }
        }
        self.finish_method_inventory(method_observation, &ret);
        ret
    }

    /// Elaborate the free function `name`, referenced as a VALUE at `span`,
    /// when the lazy profile is on and its body can reach a keyed
    /// (`-> infer!`) call (see `Checker::keyed_tainted`). The value runs
    /// wherever it is applied, out of this pass's sight, so its keyed calls are
    /// discovered here -- at its declared parameter types -- before execution
    /// starts, rather than when a running program first calls it.
    pub(super) fn elaborate_keyed_function_value(&mut self, name: &str, span: brass_parser::Span) {
        if !self.lazy_profile {
            return;
        }
        let Some(info) = self.lookup_function(name) else {
            return;
        };
        if !self.keyed_tainted.contains(&info.symbol) {
            return;
        }
        let symbol = info.symbol.clone();
        let module = info.module.clone();
        let params = info.signature.params.clone();
        let decl = info.decl.clone();
        let declared_ret = info.signature.ret_ty.clone();
        let args: Vec<Type> = params
            .iter()
            .map(|p| {
                p.resolved_ty
                    .clone()
                    .unwrap_or_else(|| self.fresh_unknown())
            })
            .collect();
        let fallback = declared_ret
            .clone()
            .or_else(|| self.function_returns.get(&symbol).cloned())
            .unwrap_or_else(|| self.fresh_unknown());
        self.instantiate_function_call(
            &symbol,
            &module,
            &params,
            &decl.body,
            declared_ret,
            fallback,
            &args,
            span,
        );
    }

    /// Choose an inferred-return body's return type: the full check's
    /// reconciliation when it produced one and the body raises no propagation
    /// (the full check observes the stores/pushes the light pass misses),
    /// otherwise the light assembly's SHAPE -- a fallible body's `Result` from
    /// its error sites, wrapped in `?` when a nullable `expr!` can return null,
    /// which the normal-return reconciliation does not build -- over the full
    /// check's Ok payload.
    ///
    /// `site` names the instantiation when its inputs are fully known: its
    /// returns and error payloads must then join, and a conflict -- one the
    /// open definitional pass could not see -- is reported against it.
    fn prefer_full_return(
        &mut self,
        full_ret: Option<Type>,
        body: &Block,
        frame: ScopeStack,
        site: Option<super::returns::InstanceSite>,
    ) -> Type {
        let errors_before = self.errors.len();
        let reported_key = site.as_ref().map(|site| site.key.clone());
        let saved_site = std::mem::replace(&mut self.conflict_site, site);
        let report = self.conflict_site.is_some();
        let ret = self.prefer_full_return_at(full_ret, body, frame, report);
        self.conflict_site = saved_site;
        if let Some(key) = reported_key
            && self.errors.len() > errors_before
        {
            self.reported_instances.insert(key);
        }
        ret
    }

    fn prefer_full_return_at(
        &mut self,
        full_ret: Option<Type>,
        body: &Block,
        frame: ScopeStack,
        report: bool,
    ) -> Type {
        let mut env = frame;
        let mut normal = Vec::new();
        let mut props = LightProps::default();
        // The walk follows the arms the full check of this elaboration just
        // selected (see `Checker::light_folds`).
        let decisions = std::mem::take(&mut self.last_static_folds);
        let saved = std::mem::replace(&mut self.light_folds, decisions);
        self.infer_returns_block(body, &mut env, &mut normal, &mut props);
        self.light_folds = saved;
        let normal = self.split_forwarded_returns(normal, &mut props);
        let has_props = !props.errors.is_empty() || !props.nulls.is_empty();
        let collected = std::mem::take(&mut self.last_returns);
        if report {
            self.report_instance_return_conflict(&collected, has_props);
        }
        // Every value this instance's live paths return is an error and the
        // body cannot fall through (which would succeed with `void`): it has
        // no Ok value at all, whatever the light walk (which does not see a
        // `return` nested in an initializer, nor this instance's pruning)
        // assembled. Its Ok payload is the uninhabited marker, so reading it
        // is rejected.
        let error_only = !collected.is_empty()
            && block_always_returns(body)
            && collected.iter().all(|(ty, _)| {
                self.resolve(ty)
                    .result_payloads()
                    .is_some_and(|(ok, _)| ok.is_unknown())
            });
        if let Some(t) = full_ret
            && !has_props
        {
            return if error_only {
                self.with_error_only_ok(t)
            } else {
                t
            };
        }
        // A propagating body's `Result`/`?` WRAPPING is the light assembly's -- the
        // full check's reconciliation does not rebuild it -- but its Ok PAYLOAD is
        // the full check's. The light pass cannot re-elaborate a method's body, so a
        // container the body fills (`HashMap.new()` then `set`) keeps OPEN element
        // types there while the full check pins them; and where the two disagree
        // outright the light pass approximated, so the full check's payload is the
        // one the call site gets.
        //
        // Call-site re-inference does not report the normal returns' conflicts
        // here (the full check's collected returns were judged above); the
        // light pass's error payloads are the only record of the error sites,
        // so an instantiation reports their conflict here.
        let light_normal = self.reconcile_return_types(&normal, false);
        let full_normal = self.full_normal_return(collected);
        let normal_ty = self.settle_light_payload(light_normal, full_normal);
        let base = self.result_from_payloads(normal_ty, &props.errors, report);
        let light = super::precompute::wrap_null_propagated_return(base, &props.nulls);
        if error_only {
            return self.with_error_only_ok(light);
        }
        light
    }

    /// The full check's reconciliation of a propagating body's VALUE returns,
    /// from the `return` types `check_block_root` collected. An `error(..)`
    /// return carries no Ok value (its payload is a variable no path produces);
    /// reconciled in, it would win and leave the payload open, so it is skipped.
    /// Where forwarded `Result`s mix with bare values, each forward takes part
    /// by its Ok payload, as in `split_forwarded_returns`.
    pub(super) fn full_normal_return(&mut self, collected: Vec<(Type, Span)>) -> Option<Type> {
        let values: Vec<(Type, Span)> = collected
            .into_iter()
            .map(|(ty, span)| (self.resolve(&ty), span))
            .filter(|(ty, _)| !ty.result_payloads().is_some_and(|(ok, _)| ok.is_unknown()))
            .collect();
        let forwards = values
            .iter()
            .filter(|(ty, _)| ty.result_payloads().is_some())
            .count();
        let values: Vec<(Type, Span)> = if forwards == 0 || forwards == values.len() {
            values
        } else {
            values
                .into_iter()
                .map(|(ty, span)| match ty.result_payloads() {
                    Some((ok, _)) => (ok.clone(), span),
                    None => (ty, span),
                })
                .collect()
        };
        self.reconcile_return_types(&values, false)
    }

    /// Settle a light-pass normal return against the full check's, which is
    /// the authority: their Ok payloads are unified when they agree (so an open
    /// light variable takes the full check's pin), and the full check's payload
    /// replaces the light one when they do not -- inside the forwarded
    /// `Result` the light pass saw, if it saw one.
    fn settle_light_payload(&mut self, light: Option<Type>, full: Option<Type>) -> Option<Type> {
        let (Some(light), Some(full)) = (light.clone(), full.clone()) else {
            return light.or(full);
        };
        let got = Self::ok_payload(&self.resolve(&full));
        if got.is_unknown() {
            return Some(light);
        }
        let light = self.resolve(&light);
        let want = Self::ok_payload(&light);
        let snapshot = self.solver.snapshot();
        if self.solver.unify(&want, &got).is_ok() {
            return Some(light);
        }
        self.solver.rollback(snapshot);
        Some(
            match (
                light.result_payloads(),
                self.resolve(&full).result_payloads(),
            ) {
                (Some((_, err)), None) => light.rebuild_result(got, err.clone()),
                _ => full,
            },
        )
    }

    /// The return a recursive call inside an elaboration of `params` at
    /// `arg_types` is typed against before the body's own return is known: the
    /// precomputed (declaration-level) entry with each signature variable
    /// replaced by the argument it is instantiated with here, and every other
    /// variable fresh. The entry describes the callable for ALL its call sites;
    /// linking it to one instance's real return (see `link_inferred_return`)
    /// would pin a generic function to its first instantiation, and every other
    /// instance's recursive calls would then read that instance's type.
    fn instance_provisional_return(
        &mut self,
        entry: &Type,
        params: &[ParamInfo],
        arg_types: &[Type],
    ) -> Type {
        let entry = self.resolve(entry);
        let mut map: HashMap<u32, Type> = HashMap::default();
        for (param, arg) in params.iter().zip(arg_types) {
            let Some(declared) = param.resolved_ty.as_ref() else {
                continue;
            };
            let declared = self.resolve(declared);
            let vars: Vec<u32> = brass_hir::type_vars(&declared).into_iter().collect();
            match_scheme_param(&declared, &self.resolve(arg), &vars, &mut map);
        }
        let mut substitution: std::collections::BTreeMap<u32, Type> = map.into_iter().collect();
        for var in brass_hir::type_vars(&entry) {
            if var != brass_hir::INFER_VAR && !substitution.contains_key(&var) {
                let fresh = self.fresh_unknown();
                substitution.insert(var, fresh);
            }
        }
        brass_hir::substitute_vars(&entry, &substitution)
    }

    /// `ret` (a `Result`, possibly nullable) with its Ok payload replaced by
    /// a fresh uninhabited-payload variable; any other type is unchanged.
    fn with_error_only_ok(&mut self, ret: Type) -> Type {
        let ok = self.fresh_uninhabited_ok();
        self.with_ok_payload(ret, ok)
    }

    /// `ret` (a `Result`, possibly nullable) with its Ok payload replaced by
    /// `ok`; any other type is unchanged.
    fn with_ok_payload(&self, ret: Type, ok: Type) -> Type {
        match self.resolve(&ret) {
            Type::Nullable(inner) => Type::nullable(self.with_ok_payload(*inner, ok)),
            resolved @ Type::Sum(_) => match resolved.result_payloads() {
                Some((_, err)) => {
                    let err = err.clone();
                    resolved.rebuild_result(ok, err)
                }
                None => resolved,
            },
            _ => ret,
        }
    }

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
        let Some((scheme_method, map)) = self.scheme_method_instance(recv_ty, method) else {
            return Vec::new();
        };
        scheme_method
            .params
            .iter()
            .filter(|(name, _)| name != "self")
            .map(|(_, ty)| {
                let inst = self.resolve(&apply_scheme_param_map(ty, &map));
                self.solver.free_vars(&inst).is_empty().then_some(inst)
            })
            .collect()
    }

    /// For each non-`self` parameter of `method` on a scheme'd record
    /// receiver (aligned like [`Self::scheme_method_param_types`]), whether
    /// the receiver instance PINS its type: the scheme states the parameter
    /// over a type parameter of the record that this instance binds (a map's
    /// `set` value is the map's own value type). The method stores such an
    /// argument into the receiver's slots, so the argument is checked as
    /// storage, not as an ordinary parameter instantiated at its own type.
    pub(super) fn scheme_method_param_pinned(&self, recv_ty: &Type, method: &str) -> Vec<bool> {
        let Some((scheme_method, map)) = self.scheme_method_instance(recv_ty, method) else {
            return Vec::new();
        };
        scheme_method
            .params
            .iter()
            .filter(|(name, _)| name != "self")
            .map(|(_, ty)| {
                brass_hir::type_vars(ty)
                    .iter()
                    .any(|var| map.contains_key(var))
            })
            .collect()
    }

    /// The scheme of `method` on the scheme'd record receiver `recv_ty`, with
    /// the map from the scheme's type parameters to this receiver instance's
    /// types.
    fn scheme_method_instance(
        &self,
        recv_ty: &Type,
        method: &str,
    ) -> Option<(&SchemeMethod, HashMap<u32, Type>)> {
        let nominal = self.scheme_receiver_record(recv_ty)?;
        let info = self.program.type_by_id(nominal.id)?;
        let scheme = self.schemes.get(&info.symbol)?;
        let scheme_method = scheme.methods.get(method)?;
        let map = scheme_instance_map(scheme, &nominal, |ty| self.resolve(ty));
        Some((scheme_method, map))
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
    pub(super) fn scheme_method_return(&self, recv_ty: &Type, method: &str) -> Option<Type> {
        let nominal = self.scheme_receiver_record(recv_ty)?;
        let info = self.program.type_by_id(nominal.id)?;
        let scheme = self.schemes.get(&info.symbol)?;
        let scheme_method = scheme.methods.get(method)?;
        let map = scheme_instance_map(scheme, &nominal, |ty| self.resolve(ty));
        // Instantiating a `?`-wrapped scheme return with a nullable value type
        // nests the nullable; collapse it (there is one `null`).
        let ret = brass_hir::collapse_nullable(&apply_scheme_param_map(&scheme_method.ret, &map));
        let ret = self.resolve(&ret);
        // Only adopt the instantiated return when it is fully resolved; an open
        // variable means the instance did not constrain it, so the re-elaborated
        // return (which can still defer) is the safer choice.
        self.solver.free_vars(&ret).is_empty().then_some(ret)
    }

    /// Peel receiver modes while resolving only the constructor exposed at
    /// each layer; scheme matching reads the record instance that remains.
    fn scheme_receiver_record(&self, recv_ty: &Type) -> Option<NominalType> {
        let mut ty = self.resolve_head(recv_ty);
        loop {
            match ty {
                Type::Ref(inner)
                | Type::Mut(inner)
                | Type::ConstOf(inner)
                | Type::Nullable(inner) => ty = self.resolve_head(&inner),
                Type::Record(nominal) => return Some(nominal),
                _ => return None,
            }
        }
    }

    /// The scope stack a callee body is checked in for one call: the globals
    /// visible from the callee's module, and a frame binding each parameter
    /// to the type it takes for these arguments (see the branches below).
    pub(super) fn signature_call_frame(
        &mut self,
        params: &[ParamInfo],
        arg_types: &[Type],
        scheme_params: &[Option<Type>],
        receiver_ty: Option<Type>,
    ) -> ScopeStack {
        // Re-checking a callee body sees the globals visible from ITS module
        // (`current_module` is the callee's here); signature parameters layer on
        // top so they shadow same-named globals.
        let mut frame = HashMap::default();
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
                    .map(|arg| self.instantiate_param_type(&annotated, arg))
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
            if param.name != "_" {
                frame.insert(param.name.clone(), ty);
            }
        }
        let mut frame = Scope::new(frame);
        if self.numeric.probing {
            let origins = self
                .numeric
                .arguments
                .get(&self.numeric.calls)
                .cloned()
                .unwrap_or_default();
            let offset = arg_types.len().saturating_sub(origins.len());
            let mut index = 0;
            for param in params {
                if param.name == "self" && receiver_ty.is_some() {
                    continue;
                }
                if param.ty.is_none()
                    && scheme_params.get(index).is_none_or(Option::is_none)
                    && let Some(Some(binding_joins::numeric::Source::Root(id))) =
                        index.checked_sub(offset).and_then(|i| origins.get(i))
                {
                    frame.numeric.insert(param.name.clone(), *id);
                }
                index += 1;
            }
        }
        vec![Scope::shared(self.global_scope()), frame]
    }

    /// The type a callee body is checked at for a parameter annotated
    /// `annotated` that receives an argument of type `actual`: the annotation
    /// instantiated against the argument ([`Self::instantiate_annotated_type`]),
    /// except where the annotation names a record and the argument carries a
    /// value of another declaration there -- a structurally wider record, an
    /// anonymous record, a primitive satisfying a protocol record. The back
    /// ends instantiate the callee at the argument's own type in that case,
    /// so the body is checked at it too: a store of the parameter into a slot
    /// of the annotated type is then seen as the representation change it is.
    /// An argument that is not usable as the annotation at all is already
    /// rejected at the call; the body is then checked at the annotation.
    /// Wrappers, nullables and arrays are followed to reach such positions; a
    /// declared sum subtype is rebuilt as the parent at the call, so a sum
    /// position keeps the annotation.
    pub(super) fn instantiate_param_type(&self, annotated: &Type, actual: &Type) -> Type {
        let actual_value = peel_value_wrappers(&self.resolve(actual)).clone();
        match (self.resolve(annotated), &actual_value) {
            (Type::ConstOf(want), _) => {
                Type::ConstOf(Box::new(self.instantiate_param_type(&want, &actual_value)))
            }
            (Type::Mut(want), _) => {
                Type::Mut(Box::new(self.instantiate_param_type(&want, &actual_value)))
            }
            (Type::Ref(want), _) => {
                Type::Ref(Box::new(self.instantiate_param_type(&want, &actual_value)))
            }
            (Type::Nullable(want), Type::Nullable(have)) => {
                Type::Nullable(Box::new(self.instantiate_param_type(&want, have)))
            }
            (Type::Nullable(want), have) if !matches!(have, Type::Never) => {
                Type::Nullable(Box::new(self.instantiate_param_type(&want, have)))
            }
            (Type::Slice(want), Type::Slice(have) | Type::Array(have, _)) => {
                Type::Slice(Box::new(self.instantiate_param_type(&want, have)))
            }
            (Type::Array(want, n), Type::Array(have, _) | Type::Slice(have)) => {
                Type::Array(Box::new(self.instantiate_param_type(&want, have)), n)
            }
            (Type::Record(want), have)
                if !matches!(have, Type::Unknown(_) | Type::Never)
                    && !matches!(have, Type::Record(h) if h.id == want.id && h.name == want.name)
                    && crate::structural::types_compatible(
                        self.program,
                        have,
                        &Type::Record(want.clone()),
                    ) =>
            {
                have.clone()
            }
            (annotated, _) => self.instantiate_annotated_type(&annotated, &actual_value),
        }
    }

    /// Whether a callee with a parameter annotated `annotated` is checked at
    /// another type than the annotation's instantiation when it receives
    /// `actual` (see [`Self::instantiate_param_type`]): its body then depends
    /// on the argument, not on the signature alone.
    pub(super) fn param_instance_follows_argument(&self, annotated: &Type, actual: &Type) -> bool {
        self.instantiate_param_type(annotated, actual)
            != self.instantiate_annotated_type(annotated, actual)
    }

    /// The annotation `annotated` with its open positions (`infer` holes,
    /// a generic record's or sum's inferred fields and method signatures)
    /// filled from the matching positions of `actual`; concrete positions
    /// keep the annotation.
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
                                    self.read_method_return(&(
                                        self.program.type_by_id(have.id)?.symbol.clone(),
                                        method_name.clone(),
                                    ))
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
/// (`_entries: _Entry<K, V>?[]` vs `_entries: _Entry<string, int32>?[]` gives
/// `K -> string`, `V -> int32`). Used to instantiate a method's scheme at a call.
pub(super) fn scheme_instance_map(
    scheme: &TypeScheme,
    recv: &NominalType,
    resolve: impl Fn(&Type) -> Type,
) -> HashMap<u32, Type> {
    let mut map = HashMap::default();
    for (fname, fty) in &scheme.fields {
        if let Some(actual) = recv.substitution.get(fname) {
            match_scheme_param(fty, &resolve(actual), &scheme.params, &mut map);
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
