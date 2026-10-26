//! The inference run: the order bodies are checked in (eager, or
//! execution-first under streaming), the preliminary scheme pass, and the
//! per-body drivers for methods, functions and module initializers.

use super::context::ContextProgramIdentity;
use super::*;

/// The infer pass's errors on `program`. The declaration-level passes'
/// diagnostics are [`crate::check`]'s.
pub fn check(program: &Program) -> Vec<TypeError> {
    analyze(program).errors
}

/// Whether the scheme pre-pass can skip co-checking `info`'s method bodies:
/// the pre-pass exists only to build [`TypeScheme`]s, so any body whose check
/// cannot influence a scheme is wasted work there. Sums never contribute (a
/// scheme is record-only). A record whose fields and bodied method signatures
/// (parameters and annotated returns) all resolve to fully-known types
/// generalizes to a parameterless scheme the declarations already spell out
/// -- the co-check would only link inference variables that do not exist.
/// An unannotated return keeps the co-check: its full-pass reconciliation can
/// differ in shape from the precomputed light-pass type the scheme would
/// otherwise fall back to.
fn scheme_pass_skips(info: &TypeInfo) -> bool {
    match &info.kind {
        TypeKind::Sum { .. } => true,
        TypeKind::Record { fields, methods } => {
            fields.iter().all(|f| {
                f.resolved_ty
                    .as_ref()
                    .is_some_and(brass_hir::is_fully_known)
            }) && methods.values().all(|m| {
                m.decl.body.is_none()
                    || (m.signature.params.iter().all(|p| {
                        p.name == "self"
                            || p.resolved_ty
                                .as_ref()
                                .is_some_and(brass_hir::is_fully_known)
                    }) && m
                        .signature
                        .ret_ty
                        .as_ref()
                        .is_some_and(brass_hir::is_fully_known))
            })
        }
    }
}

/// Check every type's method bodies in the shared per-type environment. Binding
/// `self` to the bare type makes a type's methods share one field variable, so
/// the bodies' stores and reads link each field's element to the methods'
/// parameter and return variables -- the linkage [`Checker::build_schemes`] then
/// generalizes.
fn check_method_bodies(checker: &mut Checker, program: &Program, schemes_only: bool) {
    let mut perf = brass_utils::PerfLog::start("typeck/method-body");
    checker.co_checking = true;
    for t in program.types.values() {
        // A seeded run reads the context's schemes and co-checked returns from
        // the seed; only the entry's own types are co-checked here.
        if checker.seeded_module(&t.module) {
            continue;
        }
        if schemes_only && scheme_pass_skips(t) {
            continue;
        }
        checker.current_module = t.module.clone();
        match &t.kind {
            TypeKind::Record { methods, .. } => {
                for m in methods.values() {
                    // A reflective `-> infer!` template has no fixed body type;
                    // it is specialized per key by the driver, so skip it here.
                    if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                        continue;
                    }
                    if let Some(body) = &m.decl.body {
                        let m_started = std::time::Instant::now();
                        let mut scopes = checker.signature_scopes(&m.signature.params);
                        let ret = m.signature.ret_ty.clone();
                        checker.current_co_method =
                            Some((t.symbol.clone(), m.signature.name.clone()));
                        let full = checker.check_block_with_self(
                            body,
                            &mut scopes,
                            ret.as_ref(),
                            &t.symbol,
                        );
                        checker.current_co_method = None;
                        perf.item(
                            format!("{}.{}", t.symbol, m.signature.name),
                            m_started.elapsed(),
                        );
                        let key = (t.symbol.clone(), m.signature.name.clone());
                        checker.settle_method_return(&key, body, ret.is_none());
                        if let Some(inferred) = checker.method_returns.get(&key).cloned() {
                            checker.warn_implicit_nullable_result(&m.signature, body, &inferred);
                        }
                        // Keep the return the full check reconciled here, in the
                        // shared per-type environment, for scheme generalization
                        // (see `co_method_returns`). A propagating body's shape
                        // (`Result`/`?`) only the light assembly builds, so it
                        // keeps its precomputed type.
                        if let Some(full) = full
                            && !checker.method_return_props.contains(&key)
                        {
                            checker.co_method_returns.insert(key, full);
                        }
                    }
                }
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    for m in v.methods.values() {
                        if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                            continue;
                        }
                        if let Some(body) = &m.decl.body {
                            let mut scopes = checker.signature_scopes(&m.signature.params);
                            let ret = m.signature.ret_ty.clone();
                            checker.check_block_with_self_variant(
                                body,
                                &mut scopes,
                                ret.as_ref(),
                                &t.symbol,
                                &v.name,
                            );
                            let key =
                                (format!("{}.{}", t.symbol, v.name), m.signature.name.clone());
                            checker.settle_method_return(&key, body, ret.is_none());
                            if let Some(inferred) = checker.method_returns.get(&key).cloned() {
                                checker.warn_implicit_nullable_result(
                                    &m.signature,
                                    body,
                                    &inferred,
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    checker.co_checking = false;
    perf.report();
}

/// Generalize every record into a [`TypeScheme`] on a throwaway checker, so the
/// real pass has the schemes in hand *while* it checks method bodies.
///
/// A scheme can only be built after the method bodies have been checked (that is
/// what links a field's element type to its methods' parameter variables), so the
/// real pass cannot build them any earlier than it already does. But a method
/// body that calls ANOTHER type's method needs that type's scheme to pin the
/// call's parameters from the receiver -- `map.set(k, 100)` on a width-pinned
/// `HashMap` types the bare literal as the map's `int64`, not the literal's
/// default `int32`. Without schemes during the co-check, the same call inside
/// a method body would type the literal from the argument and clash with the
/// receiver's slot.
///
/// The preliminary run's diagnostics and solver are discarded; only the schemes
/// are kept, and the real pass rebuilds them once its own method bodies are done.
/// It therefore does only the work a scheme needs: declaration validation is
/// pure diagnostics, while method-return precomputation converges internally.
fn seed_schemes(
    program: &Program,
    seed: Option<(ContextTables, u32)>,
    rows: Rc<brass_typesys::RowInfo>,
    numeric_enabled: bool,
    stats: &mut stats::ElaborationStats,
) -> (HashMap<String, TypeScheme>, Option<(ContextTables, u32)>) {
    let mut pre = Checker::new_with_numeric(program, rows, numeric_enabled);
    let applied = seed.map(|(tables, next)| (pre.apply_seed(tables, next), next));
    pre.precompute_global_bindings();
    pre.precompute_returns();
    pre.settle_numeric_globals();
    check_method_bodies(&mut pre, program, true);
    let schemes = pre.build_schemes();
    let seed = applied.map(|(metadata, next)| (pre.take_applied_seed(metadata), next));
    stats.record_checker(&pre);
    (schemes, seed)
}

/// The infer pass over the whole of `program`, unseeded and eager.
pub fn analyze(program: &Program) -> Inference {
    analyze_with(program, None)
}

/// [`analyze`], optionally seeded with the tables of a prior CONTEXT-ONLY run
/// (see [`ContextTables`]): the seeded modules' per-item passes are skipped and
/// their schemes, inferred returns, and globals are read from the seed, so the
/// run costs roughly what checking the entry module alone costs.
pub fn analyze_with(program: &Program, seed: Option<&ContextTables>) -> Inference {
    let modules = crate::AnalysisModules::new(seed);
    let (_, const_calls) = crate::constck::check_in(program, modules);
    analyze_inner(program, seed, None, Rc::new(const_calls)).0
}

/// Check only append-only methods synthesized from keyed templates, reusing
/// the completed first pass's cross-module tables. Generated methods may call
/// one another, so all declarations must already be present in `program`.
pub fn analyze_generated(
    program: &Program,
    seed: &ContextTables,
    generated: &[brass_hir::GeneratedDecl],
) -> Inference {
    let mut stats = stats::ElaborationStats::default();
    let ordinary = analyze_generated_attempt(program, seed, generated, false, &mut stats);
    let result = if ordinary.errors.is_empty() {
        ordinary
    } else {
        analyze_generated_attempt(program, seed, generated, true, &mut stats)
    };
    stats.emit_summary();
    result
}

fn analyze_generated_attempt(
    program: &Program,
    seed: &ContextTables,
    generated: &[brass_hir::GeneratedDecl],
    numeric_enabled: bool,
    stats: &mut stats::ElaborationStats,
) -> Inference {
    let rows = Rc::new(brass_typesys::RowInfo::analyze(program));
    let mut checker = Checker::new_with_numeric(program, rows, numeric_enabled);
    let (tables, next) = seed.remapped(next_unknown_after_program(program));
    checker.apply_seed(tables, next);
    checker.co_checking = true;

    for generated in generated {
        let Some(info) = program
            .types
            .values()
            .find(|info| info.name == generated.receiver && info.module == generated.module)
        else {
            continue;
        };
        checker.current_module = info.module.clone();
        match &info.kind {
            TypeKind::Record { methods, .. } => {
                let Some(method) = methods.get(&generated.decl.name) else {
                    continue;
                };
                let Some(body) = method.decl.body.as_ref() else {
                    continue;
                };
                let mut scopes = checker.signature_scopes(&method.signature.params);
                checker.current_co_method =
                    Some((info.symbol.clone(), method.signature.name.clone()));
                checker.check_block_with_self(
                    body,
                    &mut scopes,
                    method.signature.ret_ty.as_ref(),
                    &info.symbol,
                );
                checker.current_co_method = None;
                let key = (info.symbol.clone(), method.signature.name.clone());
                if let Some(inferred) = checker.method_returns.get(&key).cloned() {
                    checker.warn_implicit_nullable_result(&method.signature, body, &inferred);
                }
                checker.errors.extend(crate::exhaustive::check_block(
                    program,
                    &checker.typed,
                    &info.module,
                    body,
                ));
            }
            TypeKind::Sum { variants } => {
                for variant in variants {
                    let Some(method) = variant.methods.get(&generated.decl.name) else {
                        continue;
                    };
                    let Some(body) = method.decl.body.as_ref() else {
                        continue;
                    };
                    let mut scopes = checker.signature_scopes(&method.signature.params);
                    checker.check_block_with_self_variant(
                        body,
                        &mut scopes,
                        method.signature.ret_ty.as_ref(),
                        &info.symbol,
                        &variant.name,
                    );
                    let key = (
                        format!("{}.{}", info.symbol, variant.name),
                        method.signature.name.clone(),
                    );
                    if let Some(inferred) = checker.method_returns.get(&key).cloned() {
                        checker.warn_implicit_nullable_result(&method.signature, body, &inferred);
                    }
                    checker.errors.extend(crate::exhaustive::check_block(
                        program,
                        &checker.typed,
                        &info.module,
                        body,
                    ));
                }
            }
        }
    }
    checker.co_checking = false;
    checker.report_uninferable_error_types();
    // Function values nothing fixed take their whole signature before the
    // recorded types are resolved for the last time.
    checker.settle_function_values();
    checker.finalize_typed();

    let function_returns = checker
        .function_returns
        .iter()
        .map(|(key, ty)| (key.clone(), checker.resolve(ty)))
        .collect();
    let method_returns = checker
        .method_returns
        .iter()
        .map(|(key, ty)| (key.clone(), checker.resolve(ty)))
        .collect();
    let sum_views = checker
        .sum_views
        .iter()
        .map(|(span, ty)| (*span, checker.resolve(ty)))
        .collect();
    checker.settle_closure_instantiations();
    checker.report_undetermined_closures();
    let closure_bindings = checker.finalized_closure_bindings();
    let instance_typed = checker.finalized_instance_typed();
    let (keyed_calls, instance_keyed_calls) = checker.settled_keyed_calls();
    let numeric_calls = checker.numeric_call_map();
    let field_calls = checker.field_call_map();
    stats.record_checker(&checker);
    Inference {
        errors: checker.errors,
        warnings: checker.warnings,
        typed: checker.typed,
        instance_typed,
        schemes: checker.schemes,
        view_args: checker.view_args,
        lift_errs: checker.lift_errs,
        sum_views,
        fields_loops: checker.fields_loops,
        type_names: checker.type_names,
        keyed_calls,
        numeric_calls,
        instance_keyed_calls,
        field_calls,
        typeof_types: checker.typeof_types,
        type_tests: checker.type_tests,
        null_props: checker.null_props,
        function_returns,
        method_returns,
        closure_bindings,
        instance_returns: checker.instance_returns,
        context_tables: {
            let mut tables = seed.clone();
            tables.ordinary_numeric &= !numeric_enabled;
            tables
        },
    }
}

/// Publish body progress and seal a priority batch on its last member.
/// The driver applies the cumulative delta before observing the seal, so
/// intermediate body events cannot expose a partially applied batch.
fn emit_function_checked(
    checker: &Checker,
    ctl: &mut StreamCtl,
    priority: &std::collections::VecDeque<stream::BodyRequest>,
    batch: Option<u64>,
    symbol: String,
) {
    let batch_continues = batch.is_some_and(|batch| {
        priority
            .front()
            .is_some_and(|request| request.batch == batch)
    });
    let delta = if batch_continues {
        stream::ChannelDelta::default()
    } else {
        let mut delta = flush_delta(checker, &mut ctl.state, false);
        delta.settles_batch = batch;
        delta
    };
    ctl.sched.emit(stream::CheckEvent::BodyChecked(
        stream::BodyId::Function(symbol),
        delta,
    ));
}

/// [`analyze_with`] with optional streaming control (the lazy-check
/// pipeline): with a [`StreamCtl`], bodies are checked in an execution-first
/// order -- module initializers, then `main`, then the remaining functions,
/// reprioritized between bodies by the scheduler's requests -- and a channel
/// event is emitted after each body; a priority batch carries its cumulative
/// delta on the final event. Without one, the body order is the eager
/// pipeline's. The second return value is the terminal delta (flushed after
/// the finalize re-resolution), for the caller to emit once the remaining
/// whole-program passes are done. The cleanup owner retains streaming scratch
/// state until that terminal event has been published.
pub(crate) fn analyze_inner<'p>(
    program: &'p Program,
    seed: Option<&ContextTables>,
    mut ctl: Option<&mut StreamCtl>,
    const_calls: Rc<crate::constck::ConstCalls>,
) -> (
    Inference,
    Option<stream::ChannelDelta>,
    InferenceCleanup<'p>,
) {
    let mut stats = stats::ElaborationStats::default();
    let ordinary = analyze_attempt(
        program,
        seed,
        ctl.as_deref_mut(),
        Rc::clone(&const_calls),
        false,
        &mut stats,
    );
    // Streaming has a single attempt. Eager numeric retries belong to the
    // same analysis and contribute to its one summary.
    let result = if ctl.is_some() || ordinary.0.errors.is_empty() {
        ordinary
    } else {
        analyze_attempt(program, seed, None, const_calls, true, &mut stats)
    };
    stats.emit_summary();
    result
}

fn analyze_attempt<'p>(
    program: &'p Program,
    seed: Option<&ContextTables>,
    mut ctl: Option<&mut StreamCtl>,
    const_calls: Rc<crate::constck::ConstCalls>,
    numeric_enabled: bool,
    stats: &mut stats::ElaborationStats,
) -> (
    Inference,
    Option<stream::ChannelDelta>,
    InferenceCleanup<'p>,
) {
    let streaming = ctl.is_some();
    let phase = |name: &'static str, at: std::time::Instant| {
        brass_utils::perf_phase(name, at.elapsed());
    };
    // One remapping serves both checkers below, so the preliminary scheme pass
    // and the real pass agree on every seeded variable id.
    let remapped = seed.map(|s| s.remapped(next_unknown_after_program(program)));
    let rows = Rc::new(brass_typesys::RowInfo::analyze(program));
    let t = std::time::Instant::now();
    let (seeded, remapped) =
        seed_schemes(program, remapped, Rc::clone(&rows), numeric_enabled, stats);
    phase("typeck/seed-schemes", t);
    let mut checker = Checker::new_with_numeric(program, rows, numeric_enabled);
    checker.const_calls = const_calls;
    checker.lazy_profile = ctl.is_some();
    if checker.lazy_profile {
        checker.keyed_tainted = crate::taint::keyed_reachable(program);
    }
    if let Some((tables, next)) = remapped {
        checker.apply_seed(tables, next);
    }
    checker.schemes = seeded;
    checker.observe_scheme_install();
    let t = std::time::Instant::now();
    checker.validate_param_declarations();
    checker.precompute_global_bindings();
    checker.precompute_returns();
    checker.settle_numeric_globals();
    phase("typeck/precompute", t);
    // Check each type's method bodies, then generalize each record type into a
    // scheme. Generalizing before the function bodies are checked makes the
    // schemes available at call sites (a function instantiates a method's scheme
    // to type the call's result) and keeps the generic field variable read here
    // free of any concrete use. The bodies below are checked against the seeded
    // schemes; this rebuild replaces them with the ones this pass linked.
    let t = std::time::Instant::now();
    check_method_bodies(&mut checker, program, false);
    checker.schemes = checker.build_schemes();
    checker.observe_scheme_install();
    phase("typeck/method-bodies", t);
    if let Some(ctl) = ctl.as_deref_mut() {
        checker.report_uninferable_method_error_types();
        let delta = flush_delta(&checker, &mut ctl.state, false);
        if ctl.sched.completion_observations() {
            let mut checked_context: Vec<_> = program
                .functions
                .iter()
                .filter(|(_, f)| checker.seeded_module(&f.module))
                .map(|(symbol, _)| symbol.clone())
                .collect();
            checked_context.sort_unstable();
            ctl.sched
                .emit(stream::CheckEvent::ContextChecked(checked_context));
        }
        ctl.sched.emit(stream::CheckEvent::ContextReady(delta));
    }

    match ctl.as_deref_mut() {
        // The eager order: the module initializers, then every function body.
        // The initializers come first because their full check is what types
        // the globals the function bodies read (see `settle_global`).
        None => {
            let t = std::time::Instant::now();
            let inits_start = checker.typed.expressions.len();
            checker.const_scopes = vec![HashSet::default()];
            for init in &program.inits {
                check_init_body(&mut checker, init);
            }
            checker.const_scopes.clear();
            let inits_len = checker.typed.expressions.len() - inits_start;
            phase("typeck/inits", t);

            let mut perf = brass_utils::PerfLog::start("typeck/fn-bodies");
            for (symbol, f) in &program.functions {
                // Context bodies were checked by the run that produced the seed;
                // their call-site behavior is still exact, because a call from the
                // entry re-elaborates the callee body at the call's own types.
                if checker.seeded_module(&f.module) {
                    continue;
                }
                let fn_started = std::time::Instant::now();
                check_function_body(&mut checker, symbol, f);
                perf.item(symbol.clone(), fn_started.elapsed());
            }
            perf.report();
            checker.in_entry_main = false;
            checker.defer_typed_entries(inits_start, inits_len);
        }
        // The streaming (execution-first) order: initializers, then `main`,
        // then the remaining functions, with the scheduler's priority
        // requests jumping the queue between bodies. Body results are
        // order-tolerant by construction (the eager order is a HashMap's),
        // so the reorder changes when a body's entries become available,
        // not what they end up being.
        Some(ctl) => {
            // Method bodies were checked in the shared phase above; their
            // matches get the same early exhaustiveness verdict bodies get
            // below, so a broken method on the execution path reports
            // deterministically (the terminal whole-program pass may never
            // run under a stopped lazy run).
            for info in program.types.values() {
                let mut method_bodies: Vec<&Block> = Vec::new();
                match &info.kind {
                    TypeKind::Record { methods, .. } => {
                        method_bodies.extend(methods.values().filter_map(|m| m.decl.body.as_ref()));
                    }
                    TypeKind::Sum { variants } => {
                        for v in variants {
                            method_bodies
                                .extend(v.methods.values().filter_map(|m| m.decl.body.as_ref()));
                        }
                    }
                }
                for body in method_bodies {
                    let errs =
                        crate::exhaustive::check_block(program, &checker.typed, &info.module, body);
                    checker.errors.extend(errs);
                }
            }
            // Execution runs every module initializer before `main`, so the
            // inits are the entry code the lazy driver needs first, in
            // execution (module-load) order.
            let t = std::time::Instant::now();
            checker.const_scopes = vec![HashSet::default()];
            for (i, init) in program.inits.iter().enumerate() {
                check_init_body(&mut checker, init);
                let errs = crate::exhaustive::check_stmts(
                    program,
                    &checker.typed,
                    &init.path,
                    &init.stmts,
                );
                checker.errors.extend(errs);
                let delta = flush_delta(&checker, &mut ctl.state, false);
                ctl.sched.emit(stream::CheckEvent::BodyChecked(
                    stream::BodyId::Init(i),
                    delta,
                ));
            }
            checker.const_scopes.clear();
            phase("typeck/inits", t);

            // `main` first, the rest sorted so the static order is
            // deterministic.
            let mut queue: std::collections::VecDeque<String> = {
                let mut symbols: Vec<String> = program.functions.keys().cloned().collect();
                symbols.sort();
                if let Some(pos) = symbols.iter().position(|s| s == "main") {
                    let main = symbols.remove(pos);
                    symbols.insert(0, main);
                }
                symbols.into_iter().collect()
            };
            let mut done: HashSet<String> = HashSet::default();
            // Complete request sets remain in send order, even when a new
            // set arrives while another is in flight. Stale members stay in
            // the queue until their batch's seal has been published.
            let mut priority: std::collections::VecDeque<stream::BodyRequest> =
                std::collections::VecDeque::new();
            let mut perf = brass_utils::PerfLog::start("typeck/fn-bodies");
            loop {
                // The consumer no longer needs anything (its program ended):
                // complete received batches and their seals before stopping.
                // What was checked stays reported; the complete verdict is
                // the eager pipeline's job.
                if ctl.sched.stopped() && priority.is_empty() {
                    break;
                }
                // Priority passes also retire their background entries. A
                // completed queue must reach Finished even while paused.
                while queue.front().is_some_and(|symbol| done.contains(symbol)) {
                    queue.pop_front();
                }
                // While the consumer is settling its entry, hold the
                // background queue and park until its next request. Waking the
                // scheduler also releases this wait when execution begins.
                let parked = ctl.sched.paused()
                    && priority.is_empty()
                    && queue.front().is_some_and(|symbol| symbol != "main");
                let requests = if parked {
                    ctl.sched.wait_for_requests()
                } else {
                    ctl.sched.drain_requests()
                };
                priority.extend(requests);
                // A control wake with no demands cannot release background
                // work while the entry gate is still paused.
                if ctl.sched.paused()
                    && priority.is_empty()
                    && queue.front().is_some_and(|symbol| symbol != "main")
                {
                    continue;
                }
                let (symbol, batch, demanded_at) = if let Some(request) = priority.pop_front() {
                    (request.symbol, Some(request.batch), Some(request.type_args))
                } else if let Some(symbol) = queue.pop_front() {
                    (symbol, None, None)
                } else {
                    break;
                };
                if let Some(args) = &demanded_at {
                    checker.completion.assert_demand(program, &symbol, args);
                }
                if done.contains(&symbol) || !program.functions.contains_key(&symbol) {
                    if let Some(batch) = batch
                        && priority
                            .front()
                            .is_none_or(|request| request.batch != batch)
                    {
                        // Every received set gets exactly one seal, even if
                        // background work checked all its members in transit.
                        let mut delta = flush_delta(&checker, &mut ctl.state, false);
                        delta.settles_batch = Some(batch);
                        ctl.sched.emit(stream::CheckEvent::BatchSettled(delta));
                    }
                    continue;
                }
                let f = &program.functions[&symbol];
                // A demanded body checks at the instance the demand named
                // when its types align with the signature; anything else
                // (stale request, mismatched arity, an open type) falls back
                // to the definitional pass. So does a STRUCTURAL argument:
                // an anonymous record that does not fit the body degrades to
                // the call's fallback by design -- the row check at the
                // value's span is its error source -- and a dedicated pass
                // at such an instance would hard-error where the call site
                // deliberately does not.
                let instance_args = demanded_at.filter(|args| {
                    args.len() == f.signature.params.len()
                        && args.iter().all(brass_hir::is_fully_known)
                        && !args.iter().any(contains_structural_record)
                });
                if instance_args.is_none() && checker.seeded_module(&f.module) {
                    done.insert(symbol.clone());
                    // A seeded (context) body skips the check, as in the eager
                    // order, but is settled all the same: its entries stream
                    // in through the re-elaboration a caller's own check
                    // performs. The event ("this body is settled") must still
                    // go out, or a consumer waiting on a context function
                    // would wait forever.
                    emit_function_checked(&checker, ctl, &priority, batch, symbol);
                    continue;
                }
                let completion_key = instance_args
                    .as_ref()
                    .and_then(|args| brass_hir::InstanceKey::function(program, &symbol, args));
                let observed_cap = completion_key
                    .as_ref()
                    .is_some_and(|key| checker.completion.was_capped(key));
                if batch.is_some()
                    && let Some(key) = &completion_key
                    && observed_cap
                    && !checker
                        .instance_returns
                        .contains_key(&(symbol.clone(), key.args.clone()))
                {
                    let eligibility = checker.completion_eligibility(key);
                    tracing::debug!(target: "brass::perf", symbol = %symbol, ?eligibility, "check: completion eligibility");
                    if eligibility == super::completion_order::Eligibility::Closed {
                        // New committed edges from a completion pass can expose
                        // another dependency before the demanded member runs.
                        let mut order = checker.completion.completion_order(key).into_iter();
                        let mut revision = checker.completion.edge_revision();
                        loop {
                            let next = order.find(|next| {
                                matches!(&next.callable, brass_hir::InstanceCallable::Function(name) if !done.contains(name))
                            });
                            let Some(next) = next else {
                                break;
                            };
                            let brass_hir::InstanceCallable::Function(name) = &next.callable else {
                                unreachable!()
                            };
                            done.insert(name.clone());
                            checker.completion.active = true;
                            check_stream_function(&mut checker, name, Some(&next.args), &mut perf);
                            checker.completion.active = false;
                            checker.completion.completed(next.clone());
                            // The demanded member still owns the batch's final
                            // cumulative delta and seal, including this pass.
                            ctl.sched.emit(stream::CheckEvent::BodyChecked(
                                stream::BodyId::Function(name.clone()),
                                stream::ChannelDelta::default(),
                            ));
                            // Ordinary memo hits add no edges. Keep the rest of
                            // this order until a committed pass discovers more.
                            let current = checker.completion.edge_revision();
                            if current != revision {
                                order = checker.completion.completion_order(key).into_iter();
                                revision = current;
                            }
                        }
                    }
                }
                done.insert(symbol.clone());
                checker.completion.active = batch.is_some();
                let caps_before = checker.depth_capped;
                check_stream_function(&mut checker, &symbol, instance_args.as_deref(), &mut perf);
                checker.completion.active = false;
                if !observed_cap
                    && checker.depth_capped != caps_before
                    && let Some(key) = completion_key
                {
                    let eligibility = checker.completion_eligibility(&key);
                    tracing::debug!(target: "brass::perf", symbol = %symbol, ?eligibility, "check: completion eligibility");
                }
                emit_function_checked(&checker, ctl, &priority, batch, symbol);
            }
            perf.report();
            checker.in_entry_main = false;
        }
    }
    let t = std::time::Instant::now();
    checker.report_uninferable_error_types();
    checker.report_unfixed_init_arrays();
    // Function values nothing fixed take their whole signature before the
    // recorded types are resolved for the last time.
    checker.settle_function_values();
    checker.finalize_typed();
    phase("typeck/finalize", t);
    // The terminal flush: finalize re-resolved the recorded types in place,
    // so this delta settles every entry the earlier flushes withheld or
    // emitted provisionally. Emitted by the caller (as `Finished`) once the
    // remaining whole-program passes contribute their errors.
    let final_delta = ctl.map(|ctl| flush_delta(&checker, &mut ctl.state, true));
    let function_returns: HashMap<String, Type> = checker
        .function_returns
        .clone()
        .into_iter()
        .map(|(name, ty)| {
            let ty = checker.resolve(&ty);
            (name, ty)
        })
        .collect();
    let method_returns: HashMap<(String, String), Type> = checker
        .method_returns
        .clone()
        .into_iter()
        .map(|(key, ty)| {
            let ty = checker.resolve(&ty);
            (key, ty)
        })
        .collect();
    // The cross-module tables, deep-resolved so a consumer without this run's
    // solver sees exactly what this run's `resolve` would have shown; whatever
    // stays open is genuinely generic.
    let context_tables = ContextTables {
        ordinary_numeric: !checker.numeric_enabled && checker.numeric_seed_ordinary,
        schemes: checker
            .schemes
            .iter()
            .map(|(name, scheme)| {
                let mut s = scheme.clone();
                s.fields = s
                    .fields
                    .iter()
                    .map(|(n, t)| (n.clone(), checker.resolve(t)))
                    .collect();
                for m in s.methods.values_mut() {
                    m.params = m
                        .params
                        .iter()
                        .map(|(n, t)| (n.clone(), checker.resolve(t)))
                        .collect();
                    m.ret = checker.resolve(&m.ret);
                }
                (name.clone(), s)
            })
            .collect(),
        function_returns: function_returns.clone(),
        method_returns: method_returns.clone(),
        method_return_props: checker.method_return_props.clone(),
        co_method_returns: checker
            .co_method_returns
            .iter()
            .map(|(k, t)| (k.clone(), checker.resolve(t)))
            .collect(),
        global_defs: checker
            .global_defs
            .iter()
            .map(|(m, defs)| {
                (
                    m.clone(),
                    defs.iter()
                        .map(|(n, t)| (n.clone(), checker.resolve(t)))
                        .collect(),
                )
            })
            .collect(),
        next_var: checker.next_unknown,
        bare_names: program
            .functions
            .values()
            .map(|f| f.signature.name.clone())
            .chain(program.types.values().map(|t| t.name.clone()))
            .collect(),
        covered: None,
        program_identity: ContextProgramIdentity::of(program),
    };
    // Re-resolve the coercion targets against the final substitution: a
    // variable pinned after the site was recorded (an err payload bound by a
    // later return) must reach MIR fully known so the rebuilt value's locals
    // can be seeded. A Result payload slot still open here was pinned by
    // NOTHING anywhere -- the value never carries data in it (an Err-only
    // flow's Ok side) -- so it defaults to void IN THE CHANNEL COPY only; no
    // solver binding can leak to other callers.
    let sum_views = checker
        .sum_views
        .iter()
        .map(|(s, t)| {
            let mut t = checker.resolve(t);
            if let Type::Sum(n) = &mut t
                && n.is_result_type()
            {
                for key in [
                    brass_hir::types::RESULT_OK_VALUE,
                    brass_hir::types::RESULT_ERR_ERROR,
                ] {
                    if n.substitution.get(key).is_none_or(|t| t.is_unknown()) {
                        n.substitution.insert(key, Type::Void);
                    }
                }
            }
            (*s, t)
        })
        .collect();
    checker.settle_closure_instantiations();
    checker.report_undetermined_closures();
    let closure_bindings = checker.finalized_closure_bindings();
    let instance_typed = checker.finalized_instance_typed();
    let (keyed_calls, instance_keyed_calls) = checker.settled_keyed_calls();
    let numeric_calls = checker.numeric_call_map();
    let field_calls = checker.field_call_map();
    stats.record_checker(&checker);
    let inference = Inference {
        errors: std::mem::take(&mut checker.errors),
        warnings: std::mem::take(&mut checker.warnings),
        typed: std::mem::take(&mut checker.typed),
        instance_typed,
        schemes: std::mem::take(&mut checker.schemes),
        view_args: std::mem::take(&mut checker.view_args),
        lift_errs: std::mem::take(&mut checker.lift_errs),
        sum_views,
        fields_loops: std::mem::take(&mut checker.fields_loops),
        type_names: std::mem::take(&mut checker.type_names),
        keyed_calls,
        numeric_calls,
        instance_keyed_calls,
        field_calls,
        typeof_types: std::mem::take(&mut checker.typeof_types),
        type_tests: std::mem::take(&mut checker.type_tests),
        null_props: std::mem::take(&mut checker.null_props),
        function_returns,
        method_returns,
        closure_bindings,
        instance_returns: std::mem::take(&mut checker.instance_returns),
        context_tables,
    };
    (
        inference,
        final_delta,
        InferenceCleanup::retain(checker, streaming),
    )
}

/// Run the ordinary dedicated pass and its post-body diagnostics and publication.
pub(super) fn check_stream_function(
    checker: &mut Checker,
    symbol: &str,
    args: Option<&[Type]>,
    perf: &mut brass_utils::PerfLog,
) {
    let f = &checker.program.functions[symbol];
    let started = std::time::Instant::now();
    let ret = match args {
        Some(args) => check_function_body_at(checker, symbol, f, args),
        None => {
            check_function_body(checker, symbol, f);
            None
        }
    };
    let errors =
        crate::exhaustive::check_block(checker.program, &checker.typed, &f.module, &f.decl.body);
    checker.errors.extend(errors);
    checker.report_uninferable_function_error_type(f);
    perf.item(symbol.to_owned(), started.elapsed());
    if let (Some(args), Some(ret)) = (args, ret) {
        checker.record_instance_return(symbol.to_owned(), args.to_vec(), ret);
    }
}

/// One free function's dedicated body pass -- the per-body core both body
/// orders share. The caller decides ordering and skips seeded modules.
fn check_function_body(checker: &mut Checker, symbol: &str, f: &FunInfo) {
    checker.stats.dedicated_passes += 1;
    tracing::debug!(function = %f.signature.name, "inferring function body");
    // The module comes first: the body's bottom scope is the globals visible
    // from IT, so building the scope before setting it would hand the function
    // some other module's globals.
    checker.current_module = f.module.clone();
    let mut scopes = checker.signature_scopes(&f.signature.params);
    let ret = f.signature.ret_ty.clone();
    // The root module's bare `main` symbol is the program entry; its `!`
    // propagations abort at runtime, waiving the fallible-return-context
    // requirement for its own body.
    checker.in_entry_main = symbol == "main";
    let empty_arrays_from = checker.empty_array_elems.len();
    let tagged = checker.numeric_enabled
        || (checker.lazy_profile && checker.numeric_body_needs_settlement(&f.decl.body, &scopes));
    if tagged {
        let inputs: Vec<_> = f
            .signature
            .params
            .iter()
            .map(|param| {
                scopes
                    .iter()
                    .rev()
                    .find_map(|scope| scope.get(&param.name))
                    .cloned()
                    .unwrap_or_else(|| checker.fresh_unknown())
            })
            .collect();
        checker.enter_instance(
            brass_hir::InstanceCallable::Function(symbol.to_owned()),
            &inputs,
        );
    }
    checker.check_block_root(&f.decl.body, &mut scopes, ret.as_ref());
    if tagged {
        checker.leave_instance();
    }
    let concrete = !checker.seeded_module(&f.module)
        && f.signature.params.iter().all(|p| {
            p.resolved_ty
                .as_ref()
                .is_some_and(brass_hir::is_fully_known)
        });
    checker.report_unfixed_empty_arrays(empty_arrays_from, concrete.then_some(f.decl.body.span));
    if let Some(inferred) = checker.function_returns.get(symbol).cloned() {
        if ret.is_none() {
            let collected = std::mem::take(&mut checker.last_returns);
            if let Some(settled) =
                checker.settle_definitional_return(&inferred, &f.decl.body, collected)
            {
                checker.function_returns.insert(symbol.to_string(), settled);
            }
        }
        checker.warn_implicit_nullable_result(&f.signature, &f.decl.body, &inferred);
    }
}

/// Whether a type mentions an anonymous structural record anywhere: such an
/// argument is served by the call-site row machinery (fit-or-degrade), so a
/// demanded instance carrying one keeps the definitional pass instead of
/// `check_function_body_at`.
pub(super) fn contains_structural_record(ty: &Type) -> bool {
    match ty {
        Type::Record(n) if n.id == brass_hir::STRUCTURAL_RECORD_ID => true,
        Type::Record(n) | Type::Sum(n) => n
            .substitution
            .iter()
            .any(|(_, t)| contains_structural_record(t)),
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Nullable(inner)
        | Type::ConstOf(inner)
        | Type::Mut(inner)
        | Type::Ref(inner) => contains_structural_record(inner),
        Type::Fun(params, ret) => {
            params.iter().any(contains_structural_record) || contains_structural_record(ret)
        }
        Type::Tuple(elems) => elems.iter().any(contains_structural_record),
        _ => false,
    }
}

/// Check a demanded body at its concrete instance. Returns the instance's
/// resolved return type when it can serve as a runtime-deferral contract:
/// the body is UNANNOTATED (an annotation is already a contract), the pass
/// reported no new errors, and the reconciled return resolved fully known.
/// The caller streams it to the consumer, whose monomorphizer may then
/// compile call sites to this instance as runtime-resolved calls without
/// lowering the body at all -- the fallibility guard (`!`/`error()` bodies
/// change the ABI away from this plain return) lives on the consumer side,
/// next to the annotated deferral's own guard (`call_contract` in
/// `brass_engine`'s monomorphizer).
///
/// The pass runs at the concrete argument types the demand carried -- the
/// instance the program is about to execute -- instead of the open signature
/// frame. Checking at the instance's types is what the lazy run needs (its
/// verdict is per executed instance, and the recorded channel entries are
/// the instance's), and it makes the pass cheap: the call tree was already
/// elaborated at these same types by the caller's own pass, so the nested
/// calls hit the elaboration memo instead of being elaborated afresh at the
/// open frame's types, where a call chain can re-expand exponentially.
/// Annotated parameters keep their annotations (the frame instantiates them
/// against the arguments, annotation winning), so a fully annotated body
/// checks exactly as its definitional pass would.
fn check_function_body_at(
    checker: &mut Checker,
    symbol: &str,
    f: &FunInfo,
    arg_types: &[Type],
) -> Option<Type> {
    checker.stats.dedicated_passes += 1;
    tracing::debug!(function = %f.signature.name, "inferring function body at demanded types");
    checker.current_module = f.module.clone();
    // A demand names its instance in monomorphization's spelling, where a
    // declared record carries its annotated field types in its substitution
    // (`Dog<age=int32, name=string>`). Checking at the checker's own spelling
    // (`Dog`) makes this body's diagnostics read -- and deduplicate -- exactly
    // like the call-site elaboration's and the whole-program check's.
    let arg_types: Vec<Type> = arg_types
        .iter()
        .map(|arg| brass_hir::instance_key_type(checker.program, arg))
        .collect();
    let arg_types = arg_types.as_slice();
    let mut scopes = checker.signature_call_frame(&f.signature.params, arg_types, &[], None);
    checker.in_entry_main = symbol == "main";
    let errors_before = checker.errors.len();
    checker.enter_instance(
        brass_hir::InstanceCallable::Function(symbol.to_string()),
        arg_types,
    );
    let empty_arrays_from = checker.empty_array_elems.len();
    let capped_before = checker.depth_capped;
    let full = checker.check_block_root(&f.decl.body, &mut scopes, f.signature.ret_ty.as_ref());
    checker.report_unfixed_empty_arrays(empty_arrays_from, Some(f.decl.body.span));
    checker.leave_instance();
    if let Some(inferred) = checker.function_returns.get(symbol).cloned() {
        checker.warn_implicit_nullable_result(&f.signature, &f.decl.body, &inferred);
    }
    // A call typed from a depth-capped fallback makes the return an
    // approximation, not a contract.
    if f.signature.ret_ty.is_some()
        || checker.errors.len() != errors_before
        || checker.depth_capped != capped_before
    {
        return None;
    }
    // Only a reconciled full return serves as a contract. `None` covers more
    // than one shape (no returns at all, a propagating body whose shape only
    // the light assembly builds), so no contract is claimed for it -- nor
    // for returns with no join, whose reconciliation only stands in for the
    // first type.
    let returns = checker.last_returns.clone();
    if let Some(Err(_)) = checker.join_known_values(&returns) {
        return None;
    }
    let ret = checker.resolve(&full?);
    brass_hir::is_fully_known(&ret).then_some(ret)
}

/// One module initializer's dedicated pass -- the per-init core both body
/// orders share. The caller brackets the whole init sequence with the shared
/// `const_scopes` frame.
pub(super) fn check_init_body(checker: &mut Checker, init: &ModuleInit) {
    checker.current_module = init.path.clone();
    if !checker.numeric.active
        && !checker.numeric_zero_growth
        && (checker.numeric_enabled || checker.lazy_profile)
        && !init.stmts.is_empty()
        && !(checker.numeric_seed_ordinary && checker.seeded_module(&init.path))
        && checker.numeric_init_needs_settlement(init)
    {
        let enabled = std::mem::replace(&mut checker.numeric_enabled, true);
        let mut settled = checker.settle_numeric_init(init);
        tracing::debug!(module = ?init.path, changed = settled.changed, "settled numeric initializer");
        let zero = std::mem::replace(&mut checker.numeric_zero_growth, !settled.changed);
        if !settled.changed {
            checker.numeric_enabled = false;
            settled = Default::default();
        }
        let saved = std::mem::replace(&mut checker.numeric, settled);
        check_init_body(checker, init);
        checker.numeric = saved;
        checker.numeric_enabled = enabled;
        checker.numeric_zero_growth = zero;
        return;
    }
    // The globals of OTHER modules this one can see. Its own are left out so
    // they still accumulate as its statements are checked -- a later global is
    // not visible to an earlier initializer.
    let global_scope = checker.global_scope();
    let mut scopes = vec![Scope::shared(global_scope)];
    if let Some(own) = checker.global_defs.get(&init.path) {
        for name in own.keys() {
            scopes[0].remove(name);
        }
    }
    checker.narrowing_kills.clear();
    checker.loop_frames.clear();
    checker.narrowing_facts = Rc::new(narrowing::NarrowingFacts::of_stmts(&init.stmts));
    let empty_arrays_from = checker.empty_array_elems.len();
    let bindings = binding_joins::BlockBindings::new(&init.stmts);
    for (index, s) in init.stmts.iter().enumerate() {
        checker.check_stmt(s, &mut scopes);
        // A monomorphic closure binding's parameters take the join of every
        // application in the rest of the module's code, as in a body (see
        // `check_block_stmts`), before the global's type settles.
        if bindings.after(index).is_some() {
            checker.pin_closure_parameters(&bindings, index, &scopes);
        }
        // The binding the statement just checked is the global's type from
        // here on, for every body that reads it (see `settle_global`).
        if let Stmt::Let { pat, .. } = s {
            let mut names = Vec::new();
            checker.collect_const_bindings(pat, &mut names);
            for name in names {
                if let Some(full) = checker.lookup(&scopes, &name) {
                    checker.settle_global(&init.path, &name, &full, s.span());
                    if checker.numeric.probing && scopes[0].numeric.contains_key(&name) {
                        let ty = checker.resolve(&full);
                        checker
                            .numeric
                            .globals
                            .insert((init.path.clone(), name), ty);
                    }
                }
            }
        }
    }
    // A top-level empty array literal may be a global a function fills
    // later, so its own literals are judged once every body is checked (see
    // `Checker::report_unfixed_init_arrays`).
    let recorded: Vec<(Span, Type)> = checker
        .empty_array_elems
        .drain(empty_arrays_from..)
        .collect();
    // A `let`'s own span may end before its initializer.
    let extent = |s: &Stmt| match s {
        Stmt::Let {
            span,
            value: Some(value),
            ..
        } => (span.lo.min(value.span().lo), span.hi.max(value.span().hi)),
        other => (other.span().lo, other.span().hi),
    };
    checker
        .init_empty_arrays
        .extend(recorded.into_iter().filter(|(span, _)| {
            init.stmts
                .iter()
                .map(extent)
                .any(|(lo, hi)| span.lo >= lo && span.hi <= hi)
        }));
}
