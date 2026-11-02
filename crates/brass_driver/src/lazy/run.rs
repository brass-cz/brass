//! Demand-driven preparation and execution of a lazy program.

use super::demand::BatchIds;
use super::frontier::{LoweringFrontier, settle_demands};
use super::{
    BodySpans, CheckerCleanup, CheckerPause, FatalVerdict, LazyState, MergedChannels,
    ThreadScheduler, demand_loop_progress, drain_targets_for_spawn, finish_eagerly, judge_fatal,
    resolve_deferred, stop_checker, trace,
};
use crate::source_locations::{LocationTables, call_site_locations};
use crate::{
    MAIN_STACK_BYTES, check_front, front_load, install_jit_panic_guard, print_diags, render_errors,
    report_runtime_error,
};
use brass_hir::lower;
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::path::PathBuf;

/// The lazy-check run: type inference happens on the checker thread while
/// this thread prepares and executes the program, gating only on the bodies
/// execution actually needs.
///
/// 1. The checker thread runs the full streaming analysis; this thread
///    assembles its own identical module graph (lowering is deterministic,
///    so spans and type ids agree with the streamed channels).
/// 2. Once every module initializer and `main` are settled, entry-rooted
///    monomorphization starts. A reachable function whose body is not
///    settled yet stops it; the demand -- the function's path and the
///    concrete argument types of the call -- goes to the checker thread,
///    which checks that body next; its channel delta lands here, the body
///    is lowered, and monomorphization retries. Unreachable code never
///    gates execution.
/// 3. Declaration diagnostics and errors in needed bodies abort the run
///    with the checker's complete verdict, in its diagnostic text and source
///    locations (see [`judge_fatal`]). Once the program ran, the run's
///    verdict is the executed path's alone: the checker is stopped at the
///    next body boundary and whatever it held for code the run never needed
///    is discarded by policy (pinned by `e2e_tests/lazy/dead_code_error.cz`)
///    -- the whole-program verdict is `brass check`'s (or `--eager`'s) job.
/// 4. Keyed specialization appends generated bodies and checker channels
///    through `KeyedReady`. A keyed call discovered after execution starts
///    asks for `--eager`; executor-side assembly failures before execution
///    fall back to [`finish_eagerly`].
pub(crate) fn run_lazy(label: String, src: String, root: PathBuf) -> Result<(), u8> {
    // The checker recurses per call-site re-elaboration much like the
    // interpreter recurses per Brass call, so its thread gets the same
    // generous stack as the driver thread (virtual memory; pages commit only
    // as the stack grows).
    let counters = trace::LazyCounters::default();
    let rt = tokio::runtime::Builder::new_current_thread()
        .thread_name("brass-checker")
        .thread_stack_size(MAIN_STACK_BYTES)
        .build()
        .map_err(|e| {
            eprintln!("error: cannot start the checker runtime: {e}");
            1u8
        })?;
    // One front end for both sides: the checker thread gets a clone of the
    // assembled module graph, this thread keeps the original to execute --
    // lowering is deterministic, so spans and type ids agree with the
    // streamed channels. Syntax and module-graph problems abort here, before
    // any thread starts, exactly as eagerly.
    let search = brass_resolve::SearchPaths::from_env();
    let (front, prepared) = match front_load(&label, &src, &root, &search) {
        Ok(front) => front,
        Err(diags) => return Err(print_diags(diags)),
    };
    // Lower on this side first. Keyed calls before execution wait for the
    // append-only `KeyedReady` continuation (`LazyState::awaiting_keyed`);
    // calls discovered during execution require `--eager`.
    let (mut program, lower_errors) =
        prepared.map_or_else(|| lower(&front.modules), |prepared| prepared.lowered);
    let (events_tx, events_rx) = tokio::sync::mpsc::unbounded_channel();
    let (requests_tx, requests_rx) = tokio::sync::mpsc::unbounded_channel();
    let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    // The checker starts PAUSED: until execution begins, it serves only the
    // driver's demands, so no demand ever waits behind a definitional pass
    // the background queue happened to start first (an unannotated body's
    // open-frame pass can be arbitrarily slow; see `Scheduler::paused`).
    let paused = std::sync::Arc::new(CheckerPause {
        paused: std::sync::atomic::AtomicBool::new(true),
        requests: requests_tx,
    });
    let checker = rt.spawn_blocking({
        let front = front.clone();
        let stop = stop.clone();
        let paused = paused.clone();
        move || {
            let search = brass_resolve::SearchPaths::from_env();
            let mut sched = ThreadScheduler {
                completion_observations: super::policy::CompletionState::enabled(),
                events: events_tx,
                requests: requests_rx,
                stop,
                paused,
                requests_closed: false,
            };
            check_front(front, None, &search, LocationTables::Omit, Some(&mut sched))
        }
    });
    let _checker_cleanup = CheckerCleanup {
        stop: stop.clone(),
        paused: paused.clone(),
    };

    // Front-pass diagnostics (qualified uses, spawn ownership) are not
    // rendered here: the checker reports them with the rest, eager-identical.
    if !front.errors.is_empty() {
        return finish_eagerly(&rt, checker, &stop, &paused, events_rx, &label, &src, &root);
    }
    if !lower_errors.is_empty() {
        return finish_eagerly(&rt, checker, &stop, &paused, events_rx, &label, &src, &root);
    }
    let call_locations = call_site_locations(&front.modules, &front.sources, &search);
    let function_ranges = program
        .functions
        .iter()
        .map(|(symbol, function)| (symbol.clone(), function.decl.span.lo, function.decl.span.hi))
        .collect();
    let mut lazy = LazyState {
        selected_bodies: None,
        completion: super::policy::CompletionState::from_env(),
        counters,
        events: events_rx,
        sources: front.sources.clone(),
        merged: MergedChannels::default(),
        checked_fns: HashSet::default(),
        inits_checked: 0,
        held: Vec::new(),
        printed_warnings: HashSet::default(),
        needed: program
            .entry_function()
            .map(str::to_owned)
            .into_iter()
            .collect(),
        stop,
        paused,
        needs_eager: false,
        closed: false,
        dirty: false,
        function_ranges,
        dirty_functions: HashSet::default(),
        dirty_non_functions: false,
        awaiting_keyed: false,
        entry_open: false,
        generated: Vec::new(),
        batch_ids: BatchIds::default(),
        outstanding_batches: std::collections::VecDeque::new(),
        finished: false,
    };
    let settled = lazy.wait_gate(program.inits.len(), program.entry_function());
    if lazy.needs_eager {
        return finish_eagerly(
            &rt,
            checker,
            &lazy.stop,
            &lazy.paused,
            lazy.events,
            &label,
            &src,
            &root,
        );
    }
    if !lazy.generated.is_empty()
        && brass_hir::lower_generated_into(&mut program, &lazy.generated).is_err()
    {
        return finish_eagerly(
            &rt,
            checker,
            &lazy.stop,
            &lazy.paused,
            lazy.events,
            &label,
            &src,
            &root,
        );
    }
    lazy.entry_open = true;
    let bodies = BodySpans::new(&program);
    match judge_fatal(&mut lazy, &bodies, &front.sources) {
        FatalVerdict::Clean => {}
        FatalVerdict::Fatal(code) => return Err(code),
        FatalVerdict::NeedsEager => {
            return finish_eagerly(
                &rt,
                checker,
                &lazy.stop,
                &lazy.paused,
                lazy.events,
                &label,
                &src,
                &root,
            );
        }
    }
    if !settled {
        // The checker hung up cleanly without settling the entry: nothing
        // fatal was held, so fall back to the whole-analysis verdict.
        return finish_eagerly(
            &rt,
            checker,
            &lazy.stop,
            &lazy.paused,
            lazy.events,
            &label,
            &src,
            &root,
        );
    }

    // Demand-driven compilation: methods and inits lower up front, function
    // bodies as monomorphization discovers it needs them. A delta arriving
    // after a body was lowered can carry entries for that body's spans (a
    // cross-body pinning settles an earlier body's literal), so those owners
    // are refreshed before the mono result is trusted.
    let mut demanded: Vec<String> = Vec::new();
    // The HIR-derived lowering tables are channel-independent: computed once,
    // shared across every rebuild.
    let tables_started = std::time::Instant::now();
    let tables = brass_mir::LowerTables::new(&program);
    tracing::debug!(
        target: "brass::perf",
        elapsed_ms = tables_started.elapsed().as_secs_f64() * 1000.0,
        "lazy: lowering tables"
    );
    let (mut lowering, mut mono_session) = 'rebuild: loop {
        lazy.counters.record_lowering_rebuild();
        let mut mono_session = brass_engine::MonoSession::default();
        lazy.dirty = false;
        lazy.dirty_functions.clear();
        lazy.dirty_non_functions = false;
        tracing::debug!(
            target: "brass::perf",
            demanded = demanded.len(),
            closed = lazy.closed,
            "lazy: lowering rebuild"
        );
        let lowering_started = std::time::Instant::now();
        let mut appended = 0;
        let mut built = {
            let channels = lazy.channels(&call_locations);
            let mut built = brass_mir::SubsetLowering::new(&program, &tables, &channels);
            for symbol in &demanded {
                appended += usize::from(built.add_function(&program, &tables, symbol, &channels));
            }
            built
        };
        tracing::debug!(
            target: "brass::perf",
            elapsed_ms = lowering_started.elapsed().as_secs_f64() * 1000.0,
            "lazy: lowering rebuild complete"
        );
        lazy.counters.record_lowering_appends(appended);
        // The demand loop: monomorphize, and supply each missing body as it
        // is reported, INCREMENTALLY -- new bodies are appended against the
        // channel state of their arrival, and only a mono pass over an
        // all-deltas-folded lowering with no pending revisions is trusted.
        let mut applied = None;
        loop {
            let mono_started = std::time::Instant::now();
            let changes = applied.take().unwrap_or_else(|| {
                LoweringFrontier::default().apply(
                    &mut built,
                    &mut lazy,
                    &program,
                    &tables,
                    &call_locations,
                )
            });
            lazy.counters.record_mono_pass();
            let mono_result = mono_session.entry(
                &built.mir,
                &program,
                true,
                lazy.merged.instance_returns.clone(),
                &changes,
            );
            tracing::debug!(
                target: "brass::perf",
                elapsed_ms = mono_started.elapsed().as_secs_f64() * 1000.0,
                "lazy: monomorphization pass"
            );
            match mono_result {
                Ok(mono) => {
                    // A missing `main` can be transient while a keyed
                    // (`-> infer!`) call awaits the append-only `KeyedReady`
                    // continuation. Retry with its generated bodies and
                    // channels; only a skip against the checker's final
                    // state is a rejection, reported like the eager JIT.
                    let main_skipped =
                        program.entry_function().is_some() && mono.entry_function().is_none();
                    drop(mono);
                    if main_skipped {
                        if !lazy.closed {
                            // Waiting on the checker's own progress: run its
                            // queue, or no event would ever come.
                            lazy.resume_background();
                            lazy.pump_blocking();
                            lazy.pump_pending();
                            if lazy.needs_eager {
                                return finish_eagerly(
                                    &rt,
                                    checker,
                                    &lazy.stop,
                                    &lazy.paused,
                                    lazy.events,
                                    &label,
                                    &src,
                                    &root,
                                );
                            }
                            match judge_fatal(&mut lazy, &bodies, &front.sources) {
                                FatalVerdict::Clean => {}
                                FatalVerdict::Fatal(code) => return Err(code),
                                FatalVerdict::NeedsEager => {
                                    return finish_eagerly(
                                        &rt,
                                        checker,
                                        &lazy.stop,
                                        &lazy.paused,
                                        lazy.events,
                                        &label,
                                        &src,
                                        &root,
                                    );
                                }
                            }
                            continue 'rebuild;
                        }
                        if lazy.dirty {
                            if lazy.refresh_lowering(&mut built, &program, &tables, &call_locations)
                            {
                                continue;
                            }
                            continue 'rebuild;
                        }
                        match judge_fatal(&mut lazy, &bodies, &front.sources) {
                            FatalVerdict::Clean => {}
                            FatalVerdict::Fatal(code) => return Err(code),
                            FatalVerdict::NeedsEager => {
                                return finish_eagerly(
                                    &rt,
                                    checker,
                                    &lazy.stop,
                                    &lazy.paused,
                                    lazy.events,
                                    &label,
                                    &src,
                                    &root,
                                );
                            }
                        }
                    } else {
                        if lazy.dirty {
                            if lazy.refresh_lowering(&mut built, &program, &tables, &call_locations)
                            {
                                continue;
                            }
                            // A method or initializer changed: rebuild the subset
                            // base before trusting the successful mono pass.
                            continue 'rebuild;
                        }
                    }
                    break 'rebuild (built, mono_session);
                }
                Err(brass_engine::MonoStop::MissingBodies(demands)) => {
                    tracing::debug!(target: "brass::perf", count = demands.len(), "lazy: missing bodies");
                    let settled =
                        settle_demands(demands, &program, &built, &mut lazy, Some(&demanded));
                    let newly_settled = settled.outcome.newly_settled;
                    if !settled.members.is_empty() && !settled.outcome.complete {
                        if lazy.needs_eager {
                            return finish_eagerly(
                                &rt,
                                checker,
                                &lazy.stop,
                                &lazy.paused,
                                lazy.events,
                                &label,
                                &src,
                                &root,
                            );
                        }
                        match judge_fatal(&mut lazy, &bodies, &front.sources) {
                            FatalVerdict::Clean => {}
                            FatalVerdict::Fatal(code) => return Err(code),
                            FatalVerdict::NeedsEager => {
                                return finish_eagerly(
                                    &rt,
                                    checker,
                                    &lazy.stop,
                                    &lazy.paused,
                                    lazy.events,
                                    &label,
                                    &src,
                                    &root,
                                );
                            }
                        }
                        let symbols = settled
                            .members
                            .iter()
                            .map(|d| d.symbol.as_str())
                            .collect::<Vec<_>>()
                            .join("`, `");
                        eprintln!("error: lazy compilation cannot supply `{symbols}`");
                        return Err(1);
                    }
                    if !settled.members.is_empty() {
                        // Every requested body is now settled. Judge their
                        // held diagnostics together before lowering any code.
                        match judge_fatal(&mut lazy, &bodies, &front.sources) {
                            FatalVerdict::Clean => {}
                            FatalVerdict::Fatal(code) => return Err(code),
                            FatalVerdict::NeedsEager => {
                                return finish_eagerly(
                                    &rt,
                                    checker,
                                    &lazy.stop,
                                    &lazy.paused,
                                    lazy.events,
                                    &label,
                                    &src,
                                    &root,
                                );
                            }
                        }
                    }
                    let append_started = std::time::Instant::now();
                    let append_count = settled.members.len();
                    demanded.extend(settled.members.iter().map(|demand| demand.symbol.clone()));
                    // A method or initializer revision invalidates the base.
                    // Rebuild it before applying this settled window, rather
                    // than running mono once against the stale base first.
                    if lazy.dirty_non_functions {
                        continue 'rebuild;
                    }
                    let lowering_frontier = settled.into_lowering(&mut lazy);
                    let supplied_bodies = lowering_frontier.supplied_bodies(&built);
                    applied = Some(lowering_frontier.apply(
                        &mut built,
                        &mut lazy,
                        &program,
                        &tables,
                        &call_locations,
                    ));
                    tracing::debug!(
                        target: "brass::perf",
                        count = append_count,
                        elapsed_ms = append_started.elapsed().as_secs_f64() * 1000.0,
                        "lazy: lowering append"
                    );
                    if let Err(error) =
                        demand_loop_progress(append_count, newly_settled, supplied_bodies)
                    {
                        eprintln!("error: {error}");
                        // The checker may be parked waiting for another demand;
                        // wake it so the runtime can join the stopped task.
                        lazy.stop.store(true, std::sync::atomic::Ordering::Relaxed);
                        lazy.resume_background();
                        return Err(1);
                    }
                }
                Err(brass_engine::MonoStop::Fail(e)) => {
                    // Monomorphization can fail TRANSIENTLY under lazy
                    // checking: an entry a later body pins (or a whole delta
                    // still in flight) may be exactly what the failed
                    // inference needed. Wait for more of the check and
                    // retry; only a failure against the checker's FINAL
                    // state -- where eager would have failed identically --
                    // is real. Diagnostics, when the checker found any,
                    // explain the program better than the mono error does;
                    // prefer them.
                    if !lazy.closed {
                        // Waiting on the checker's own progress: run its
                        // queue, or no event would ever come.
                        lazy.resume_background();
                        lazy.pump_blocking();
                        lazy.pump_pending();
                        if lazy.needs_eager {
                            return finish_eagerly(
                                &rt,
                                checker,
                                &lazy.stop,
                                &lazy.paused,
                                lazy.events,
                                &label,
                                &src,
                                &root,
                            );
                        }
                        match judge_fatal(&mut lazy, &bodies, &front.sources) {
                            FatalVerdict::Clean => {}
                            FatalVerdict::Fatal(code) => return Err(code),
                            FatalVerdict::NeedsEager => {
                                return finish_eagerly(
                                    &rt,
                                    checker,
                                    &lazy.stop,
                                    &lazy.paused,
                                    lazy.events,
                                    &label,
                                    &src,
                                    &root,
                                );
                            }
                        }
                        continue 'rebuild;
                    }
                    if lazy.dirty {
                        if lazy.refresh_lowering(&mut built, &program, &tables, &call_locations) {
                            continue;
                        }
                        continue 'rebuild;
                    }
                    match judge_fatal(&mut lazy, &bodies, &front.sources) {
                        FatalVerdict::Clean => {}
                        FatalVerdict::Fatal(code) => return Err(code),
                        FatalVerdict::NeedsEager => {
                            return finish_eagerly(
                                &rt,
                                checker,
                                &lazy.stop,
                                &lazy.paused,
                                lazy.events,
                                &label,
                                &src,
                                &root,
                            );
                        }
                    }
                    // A rejection against the checker's final state: held
                    // diagnostics elsewhere (a broken method the entry
                    // needs) usually explain it better than the mono error.
                    let held = lazy.held_all();
                    if !held.is_empty() {
                        for line in render_errors(&held, &front.sources) {
                            eprintln!("{line}");
                        }
                        return Err(1);
                    }
                    report_runtime_error(&format!("typed lowering failed: {e}"));
                    return Err(1);
                }
            }
        }
    };
    // Deterministic inputs: the re-run reproduces the loop's successful pass
    // (the same instance-return contracts included -- without them a
    // deferred unannotated call would re-demand its body here).
    lazy.refresh_channels(&mut lowering, &call_locations);
    lazy.counters.record_mono_pass();
    let Ok(mono) = mono_session.entry(
        &lowering.mir,
        &program,
        true,
        lazy.merged.instance_returns.clone(),
        lowering.changed_inputs(),
    ) else {
        eprintln!("error: lazy compilation diverged between passes");
        // The checker may still be paused; a plain return would deadlock the
        // runtime drop joining its blocking task.
        lazy.stop.store(true, std::sync::atomic::Ordering::Relaxed);
        return Err(1);
    };

    // Everything execution can reach is settled. A diagnostic on the needed
    // path that arrived meanwhile aborts before the program runs; held
    // diagnostics elsewhere stay held -- lazy checking ignores code the run
    // never executes.
    lazy.need_monomorphized_bodies(&lowering.mir, &mono);
    lazy.pump_pending();
    if lazy.needs_eager {
        drop(mono);
        return finish_eagerly(
            &rt,
            checker,
            &lazy.stop,
            &lazy.paused,
            lazy.events,
            &label,
            &src,
            &root,
        );
    }
    match judge_fatal(&mut lazy, &bodies, &front.sources) {
        FatalVerdict::Clean => {}
        FatalVerdict::Fatal(code) => return Err(code),
        FatalVerdict::NeedsEager => {
            return finish_eagerly(
                &rt,
                checker,
                &lazy.stop,
                &lazy.paused,
                lazy.events,
                &label,
                &src,
                &root,
            );
        }
    }
    install_jit_panic_guard();
    // The deferred runtime: reject an untypeable `main` exactly as `run_mono`
    // would, compile the startup set, then run with the resolver installed --
    // a deferred site's first call lands there.
    if program.entry_function().is_some() && mono.entry_function().is_none() {
        // A rejected entry may have prevented monomorphization from exposing
        // its method dependencies. Prefer the completed source verdict over
        // a secondary lowering failure, as for MonoStop::Fail above.
        let held = lazy.held_all();
        if !held.is_empty() {
            return Err(print_diags(render_errors(&held, &front.sources)));
        }
        let reason = match &mono.main_skip {
            Some(reason) => brass_engine::refusal("cannot compile `main` for execution", reason),
            None => "cannot compile `main` for execution".to_string(),
        };
        report_runtime_error(&reason);
        return Err(1);
    }
    let codegen_started = std::time::Instant::now();
    let context = brass_jit_llvm::OrcContext::new();
    let mut backend = brass_jit_llvm::LlvmCodegen::new_orc_backend(&context, &program);
    let _resolved_session = brass_jit_llvm::resolved_session();
    let prepared = backend.prepare_lazy_orc(&mono);
    tracing::debug!(
        target: "brass::perf",
        elapsed_ms = codegen_started.elapsed().as_secs_f64() * 1000.0,
        "lazy: codegen startup"
    );
    let mut targets: HashMap<String, brass_engine::DeferredSig> = mono.deferred.clone();
    // The startup run typed every init, so its global table is complete;
    // runtime single-instance monos read module globals through it.
    let globals: Vec<(String, brass_hir::Type)> = mono.globals.clone();
    let startup_spawns = brass_engine::batch_spawns(&mono);
    // Free the lowering for the resolver's on-demand additions.
    drop(mono);
    let finalize_started = std::time::Instant::now();
    let finalized = prepared.and_then(|()| backend.precompile_spawn());
    tracing::debug!(
        target: "brass::perf",
        elapsed_ms = finalize_started.elapsed().as_secs_f64() * 1000.0,
        "lazy: finalize startup"
    );
    let execution_started = std::time::Instant::now();
    let result = match finalized {
        Ok(()) => {
            // The startup set spawns: compile and prime every recorded
            // target BEFORE anything runs, so worker threads -- which can
            // only read the resolved-address cache -- never reach an
            // unresolved site.
            let drained = !startup_spawns
                || drain_targets_for_spawn(
                    &mut backend,
                    &program,
                    &tables,
                    &call_locations,
                    &front.sources,
                    &bodies,
                    &globals,
                    &mut lowering,
                    &mut lazy,
                    &mut targets,
                );
            if drained {
                // Execution begins: from here the background queue fills the
                // wait on the running program.
                lazy.resume_background();
                lazy.begin_execution();
                let mut resolve = |backend: &mut brass_jit_llvm::LlvmCodegen, symbol: &str| {
                    resolve_deferred(
                        backend,
                        symbol,
                        &program,
                        &tables,
                        &call_locations,
                        &front.sources,
                        &bodies,
                        &globals,
                        &mut lowering,
                        &mut lazy,
                        &mut targets,
                    )
                };
                backend.execute_with_resolver(&mut resolve)
            } else {
                Err("lazy compilation could not pre-compile the spawned code".to_string())
            }
        }
        Err(e) => Err(e),
    };
    tracing::debug!(
        target: "brass::perf",
        elapsed_ms = execution_started.elapsed().as_secs_f64() * 1000.0,
        "lazy: execute"
    );
    // The program finished (or failed at runtime); the checker may still be
    // working through code this run never executed, and lazy checking
    // ignores whatever it would find there -- the complete verdict is
    // `brass check`'s job. Stop it at the next body boundary and reclaim the
    // thread; held diagnostics are discarded by policy.
    let stop_started = std::time::Instant::now();
    stop_checker(&rt, checker, &mut lazy);
    tracing::debug!(
        target: "brass::perf",
        elapsed_ms = stop_started.elapsed().as_secs_f64() * 1000.0,
        "lazy: stop checker"
    );
    match result {
        Ok(()) => Ok(()),
        Err(e) => {
            report_runtime_error(&e);
            Err(1)
        }
    }
}
