//! Runtime resolution of deferred lazy instances.

use super::demand::{Demand, DemandFrontier};
use super::frontier::{LoweringFrontier, settle_demands};
use super::{BodySpans, LazyState, demand_loop_progress, drain_targets_for_spawn, exit_if_fatal};
use crate::{print_diags, render_errors};
use brass_hir::Program;
use brass_parser::Span;
use fxhash::FxHashMap as HashMap;
use std::io;

/// The runtime half of deferral: called (through `pp_resolve`) the first
/// time execution reaches a deferred call site. Ensures the target's body is
/// checked -- sending the function's path and the site's concrete argument
/// types to the checker and waiting, when it is not -- lowers it, then
/// monomorphizes and compiles the instance (and everything it newly needs;
/// its own calls may defer further) into the LIVE engine. Returns the
/// callable address, or 0 after reporting -- the site then traps, keeping a
/// resolver failure defined.
///
/// A fatal diagnostic discovered here means the program needed ill-typed
/// code: the checker's complete verdict is printed and the process exits 1
/// (see [`exit_if_fatal`]), exactly as if the error had been found before
/// execution -- output the program already produced stands, as documented
/// for lazy checking. Held diagnostics in bodies execution never needs decide
/// nothing on their own.
#[allow(clippy::too_many_arguments)] // the execution-side state is one bundle
pub(super) fn resolve_deferred(
    backend: &mut brass_jit_llvm::LlvmCodegen,
    symbol: &str,
    program: &Program,
    tables: &brass_mir::LowerTables,
    call_locations: &HashMap<Span, (String, u32, u32)>,
    sources: &brass_resolve::SourceMap,
    bodies: &BodySpans,
    globals: &[(String, brass_hir::Type)],
    lowering: &mut brass_mir::SubsetLowering,
    lazy: &mut LazyState,
    targets: &mut HashMap<String, brass_engine::DeferredSig>,
) -> usize {
    lazy.counters.record_runtime_resolve();
    lazy.observe_resolve();
    tracing::debug!(target: "brass::perf", %symbol, "lazy: runtime resolve");
    // Already compiled -- by the startup set, or by an earlier resolution.
    if let Some(addr) = backend.address_of(symbol) {
        return addr;
    }
    let Some(sig) = targets.get(symbol).cloned() else {
        eprintln!("error: deferred call to unrecorded instance `{symbol}`");
        return 0;
    };
    // A diagnostic on the (just grown) needed path stops the run here,
    // before the ill-typed code could execute.
    let fatal_exit = |lazy: &mut LazyState, fallback: &str| -> usize {
        exit_if_fatal(lazy, bodies, sources);
        eprintln!("{fallback}");
        0
    };
    let mut applied = None;
    if !lowering.is_lowered(&sig.base) {
        tracing::debug!(target: "brass::perf", base = %sig.base, "lazy: runtime lower");
        let mut frontier = DemandFrontier::default();
        frontier.push(Demand {
            symbol: sig.base.clone(),
            type_args: sig.type_args.clone(),
            needs_body: true,
        });
        let batch = frontier
            .seal(&mut lazy.batch_ids)
            .expect("one runtime target");
        if !lazy.settle(batch).complete {
            return fatal_exit(
                lazy,
                &format!("error: the check of `{}` did not complete", sig.base),
            );
        }
        // The demanded body joined the needed set: a held diagnostic in it
        // is now fatal, before its code could ever run.
        exit_if_fatal(lazy, bodies, sources);
        let frontier = LoweringFrontier::settled(
            [Demand {
                symbol: sig.base.clone(),
                type_args: sig.type_args.clone(),
                needs_body: true,
            }],
            lazy,
            true,
        );
        applied = Some(frontier.apply(lowering, lazy, program, tables, call_locations));
    }
    let mut mono_session = brass_engine::MonoSession::default();
    loop {
        let changes = applied.take().unwrap_or_else(|| {
            LoweringFrontier::default().apply(lowering, lazy, program, tables, call_locations)
        });
        lazy.counters.record_mono_pass();
        match mono_session.instance(
            &lowering.mir,
            program,
            &sig,
            globals,
            lazy.merged.instance_returns.clone(),
            &changes,
        ) {
            Ok(mono) => {
                lazy.need_monomorphized_bodies(&lowering.mir, &mono);
                exit_if_fatal(lazy, bodies, sources);
                // An UNANNOTATED instance was deferred against the checker's
                // reported return; the monomorphized body is the authority.
                // A mismatch would make the already-compiled call site an
                // ill-typed indirect call, so it fails resolution (defined,
                // pre-execution of the instance) instead of miscompiling.
                let unannotated = program
                    .functions
                    .get(&sig.base)
                    .is_some_and(|f| f.signature.ret_ty.is_none());
                if unannotated
                    && let Some(f) = mono.lookup(symbol)
                    && f.ret != sig.ret
                {
                    eprintln!(
                        "error: deferred instance `{}` resolved with return type `{}` \
                         but its call site was compiled for `{}`; annotate the return \
                         type of `{}`",
                        symbol,
                        f.ret.display(),
                        sig.ret.display(),
                        sig.base
                    );
                    return 0;
                }
                targets.extend(mono.deferred.clone());
                let batch_spawns = brass_engine::batch_spawns(&mono);
                // Register the entire batch before a lookup can materialize
                // any mutually recursive bodies. Registration skips definitions
                // already supplied by startup or an earlier runtime batch.
                for f in &mono.functions {
                    if !backend.has_instance(&f.symbol) {
                        tracing::debug!(target: "brass::perf", symbol = %f.symbol, "lazy: runtime compile");
                    }
                }
                if let Err(error) = backend.register_batch(&mono) {
                    eprintln!("error: runtime compilation of `{symbol}` failed: {error}");
                    return 0;
                }
                drop(mono);
                let addr = backend.address_of(symbol).unwrap_or(0);
                if addr != 0 {
                    brass_jit_llvm::prime_resolved(symbol, addr);
                }
                // The batch spawns: everything a worker thread could reach
                // must be compiled and primed before this call returns (the
                // spawn runs after it) -- workers cannot compile.
                if addr != 0
                    && batch_spawns
                    && !drain_targets_for_spawn(
                        backend,
                        program,
                        tables,
                        call_locations,
                        sources,
                        bodies,
                        globals,
                        lowering,
                        lazy,
                        targets,
                    )
                {
                    return 0;
                }
                return addr;
            }
            Err(brass_engine::MonoStop::MissingBodies(demands)) => {
                let settled = settle_demands(demands, program, lowering, lazy, None);
                let result = &settled.outcome;
                let members = &settled.members;
                if !members.is_empty() && !result.complete {
                    let miss = members
                        .iter()
                        .find(|d| !lazy.checked_fns.contains(&d.symbol))
                        .unwrap_or(&members[0]);
                    return fatal_exit(
                        lazy,
                        &format!("error: the check of `{}` did not complete", miss.symbol),
                    );
                }
                if !members.is_empty() {
                    exit_if_fatal(lazy, bodies, sources);
                }
                let new_requests = result.new_requests;
                let newly_settled = result.newly_settled;
                let frontier = settled.into_lowering(lazy);
                let supplied_bodies = frontier.supplied_bodies(lowering);
                applied = Some(frontier.apply(lowering, lazy, program, tables, call_locations));
                if let Err(error) =
                    demand_loop_progress(new_requests, newly_settled, supplied_bodies)
                {
                    eprintln!("error: {error}");
                    return 0;
                }
            }
            Err(brass_engine::MonoStop::Fail(e)) => {
                // The same transient-vs-final rule as start-up: retry once
                // more of the check has landed; a failure against the final
                // state is real.
                if !lazy.closed {
                    lazy.resume_background();
                    lazy.pump_blocking();
                    lazy.pump_pending();
                    if !lazy.needs_eager {
                        continue;
                    }
                }
                // A failed batch may never expose its method dependencies.
                // The completed source verdict takes precedence over the
                // secondary compilation error, just as at the entry gate.
                if lazy.closed && !lazy.needs_eager {
                    let held = lazy.held_all();
                    if !held.is_empty() {
                        use std::io::Write;
                        let _ = io::stdout().flush();
                        print_diags(render_errors(&held, sources));
                        lazy.counters.emit_summary();
                        std::process::exit(1);
                    }
                }
                return fatal_exit(
                    lazy,
                    &format!("error: runtime compilation of `{}` failed: {e}", sig.base),
                );
            }
        }
    }
}
