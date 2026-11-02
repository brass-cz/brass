//! Whole-program execution through ORC: lower and monomorphize a checked
//! program, prepare its session (the support module and the lazy function
//! groups), and run the module initializers followed by `main`. The lazy
//! pipeline drives the same `LlvmCodegen` session API from the driver,
//! registering further batches while the program runs.

use brass_hir::Program;

/// Compile and run a checked program through the LLVM JIT.
///
/// The program is lowered to MIR with the checker's `channels`, monomorphized
/// as a whole, and run by [`run_mono`] on the typed, fully unboxed back end. A
/// program whose `main` reaches a construct outside the typed subset is
/// rejected rather than executed.
pub fn run(program: &Program, channels: &brass_mir::CheckerChannels<'_>) -> Result<(), String> {
    let mir = lower_checked(program, channels);
    let t = std::time::Instant::now();
    let mono = brass_engine::monomorphize(&mir, program)
        .map_err(|e| format!("typed lowering failed: {e}"))?;
    tracing::debug!(
        target: "brass::perf",
        "back/monomorphize: total {:.3}ms",
        t.elapsed().as_secs_f64() * 1000.0
    );
    run_mono(program, &mono)
}

/// Compile and run an already-monomorphized program: the back half of
/// [`run`]. Rejects a program whose `main` fell outside the typed subset, then
/// compiles and executes through the ORC per-function pipeline: IR is emitted
/// and verified for every instance up front, but optimization and instruction
/// selection run on demand, so an eager run does not pay a full-module
/// finalize for functions it never executes.
pub fn run_mono(program: &Program, mono: &brass_engine::MonoProgram) -> Result<(), String> {
    require_main(program, mono)?;
    let context = crate::OrcContext::new();
    let mut backend = crate::LlvmCodegen::new_orc_backend(&context, program);
    backend.prepare_lazy_orc(mono)?;
    let result = backend.execute_lazy_orc();
    let cleanup = std::time::Instant::now();
    drop(backend);
    drop(context);
    brass_utils::perf_phase("back/eager-session-cleanup", cleanup.elapsed());
    result
}

fn lower_checked(
    program: &Program,
    channels: &brass_mir::CheckerChannels,
) -> brass_mir::MirProgram {
    let t = std::time::Instant::now();
    let mir = brass_mir::lower_program_with_types(program, channels);
    tracing::debug!(
        target: "brass::perf",
        "back/lower-mir: total {:.3}ms",
        t.elapsed().as_secs_f64() * 1000.0
    );
    // MIR is rendered only on request because it can dwarf ordinary logs.
    if tracing::enabled!(target: "brass::mir", tracing::Level::TRACE) {
        tracing::trace!(target: "brass::mir", "\n{}", brass_mir::program_to_string(&mir));
    }
    mir
}

fn require_main(program: &Program, mono: &brass_engine::MonoProgram) -> Result<(), String> {
    if program.entry_function().is_some() && mono.entry_function().is_none() {
        return Err(match &mono.main_skip {
            Some(reason) => brass_engine::refusal("cannot compile `main` for execution", reason),
            None => "cannot compile `main` for execution".to_string(),
        });
    }
    Ok(())
}
