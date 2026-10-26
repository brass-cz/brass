//! The execution engine: drive a [`Codegen`] back end over a monomorphized
//! program to compile and run it.
//!
//! It performs no target-specific work itself; it only sequences the trait's
//! phases -- declare, emit, finalize, execute -- so every [`Codegen`]
//! implementation (the LLVM JIT, a test back end) runs MIR the same way.

use crate::codegen::Codegen;
use crate::mono::MonoProgram;

/// Drives a back end through the full compile-and-run sequence for one program.
pub struct Engine;

impl Engine {
    /// Compile `program` with `backend` and run it: declare all items, emit every
    /// body, finalize (build the executable form), then run initializers and
    /// `main`. Stops and returns the error if finalization or execution fails.
    pub fn run<B: Codegen>(backend: &mut B, program: &MonoProgram) -> Result<(), String> {
        backend.begin_program(program);
        let t = std::time::Instant::now();
        backend.codegen_program(program);
        brass_utils::perf_phase("back/codegen", t.elapsed());
        let t = std::time::Instant::now();
        backend.finalize()?;
        brass_utils::perf_phase("back/finalize", t.elapsed());
        backend.execute()
    }

    /// Compile `program` with `backend` without running it. Useful for inspecting
    /// the generated form (e.g. tests that check emitted signatures).
    pub fn compile<B: Codegen>(backend: &mut B, program: &MonoProgram) -> Result<(), String> {
        backend.begin_program(program);
        backend.codegen_program(program);
        backend.finalize()
    }
}
