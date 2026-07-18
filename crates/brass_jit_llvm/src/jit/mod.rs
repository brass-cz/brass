//! LLVM JIT execution.
//!
//! This module owns the runtime side of the LLVM back end: it builds an
//! execution engine for a generated module, maps the runtime's C-ABI primitives
//! to their host addresses, and runs the program. Code
//! *generation* lives in [`crate::codegen`]. The runtime monomorphization cache
//! and the `RuntimeJit` orchestration for deferred monomorphization live
//! backend-agnostically in `brass_engine`; the LLVM-specific runtime
//! compilation is `impl brass_engine::RuntimeJit for LlvmCodegen` in
//! [`crate::codegen`].

pub mod engine;
pub(crate) mod orc;

pub use engine::{run, run_lazy, run_mono};
