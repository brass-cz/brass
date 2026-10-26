//! LLVM JIT execution.
//!
//! This module owns the runtime side of the LLVM back end: the ORC session
//! that compiles generated modules on demand (`orc`), the content-addressed
//! store of their native objects (`objcache`), and the entry points that run
//! a program (`engine`). Code *generation* lives in [`crate::codegen`],
//! including the batches the lazy JIT compiles into the live session while the
//! program runs (`LlvmCodegen::register_batch`); the deferred call sites reach
//! the driver's resolver through [`crate::dispatch`].

pub mod engine;
pub(crate) mod objcache;
pub(crate) mod orc;

pub use engine::{run, run_mono};
