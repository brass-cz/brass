//! The LLVM JIT back end for Brass.
//!
//! This crate generates typed, fully unboxed LLVM IR (the [`codegen`] module
//! implementing `brass_engine::Codegen` over monomorphized MIR) and runs it:
//! the [`jit`] module owns OrcJIT execution. The entry point [`jit::run`] is
//! re-exported at the crate root.
//!
pub mod closure;
pub mod codegen;
pub mod dispatch;
pub mod jit;
pub mod layout;
pub mod monomorph;
pub mod ownership;

pub use codegen::LlvmCodegen;
pub use dispatch::prime_resolved;
pub use dispatch::{RuntimeDispatcher, pp_resolve, with_dispatcher};
pub use jit::{run, run_lazy, run_mono};
pub use monomorph::{mangle_closure, mangle_fn, mangle_init, mangle_method};
