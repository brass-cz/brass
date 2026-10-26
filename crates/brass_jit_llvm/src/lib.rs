//! The LLVM JIT back end for Brass.
//!
//! This crate generates typed, fully unboxed LLVM IR (the [`codegen`] module
//! implementing `brass_engine::Codegen` over monomorphized MIR) and runs it:
//! the [`jit`] module owns ORC execution. Its entry points [`jit::run`] and
//! [`jit::run_mono`] are re-exported at the crate root. The other modules:
//!
//! - [`layout`]: the LLVM representation of Brass types and the declarations
//!   of the runtime's C-ABI primitives;
//! - [`monomorph`]: LLVM symbol names for monomorphized instances;
//! - [`dispatch`]: runtime resolution of the lazy JIT's deferred call sites;
//! - [`ownership`]: the ownership analysis and rewrite for `spawn` captures,
//!   run over the AST before name resolution;
//! - [`closure`]: name-collection helpers over closure bodies.

pub mod closure;
pub mod codegen;
pub mod dispatch;
pub mod jit;
pub mod layout;
pub mod monomorph;
pub mod ownership;

pub use codegen::LlvmCodegen;
pub use dispatch::{ResolvedSession, prime_resolved, resolved_session};
pub use jit::orc::OrcContext;
pub use jit::{run, run_mono};
pub use monomorph::mangle_fn;

pub use jit::objcache::{
    JitCacheLocation, JitCacheUsage, clean_jit_cache, disable_jit_cache, jit_cache_location,
    jit_cache_usage,
};
