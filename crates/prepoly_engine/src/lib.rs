//! The Prepoly execution engine: monomorphization plus a backend-agnostic
//! code-generation interface that drives MIR to running code.
//!
//! This crate sits between `prepoly_mir` (the type-independent control-flow IR)
//! and a concrete typed back end such as `prepoly_jit_llvm`. It provides:
//!
//!  - [`monomorphize`], which performs *true* single-specialization: it checks a
//!    [`prepoly_mir::MirProgram`] and instantiates every reachable callable into
//!    a [`MonoProgram`] of concrete-typed instances (DESIGN.md 7);
//!  - the [`Codegen`] trait, whose default methods walk the monomorphized MIR and
//!    dispatch to small *typed* leaf operations a back end implements -- every
//!    value has a concrete type, so the back end emits unboxed code and this
//!    crate names no target dependency;
//!  - the [`Engine`], which sequences a back end through compile-and-run.
//!
//! A back end implements [`Codegen`] for a type holding its target state and is
//! handed to [`Engine::run`] together with a [`MonoProgram`].

mod codegen;
mod engine;
mod mir_infer;
mod mono;
mod runtime;

pub use codegen::{Codegen, element_type, program_uses_with, rc_managed};
pub use engine::Engine;
pub use mir_infer::{
    MirTypeError, NullResolver, ProgramResolver, Resolver, StructuralReq, gather_requirements,
    infer_body,
};
pub use mono::{
    MonoFunction, MonoProgram, SYNTH_SIGIL, binary_operand_type, boundary_record_type,
    boundary_record_type_by_id, boundary_record_type_by_name, boundary_record_type_from_fields,
    check_instances, closure_symbol, cond_static_truthiness, float_kind_name, instance_symbol,
    int_kind_name, is_comparison, method_symbol, monomorphize, monomorphize_instance,
    numeric_conv_ret, operand_type_of, parse_structural_descriptor, static_symbol,
};
pub use runtime::{MonomorphCache, RuntimeJit, resolve_or_compile};
