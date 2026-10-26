//! The Brass execution engine: monomorphization plus a backend-agnostic
//! code-generation interface that drives MIR to running code.
//!
//! This crate sits between `brass_mir` (the type-independent control-flow IR)
//! and a concrete typed back end such as `brass_jit_llvm`. It provides:
//!
//!  - [`monomorphize`] (and the lazy pipeline's [`monomorphize_entry`] and
//!    [`monomorphize_instance_deferred`]), which performs *true*
//!    single-specialization: it types a [`brass_mir::MirProgram`] per call
//!    instance and collects every reachable callable into a [`MonoProgram`]
//!    of concrete-typed instances;
//!  - the [`Codegen`] trait, whose default methods walk the monomorphized MIR and
//!    dispatch to small *typed* leaf operations a back end implements -- every
//!    value has a concrete type, so the back end emits unboxed code and this
//!    crate names no target dependency;
//!  - the [`Engine`], which sequences a back end through compile-and-run.
//!
//! A back end implements [`Codegen`] for a type holding its target state.
//! [`Engine::run`] is the plain compile-and-run sequence over such a back end;
//! the LLVM JIT drives the same trait from its own lazy, per-function session.
//! The REPL interpreter executes a [`MonoProgram`] directly and shares the
//! engine's type queries, equality and rendering rules instead.

mod codegen;
mod engine;
mod equality;
mod mono;
mod render;

pub use codegen::{
    Codegen, ViewFieldPlan, aggregate_field_type, batch_spawns, element_type, program_uses_with,
    rc_managed, record_field_names, record_field_type, record_from_field_flows,
    record_from_succeeds, result_ok_type, spawn_precompile, str_const, strip_wrappers,
    view_field_plans,
};
pub use engine::Engine;
pub use equality::{EqualityKind, equality_defined, equality_kind};
pub use mono::{
    DeferredSig, MonoFunction, MonoProgram, MonoSession, MonoStop, SYNTH_SIGIL,
    binary_operand_type, closure_symbol, cond_static_truthiness, display_instance, float_kind_name,
    instance_symbol, int_kind_name, is_comparison, method_symbol, monomorphize, monomorphize_entry,
    monomorphize_entry_with_returns, monomorphize_instance_deferred,
    monomorphize_instance_deferred_with_returns, nullable_display_instance, numeric_conv_ret,
    operand_type_of, prim_method_instance, refusal, static_symbol, unwrap_nullable,
};
pub use render::{render_record_fields, render_variant_fields};
