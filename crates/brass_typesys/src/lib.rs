//! The single authority for RELATIONS between Brass types, and for the
//! type-directed analyses the checker and the back ends must agree on:
//!
//! - numeric flow: which implicit conversions exist (`flow`);
//! - numeric literal and operator typing (`operators`) and the value join of
//!   returns, branch values and other value sets (`join`);
//! - usability: structural record satisfaction, declared sum subtyping,
//!   function subtyping and type-test acceptance (`structural`), and the
//!   representation identity storage sites require on top of it (`storage`);
//! - the value-flow leniency of the checker's unification: nullable
//!   stripping, the non-committing flow probe, and which requirements shape
//!   a construction (`valueflow`);
//! - row inference for anonymous-record arguments and their views (`rows`);
//! - default-skeleton constructibility (`defaults`);
//! - reflective decoders: `infer.from` resolution (`convert`) and per-key
//!   specialization (`specialize`).
//!
//! Every pass that needs to DECIDE one of these (the infer checker with its
//! light pre-pass, monomorphization, the JIT code generator, the REPL
//! interpreter, the driver's reflective specialization) asks this crate;
//! none keeps a private copy. Per-type utilities with no second type involved
//! (`peel_modes`, `is_fully_known`, ...) stay in `brass_hir`.

pub mod convert;
pub mod defaults;
pub mod flow;
pub mod join;
pub mod operators;
pub mod rows;
pub mod specialize;
pub mod storage;
pub mod structural;
pub mod valueflow;

pub use defaults::default_constructible;
pub use flow::{Flow, common_numeric_type, numeric_flow, numeric_flows_into};
pub use join::{JoinConflict, JoinOperand, join_values, numeric_element_join};
pub use operators::{
    NumericBinary, NumericLiteral, NumericOperand, OperatorError, common_operand_type,
    int_literal_kind, literal_fits, numeric_binary,
};
pub use rows::{
    ParamRow, Presence, Row, RowField, RowInfo, RowTy, check_row, field_satisfies, view_type,
};
pub use specialize::{Generated, KeyedNeed, mangled_name, specialize_all};
pub use storage::{function_values_keep_representation, same_representation};
pub use structural::{
    function_part_compatible, record_satisfies, record_satisfies_fields, signature_satisfies,
    type_test_accepts, types_compatible, types_invariant,
};
pub use valueflow::{flow_probe, shapes_constructions, strip_nullable};
