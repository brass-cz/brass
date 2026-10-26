//! High-level IR for Brass: the type representation and the collected,
//! id-assigned program model the type checker annotates and MIR lowering
//! consumes.

pub mod expand;
pub mod generalize;
pub mod hir;
pub mod instance;
pub mod lower;
pub mod mutation;
pub mod plugin;
pub mod typed;
pub mod typedecl;
pub mod types;

pub use expand::{
    SPAN_SHIFT_UNIT, expand_fields_body, fields_loop_target, keyed_return, unshift_span,
};
pub use generalize::generalized_closure_bindings;
pub use hir::{
    BracedHead, CallableSignature, FieldInfo, FunInfo, GeneratedDecl, LoadedModule, MethodInfo,
    ModuleInit, ParamInfo, PatternScope, PatternTypeHead, Program, QualifiedName,
    RESERVED_FUNCTION_NAMES, RESULT_TYPE_ID, SchemeMethod, TypeAlias, TypeInfo, TypeKind,
    TypeScheme, VariantInfo, definition_is_visible, generated_type_id, generated_type_name,
    qualify, resolve_marker_key, resolve_qualified,
};
pub use instance::{
    InstanceCallable, InstanceChannel, InstanceKey, NumericCallEntry, NumericCalls, NumericLayout,
    instance_key_type, numeric_instance_base,
};
pub use lower::{LowerError, lower, lower_generated_into};
pub use mutation::{
    MutationInfo, ParamDecl, annotated_type_passes_by_copy, mutates_root, mutates_value,
    param_infers_pass_mode, param_is_immutable_ref, param_is_infer, param_is_mut_ref,
    param_receives_copy, root_ident,
};
pub use plugin::{plugin_builtin_code, plugin_builtin_return, plugin_sig_types, plugin_type_code};
pub use typed::{Constness, TypedExpr, TypedExprKind, TypedProgram};
pub use types::{
    FloatKind, INFER_VAR, IntKind, NominalInfo, NominalKind, NominalType, PassingMode,
    RESULT_TYPE_NAME, STRUCTURAL_RECORD_ID, STRUCTURAL_RECORD_NAME, Substitution, Type,
    array_literal_needs_seed, bind_data_self, collapse_nullable, erase_modes, fallible_over,
    freshen_infer, freshen_unknowns, index_element, is_fully_known, mismatch_display, nominal_ref,
    passing_modes_match, peel_modes, prim_method_symbol, primitive_kind_conflict, resolve,
    resolve_with_aliases, split_passing_mode, structural_record, substitute_self, substitute_vars,
    type_key, type_test_matches, type_vars, unrenderable_part,
};

/// Re-exported so back ends can name source spans (e.g. typed-literal codegen
/// keyed by span) without depending on the lexer crate directly.
pub use brass_parser::Span;

/// Scoped capture analysis for source closures.
pub mod captures;
