//! High-level IR for Prepoly: the type representation and the collected,
//! id-assigned program model the type checker annotates and the code generator
//! consumes.

pub mod expand;
pub mod hir;
pub mod lower;
pub mod mutation;
pub mod plugin;
pub mod typed;
pub mod typedecl;
pub mod types;

pub use expand::{
    SPAN_SHIFT_UNIT, expand_fields_body, fields_loop_target, keyed_return, unshift_span,
};
pub use hir::{
    CallableSignature, FieldInfo, FunInfo, LoadedModule, MethodInfo, ModuleInit, ParamInfo,
    Program, QualifiedName, RESERVED_FUNCTION_NAMES, RESULT_TYPE_ID, SchemeMethod, TypeAlias,
    TypeInfo, TypeKind, TypeScheme, VariantInfo, qualify, resolve_qualified,
};
pub use lower::{LowerError, lower};
pub use mutation::{
    MutationInfo, annotated_type_passes_by_copy, mutates_root, mutates_value,
    param_infers_pass_mode, param_is_immutable_ref, param_is_infer, param_is_mut_ref,
    param_receives_copy, root_ident,
};
pub use plugin::{plugin_builtin_code, plugin_builtin_return, plugin_sig_types, plugin_type_code};
pub use typed::{Constness, Ownership, RegionId, TypedExpr, TypedExprKind, TypedProgram};
pub use types::{
    FloatKind, INFER_VAR, IntKind, NominalInfo, NominalKind, NominalType, PassingMode,
    STRUCTURAL_RECORD_ID, STRUCTURAL_RECORD_NAME, Substitution, Type, collapse_nullable,
    freshen_infer, freshen_unknowns, index_element, int_literal_kind, is_fully_known,
    mismatch_display, passing_modes_match, peel_modes, prim_method_symbol, primitive_kind_conflict,
    resolve, split_passing_mode, structural_record, substitute_vars, type_key, type_vars,
};

/// Re-exported so back ends can name source spans (e.g. typed-literal codegen
/// keyed by span) without depending on the lexer crate directly.
pub use prepoly_parser::Span;
