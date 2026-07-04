//! High-level IR for Prepoly: the type representation and the collected,
//! id-assigned program model the type checker annotates and the code generator
//! consumes.

pub mod expand;
pub mod hir;
pub mod lower;
pub mod mutation;
pub mod typed;
pub mod types;

pub use expand::{
    SPAN_SHIFT_UNIT, expand_fields_body, fields_loop_target, keyed_return, unshift_span,
};
pub use hir::{
    CallableSignature, FieldInfo, FunInfo, LoadedModule, MethodInfo, ModuleInit, ParamInfo,
    Program, QualifiedName, RESULT_TYPE_ID, SchemeMethod, TypeInfo, TypeKind, TypeScheme,
    VariantInfo, qualify, resolve_qualified,
};
pub use lower::{LowerError, lower};
pub use mutation::{
    MutationInfo, annotated_type_passes_by_copy, mutates_root, param_infers_pass_mode,
    param_is_immutable_ref, param_is_infer, param_is_mut_ref, param_receives_copy, root_ident,
};
pub use typed::{Constness, Ownership, RegionId, TypedExpr, TypedExprKind, TypedProgram};
pub use types::{
    FloatKind, INFER_VAR, IntKind, NominalInfo, NominalKind, NominalType, STRUCTURAL_RECORD_ID,
    STRUCTURAL_RECORD_NAME, Substitution, Type, freshen_infer, index_element, int_literal_kind,
    is_fully_known, peel_modes, prim_method_symbol, primitive_kind_conflict, resolve,
    structural_record, type_key,
};

/// Re-exported so back ends can name source spans (e.g. typed-literal codegen
/// keyed by span) without depending on the lexer crate directly.
pub use prepoly_lexer::Span;
