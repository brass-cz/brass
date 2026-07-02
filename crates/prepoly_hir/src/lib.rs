//! High-level IR for Prepoly: the type representation and the collected,
//! id-assigned program model the type checker annotates and the code generator
//! consumes.

pub mod hir;
pub mod lower;
pub mod mutation;
pub mod typed;
pub mod types;

pub use hir::{
    CallableSignature, FieldInfo, FunInfo, LoadedModule, MethodInfo, ModuleInit, ParamInfo,
    Program, QualifiedName, RESULT_TYPE_ID, SchemeMethod, TypeInfo, TypeKind, TypeScheme,
    VariantInfo, qualify, resolve_qualified,
};
pub use lower::{LowerError, lower};
pub use mutation::{
    MutationInfo, mutates_root, param_infers_pass_mode, param_is_copied, param_is_immutable_ref,
    param_is_infer, param_is_mut_ref, root_ident,
};
pub use typed::{Constness, Ownership, RegionId, TypedExpr, TypedExprKind, TypedProgram};
pub use types::{
    FloatKind, INFER_VAR, IntKind, NominalInfo, NominalKind, NominalType, STRUCTURAL_RECORD_ID,
    STRUCTURAL_RECORD_NAME, Substitution, Type, common_numeric_type, freshen_infer, index_element,
    int_literal_kind, numeric_flows_into, prim_method_symbol, resolve, structural_record,
};

/// Re-exported so back ends can name source spans (e.g. typed-literal codegen
/// keyed by span) without depending on the lexer crate directly.
pub use prepoly_lexer::Span;
