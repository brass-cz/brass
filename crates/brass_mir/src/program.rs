//! The program-level MIR: every callable in a `brass_hir::Program` lowered to
//! a body, plus the closures they spawn.
//!
//! The collection mirrors how the current codegen enumerates work
//! (`codegen::gen_functions`/`gen_inits`): free functions, then record and sum
//! methods, then module init bodies, with nested closures gathered into a shared
//! table keyed by [`crate::ClosureId`]. Each item keeps the identifying metadata
//! a back end needs to mangle its symbol and route calls to it.

use crate::cfg::MirBody;
use crate::ids::{ClosureId, LocalId};

/// A free function body.
pub struct MirFunction {
    /// Source name (display/diagnostics).
    pub name: String,
    /// Globally unique storage/codegen symbol (matches `FunInfo::symbol`).
    pub symbol: String,
    /// Defining module path, needed to resolve calls made from this body.
    pub module: Vec<String>,
    /// Whether the body uses `error(...)`/`expr!`, so its plain returns wrap in
    /// `Result.Ok`. Recorded here so codegen need not re-scan the AST.
    pub fallible: bool,
    pub body: MirBody,
}

/// A record or sum-variant method body.
pub struct MirMethod {
    /// Owning type's source name.
    pub type_name: String,
    /// Owning type's unique storage symbol (dispatch key).
    pub type_symbol: String,
    /// `Some(variant)` for a sum-variant method, `None` for a record method.
    pub variant: Option<String>,
    /// Method name.
    pub method: String,
    /// The `Self` type name in scope for the body (the owning type's name).
    pub self_type: Option<String>,
    /// Defining module path (the owning type's module), for resolving the type
    /// names this body constructs.
    pub module: Vec<String>,
    pub fallible: bool,
    pub body: MirBody,
}

/// A lowered closure body. `params` and `captures` are locals *within* `body`;
/// the enclosing [`crate::Rvalue::Closure`] supplies the capture operands in the
/// same order as `captures`.
pub struct MirClosure {
    pub id: ClosureId,
    pub params: Vec<LocalId>,
    pub captures: Vec<LocalId>,
    /// Source names of the captured free variables, aligned with `captures`.
    pub capture_names: Vec<String>,
    /// Defining module path (inherited from the enclosing body), for resolving
    /// the type names this closure constructs.
    pub module: Vec<String>,
    /// Whether the body uses `error(...)` or a Result-operand `expr!`: the
    /// closure returns `Result<ok, err>` and a bare `return v` is implicitly
    /// wrapped as `Ok { value: v }`, exactly like a named function whose
    /// unannotated body raises (closures have no return annotation, so this is
    /// always the inferred form). Per instance the backend still requires a
    /// live error site (see the monomorphizer's `live_fallible_site`).
    pub fallible: bool,
    pub body: MirBody,
}

/// A module's top-level initialization body (run once at startup). Top-level
/// `let`/`const` lower to [`crate::MirStmt::SetGlobal`]; other statements run as
/// ordinary code.
pub struct MirInit {
    pub module: Vec<String>,
    pub body: MirBody,
}

/// The whole program lowered to MIR.
#[derive(Default)]
pub struct MirProgram {
    pub functions: Vec<MirFunction>,
    pub methods: Vec<MirMethod>,
    pub closures: Vec<MirClosure>,
    pub inits: Vec<MirInit>,
}
