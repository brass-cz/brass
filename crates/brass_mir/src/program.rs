//! The program-level MIR: every callable in a `brass_hir::Program` lowered to
//! a body, plus the closures they spawn.
//!
//! The collection holds free functions, record and sum methods, and module
//! init bodies, with nested closures gathered into a shared table keyed by
//! [`crate::ClosureId`]. Each item keeps the identifying metadata a back end
//! needs to mangle its symbol and route calls to it.

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
    /// Source body identity shared with checker observations.
    pub source: brass_parser::Span,
    /// Source use creating this closure value, including generalized uses.
    pub created_at: Option<brass_parser::Span>,
    /// Whether each physical capture stores a mutable binding cell.
    pub capture_cells: Vec<bool>,
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
    /// always the inferred form). Monomorphization keeps an instance fallible
    /// only while a block live in that instance holds an error site (see its
    /// `live_fallible_site`).
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
    /// The checker's fully-known return of each unannotated function instance
    /// its call-site elaborations settled, keyed by (function symbol, argument
    /// types). Monomorphization types a call into an instance still being
    /// typed (mutual recursion without annotations) against it.
    pub instance_returns: fxhash::FxHashMap<(String, Vec<brass_hir::Type>), brass_hir::Type>,
    /// The checker's exact-instance aggregate seeds, including spans whose
    /// observed instances agree (see [`brass_hir::InstanceChannel`]):
    /// monomorphization seeds a local whose [`crate::LocalDecl::seed_site`]
    /// is such a span from the entry of the instance it is typing, never
    /// from the span-shared seed.
    pub instance_seeds: brass_hir::InstanceChannel<brass_hir::Type>,
    /// The generated specialization each instance's reflective call
    /// dispatches to, for the calls whose instances key them differently
    /// (lowered as [`crate::Callee::Keyed`]).
    pub instance_dispatch: brass_hir::InstanceChannel<String>,
    /// Checked per-instance field lists for divergent reflection loops.
    pub instance_fields: brass_hir::InstanceChannel<Vec<String>>,
    /// Settled return-origin contracts, keyed by call and enclosing instance.
    pub numeric_calls: brass_hir::NumericCalls,
}
