//! Mid-level IR for Prepoly: a type-independent control-flow graph that sits
//! between the typed HIR and the back end (MIR lowering).
//!
//! The HIR still carries source AST bodies. This crate lowers each callable body
//! to a [`MirBody`]: a CFG in three-address form where `if`/`while`/`for`/
//! `match`/`if let`/`&&`/`||`/`expr!` are decomposed into basic blocks, and
//! every intermediate value is named by a local. Crucially the lowering is
//! *type-independent*: locals carry type *variables*, not
//! concrete types. The pipeline then concretizes those variables per call
//! instance (monomorphization) and lets a type-driven back end map each node to
//! an instruction. Building the CFG exactly once, here, removes the duplicate
//! control-flow construction the AST-walking codegen does per type path.
//!
//! The entry point is [`lower_program`], which mirrors how codegen enumerates
//! work: free functions, record/sum methods, module init bodies, and the
//! closures they spawn.

mod analysis;
mod builder;
mod cfg;
mod display;
mod ids;
mod lower;
mod program;
mod ty;
mod value;

pub use analysis::{fallible_block, free_vars_of};
pub use cfg::{BasicBlock, LocalDecl, MirBody, MirStmt, Terminator};
pub use display::{body_to_string, program_to_string};
pub use ids::{BlockId, ClosureId, LocalId};
pub use lower::{lower_body, lower_program};
pub use program::{MirClosure, MirFunction, MirInit, MirMethod, MirProgram};
pub use ty::TypeRef;
pub use value::{Callee, Literal, Operand, Place, Projection, Rvalue};
