//! Mid-level IR for Brass: a type-independent control-flow graph that sits
//! between the checked HIR and the back ends.
//!
//! The HIR carries source AST bodies. This crate lowers each callable body to
//! a [`MirBody`]: a CFG in three-address form where `if`/`while`/`for`/
//! `match`/`if let`/`&&`/`||`/`expr!` are decomposed into basic blocks, and
//! every intermediate value is named by a local. The lowering is
//! *type-independent*: locals carry type *variables*, except where the
//! checker's span-keyed channels fix a type the operands cannot recover.
//! Monomorphization (`brass_engine`) then concretizes those variables per call
//! instance, and each back end (the LLVM JIT, the REPL interpreter) maps the
//! typed nodes to its own operations, so all of them share one control-flow
//! construction.
//!
//! The entry points are [`lower_program_with_types`] (the whole program, with
//! the checker's channels), [`SubsetLowering`] (the lazy pipeline's
//! on-demand form), and [`lower_program`] (no channels, for tests). Each
//! lowers free functions, record/sum methods, module init bodies, and the
//! closures they spawn.

mod analysis;
mod changed_inputs;
pub use changed_inputs::{ChangedInputs, ChangedKeys};
mod builder;
mod cfg;
mod display;
mod ids;
mod lower;
mod program;
mod promote;
mod ty;
mod value;

pub use analysis::{constructs_error_block, fallible_block, free_vars_of};
pub use cfg::{BasicBlock, LocalDecl, MirBody, MirStmt, Terminator};
pub use display::{body_to_string, program_to_string};
pub use ids::{BlockId, ClosureId, LocalId};
pub use lower::{
    CheckerChannels, LowerTables, LoweringRegion, SubsetLowering, lower_body, lower_program,
    lower_program_with_types, resolve_simple_type,
};
pub use program::{MirClosure, MirFunction, MirInit, MirMethod, MirProgram};
pub use ty::TypeRef;
pub use value::{Callee, Literal, Operand, Place, Projection, Rvalue};
