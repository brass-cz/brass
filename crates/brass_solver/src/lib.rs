//! The type-inference constraint solver: a persistent union-find substitution
//! over `brass_hir::Type` with occurs check, snapshot/rollback and
//! inference-variable classification. It is the type-variable store of the
//! checker (`brass_typeck`) and of the value-flow probe and the value join in
//! `brass_typesys`, so all of them resolve type variables with the same
//! unification semantics. Monomorphization and the back ends see only
//! resolved types and do not use it.

pub mod solver;
pub mod unify;
