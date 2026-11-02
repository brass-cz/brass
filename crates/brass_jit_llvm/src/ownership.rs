//! Automatic ownership analysis for `spawn` captures.
//!
//! A `spawn` runs its closure on a real OS thread, so each captured value is
//! shared between the spawner and that thread. The decision here is therefore
//! load-bearing, not advisory: [`auto_acquire`] realizes it before the spawn so
//! the capture has an atomic reference count from its first cross-thread
//! reference. A capture that is mutated *anywhere in the function* is made a cown
//! -- its access wrapped in `with` (or the group form `_with_all` when one body
//! touches several cowns), which lock-guards it on both the task and the spawner
//! side; a capture that is genuinely read-only is frozen (deeply immutable).
//! Both are `rc_atomic` owner classes, which is what makes the otherwise-racy
//! cross-thread reference counting sound. [`decide`] classifies captures by
//! liveness and mutation; [`AutoAcquireReport`] records inserted access guards.
//!
//! Spawn arguments the pass can see through are a closure literal or a local
//! bound to one in the same function; any other argument (a parameter, a field,
//! a call result) is rejected with a compile error ([`SpawnError`]) -- an
//! unanalyzed spawn would share its captures with no promotion and no lock,
//! which is exactly the silent data race this pass exists to prevent.
//!
//! [`spawn_capture_summaries`] additionally computes, per function, which
//! parameters are captured by a spawn reachable inside it (iterated to fixpoint
//! over the call graph); [`auto_acquire`] uses the summaries to promote and
//! guard a caller's local that it hands to such a function, so a spawn hidden in
//! a helper still serializes the caller's own accesses.
//!
//! The pass is split by role: `analysis` (captures, mutation, and the per-capture
//! decision), `scopes` (statement-tree traversal and lexical scoping), `sites`
//! (spawn-site shapes and closure-binding resolution), `summaries` (the
//! interprocedural spawn-capture summaries), `prechecks` (spawn shapes rejected
//! before the rewrite), `acquire` (the auto-acquire rewrite), and `guard` (lock
//! roots and the wrapping of guarded accesses).

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use brass_parser::Span;

mod acquire;
mod analysis;
mod guard;
mod prechecks;
mod scopes;
mod sites;
mod summaries;

pub use acquire::auto_acquire;
pub use analysis::{
    CaptureDecision, analyze_spawns, analyze_spawns_stmts, captured, decide, mutates,
    rebound_captures,
};
pub use prechecks::{all_spawn_spans, pre_spawn_errors};
pub use summaries::spawn_capture_summaries;

/// How one `spawn` capture crosses to the spawned thread, as [`decide`]
/// classifies it from liveness and mutation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ownership {
    /// Not live after the spawn: hand exclusive ownership to the thread.
    Move,
    /// Live after the spawn and mutated by no one: freeze (immutable share).
    Freeze,
    /// Mutated anywhere in the function (by the closure, the spawner, or through
    /// an alias), or a parameter whose callers the analysis cannot see: wrap in a
    /// cown with auto-acquire.
    Cown,
}

/// A diagnostic the pass reports through the driver's error path: a `spawn`
/// whose argument it cannot resolve to a closure body. Compiling it silently
/// would hand unguarded shared state to a thread.
#[derive(Clone, Debug)]
pub struct SpawnError {
    pub message: String,
    pub span: Span,
}

/// An access wrapped in an automatic lock in its spawning execution scope.
#[derive(Clone, Debug)]
pub struct GuardedAccess {
    /// The spawned body extent, or `None` for the enclosing function body.
    pub scope: Option<Span>,
    /// The promoted binding whose lock guards the access, including aliases.
    pub root_binding: String,
    /// The source expression or assignment that acquires the lock.
    pub span: Span,
}

/// Diagnostics from the ownership rewrite, including guards on caller accesses.
/// Task-entry and deferred-closure wrappers do not count as caller accesses.
#[derive(Clone, Debug, Default)]
pub struct AutoAcquireReport {
    /// Whether ownership operations or closure-body normalization can rewrite syntax.
    /// False certifies unchanged bodies; true requires re-lowering before reuse.
    pub may_rewrite: bool,
    /// Spawn arguments that the rewrite cannot analyze.
    pub errors: Vec<SpawnError>,
    /// Inserted access guards, before deduplication by execution scope and root.
    pub guarded_accesses: Vec<GuardedAccess>,
}

/// Interprocedural summaries: for each function or method name, the parameter
/// indices (0-based, `self` included for methods) whose argument object is
/// captured by a `spawn` reachable inside the callee. Keyed by bare name -- the
/// pass runs before name resolution -- so same-named functions merge; that only
/// over-approximates (extra promotion/locking), never under.
pub type SpawnSummaries = HashMap<String, HashSet<usize>>;

#[cfg(test)]
mod tests;
