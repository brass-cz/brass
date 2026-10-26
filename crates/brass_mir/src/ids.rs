//! Numeric handles used throughout the MIR.
//!
//! These are plain indices into the per-body local/block tables and into the
//! program-wide closure table. They are newtyped so a `LocalId` can never be
//! confused with a `BlockId`, and so display/debug output stays terse (`_3`,
//! `bb1`, `clo2`).

use std::fmt;

/// Index of a local slot inside one [`crate::MirBody`]. Locals are mutable
/// storage cells, not SSA values: the same id may be assigned in several blocks
/// and read after a control-flow merge (this is what lets `if`/`match`/`&&`
/// lower without phi nodes; see the `lower` module).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct LocalId(pub u32);

/// Index of a basic block inside one [`crate::MirBody`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct BlockId(pub u32);

/// Index of a lowered closure body in [`crate::MirProgram::closures`]. A closure
/// expression lowers to its own body referenced by this id; the enclosing body
/// only keeps the id plus the captured operands.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ClosureId(pub u32);

impl LocalId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl BlockId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl ClosureId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

impl fmt::Display for ClosureId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "clo{}", self.0)
    }
}
