//! The control-flow graph: statements, terminators, basic blocks, and the body
//! that owns them.
//!
//! A [`MirBody`] is a flat list of locals and basic blocks plus an entry block.
//! Each [`BasicBlock`] is a straight-line statement sequence ended by exactly
//! one [`Terminator`]; all branching lives in terminators, so the body is a
//! proper CFG. This is the type-independent shape the whole pipeline shares: it
//! is built once per callable and later walked by codegen,
//! which reinterprets nothing structural and only maps each node to an
//! instruction by type.

use crate::ids::{BlockId, LocalId};
use crate::ty::TypeRef;
use crate::value::{Operand, Place, Rvalue};

/// A straight-line statement. Branching never appears here.
#[derive(Clone, Debug, PartialEq)]
pub enum MirStmt {
    /// `local = rvalue`. The local is (re)written; locals are mutable slots.
    Assign(LocalId, Rvalue),
    /// `place = operand` for a field/element place. Used for `obj.f = v` and
    /// `arr[i] = v`; assigning a bare local uses [`MirStmt::Assign`] instead.
    Store(Place, Operand),
    /// Write a module-level global by source name (`counter = v`, and top-level
    /// `let` initializers in a module init body).
    SetGlobal(String, Operand),
    /// Evaluate an rvalue for its side effects and discard the result (a call
    /// statement, `panic`, an array `push`, ...).
    Eval(Rvalue),
}

/// How a basic block hands control to its successors. Every block has exactly
/// one. These four cover all of Prepoly's control flow once `if`/`while`/`for`/
/// `match`/`if let`/`&&`/`||`/`expr!` have been lowered to blocks.
#[derive(Clone, Debug, PartialEq)]
pub enum Terminator {
    /// Return a value from the enclosing callable.
    Return(Operand),
    /// Unconditional jump.
    Goto(BlockId),
    /// Two-way branch on a boolean operand.
    CondBranch {
        cond: Operand,
        then: BlockId,
        els: BlockId,
    },
    /// No successor: control cannot fall through here (after a `panic`, or an
    /// unmatched `match`).
    Unreachable,
}

/// A basic block: its statements and the terminator that ends it.
#[derive(Clone, Debug, PartialEq)]
pub struct BasicBlock {
    pub stmts: Vec<MirStmt>,
    pub term: Terminator,
}

/// Declaration of one local slot: its (still abstract) type and, for locals
/// that come from a source binding, the source name (kept for readable dumps;
/// codegen does not depend on it).
#[derive(Clone, Debug, PartialEq)]
pub struct LocalDecl {
    pub ty: TypeRef,
    pub name: Option<String>,
}

/// A lowered callable body: a CFG over a flat local table.
#[derive(Clone, Debug, PartialEq)]
pub struct MirBody {
    pub locals: Vec<LocalDecl>,
    pub blocks: Vec<BasicBlock>,
    pub entry: BlockId,
    /// The locals bound to the callable's parameters, in declaration order.
    /// Codegen loads incoming arguments into these.
    pub params: Vec<LocalId>,
}

impl MirBody {
    pub fn local(&self, id: LocalId) -> &LocalDecl {
        &self.locals[id.index()]
    }

    pub fn block(&self, id: BlockId) -> &BasicBlock {
        &self.blocks[id.index()]
    }
}
