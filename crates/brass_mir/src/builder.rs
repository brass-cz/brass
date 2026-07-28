//! Incremental construction of a [`MirBody`].
//!
//! The builder keeps a "current block" cursor. Lowering pushes statements into
//! it and, when it emits control flow, calls [`BodyBuilder::terminate`] and
//! switches the cursor to a freshly created block. Once a block is terminated,
//! further statement pushes are dropped: this models the fact that source code
//! after a `return`/`break`/`continue` (or after a fully-diverging `if`) is
//! dead, exactly as the AST-walking codegen skips it.
//!
//! Locals are append-only and each is born with a fresh type *variable*
//! ([`TypeRef::Var`]); the body is type-independent until monomorphization.

use crate::cfg::{BasicBlock, LocalDecl, MirBody, MirStmt, Terminator};
use crate::ids::{BlockId, LocalId};
use crate::ty::TypeRef;
use crate::value::{Operand, Rvalue};

/// A block under construction: its terminator is filled in once known.
struct BlockBuf {
    stmts: Vec<MirStmt>,
    term: Option<Terminator>,
}

pub struct BodyBuilder {
    locals: Vec<LocalDecl>,
    blocks: Vec<BlockBuf>,
    cur: BlockId,
}

impl BodyBuilder {
    /// Start a body with a single empty entry block.
    pub fn new() -> Self {
        BodyBuilder {
            locals: Vec::new(),
            blocks: vec![BlockBuf {
                stmts: Vec::new(),
                term: None,
            }],
            cur: BlockId(0),
        }
    }

    /// Allocate a fresh local with a new type variable and an optional source
    /// name. The variable id is the local's own index, giving a stable 1:1 map
    /// that monomorphization can rebind.
    pub fn fresh_local(&mut self, name: Option<String>) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(LocalDecl {
            ty: TypeRef::Var(id.0),
            name,
        });
        id
    }

    /// Allocate a fresh local whose type is fixed by a source annotation
    /// (`let x: T = ...`). Monomorphization seeds such a local with `ty` instead of
    /// inferring it, so an annotation that the inference cannot recover from the
    /// initializer alone (e.g. `let x: int32? = null`) is preserved.
    pub fn fresh_local_typed(&mut self, name: Option<String>, ty: brass_hir::Type) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(LocalDecl {
            ty: TypeRef::Known(ty),
            name,
        });
        id
    }

    /// Create a new, empty, unterminated block. Does not move the cursor.
    pub fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(BlockBuf {
            stmts: Vec::new(),
            term: None,
        });
        id
    }

    /// Move the cursor to `block`. The block must not already be terminated.
    pub fn switch_to(&mut self, block: BlockId) {
        self.cur = block;
    }

    /// Whether the current block already has a terminator. Lowering checks this
    /// to avoid appending after a divergent construct.
    pub fn terminated(&self) -> bool {
        self.blocks[self.cur.index()].term.is_some()
    }

    /// Append a statement to the current block, unless it is already terminated.
    pub fn push(&mut self, stmt: MirStmt) {
        if self.terminated() {
            return;
        }
        self.blocks[self.cur.index()].stmts.push(stmt);
    }

    /// Terminate the current block, unless it already is. The first terminator
    /// wins, matching codegen, where the first `return`/branch ends the block.
    pub fn terminate(&mut self, term: Terminator) {
        let buf = &mut self.blocks[self.cur.index()];
        if buf.term.is_none() {
            buf.term = Some(term);
        }
    }

    /// Assign `rv` to a fresh temporary and return it as an operand. The common
    /// way to three-address a sub-expression.
    pub fn emit(&mut self, rv: Rvalue) -> Operand {
        let tmp = self.fresh_local(None);
        self.push(MirStmt::Assign(tmp, rv));
        Operand::Local(tmp)
    }

    /// Like [`emit`](Self::emit), but the temporary's type is fixed to `ty`
    /// (a `Known` local). Lowering uses this to carry a type the checker already
    /// resolved -- the result type of a call -- so monomorphization seeds it
    /// instead of inferring, which a witness-free constructor's caller needs.
    pub fn emit_known(&mut self, rv: Rvalue, ty: brass_hir::Type) -> Operand {
        let tmp = self.fresh_local_typed(None, ty);
        self.push(MirStmt::Assign(tmp, rv));
        Operand::Local(tmp)
    }

    /// Materialize an operand as a local: locals pass through; constants are
    /// stored into a fresh temporary so the result can be used as a place base
    /// or a projection target.
    pub fn make_local(&mut self, op: Operand) -> LocalId {
        match op {
            Operand::Local(id) => id,
            other => {
                let tmp = self.fresh_local(None);
                self.push(MirStmt::Assign(tmp, Rvalue::Use(other)));
                tmp
            }
        }
    }

    /// Finish the body. Any block still missing a terminator (only the dangling
    /// tail under normal lowering) is closed with `return void`.
    pub fn finish(self, params: Vec<LocalId>, entry: BlockId) -> MirBody {
        let blocks = self
            .blocks
            .into_iter()
            .map(|b| BasicBlock {
                stmts: b.stmts,
                term: b.term.unwrap_or(Terminator::Return(Operand::void())),
            })
            .collect();
        MirBody {
            locals: self.locals,
            blocks,
            entry,
            params,
            declared_fallible: false,
        }
    }
}

impl Default for BodyBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::Terminator;
    use crate::value::Literal;

    #[test]
    fn statements_after_a_terminator_are_dropped() {
        // Once a block is terminated, later pushes are dead code and ignored,
        // and a second terminate does not overwrite the first.
        let mut b = BodyBuilder::new();
        let l = b.fresh_local(None);
        b.terminate(Terminator::Return(Operand::Local(l)));
        b.push(MirStmt::Assign(
            l,
            Rvalue::Use(Operand::Const(Literal::Void)),
        ));
        b.terminate(Terminator::Unreachable);
        let body = b.finish(vec![], BlockId(0));
        assert!(body.blocks[0].stmts.is_empty());
        assert_eq!(body.blocks[0].term, Terminator::Return(Operand::Local(l)));
    }

    #[test]
    fn finish_closes_open_blocks_with_return_void() {
        // A block left without a terminator is closed with `return void`.
        let mut b = BodyBuilder::new();
        let next = b.new_block();
        b.switch_to(next);
        let body = b.finish(vec![], BlockId(0));
        assert_eq!(body.blocks[1].term, Terminator::Return(Operand::void()));
    }
}
