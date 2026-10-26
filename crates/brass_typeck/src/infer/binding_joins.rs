//! Structural binding sites and their borrowed lexical continuations.

use super::Checker;
use brass_parser::ast::Arg;
use brass_parser::ast::Stmt;
use std::cell::OnceCell;

mod applications;
pub(super) mod numeric;

impl Checker<'_> {
    /// Fork the solver and every mutable checker sidecar together. A probe
    /// owns its writes; callers explicitly select any evidence that escapes.
    pub(super) fn fork_probe(&self) -> Self {
        let mut probe = self.clone();
        probe.completion.active = false;
        probe
    }
}

/// Initialized bindings in one statement sequence. Each ordinal belongs to
/// this sequence, so equal names and nested shadowing cannot merge sites.
pub(super) struct BlockBindings<'s> {
    stmts: &'s [Stmt],
    initialized: Vec<usize>,
    applications: OnceCell<applications::ApplicationIndex<'s>>,
}

impl<'s> BlockBindings<'s> {
    /// Index only this scope's initialized declarations; nested scopes own
    /// their indexes when the checker enters them.
    pub(super) fn new(stmts: &'s [Stmt]) -> Self {
        Self {
            stmts,
            applications: OnceCell::new(),
            initialized: stmts
                .iter()
                .enumerate()
                .filter_map(|(index, stmt)| {
                    matches!(stmt, Stmt::Let { value: Some(_), .. }).then_some(index)
                })
                .collect(),
        }
    }

    /// The binding checked at `index` and its lexical continuation. The
    /// continuation borrows the source, including any nested closure bodies.
    pub(super) fn after(&self, index: usize) -> Option<(&'s Stmt, &'s [Stmt])> {
        self.initialized
            .binary_search(&index)
            .ok()
            .map(|_| (&self.stmts[index], &self.stmts[index + 1..]))
    }

    /// All literal applications of this declaration, when the index can
    /// certify that no alias, shadowing or conditional use needs a probe.
    pub(super) fn literal_calls(&self, name: &str, after: usize) -> Option<Vec<&'s [Arg]>> {
        self.applications
            .get_or_init(|| applications::ApplicationIndex::new(self.stmts))
            .literal_calls(name, after)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use brass_parser::{Span, ast::*};

    #[test]
    fn continuations_borrow_the_owning_scope_after_each_declaration() {
        let binding = |name: &str, at| Stmt::Let {
            pat: Pattern::Binding(name.into(), None, Span::new(at, at + 1)),
            ty: None,
            value: Some(Expr::Int(0, Span::new(at + 2, at + 3))),
            is_const: false,
            span: Span::new(at, at + 3),
        };
        // Repeated spellings identify separate declaration sites. An
        // intervening expression does not create another binding query.
        let stmts = [
            binding("f", 0),
            Stmt::Expr(Expr::Int(1, Span::new(4, 5))),
            binding("f", 6),
        ];
        let index = BlockBindings::new(&stmts);
        let (first, rest) = index.after(0).unwrap();
        assert!(std::ptr::eq(first, &stmts[0]));
        assert!(std::ptr::eq(rest.as_ptr(), stmts[1..].as_ptr()));
        assert_eq!(rest.len(), 2);
        assert!(index.after(1).is_none());
        assert!(index.after(2).unwrap().1.is_empty());
    }
}
