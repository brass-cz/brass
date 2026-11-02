//! Effects of an instantiated walk without a record co-return-link owner.
//!
//! A closed sum's declaration frame has no open field cells and contributes no
//! record scheme. Its open parameters and return are not shared scheme cells.
//! Nested ordinary calls bind arguments/receiver instances, not the callee's
//! declaration frame, and cannot install a co owner. Local arrays, fresh nominal
//! instances, field reads and return reconciliation therefore cannot write a
//! record scheme. Bare nominal annotations and narrowed views are separately
//! rejected when they can expose another declaration's open cells.
//! Global reads remain conservative: constraining a value read
//! from an open global can change that cell without a syntactic assignment.
//!
//! Virtual calls include the entire source family, not just inhabited receivers;
//! this proof cannot use execution reachability to hide a possible shared write.
//! Unresolved callback calls retain the body. Callable field producers are
//! covered by value edges, capture barriers and global dependencies.
//! Builtin typing only constrains
//! its operands; source shadowing and source hook bodies are visited separately.

use super::{Edges, Expr};

mod borrowed;

impl Edges<'_, '_> {
    /// Track external callable effects without treating private inference cells
    /// as record scheme cells. Value and virtual edges remain conservative.
    pub(super) fn rootless_expression(&mut self, expr: &Expr) {
        self.borrowed_pattern_effect(expr);
        if matches!(expr, Expr::SelfExpr(_))
            && !self.locals.contains("self")
            && self.owner.is_some_and(|owner| {
                crate::reachability::certificate::borrows_layout(self.index, &owner.type_ref())
            })
        {
            self.rootless
                .shared_cells
                .insert(self.site(expr, "static self layout"));
        }
        if let Expr::Ident(name, _) = expr
            && let Some(function) = self.names.function(name)
        {
            self.rootless_calls
                .push(self.index.functions[function.symbol.as_str()]);
        }
        if matches!(expr, Expr::Str(parts, _) if parts.iter().any(|p| matches!(p, brass_parser::ast::StrSeg::Expr(_))))
        {
            self.rootless_calls
                .extend(self.method_targets(None, brass_hir::rendering::DISPLAY_METHOD));
        }
        let Expr::Call(callee, _, _) = expr else {
            return;
        };
        let exact = self.exact_call_targets(callee);
        if !exact.is_empty() {
            self.rootless_calls.extend(exact);
            return;
        }
        let opaque = match callee.as_ref() {
            Expr::Ident(name, _) => {
                self.locals.contains(name)
                    || !matches!(name.as_str(), "fields" | "typeof")
                        && brass_hir::builtin_returns::builtin_return(name, || false).is_none()
            }
            Expr::Field(base, name, _) => {
                // Primitive static conversions cannot dispatch to a nominal
                // method with the same spelling.
                if let Some(class) = self.qualifier_class(base) {
                    if class == "string" && name == "from" {
                        self.rootless_calls.extend(
                            self.method_targets(None, brass_hir::rendering::DISPLAY_METHOD),
                        );
                    }
                    return;
                }
                self.rootless_calls
                    .extend(self.method_targets(self.receiver(base), name));
                if name == "debug" {
                    self.rootless_calls
                        .extend(self.method_targets(None, brass_hir::rendering::DISPLAY_METHOD));
                }
                // Callable field producers cannot be invisible to this proof:
                // function values add their body edge, closures taint captures,
                // and globals taint reads. An open formal input has no concrete
                // closure body for the checker to instantiate. Source virtual
                // implementations still range over the complete catalog.
                !(self.index.families.contains_key(name.as_str())
                    || self.index.primitive_families.contains_key(name.as_str())
                    || matches!(
                        name.as_str(),
                        "push"
                            | "pop"
                            | "insert"
                            | "remove"
                            | "len"
                            | "from"
                            | "default"
                            | "parse"
                            | "debug"
                            | "context"
                    ))
            }
            _ => true,
        };
        if opaque {
            self.rootless
                .unknown_calls
                .insert(self.site(expr, "opaque callable"));
        }
    }
}
