//! Match exhaustiveness: a match whose arms reference variants
//! of a sum type must cover every variant unless a catch-all (wildcard or
//! whole-value binding) is present.

use std::collections::HashSet;

use prepoly_hir::{Program, TypeKind};
use prepoly_lexer::Span;
use prepoly_parser::ast::*;

use crate::TypeError;
use crate::walk::{ExprVisitor, walk_program_exprs};

pub fn check(program: &Program) -> Vec<TypeError> {
    let mut v = ExhaustiveVisitor {
        program,
        errors: Vec::new(),
    };
    walk_program_exprs(program, &mut v);
    v.errors
}

struct ExhaustiveVisitor<'a> {
    program: &'a Program,
    errors: Vec<TypeError>,
}

impl ExprVisitor for ExhaustiveVisitor<'_> {
    fn visit(&mut self, e: &Expr) {
        if let Expr::Match(_, arms, span) = e {
            self.check_match(arms, *span);
        }
    }
}

impl ExhaustiveVisitor<'_> {
    fn owning_sum(&self, vname: &str) -> Option<String> {
        for (tn, info) in &self.program.types {
            if let TypeKind::Sum { variants } = &info.kind
                && variants.iter().any(|v| v.name == vname)
            {
                return Some(tn.clone());
            }
        }
        None
    }

    /// Whether a record field sub-pattern always matches. Shorthand `{ name }`
    /// (no sub-pattern) binds the field and is irrefutable.
    fn field_irrefutable(&self, f: &FieldPat) -> bool {
        match &f.pat {
            None => true,
            Some(p) => self.pattern_irrefutable(p),
        }
    }

    /// Whether a pattern matches every value of its type, so an arm built from it
    /// exhausts what it is matched against. A literal, a fixed-length array
    /// destructure (refutable on length), a nested variant test, or any compound
    /// containing one is refutable.
    fn pattern_irrefutable(&self, p: &Pattern) -> bool {
        match p {
            Pattern::Wildcard(_) => true,
            // A bare name is an irrefutable binding unless it names a variant, in
            // which case it is a refutable unit-variant test on the field.
            Pattern::Binding(n, _) => self.owning_sum(n).is_none(),
            Pattern::Record(_, fields, _) => fields.iter().all(|f| self.field_irrefutable(f)),
            Pattern::Literal(_, _) | Pattern::Array(_, _) => false,
        }
    }

    fn check_match(&mut self, arms: &[MatchArm], span: Span) {
        let mut owner = None;
        for a in arms {
            let name = match &a.pattern {
                Pattern::Record(n, _, _) | Pattern::Binding(n, _) => Some(n.as_str()),
                _ => None,
            };
            if let Some(n) = name
                && let Some(t) = self.owning_sum(n)
            {
                owner = Some(t);
                break;
            }
        }
        let Some(owner) = owner else { return };
        let TypeKind::Sum { variants } = &self.program.types[&owner].kind else {
            return;
        };
        let all: Vec<String> = variants.iter().map(|v| v.name.clone()).collect();
        let mut covered: HashSet<String> = HashSet::new();
        let mut catch_all = false;
        for a in arms {
            match &a.pattern {
                Pattern::Wildcard(_) => catch_all = true,
                Pattern::Record(n, fields, _) => {
                    // A variant pattern covers the variant only when every field
                    // sub-pattern is irrefutable; a refutable one (e.g. a literal
                    // `Both { left: 1, .. }`) matches only some of the variant's
                    // values, so the rest must still be handled by another arm or a
                    // catch-all -- otherwise an unmatched value reaches `unreachable`.
                    if fields.iter().all(|f| self.field_irrefutable(f)) {
                        covered.insert(n.clone());
                    }
                }
                Pattern::Binding(n, _) => {
                    if all.contains(n) {
                        covered.insert(n.clone());
                    } else {
                        catch_all = true;
                    }
                }
                _ => {}
            }
        }
        if !catch_all {
            let missing: Vec<&str> = all
                .iter()
                .filter(|v| !covered.contains(*v))
                .map(|s| s.as_str())
                .collect();
            if !missing.is_empty() {
                tracing::debug!(sum = %owner, missing = ?missing, "non-exhaustive match");
                self.errors.push(TypeError {
                    message: format!(
                        "non-exhaustive match on `{owner}`: missing variant(s) {}",
                        missing.join(", ")
                    ),
                    span,
                });
            }
        }
    }
}
