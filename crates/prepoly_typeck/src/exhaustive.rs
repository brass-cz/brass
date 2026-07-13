//! Match exhaustiveness: a match whose arms reference variants
//! of a sum type must cover every variant unless a catch-all (wildcard or
//! whole-value binding) is present.

use std::collections::HashSet;

use prepoly_hir::{Program, Type, TypeInfo, TypeKind, TypedProgram, peel_modes};
use prepoly_parser::Span;
use prepoly_parser::ast::*;

use crate::TypeError;
use crate::walk::{ExprVisitor, walk_program_exprs};

pub fn check(program: &Program, typed: &TypedProgram) -> Vec<TypeError> {
    let mut v = ExhaustiveVisitor {
        program,
        typed,
        errors: Vec::new(),
    };
    walk_program_exprs(program, &mut v);
    v.errors
}

/// Whether a bare name in a pattern names some sum's variant (a refutable
/// unit-variant test) rather than a plain binding.
fn is_variant_name(program: &Program, name: &str) -> bool {
    !program.sums_containing_variant(name).is_empty()
}

/// Whether a record field sub-pattern always matches. Shorthand `{ name }`
/// (no sub-pattern) binds the field and is irrefutable.
fn field_irrefutable(program: &Program, f: &FieldPat) -> bool {
    match &f.pat {
        None => true,
        Some(p) => pattern_irrefutable(program, p),
    }
}

/// Whether a pattern matches every value of its type, so an arm built from it
/// exhausts what it is matched against. A literal, a fixed-length array
/// destructure (refutable on length), a nested variant test, or any compound
/// containing one is refutable. Shared with the control-flow pass, which only
/// treats a match as diverging when an arm is guaranteed to run.
pub(crate) fn pattern_irrefutable(program: &Program, p: &Pattern) -> bool {
    match p {
        Pattern::Wildcard(_) => true,
        // A bare name is an irrefutable binding unless it names a variant, in
        // which case it is a refutable unit-variant test on the field.
        Pattern::Binding(n, _) => !is_variant_name(program, n),
        Pattern::Record(_, fields, _) => fields.iter().all(|f| field_irrefutable(program, f)),
        Pattern::Literal(_, _) | Pattern::Array(_, _) => false,
    }
}

/// Whether a top-level match arm pattern references a sum variant, meaning the
/// match is covered by this pass's sum-coverage check. Shared with the
/// control-flow pass: a match with neither a catch-all nor variant arms (e.g.
/// all integer literals) is never verified exhaustive, so control can fall
/// through every arm.
pub(crate) fn pattern_names_sum_variant(program: &Program, p: &Pattern) -> bool {
    match p {
        Pattern::Record(n, _, _) | Pattern::Binding(n, _) => is_variant_name(program, n),
        _ => false,
    }
}

struct ExhaustiveVisitor<'a> {
    program: &'a Program,
    typed: &'a TypedProgram,
    errors: Vec<TypeError>,
}

impl ExprVisitor for ExhaustiveVisitor<'_> {
    fn visit(&mut self, e: &Expr) {
        if let Expr::Match(scrutinee, arms, span) = e {
            for id in self.scrutinee_sum_ids(scrutinee) {
                if let Some(sum) = self.program.type_by_id(id).cloned() {
                    self.check_match(&sum, arms, *span);
                }
            }
        }
    }
}

impl ExhaustiveVisitor<'_> {
    /// Every concrete sum inferred for this source scrutinee. Re-elaboration may
    /// record the same expression more than once at different call instances;
    /// checking every distinct nominal id keeps a polymorphic match safe for all
    /// of them instead of letting the last sidecar entry decide coverage.
    fn scrutinee_sum_ids(&self, scrutinee: &Expr) -> Vec<i32> {
        let mut seen = HashSet::new();
        self.typed
            .expressions
            .iter()
            .filter(|expr| expr.span == scrutinee.span())
            .filter_map(|expr| match peel_modes(&expr.ty) {
                Type::Sum(sum) => Some(sum.id),
                _ => None,
            })
            .filter(|id| seen.insert(*id))
            .collect()
    }

    fn check_match(&mut self, sum: &TypeInfo, arms: &[MatchArm], span: Span) {
        let TypeKind::Sum { variants } = &sum.kind else {
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
                    if let Some(variant) = variant_name(sum, n)
                        && fields.iter().all(|f| field_irrefutable(self.program, f))
                    {
                        covered.insert(variant.to_string());
                    }
                }
                Pattern::Binding(n, _) => {
                    if let Some(variant) = variant_name(sum, n) {
                        covered.insert(variant.to_string());
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
                tracing::debug!(sum = %sum.symbol, missing = ?missing, "non-exhaustive match");
                self.errors.push(TypeError {
                    message: format!(
                        "non-exhaustive match on `{}`: missing variant(s) {}",
                        sum.symbol,
                        missing.join(", ")
                    ),
                    span,
                });
            }
        }
    }
}

fn variant_name<'a>(sum: &TypeInfo, pattern_name: &'a str) -> Option<&'a str> {
    if sum.variant(pattern_name).is_some() {
        return Some(pattern_name);
    }
    let unqualified = pattern_name.rsplit('.').next()?;
    sum.variant(unqualified).is_some().then_some(unqualified)
}
