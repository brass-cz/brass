//! Match exhaustiveness: a match on a value of a sum type must cover every
//! variant unless a catch-all (wildcard or whole-value binding) is present; a
//! variant arm covers its variant only when its field sub-patterns are
//! irrefutable. A nullable sum scrutinee must also cover `null`, with a `null`
//! arm or the catch-all. The sums come from the scrutinee's inferred types
//! (each instantiation's), so this runs after inference.

use fxhash::FxHashSet as HashSet;

use brass_hir::{Program, Type, TypeInfo, TypeKind, TypedExprKind, TypedProgram, peel_modes};
use brass_parser::Span;
use brass_parser::ast::*;

use crate::TypeError;
use crate::walk::{ExprVisitor, walk_program_exprs_in};

/// Check every match of `program` against the scrutinee types recorded in
/// `typed`.
pub fn check(program: &Program, typed: &TypedProgram) -> Vec<TypeError> {
    check_in(program, typed, crate::AnalysisModules::all())
}

/// [`check`] over the modules `modules` checks.
pub(crate) fn check_in(
    program: &Program,
    typed: &TypedProgram,
    modules: crate::AnalysisModules<'_>,
) -> Vec<TypeError> {
    let mut v = ExhaustiveVisitor {
        program,
        typed,
        module: Vec::new(),
        errors: Vec::new(),
    };
    walk_program_exprs_in(program, modules, &mut v);
    v.errors
}

/// [`check`] scoped to one body block. The streaming (lazy) profile runs
/// this right after checking a body (a dedicated pass, or a method body
/// elaborated at a call site), so a non-exhaustive match is reported in that
/// body's own delta -- deterministically, before execution could reach it --
/// instead of only in the terminal whole-program pass, which a stopped lazy
/// run never reaches; the keyed continuation runs it on each generated
/// method. Instantiations recorded later can only ADD required coverage, so
/// the early check under-approximates and never falsely rejects; `check` (run
/// by `brass check` and eager runs) remains the complete verdict. `module` is
/// the module the body belongs to.
pub fn check_block(
    program: &Program,
    typed: &TypedProgram,
    module: &[String],
    block: &Block,
) -> Vec<TypeError> {
    let mut v = ExhaustiveVisitor {
        program,
        typed,
        module: module.to_vec(),
        errors: Vec::new(),
    };
    crate::walk::walk_block(block, &mut v);
    v.errors
}

/// [`check_block`] for a module initializer's statement list.
pub fn check_stmts(
    program: &Program,
    typed: &TypedProgram,
    module: &[String],
    stmts: &[Stmt],
) -> Vec<TypeError> {
    let mut v = ExhaustiveVisitor {
        program,
        typed,
        module: module.to_vec(),
        errors: Vec::new(),
    };
    for s in stmts {
        crate::walk::walk_stmt(s, &mut v);
    }
    v.errors
}

/// Whether an unqualified bare name in a pattern written in `module` names
/// the variant of a sum in scope there (a refutable variant test) rather than
/// a plain binding.
fn is_variant_name(program: &Program, module: &[String], name: &str) -> bool {
    !program.pattern_scope(module).owner_ids(name).is_empty()
}

/// Whether a record field sub-pattern always matches. Shorthand `{ name }`
/// (no sub-pattern) binds the field and is irrefutable.
fn field_irrefutable(program: &Program, module: &[String], f: &FieldPat) -> bool {
    match &f.pat {
        None => true,
        Some(p) => pattern_irrefutable(program, module, p),
    }
}

/// Whether a pattern matches every value of its type, so an arm built from it
/// exhausts what it is matched against. A literal, a fixed-length array
/// destructure (refutable on length), a nested variant test, or any compound
/// containing one is refutable. Shared with the control-flow pass, which only
/// treats a match as diverging when an arm is guaranteed to run. Names
/// resolve in `module`, the module the pattern is written in.
pub(crate) fn pattern_irrefutable(program: &Program, module: &[String], p: &Pattern) -> bool {
    match p {
        Pattern::Wildcard(_) => true,
        // A bare name is an irrefutable binding unless it names a variant in
        // scope, in which case it is a refutable unit-variant test.
        Pattern::Binding(n, qualifier, _) => {
            qualifier.is_none() && !is_variant_name(program, module, n)
        }
        Pattern::Record(_, _, fields, _) => {
            fields.iter().all(|f| field_irrefutable(program, module, f))
        }
        Pattern::Literal(_, _) | Pattern::Array(_, _) => false,
    }
}

/// Whether a top-level match arm pattern references a sum variant, meaning the
/// match is covered by this pass's sum-coverage check. Shared with the
/// control-flow pass: a match with neither a catch-all nor variant arms (e.g.
/// all integer literals) is never verified exhaustive, so control can fall
/// through every arm.
pub(crate) fn pattern_names_sum_variant(program: &Program, module: &[String], p: &Pattern) -> bool {
    match p {
        Pattern::Binding(n, qualifier, _) => {
            qualifier.is_some() || is_variant_name(program, module, n)
        }
        // Module-qualified record heads are dotted type markers, and a head
        // naming only a record type is a plain record pattern.
        Pattern::Record(n, qualifier, _, _) => {
            qualifier.is_some()
                || !matches!(
                    program.braced_pattern_head(module, n),
                    brass_hir::BracedHead::Record
                )
        }
        _ => false,
    }
}

struct ExhaustiveVisitor<'a> {
    program: &'a Program,
    typed: &'a TypedProgram,
    /// The module of the body being walked; pattern names resolve there.
    module: Vec<String>,
    errors: Vec<TypeError>,
}

impl ExprVisitor for ExhaustiveVisitor<'_> {
    fn enter_module(&mut self, module: &[String]) {
        self.module = module.to_vec();
    }

    fn visit(&mut self, e: &Expr) {
        if let Expr::Match(scrutinee, arms, span) = e {
            for (id, nullable) in self.scrutinee_sums(scrutinee) {
                if let Some(sum) = self.program.type_by_id(id).cloned() {
                    self.check_match(&sum, nullable, arms, *span);
                }
            }
        }
    }
}

impl ExhaustiveVisitor<'_> {
    /// Every concrete sum inferred for this source scrutinee, with whether it
    /// is the nullable form `S?`. Re-elaboration may record the same
    /// expression more than once at different call instances; checking every
    /// distinct instance keeps a polymorphic match safe for all of them
    /// instead of letting the last sidecar entry decide coverage.
    fn scrutinee_sums(&self, scrutinee: &Expr) -> Vec<(i32, bool)> {
        let mut seen = HashSet::default();
        self.typed
            .expressions
            .iter()
            // Method-receiver evidence deliberately shares the enclosing call's
            // span; it is not the scrutinee expression's result type.
            .filter(|expr| {
                expr.span == scrutinee.span() && !matches!(expr.kind, TypedExprKind::MethodReceiver)
            })
            .filter_map(|expr| match peel_modes(&expr.ty) {
                Type::Sum(sum) => Some((sum.id, false)),
                Type::Nullable(inner) => match peel_modes(inner) {
                    Type::Sum(sum) => Some((sum.id, true)),
                    _ => None,
                },
                _ => None,
            })
            .filter(|key| seen.insert(*key))
            .collect()
    }

    fn check_match(&mut self, sum: &TypeInfo, nullable: bool, arms: &[MatchArm], span: Span) {
        let TypeKind::Sum { variants } = &sum.kind else {
            return;
        };
        let all: Vec<String> = variants.iter().map(|v| v.name.clone()).collect();
        let mut covered: HashSet<String> = HashSet::default();
        let mut catch_all = false;
        let mut null_covered = !nullable;
        for a in arms {
            match &a.pattern {
                Pattern::Wildcard(_) => catch_all = true,
                Pattern::Literal(lit, _) if matches!(**lit, Expr::Null(_)) => null_covered = true,
                Pattern::Record(n, _, fields, _) => {
                    // A variant pattern covers the variant only when every field
                    // sub-pattern is irrefutable; a refutable one (e.g. a literal
                    // `Both { left: 1, .. }`) matches only some of the variant's
                    // values, so the rest must still be handled by another arm or a
                    // catch-all -- otherwise an unmatched value reaches `unreachable`.
                    if let Some(variant) = variant_name(sum, n)
                        && fields
                            .iter()
                            .all(|f| field_irrefutable(self.program, &self.module, f))
                    {
                        covered.insert(variant.to_string());
                    }
                }
                Pattern::Binding(n, qualifier, _) => {
                    // An unqualified name that is no variant in scope binds
                    // the whole value, whatever variants the sum declares.
                    if qualifier.is_none() && !is_variant_name(self.program, &self.module, n) {
                        catch_all = true;
                    } else if let Some(variant) = variant_name(sum, n) {
                        covered.insert(variant.to_string());
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
            } else if !null_covered {
                self.errors.push(TypeError {
                    message: format!(
                        "non-exhaustive match on `{}?`: `null` is not matched; add a `null` \
                         or `_` arm",
                        sum.symbol
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
