//! Control-flow completeness. A function or method with an
//! explicit non-`void` return type must produce a value on every path. Without
//! this check a body that falls off its end would yield an undefined value at
//! runtime while still satisfying the declared return type statically. The
//! module also rejects `break`/`continue` outside of a loop.
//!
//! The analysis is syntactic and conservative: a body passes only when every
//! path provably ends in a `return` or diverges. Constructs that diverge by
//! their shape count -- an `if`/`else` whose both sides do, a `match` whose
//! arms all do and one of which must run, `while true { ... }` with no
//! `break` -- but conditions are not evaluated, so a body whose last
//! `return` sits behind a condition that always holds is still reported.
//! Inferred-return checking also supplies this instance's `never` expressions
//! and static branch choices, without changing the types of branch values.

use brass_hir::{CallableSignature, Program, Type, TypeKind};
use brass_parser::Span;
use brass_parser::ast::*;
use fxhash::{FxHashMap, FxHashSet};

use crate::TypeError;
use crate::exhaustive::{pattern_irrefutable, pattern_names_sum_variant};

/// The program and the module whose body is analyzed: pattern names resolve
/// against that module's scope (a bare name is a variant test only where its
/// sum is in scope).
#[derive(Clone, Copy)]
struct Scope<'a> {
    program: &'a Program,
    module: &'a [String],
    diverging_exprs: Option<&'a FxHashSet<Span>>,
    static_folds: Option<&'a FxHashMap<Span, bool>>,
}

/// Report every function/method whose explicit non-`void` return type can be
/// bypassed by falling through the end of the body, and every
/// `break`/`continue` outside of a loop.
pub fn check(program: &Program) -> Vec<TypeError> {
    check_in(program, crate::AnalysisModules::all())
}

/// [`check`] over the modules `modules` checks.
pub(crate) fn check_in(program: &Program, modules: crate::AnalysisModules<'_>) -> Vec<TypeError> {
    let mut errors = Vec::new();
    for f in program.functions.values() {
        if !modules.checks(&f.module) || !modules.checks_body(f.decl.span) {
            continue;
        }
        check_callable(
            Scope {
                program,
                module: &f.module,
                diverging_exprs: None,
                static_folds: None,
            },
            &f.signature,
            Some(&f.decl.body),
            &mut errors,
        );
    }
    for info in program.types.values() {
        if !modules.checks(&info.module) {
            continue;
        }
        match &info.kind {
            TypeKind::Record { methods, .. } => {
                for m in methods.values() {
                    if !modules.checks_body(m.decl.span) {
                        continue;
                    }
                    if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                        continue;
                    }
                    check_callable(
                        Scope {
                            program,
                            module: &info.module,
                            diverging_exprs: None,
                            static_folds: None,
                        },
                        &m.signature,
                        m.decl.body.as_ref(),
                        &mut errors,
                    );
                }
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    for m in v.methods.values() {
                        if !modules.checks_body(m.decl.span) {
                            continue;
                        }
                        if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                            continue;
                        }
                        check_callable(
                            Scope {
                                program,
                                module: &info.module,
                                diverging_exprs: None,
                                static_folds: None,
                            },
                            &m.signature,
                            m.decl.body.as_ref(),
                            &mut errors,
                        );
                    }
                }
            }
        }
    }
    for init in &program.inits {
        if !modules.checks(&init.path) {
            continue;
        }
        check_loop_control(&init.stmts, false, &mut errors);
    }
    errors
}

fn check_callable(
    scope: Scope<'_>,
    sig: &CallableSignature,
    body: Option<&Block>,
    errors: &mut Vec<TypeError>,
) {
    if let Some(body) = body {
        check_loop_control(&body.stmts, false, errors);
    }
    let Some(ret) = non_void_return(sig) else {
        return;
    };
    let Some(body) = body else {
        return;
    };
    if !block_returns(scope, body) {
        let span = sig.ret.as_ref().map(|r| r.span()).unwrap_or(sig.span);
        errors.push(TypeError {
            message: format!(
                "function `{}` may finish without returning a value of type `{}`",
                sig.name,
                ret.display()
            ),
            span,
        });
    }
}

/// The declared return type when it is explicitly annotated and not `void`.
/// An unannotated return is not enforced here: its type is the join of the
/// body's `return`s, which the infer pass decides. A fallible void return
/// (`-> void!`) is exempt like `void` itself: falling off the end IS the Ok
/// exit (the back ends construct `Ok` on the fall-through path of a fallible
/// body), so completeness has nothing to demand.
fn non_void_return(sig: &CallableSignature) -> Option<&Type> {
    sig.ret.as_ref()?;
    match sig.ret_ty.as_ref()? {
        Type::Void => None,
        ty if ty
            .result_payloads()
            .is_some_and(|(ok, _)| matches!(ok, Type::Void)) =>
        {
            None
        }
        ty => Some(ty),
    }
}

/// Report `break`/`continue` that are not inside a loop. `in_loop` is true only
/// within `while`/`for` bodies of the same function; a closure resets it because
/// its `break` cannot bind to an enclosing loop.
fn check_loop_control(stmts: &[Stmt], in_loop: bool, errors: &mut Vec<TypeError>) {
    for stmt in stmts {
        match stmt {
            Stmt::Break(span) if !in_loop => errors.push(TypeError {
                message: "`break` outside of a loop".to_string(),
                span: *span,
            }),
            Stmt::Continue(span) if !in_loop => errors.push(TypeError {
                message: "`continue` outside of a loop".to_string(),
                span: *span,
            }),
            Stmt::Break(_) | Stmt::Continue(_) => {}
            Stmt::While { cond, body, .. } => {
                check_loop_control_expr(cond, in_loop, errors);
                check_loop_control(&body.stmts, true, errors);
            }
            Stmt::For { iter, body, .. } => {
                check_loop_control_expr(iter, in_loop, errors);
                check_loop_control(&body.stmts, true, errors);
            }
            Stmt::Let {
                value: Some(value), ..
            } => check_loop_control_expr(value, in_loop, errors),
            Stmt::Let { value: None, .. } => {}
            Stmt::Assign { target, value, .. } => {
                check_loop_control_expr(target, in_loop, errors);
                check_loop_control_expr(value, in_loop, errors);
            }
            Stmt::Expr(e) => check_loop_control_expr(e, in_loop, errors),
            Stmt::Return(Some(e), _) => check_loop_control_expr(e, in_loop, errors),
            Stmt::Return(None, _) => {}
        }
    }
}

/// Walk every expression position that can contain a statement block (and thus
/// a `break`/`continue`): a partial walk here would let loop-control hide in a
/// call argument or an operand and slip past the guard.
fn check_loop_control_expr(expr: &Expr, in_loop: bool, errors: &mut Vec<TypeError>) {
    match expr {
        Expr::TypeTest(subject, _, _, _) => check_loop_control_expr(subject, in_loop, errors),
        Expr::If(cond, then, els, _) => {
            check_loop_control_expr(cond, in_loop, errors);
            check_loop_control(&then.stmts, in_loop, errors);
            if let Some(els) = els {
                check_loop_control_expr(els, in_loop, errors);
            }
        }
        Expr::IfLet(_, scrut, then, els, _) => {
            check_loop_control_expr(scrut, in_loop, errors);
            check_loop_control(&then.stmts, in_loop, errors);
            if let Some(els) = els {
                check_loop_control_expr(els, in_loop, errors);
            }
        }
        Expr::Match(scrut, arms, _) => {
            check_loop_control_expr(scrut, in_loop, errors);
            for arm in arms {
                check_loop_control_expr(&arm.body, in_loop, errors);
            }
        }
        Expr::Block(block, _) => check_loop_control(&block.stmts, in_loop, errors),
        // A closure introduces a new control-flow scope; its body cannot break
        // an enclosing loop.
        Expr::Closure(_, body, _) => check_loop_control_expr(body, false, errors),
        Expr::Unary(_, a, _) | Expr::ErrorProp(a, _) | Expr::Field(a, _, _) => {
            check_loop_control_expr(a, in_loop, errors)
        }
        Expr::Binary(_, a, b, _) | Expr::Range(a, b, _) | Expr::Index(a, b, _) => {
            check_loop_control_expr(a, in_loop, errors);
            check_loop_control_expr(b, in_loop, errors);
        }
        Expr::Call(callee, args, _) => {
            check_loop_control_expr(callee, in_loop, errors);
            for a in args {
                check_loop_control_expr(&a.expr, in_loop, errors);
            }
        }
        Expr::Array(items, _) => {
            for e in items {
                check_loop_control_expr(e, in_loop, errors);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, e) in fields {
                check_loop_control_expr(e, in_loop, errors);
            }
        }
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(e) = seg {
                    check_loop_control_expr(e, in_loop, errors);
                }
            }
        }
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => {}
    }
}

/// True when control cannot fall off the end of the block: every path either
/// returns or diverges. A diverging statement makes the rest of the block
/// unreachable, so the presence of any diverging statement is sufficient.
/// `diverging_exprs` and `static_folds` are facts from checking this instance.
pub(crate) fn block_diverges(
    program: &Program,
    module: &[String],
    block: &Block,
    diverging_exprs: &FxHashSet<Span>,
    static_folds: &FxHashMap<Span, bool>,
) -> bool {
    block_returns(
        Scope {
            program,
            module,
            diverging_exprs: Some(diverging_exprs),
            static_folds: Some(static_folds),
        },
        block,
    )
}

fn block_returns(scope: Scope<'_>, block: &Block) -> bool {
    block.stmts.iter().any(|s| stmt_diverges(scope, s))
}

fn stmt_diverges(scope: Scope<'_>, stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Return(..) => true,
        Stmt::Expr(e) => expr_diverges(scope, e),
        Stmt::Let {
            value: Some(value), ..
        } => expr_diverges(scope, value),
        Stmt::Let { value: None, .. } => false,
        Stmt::Assign { target, value, .. } => {
            expr_diverges(scope, value) || expr_diverges(scope, target)
        }
        Stmt::While { cond, body, .. } => {
            expr_diverges(scope, cond) || is_infinite_loop(cond, body)
        }
        // A `for` loop may iterate zero times, but its iterand is always
        // evaluated before that decision.
        Stmt::For { iter, .. } => expr_diverges(scope, iter),
        // `break`/`continue` leave a loop, not the function.
        Stmt::Break(_) | Stmt::Continue(_) => false,
    }
}

fn expr_diverges(scope: Scope<'_>, expr: &Expr) -> bool {
    if scope
        .diverging_exprs
        .is_some_and(|spans| spans.contains(&expr.span()))
    {
        return true;
    }
    match expr {
        Expr::Unary(_, inner, _) | Expr::Field(inner, _, _) | Expr::TypeTest(inner, _, _, _) => {
            expr_diverges(scope, inner)
        }
        // Literal absence and the reserved error constructor have no success
        // path, so propagating either always leaves the enclosing callable.
        Expr::ErrorProp(inner, _) => {
            expr_diverges(scope, inner)
                || matches!(&**inner, Expr::Null(_))
                || matches!(&**inner, Expr::Call(callee, _, _)
                    if matches!(&**callee, Expr::Ident(name, _) if name == "error"))
        }
        Expr::Binary(op, left, right, _) => {
            expr_diverges(scope, left)
                || binary_rhs_is_unconditional(*op, left) && expr_diverges(scope, right)
        }
        Expr::Index(base, index, _) | Expr::Range(base, index, _) => {
            expr_diverges(scope, base) || expr_diverges(scope, index)
        }
        Expr::Call(callee, args, _) => {
            expr_diverges(scope, callee) || args.iter().any(|arg| expr_diverges(scope, &arg.expr))
        }
        // Constructing a closure does not evaluate its body.
        Expr::Closure(..) => false,
        Expr::Array(items, _) => items.iter().any(|item| expr_diverges(scope, item)),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            fields.iter().any(|(_, value)| expr_diverges(scope, value))
        }
        Expr::Str(segments, _) => segments.iter().any(|segment| match segment {
            StrSeg::Expr(inner) => expr_diverges(scope, inner),
            StrSeg::Lit(_) => false,
        }),
        // A decided test follows its chosen arm; otherwise both arms must
        // return. The condition is evaluated on every path first.
        Expr::If(cond, then, els, span) | Expr::IfLet(_, cond, then, els, span) => {
            expr_diverges(scope, cond)
                || match scope
                    .static_folds
                    .and_then(|folds| folds.get(span).or_else(|| folds.get(&cond.span())))
                {
                    Some(true) => block_returns(scope, then),
                    Some(false) => els.as_deref().is_some_and(|els| expr_diverges(scope, els)),
                    None => els
                        .as_deref()
                        .is_some_and(|els| block_returns(scope, then) && expr_diverges(scope, els)),
                }
        }
        // A `match` returns when every arm returns AND an arm is guaranteed to
        // run: a catch-all (irrefutable) arm, or arms naming a sum's variants
        // (whose coverage the exhaustiveness pass enforces or rejects). Without
        // that guarantee -- e.g. a match over integer literals with no wildcard
        // -- control can fall through every arm at runtime, so the match must
        // not be treated as diverging.
        Expr::Match(scrutinee, arms, _) => {
            expr_diverges(scope, scrutinee)
                || !arms.is_empty()
                    && arms.iter().all(|arm| expr_diverges(scope, &arm.body))
                    && match_coverage_is_checked(scope, arms)
        }
        Expr::Block(block, _) => block_returns(scope, block),
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => false,
    }
}

/// Logical RHS operands are short-circuited unless the literal LHS forces
/// their evaluation; every other binary operator evaluates both operands.
fn binary_rhs_is_unconditional(op: BinOp, left: &Expr) -> bool {
    match op {
        BinOp::And => matches!(left, Expr::Bool(true, _)),
        BinOp::Or => matches!(left, Expr::Bool(false, _)),
        _ => true,
    }
}

/// Whether some static check guarantees one of the match's arms runs: an
/// irrefutable (catch-all) arm always matches, and a match whose arms name sum
/// variants is verified exhaustive by the exhaustiveness pass (or rejected
/// there). A match over non-sum scrutinees (int/string literals) with no
/// catch-all has no such guarantee.
fn match_coverage_is_checked(scope: Scope<'_>, arms: &[MatchArm]) -> bool {
    arms.iter()
        .any(|arm| pattern_irrefutable(scope.program, scope.module, &arm.pattern))
        || arms
            .iter()
            .any(|arm| pattern_names_sum_variant(scope.program, scope.module, &arm.pattern))
}

/// A `while true { ... }` with no `break` reachable in its own body never
/// terminates, so a function ending in one cannot fall through.
fn is_infinite_loop(cond: &Expr, body: &Block) -> bool {
    matches!(cond, Expr::Bool(true, _)) && !block_has_break(body)
}

fn block_has_break(block: &Block) -> bool {
    block.stmts.iter().any(stmt_has_break)
}

fn stmt_has_break(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Break(_) => true,
        Stmt::Expr(e) => expr_has_break(e),
        Stmt::Let { value, .. } => value.as_ref().is_some_and(expr_has_break),
        Stmt::Assign { target, value, .. } => expr_has_break(target) || expr_has_break(value),
        Stmt::Return(Some(e), _) => expr_has_break(e),
        // A `break` inside a nested loop's BODY binds to that loop, so it does
        // not make the enclosing loop terminable. The condition/iterand,
        // however, is lowered before the nested loop's targets exist, so a
        // break there binds outward.
        Stmt::While { cond, .. } => expr_has_break(cond),
        Stmt::For { iter, .. } => expr_has_break(iter),
        Stmt::Return(None, _) | Stmt::Continue(_) => false,
    }
}

/// Walk every expression position that can hide a statement block with a
/// `break` binding to the enclosing loop. Missing a position here makes a
/// breakable `while true` look infinite, which then vouches for a missing
/// return the loop does not actually guarantee.
fn expr_has_break(expr: &Expr) -> bool {
    match expr {
        Expr::TypeTest(subject, _, _, _) => expr_has_break(subject),
        Expr::If(cond, then, els, _) => {
            expr_has_break(cond)
                || block_has_break(then)
                || els.as_deref().is_some_and(expr_has_break)
        }
        Expr::IfLet(_, scrut, then, els, _) => {
            expr_has_break(scrut)
                || block_has_break(then)
                || els.as_deref().is_some_and(expr_has_break)
        }
        Expr::Match(scrut, arms, _) => {
            expr_has_break(scrut) || arms.iter().any(|arm| expr_has_break(&arm.body))
        }
        Expr::Block(block, _) => block_has_break(block),
        // A closure's `break` binds inside the closure, not to this loop.
        Expr::Closure(..) => false,
        Expr::Unary(_, a, _) | Expr::ErrorProp(a, _) | Expr::Field(a, _, _) => expr_has_break(a),
        Expr::Binary(_, a, b, _) | Expr::Range(a, b, _) | Expr::Index(a, b, _) => {
            expr_has_break(a) || expr_has_break(b)
        }
        Expr::Call(callee, args, _) => {
            expr_has_break(callee) || args.iter().any(|a| expr_has_break(&a.expr))
        }
        Expr::Array(items, _) => items.iter().any(expr_has_break),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            fields.iter().any(|(_, e)| expr_has_break(e))
        }
        Expr::Str(segs, _) => segs.iter().any(|seg| match seg {
            StrSeg::Expr(e) => expr_has_break(e),
            _ => false,
        }),
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => false,
    }
}
