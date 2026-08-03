//! Control-flow completeness. A function or method with an
//! explicit non-`void` return type must produce a value on every path. Without
//! this check a body that falls off its end would yield an undefined value at
//! runtime while still satisfying the declared return type statically.
//!
//! The analysis is intentionally conservative: it only flags bodies that are
//! provably able to reach their end. Genuinely diverging constructs such as
//! `while true { ... }` with no `break` are treated as non-returning so they are
//! never falsely reported.

use brass_hir::{CallableSignature, Program, Type, TypeKind};
use brass_parser::ast::*;

use crate::TypeError;
use crate::exhaustive::{pattern_irrefutable, pattern_names_sum_variant};

/// Report every function/method whose explicit non-`void` return type can be
/// bypassed by falling through the end of the body.
pub fn check(program: &Program) -> Vec<TypeError> {
    check_in(program, crate::AnalysisModules::all())
}

pub(crate) fn check_in(program: &Program, modules: crate::AnalysisModules<'_>) -> Vec<TypeError> {
    let mut errors = Vec::new();
    for f in program.functions.values() {
        if !modules.checks(&f.module) {
            continue;
        }
        check_callable(program, &f.signature, Some(&f.decl.body), &mut errors);
    }
    for info in program.types.values() {
        if !modules.checks(&info.module) {
            continue;
        }
        match &info.kind {
            TypeKind::Record { methods, .. } => {
                for m in methods.values() {
                    if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                        continue;
                    }
                    check_callable(program, &m.signature, m.decl.body.as_ref(), &mut errors);
                }
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    for m in v.methods.values() {
                        if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                            continue;
                        }
                        check_callable(program, &m.signature, m.decl.body.as_ref(), &mut errors);
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
    program: &Program,
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
    if !block_returns(program, body) {
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
/// Inferred return types are not enforced here so that fallthrough remains a
/// `void` return rather than an error. A fallible void return (`-> void!`)
/// is exempt like `void` itself: falling off the end IS the Ok exit (the
/// back ends construct `Ok` on the fall-through path of a fallible body),
/// so completeness has nothing to demand.
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
        Expr::TypeTest(subject, _, _) => check_loop_control_expr(subject, in_loop, errors),
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
fn block_returns(program: &Program, block: &Block) -> bool {
    block.stmts.iter().any(|s| stmt_diverges(program, s))
}

fn stmt_diverges(program: &Program, stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Return(..) => true,
        Stmt::Expr(e) => expr_diverges(program, e),
        Stmt::While { cond, body, .. } => is_infinite_loop(cond, body),
        // A `for` loop may iterate zero times; `let`/`assign` never return;
        // `break`/`continue` leave a loop, not the function.
        _ => false,
    }
}

fn expr_diverges(program: &Program, expr: &Expr) -> bool {
    match expr {
        // An `if` returns on every path only when it has an `else` and both
        // sides return.
        Expr::If(_, then, Some(els), _) => {
            block_returns(program, then) && expr_diverges(program, els)
        }
        Expr::IfLet(_, _, then, Some(els), _) => {
            block_returns(program, then) && expr_diverges(program, els)
        }
        // A `match` returns when every arm returns AND an arm is guaranteed to
        // run: a catch-all (irrefutable) arm, or arms naming a sum's variants
        // (whose coverage the exhaustiveness pass enforces or rejects). Without
        // that guarantee -- e.g. a match over integer literals with no wildcard
        // -- control can fall through every arm at runtime, so the match must
        // not be treated as diverging.
        Expr::Match(_, arms, _) => {
            !arms.is_empty()
                && arms.iter().all(|arm| expr_diverges(program, &arm.body))
                && match_coverage_is_checked(program, arms)
        }
        Expr::Block(block, _) => block_returns(program, block),
        _ => false,
    }
}

/// Whether some static check guarantees one of the match's arms runs: an
/// irrefutable (catch-all) arm always matches, and a match whose arms name sum
/// variants is verified exhaustive by the exhaustiveness pass (or rejected
/// there). A match over non-sum scrutinees (int/string literals) with no
/// catch-all has no such guarantee.
fn match_coverage_is_checked(program: &Program, arms: &[MatchArm]) -> bool {
    arms.iter()
        .any(|arm| pattern_irrefutable(program, &arm.pattern))
        || arms
            .iter()
            .any(|arm| pattern_names_sum_variant(program, &arm.pattern))
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
        Expr::TypeTest(subject, _, _) => expr_has_break(subject),
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
