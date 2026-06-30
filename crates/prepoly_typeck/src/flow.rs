//! Control-flow completeness. A function or method with an
//! explicit non-`void` return type must produce a value on every path. Without
//! this check a body that falls off its end would yield an undefined value at
//! runtime while still satisfying the declared return type statically.
//!
//! The analysis is intentionally conservative: it only flags bodies that are
//! provably able to reach their end. Genuinely diverging constructs such as
//! `while true { ... }` with no `break` are treated as non-returning so they are
//! never falsely reported.

use prepoly_hir::{CallableSignature, Program, Type, TypeKind};
use prepoly_parser::ast::*;

use crate::TypeError;

/// Report every function/method whose explicit non-`void` return type can be
/// bypassed by falling through the end of the body.
pub fn check(program: &Program) -> Vec<TypeError> {
    let mut errors = Vec::new();
    for f in program.functions.values() {
        check_callable(&f.signature, Some(&f.decl.body), &mut errors);
    }
    for info in program.types.values() {
        match &info.kind {
            TypeKind::Record { methods, .. } => {
                for m in methods.values() {
                    check_callable(&m.signature, m.decl.body.as_ref(), &mut errors);
                }
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    for m in v.methods.values() {
                        check_callable(&m.signature, m.decl.body.as_ref(), &mut errors);
                    }
                }
            }
        }
    }
    for init in &program.inits {
        check_loop_control(&init.stmts, false, &mut errors);
    }
    errors
}

fn check_callable(sig: &CallableSignature, body: Option<&Block>, errors: &mut Vec<TypeError>) {
    if let Some(body) = body {
        check_loop_control(&body.stmts, false, errors);
    }
    let Some(ret) = non_void_return(sig) else {
        return;
    };
    let Some(body) = body else {
        return;
    };
    if !block_returns(body) {
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
/// `void` return rather than an error.
fn non_void_return(sig: &CallableSignature) -> Option<&Type> {
    sig.ret.as_ref()?;
    match sig.ret_ty.as_ref()? {
        Type::Void => None,
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
            Stmt::While { body, .. } | Stmt::For { body, .. } => {
                check_loop_control(&body.stmts, true, errors);
            }
            Stmt::Let { value, .. } => check_loop_control_expr(value, in_loop, errors),
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

fn check_loop_control_expr(expr: &Expr, in_loop: bool, errors: &mut Vec<TypeError>) {
    match expr {
        Expr::If(_, then, els, _) => {
            check_loop_control(&then.stmts, in_loop, errors);
            if let Some(els) = els {
                check_loop_control_expr(els, in_loop, errors);
            }
        }
        Expr::IfLet(_, _, then, els, _) => {
            check_loop_control(&then.stmts, in_loop, errors);
            if let Some(els) = els {
                check_loop_control_expr(els, in_loop, errors);
            }
        }
        Expr::Match(_, arms, _) => {
            for arm in arms {
                check_loop_control_expr(&arm.body, in_loop, errors);
            }
        }
        Expr::Block(block, _) => check_loop_control(&block.stmts, in_loop, errors),
        // A closure introduces a new control-flow scope; its body cannot break
        // an enclosing loop.
        Expr::Closure(_, body, _) => check_loop_control_expr(body, false, errors),
        _ => {}
    }
}

/// True when control cannot fall off the end of the block: every path either
/// returns or diverges. A diverging statement makes the rest of the block
/// unreachable, so the presence of any diverging statement is sufficient.
fn block_returns(block: &Block) -> bool {
    block.stmts.iter().any(stmt_diverges)
}

fn stmt_diverges(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Return(..) => true,
        Stmt::Expr(e) => expr_diverges(e),
        Stmt::While { cond, body, .. } => is_infinite_loop(cond, body),
        // A `for` loop may iterate zero times; `let`/`assign` never return;
        // `break`/`continue` leave a loop, not the function.
        _ => false,
    }
}

fn expr_diverges(expr: &Expr) -> bool {
    match expr {
        // An `if` returns on every path only when it has an `else` and both
        // sides return.
        Expr::If(_, then, Some(els), _) => block_returns(then) && expr_diverges(els),
        Expr::IfLet(_, _, then, Some(els), _) => block_returns(then) && expr_diverges(els),
        // A `match` returns when every arm returns. Non-exhaustive matches are
        // reported separately, so treating all-arms-return as diverging never
        // hides a missing-return that exhaustiveness would not already catch.
        Expr::Match(_, arms, _) => {
            !arms.is_empty() && arms.iter().all(|arm| expr_diverges(&arm.body))
        }
        Expr::Block(block, _) => block_returns(block),
        _ => false,
    }
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
        // A `break` inside a nested loop binds to that loop, so it does not make
        // the enclosing loop terminable.
        Stmt::While { .. } | Stmt::For { .. } => false,
        _ => false,
    }
}

fn expr_has_break(expr: &Expr) -> bool {
    match expr {
        Expr::If(_, then, els, _) => {
            block_has_break(then) || els.as_deref().is_some_and(expr_has_break)
        }
        Expr::IfLet(_, _, then, els, _) => {
            block_has_break(then) || els.as_deref().is_some_and(expr_has_break)
        }
        Expr::Match(_, arms, _) => arms.iter().any(|arm| expr_has_break(&arm.body)),
        Expr::Block(block, _) => block_has_break(block),
        _ => false,
    }
}
