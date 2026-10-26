//! Syntactic analyses over the AST that lowering (and monomorphization)
//! share: a closure's free variables and the locals promoted to shared cells,
//! and whether a body is fallible.
//!
//! Given a closure's parameters and body, [`free_vars_of`] returns the
//! identifiers it references but does not itself bind; lowering keeps those that
//! are bound in the enclosing scope as the closure's captured operands.

use fxhash::FxHashSet as HashSet;

use brass_parser::Span;
use brass_parser::ast::*;

/// Locals that must be heap-promoted to a shared cell: those a
/// closure captures *and* that are assigned (mutated) somewhere -- in the closure or
/// the enclosing body -- so the mutation is observed through the shared capture, not
/// made on a per-closure copy. Read-only captures stay by-value. The cell is modeled
/// as a one-element array, reusing the array machinery (alloc, indexed get/set, RC).
pub fn cell_promotions(body: &Block) -> HashSet<String> {
    let mut captured = HashSet::default();
    let mut mutated = HashSet::default();
    promo_block(body, &mut captured, &mut mutated);
    captured.intersection(&mutated).cloned().collect()
}

fn promo_block(b: &Block, cap: &mut HashSet<String>, mutd: &mut HashSet<String>) {
    for s in &b.stmts {
        match s {
            Stmt::Let {
                value: Some(value), ..
            } => promo_expr(value, cap, mutd),
            Stmt::Let { value: None, .. } => {}
            Stmt::Assign { target, value, .. } => {
                if let Expr::Ident(n, _) = target {
                    mutd.insert(n.clone());
                }
                promo_expr(target, cap, mutd);
                promo_expr(value, cap, mutd);
            }
            Stmt::Expr(e) => promo_expr(e, cap, mutd),
            Stmt::While { cond, body, .. } => {
                promo_expr(cond, cap, mutd);
                promo_block(body, cap, mutd);
            }
            Stmt::For { iter, body, .. } => {
                promo_expr(iter, cap, mutd);
                promo_block(body, cap, mutd);
            }
            Stmt::Return(Some(e), _) => promo_expr(e, cap, mutd),
            _ => {}
        }
    }
}

fn promo_expr(e: &Expr, cap: &mut HashSet<String>, mutd: &mut HashSet<String>) {
    match e {
        Expr::Closure(params, cbody, _) => {
            let cb = closure_as_block(cbody);
            for v in free_vars_of(params, &cb) {
                cap.insert(v);
            }
            promo_block(&cb, cap, mutd);
        }
        Expr::Block(b, _) => promo_block(b, cap, mutd),
        Expr::If(c, t, els, _) => {
            promo_expr(c, cap, mutd);
            promo_block(t, cap, mutd);
            if let Some(e) = els {
                promo_expr(e, cap, mutd);
            }
        }
        Expr::IfLet(_, s, t, els, _) => {
            promo_expr(s, cap, mutd);
            promo_block(t, cap, mutd);
            if let Some(e) = els {
                promo_expr(e, cap, mutd);
            }
        }
        Expr::Match(s, arms, _) => {
            promo_expr(s, cap, mutd);
            for a in arms {
                promo_expr(&a.body, cap, mutd);
            }
        }
        _ => walk_subexprs(e, &mut |sub| promo_expr(sub, cap, mutd)),
    }
}

/// A closure body viewed as a block (an expression body becomes a one-statement
/// block). Mirrors `lower::closure_block`.
fn closure_as_block(body: &Expr) -> Block {
    match body {
        Expr::Block(b, _) => b.clone(),
        other => Block {
            stmts: vec![Stmt::Expr(other.clone())],
            span: other.span(),
        },
    }
}

/// Whether a body auto-wraps plain returns in `Result.Ok`, i.e. it uses
/// `error(...)` or the `expr!` propagation operator (a closure's body does not
/// count: it is a callable of its own).
pub fn fallible_block(b: &Block) -> bool {
    scan_block(b, Props::Count(&HashSet::default()))
}

/// Like [`fallible_block`], but an `expr!` whose span is in `null_props` (a
/// nullable-operand propagation, per the checker) does not count: its failure
/// arm returns `null`, not an error `Result`, so a body whose only `!`s are
/// nullable is not fallible -- its return type is nullable instead.
pub fn fallible_block_except(b: &Block, null_props: &HashSet<Span>) -> bool {
    scan_block(b, Props::Count(null_props))
}

/// Whether a body constructs an error `Result` with `error(...)`. Unlike
/// [`fallible_block`], `expr!` does not count: in the entry `main` a failed
/// propagation aborts the program instead of returning an error Result, so
/// only an explicit `error(...)` makes such a body fallible.
pub fn constructs_error_block(b: &Block) -> bool {
    scan_block(b, Props::Ignore)
}

/// How `expr!` sites count while scanning for fallibility: as error sources
/// (except the given nullable-operand spans), or not at all.
#[derive(Clone, Copy)]
enum Props<'a> {
    Count(&'a HashSet<Span>),
    Ignore,
}

impl Props<'_> {
    fn counts(&self, span: Span) -> bool {
        match self {
            Props::Count(null_props) => !null_props.contains(&span),
            Props::Ignore => false,
        }
    }
}

fn scan_block(b: &Block, props: Props) -> bool {
    b.stmts.iter().any(|s| scan_stmt(s, props))
}

fn scan_stmt(s: &Stmt, props: Props) -> bool {
    match s {
        Stmt::Let { value, .. } => value.as_ref().is_some_and(|e| scan_expr(e, props)),
        Stmt::Assign { target, value, .. } => scan_expr(target, props) || scan_expr(value, props),
        Stmt::Expr(e) => scan_expr(e, props),
        Stmt::While { cond, body, .. } => scan_expr(cond, props) || scan_block(body, props),
        Stmt::For { iter, body, .. } => scan_expr(iter, props) || scan_block(body, props),
        Stmt::Return(Some(e), _) => scan_expr(e, props),
        _ => false,
    }
}

fn scan_expr(e: &Expr, props: Props) -> bool {
    match e {
        // `error(..)!` immediately unwraps (aborts at an entry, propagates
        // elsewhere -- and the propagation is counted via `props`); the
        // construction never escapes as this body's own Result, so it alone
        // does not make the body fallible. Its arguments are still scanned.
        Expr::ErrorProp(inner, span) => {
            if let Expr::Call(c, args, _) = &**inner
                && matches!(&**c, Expr::Ident(n, _) if n == "error")
            {
                return props.counts(*span) || args.iter().any(|a| scan_expr(&a.expr, props));
            }
            props.counts(*span) || scan_expr(inner, props)
        }
        Expr::Call(c, args, _) => {
            matches!(&**c, Expr::Ident(n, _) if n == "error")
                || scan_expr(c, props)
                || args.iter().any(|a| scan_expr(&a.expr, props))
        }
        Expr::Unary(_, a, _) | Expr::Field(a, _, _) | Expr::TypeTest(a, _, _, _) => {
            scan_expr(a, props)
        }
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
            scan_expr(a, props) || scan_expr(b, props)
        }
        Expr::Array(es, _) => es.iter().any(|e| scan_expr(e, props)),
        Expr::TypeLit(_, fs, _) | Expr::VariantLit(_, _, fs, _) => {
            fs.iter().any(|(_, v)| scan_expr(v, props))
        }
        Expr::Str(segs, _) => segs
            .iter()
            .any(|s| matches!(s, StrSeg::Expr(e) if scan_expr(e, props))),
        Expr::If(c, t, e, _) => {
            scan_expr(c, props)
                || scan_block(t, props)
                || e.as_ref().is_some_and(|e| scan_expr(e, props))
        }
        Expr::IfLet(_, s, t, e, _) => {
            scan_expr(s, props)
                || scan_block(t, props)
                || e.as_ref().is_some_and(|e| scan_expr(e, props))
        }
        Expr::Match(s, arms, _) => {
            scan_expr(s, props) || arms.iter().any(|a| scan_expr(&a.body, props))
        }
        Expr::Block(b, _) => scan_block(b, props),
        // A closure is a separate callable with its own return ABI. Its body
        // must not make the enclosing callable fallible.
        Expr::Closure(..)
        | Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(..)
        | Expr::Ident(..)
        | Expr::SelfExpr(..) => false,
    }
}

// Capture order and scope boundaries have one syntactic authority.
pub use brass_hir::captures::free_vars_of;
use brass_hir::captures::walk_subexprs;
