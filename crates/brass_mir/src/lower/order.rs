//! Left-to-right evaluation of sibling operands.
//!
//! Lowering names a variable's value by its slot: reading a plain local yields
//! `Operand::Local(slot)` without a copy, which keeps the common case free of
//! temporaries. That reference is only a faithful *value* while nothing
//! rebinds the slot before the operand is consumed. Operands, arguments,
//! array/tuple elements, record literal fields, an assignment's place parts,
//! and a `for` loop's iterable are evaluated left to right, and each one's
//! value is the value at the time it was evaluated; a later sibling that
//! assigns the same variable (`x + { x = 10; 1 }`) must not change it.
//!
//! [`FnLower::hold`] implements that rule: a plain-local operand is copied
//! into a fresh temporary exactly when code that runs before the operand is
//! consumed may rebind the variable, and passes through by reference
//! otherwise. The may-rebind test is syntactic and conservative (it ignores
//! shadowing), so an occasional copy is redundant but never missing.
//! A heap-promoted cell binding never needs the copy: its read already loads
//! the cell's element into a temporary.

use fxhash::FxHashSet as HashSet;

use brass_parser::ast::{Block, Expr, Stmt, StrSeg};

use crate::cfg::MirStmt;
use crate::lower::FnLower;
use crate::value::{Operand, Rvalue};

/// The variable names `e` may rebind when evaluated: every whole-variable
/// assignment target (`x = ..`, `x op= ..`) anywhere inside it, including
/// nested blocks and closure bodies. Shadowing is ignored, so the set may
/// over-approximate.
pub(crate) fn assigned_names<'e>(es: impl IntoIterator<Item = &'e Expr>) -> HashSet<String> {
    let mut out = HashSet::default();
    for e in es {
        collect_expr(e, &mut out);
    }
    out
}

/// [`assigned_names`] of a statement block.
pub(crate) fn assigned_names_block(b: &Block) -> HashSet<String> {
    let mut out = HashSet::default();
    collect_block(b, &mut out);
    out
}

/// For each position `i` of a left-to-right sibling sequence, the names the
/// siblings AFTER `i` may rebind (see [`assigned_names`]). The last position
/// always has an empty set.
pub(crate) fn later_assigned(es: &[&Expr]) -> Vec<HashSet<String>> {
    let mut later = vec![HashSet::default(); es.len()];
    let mut acc = HashSet::default();
    for (i, e) in es.iter().enumerate().rev() {
        if !acc.is_empty() {
            later[i] = acc.clone();
        }
        collect_expr(e, &mut acc);
    }
    later
}

fn collect_block(b: &Block, out: &mut HashSet<String>) {
    for s in &b.stmts {
        collect_stmt(s, out);
    }
}

fn collect_stmt(s: &Stmt, out: &mut HashSet<String>) {
    match s {
        Stmt::Let { value, .. } => {
            if let Some(v) = value {
                collect_expr(v, out);
            }
        }
        Stmt::Assign { target, value, .. } => {
            match target {
                Expr::Ident(name, _) => {
                    out.insert(name.clone());
                }
                Expr::SelfExpr(_) => {
                    out.insert("self".to_string());
                }
                other => collect_expr(other, out),
            }
            collect_expr(value, out);
        }
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => collect_expr(e, out),
        Stmt::While { cond, body, .. } => {
            collect_expr(cond, out);
            collect_block(body, out);
        }
        Stmt::For { iter, body, .. } => {
            collect_expr(iter, out);
            collect_block(body, out);
        }
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

fn collect_expr(e: &Expr, out: &mut HashSet<String>) {
    match e {
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(..)
        | Expr::Ident(..)
        | Expr::SelfExpr(..) => {}
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(e) = seg {
                    collect_expr(e, out);
                }
            }
        }
        Expr::Unary(_, inner, _)
        | Expr::Field(inner, _, _)
        | Expr::ErrorProp(inner, _)
        | Expr::TypeTest(inner, _, _, _) => collect_expr(inner, out),
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
            collect_expr(a, out);
            collect_expr(b, out);
        }
        Expr::Call(callee, args, _) => {
            collect_expr(callee, out);
            for a in args {
                collect_expr(&a.expr, out);
            }
        }
        Expr::Closure(_, body, _) => collect_expr(body, out),
        Expr::Array(items, _) => {
            for item in items {
                collect_expr(item, out);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, v) in fields {
                collect_expr(v, out);
            }
        }
        Expr::If(cond, then, els, _) => {
            collect_expr(cond, out);
            collect_block(then, out);
            if let Some(e) = els {
                collect_expr(e, out);
            }
        }
        Expr::IfLet(_, subject, then, els, _) => {
            collect_expr(subject, out);
            collect_block(then, out);
            if let Some(e) = els {
                collect_expr(e, out);
            }
        }
        Expr::Match(subject, arms, _) => {
            collect_expr(subject, out);
            for arm in arms {
                collect_expr(&arm.body, out);
            }
        }
        Expr::Block(b, _) => collect_block(b, out),
    }
}

impl FnLower<'_, '_> {
    /// Keep `op`'s current value while code that may rebind one of `later`'s
    /// names runs before `op` is consumed. A plain-local operand bound to such
    /// a name (by its innermost, non-cell binding) is copied into a fresh
    /// temporary; any other operand -- a constant, an expression temporary,
    /// an unaffected variable -- is returned unchanged.
    pub(crate) fn hold(&mut self, op: Operand, later: &HashSet<String>) -> Operand {
        if later.is_empty() {
            return op;
        }
        let Operand::Local(id) = op else {
            return op;
        };
        let rebound = later.iter().any(|name| {
            self.local_binding(name)
                .is_some_and(|(local, cell)| local == id && !cell)
        });
        if !rebound {
            return op;
        }
        let copy = self.b.fresh_local(None);
        self.b.push(MirStmt::Assign(copy, Rvalue::Use(op)));
        Operand::Local(copy)
    }

    /// Lower `es` as a left-to-right sibling sequence (arguments, elements,
    /// field values): each operand keeps the value it had when it was
    /// evaluated, even when a later sibling rebinds its variable.
    pub(crate) fn lower_in_order(&mut self, es: &[&Expr]) -> Vec<Operand> {
        let later = later_assigned(es);
        es.iter()
            .zip(&later)
            .map(|(e, later)| {
                let v = self.lower_expr(e);
                self.hold(v, later)
            })
            .collect()
    }
}
