//! Statement-tree traversal and lexical scoping shared by the analyses and the
//! rewrite: the statement lists nested in a statement, pattern bindings, and the
//! bindings visible at each spawn site and closure-valued binding.

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use brass_parser::Span;
use brass_parser::ast::*;

use super::sites::{spawn_arg, spawn_stmt_span, stmt_span};

/// Collect the broad local namespace used for scope-wide guarding. Spawn
/// capture classification uses [`lexical_scopes`] instead, preserving the
/// source order and nesting of bindings.
pub(super) fn collect_local_bindings(stmts: &[Stmt], out: &mut HashSet<String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { pat, .. } => collect_pattern_bindings(pat, out),
            Stmt::For { pat, .. } => collect_pattern_bindings(pat, out),
            _ => {}
        }
        nested_block_stmts(stmt, &mut |inner| collect_local_bindings(inner, out));
    }
}

/// The names visible at each spawn site and at each closure-valued binding,
/// keyed by the statement's span (see [`lexical_scopes`]).
#[derive(Default)]
pub(super) struct LexicalScopes {
    pub(super) spawn_sites: HashMap<Span, HashSet<String>>,
    pub(super) closure_bindings: HashMap<Span, HashSet<String>>,
}

/// Record the bindings visible at each spawn site and closure-valued binding.
pub(super) fn lexical_scopes(stmts: &[Stmt], in_scope: &HashSet<String>) -> LexicalScopes {
    let mut scopes = LexicalScopes::default();
    collect_lexical_stmts(stmts, in_scope, &mut scopes);
    scopes
}

fn collect_lexical_stmts(stmts: &[Stmt], in_scope: &HashSet<String>, scopes: &mut LexicalScopes) {
    let mut visible = in_scope.clone();
    for stmt in stmts {
        if spawn_arg(stmt).is_some() {
            scopes
                .spawn_sites
                .insert(spawn_stmt_span(stmt), visible.clone());
        }
        if matches!(
            stmt,
            Stmt::Let {
                value: Some(Expr::Closure(..)),
                ..
            } | Stmt::Assign {
                value: Expr::Closure(..),
                ..
            }
        ) {
            scopes
                .closure_bindings
                .insert(stmt_span(stmt), visible.clone());
        }
        collect_lexical_stmt_exprs(stmt, &visible, scopes);
        if let Stmt::Let { pat, .. } = stmt {
            collect_pattern_bindings(pat, &mut visible);
        }
    }
}

fn collect_lexical_stmt_exprs(stmt: &Stmt, visible: &HashSet<String>, scopes: &mut LexicalScopes) {
    match stmt {
        Stmt::Let {
            value: Some(value), ..
        }
        | Stmt::Expr(value)
        | Stmt::Return(Some(value), _) => collect_lexical_expr(value, visible, scopes),
        Stmt::Assign { target, value, .. } => {
            collect_lexical_expr(target, visible, scopes);
            collect_lexical_expr(value, visible, scopes);
        }
        Stmt::While { cond, body, .. } => {
            collect_lexical_expr(cond, visible, scopes);
            collect_lexical_stmts(&body.stmts, visible, scopes);
        }
        Stmt::For {
            pat, iter, body, ..
        } => {
            collect_lexical_expr(iter, visible, scopes);
            let mut inner = visible.clone();
            collect_pattern_bindings(pat, &mut inner);
            collect_lexical_stmts(&body.stmts, &inner, scopes);
        }
        Stmt::Let { value: None, .. }
        | Stmt::Return(None, _)
        | Stmt::Break(_)
        | Stmt::Continue(_) => {}
    }
}

fn collect_lexical_expr(expr: &Expr, visible: &HashSet<String>, scopes: &mut LexicalScopes) {
    match expr {
        Expr::Unary(_, inner, _) | Expr::Field(inner, _, _) | Expr::ErrorProp(inner, _) => {
            collect_lexical_expr(inner, visible, scopes);
        }
        Expr::Binary(_, left, right, _)
        | Expr::Index(left, right, _)
        | Expr::Range(left, right, _) => {
            collect_lexical_expr(left, visible, scopes);
            collect_lexical_expr(right, visible, scopes);
        }
        Expr::Call(callee, args, _) => {
            collect_lexical_expr(callee, visible, scopes);
            for arg in args {
                collect_lexical_expr(&arg.expr, visible, scopes);
            }
        }
        Expr::Array(items, _) => {
            for item in items {
                collect_lexical_expr(item, visible, scopes);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, value) in fields {
                collect_lexical_expr(value, visible, scopes);
            }
        }
        Expr::Str(segments, _) => {
            for segment in segments {
                if let StrSeg::Expr(value) = segment {
                    collect_lexical_expr(value, visible, scopes);
                }
            }
        }
        Expr::If(cond, then, els, _) => {
            collect_lexical_expr(cond, visible, scopes);
            collect_lexical_stmts(&then.stmts, visible, scopes);
            if let Some(els) = els {
                collect_lexical_expr(els, visible, scopes);
            }
        }
        Expr::IfLet(pat, scrutinee, then, els, _) => {
            collect_lexical_expr(scrutinee, visible, scopes);
            let mut inner = visible.clone();
            collect_pattern_bindings(pat, &mut inner);
            collect_lexical_stmts(&then.stmts, &inner, scopes);
            if let Some(els) = els {
                collect_lexical_expr(els, visible, scopes);
            }
        }
        Expr::Match(scrutinee, arms, _) => {
            collect_lexical_expr(scrutinee, visible, scopes);
            for arm in arms {
                let mut inner = visible.clone();
                collect_pattern_bindings(&arm.pattern, &mut inner);
                collect_lexical_expr(&arm.body, &inner, scopes);
            }
        }
        Expr::Block(block, _) => collect_lexical_stmts(&block.stmts, visible, scopes),
        Expr::TypeTest(subject, _, _, _) => collect_lexical_expr(subject, visible, scopes),
        Expr::Closure(..)
        | Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => {}
    }
}

/// Apply `f` to every statement list directly nested in `stmt` through control
/// flow: loop bodies, `if`/`if let` branches, `match` arms (block bodies), and
/// block expressions. Closures are *not* descended into (a spawn closure is a
/// separate execution scope). The mutable twin is [`nested_block_stmts_mut`].
pub(super) fn nested_block_stmts(stmt: &Stmt, f: &mut dyn FnMut(&[Stmt])) {
    match stmt {
        Stmt::While { cond, body, .. } => {
            nested_block_stmts_expr(cond, f);
            f(&body.stmts);
        }
        Stmt::For { iter, body, .. } => {
            nested_block_stmts_expr(iter, f);
            f(&body.stmts);
        }
        Stmt::Expr(e) | Stmt::Let { value: Some(e), .. } | Stmt::Return(Some(e), _) => {
            nested_block_stmts_expr(e, f)
        }
        Stmt::Assign { target, value, .. } => {
            nested_block_stmts_expr(target, f);
            nested_block_stmts_expr(value, f);
        }
        _ => {}
    }
}

fn nested_block_stmts_expr(e: &Expr, f: &mut dyn FnMut(&[Stmt])) {
    match e {
        Expr::Unary(_, inner, _) | Expr::Field(inner, _, _) | Expr::ErrorProp(inner, _) => {
            nested_block_stmts_expr(inner, f)
        }
        Expr::Binary(_, left, right, _)
        | Expr::Index(left, right, _)
        | Expr::Range(left, right, _) => {
            nested_block_stmts_expr(left, f);
            nested_block_stmts_expr(right, f);
        }
        Expr::Call(callee, args, _) => {
            nested_block_stmts_expr(callee, f);
            for arg in args {
                nested_block_stmts_expr(&arg.expr, f);
            }
        }
        Expr::Array(items, _) => {
            for item in items {
                nested_block_stmts_expr(item, f);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, value) in fields {
                nested_block_stmts_expr(value, f);
            }
        }
        Expr::Str(segments, _) => {
            for segment in segments {
                if let StrSeg::Expr(value) = segment {
                    nested_block_stmts_expr(value, f);
                }
            }
        }
        Expr::If(cond, t, els, _) => {
            nested_block_stmts_expr(cond, f);
            f(&t.stmts);
            if let Some(els) = els {
                nested_block_stmts_expr(els, f);
            }
        }
        Expr::IfLet(_, scrutinee, t, els, _) => {
            nested_block_stmts_expr(scrutinee, f);
            f(&t.stmts);
            if let Some(els) = els {
                nested_block_stmts_expr(els, f);
            }
        }
        Expr::Block(b, _) => f(&b.stmts),
        Expr::Match(scrutinee, arms, _) => {
            nested_block_stmts_expr(scrutinee, f);
            for arm in arms {
                nested_block_stmts_expr(&arm.body, f);
            }
        }
        Expr::TypeTest(subject, _, _, _) => nested_block_stmts_expr(subject, f),
        Expr::Closure(..)
        | Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => {}
    }
}

/// Mutable [`nested_block_stmts`]: apply `f` to every directly-nested statement
/// list so a pass that rewrites the AST (auto-acquire) reaches spawns nested in
/// conditionals and blocks, not only at the top level of a function or loop.
pub(super) fn nested_block_stmts_mut(stmt: &mut Stmt, f: &mut dyn FnMut(&mut Vec<Stmt>)) {
    match stmt {
        Stmt::While { cond, body, .. } => {
            nested_block_stmts_expr_mut(cond, f);
            f(&mut body.stmts);
        }
        Stmt::For { iter, body, .. } => {
            nested_block_stmts_expr_mut(iter, f);
            f(&mut body.stmts);
        }
        Stmt::Expr(e) | Stmt::Let { value: Some(e), .. } | Stmt::Return(Some(e), _) => {
            nested_block_stmts_expr_mut(e, f)
        }
        Stmt::Assign { target, value, .. } => {
            nested_block_stmts_expr_mut(target, f);
            nested_block_stmts_expr_mut(value, f);
        }
        _ => {}
    }
}

fn nested_block_stmts_expr_mut(e: &mut Expr, f: &mut dyn FnMut(&mut Vec<Stmt>)) {
    match e {
        Expr::Unary(_, inner, _) | Expr::Field(inner, _, _) | Expr::ErrorProp(inner, _) => {
            nested_block_stmts_expr_mut(inner, f)
        }
        Expr::Binary(_, left, right, _)
        | Expr::Index(left, right, _)
        | Expr::Range(left, right, _) => {
            nested_block_stmts_expr_mut(left, f);
            nested_block_stmts_expr_mut(right, f);
        }
        Expr::Call(callee, args, _) => {
            nested_block_stmts_expr_mut(callee, f);
            for arg in args {
                nested_block_stmts_expr_mut(&mut arg.expr, f);
            }
        }
        Expr::Array(items, _) => {
            for item in items {
                nested_block_stmts_expr_mut(item, f);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, value) in fields {
                nested_block_stmts_expr_mut(value, f);
            }
        }
        Expr::Str(segments, _) => {
            for segment in segments {
                if let StrSeg::Expr(value) = segment {
                    nested_block_stmts_expr_mut(value, f);
                }
            }
        }
        Expr::If(cond, t, els, _) => {
            nested_block_stmts_expr_mut(cond, f);
            f(&mut t.stmts);
            if let Some(els) = els {
                nested_block_stmts_expr_mut(els, f);
            }
        }
        Expr::IfLet(_, scrutinee, t, els, _) => {
            nested_block_stmts_expr_mut(scrutinee, f);
            f(&mut t.stmts);
            if let Some(els) = els {
                nested_block_stmts_expr_mut(els, f);
            }
        }
        Expr::Block(b, _) => f(&mut b.stmts),
        Expr::Match(scrutinee, arms, _) => {
            nested_block_stmts_expr_mut(scrutinee, f);
            for arm in arms {
                nested_block_stmts_expr_mut(&mut arm.body, f);
            }
        }
        Expr::TypeTest(subject, _, _, _) => nested_block_stmts_expr_mut(subject, f),
        Expr::Closure(..)
        | Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => {}
    }
}

pub(super) fn collect_pattern_bindings(pat: &Pattern, out: &mut HashSet<String>) {
    match pat {
        Pattern::Binding(name, _, _) => {
            out.insert(name.clone());
        }
        Pattern::Record(_, _, fields, _) => {
            for field in fields {
                match &field.pat {
                    Some(sub) => collect_pattern_bindings(sub, out),
                    None => {
                        out.insert(field.name.clone());
                    }
                }
            }
        }
        Pattern::Array(pats, _) => pats.iter().for_each(|p| collect_pattern_bindings(p, out)),
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
    }
}
