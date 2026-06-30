//! Top-level initialization ordering. Module globals are
//! initialized in appearance order, so an initializer that references a global
//! defined later in the same module is a compile error. Cycles always manifest
//! as such a forward reference (the first member of the cycle to be initialized
//! refers to a not-yet-initialized later member), so detecting forward
//! references also rejects circular initialization without a separate graph
//! pass.
//!
//! Only references to other module globals are constrained: function and type
//! names are resolved regardless of order, and imported globals belong to a
//! module that is initialized earlier by the import topological order.

use std::collections::{HashMap, HashSet};

use prepoly_hir::Program;
use prepoly_lexer::Span;
use prepoly_parser::ast::*;

use crate::TypeError;

pub fn check(program: &Program) -> Vec<TypeError> {
    let mut errors = Vec::new();
    for module in &program.inits {
        check_module(&module.stmts, &mut errors);
    }
    errors
}

fn check_module(stmts: &[Stmt], errors: &mut Vec<TypeError>) {
    // First-definition index of each global binding name in this module.
    let mut def_index: HashMap<String, usize> = HashMap::new();
    for (i, stmt) in stmts.iter().enumerate() {
        if let Stmt::Let { pat, .. } = stmt {
            for name in pattern_names(pat) {
                def_index.entry(name).or_insert(i);
            }
        }
    }
    let globals: HashSet<String> = def_index.keys().cloned().collect();
    if globals.is_empty() {
        return;
    }
    for (i, stmt) in stmts.iter().enumerate() {
        let mut refs = Vec::new();
        collect_stmt_refs(stmt, &globals, &HashSet::new(), &mut refs);
        for (name, span) in refs {
            // A reference to a global whose definition is at or after the
            // current statement is a forward (or self) reference.
            if def_index.get(&name).is_some_and(|&j| j >= i) {
                errors.push(TypeError {
                    message: format!("global `{name}` is used before it is initialized"),
                    span,
                });
            }
        }
    }
}

fn collect_stmt_refs(
    stmt: &Stmt,
    globals: &HashSet<String>,
    bound: &HashSet<String>,
    out: &mut Vec<(String, Span)>,
) {
    match stmt {
        Stmt::Let { value, .. } => collect_expr_refs(value, globals, bound, out),
        Stmt::Assign { target, value, .. } => {
            collect_expr_refs(target, globals, bound, out);
            collect_expr_refs(value, globals, bound, out);
        }
        Stmt::Expr(e) => collect_expr_refs(e, globals, bound, out),
        Stmt::While { cond, body, .. } => {
            collect_expr_refs(cond, globals, bound, out);
            collect_block_refs(body, globals, bound, out);
        }
        Stmt::For {
            var, iter, body, ..
        } => {
            collect_expr_refs(iter, globals, bound, out);
            let mut inner = bound.clone();
            inner.insert(var.clone());
            collect_block_refs(body, globals, &inner, out);
        }
        Stmt::Return(Some(e), _) => collect_expr_refs(e, globals, bound, out),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

/// Walk a block tracking the locals introduced by earlier `let` statements so
/// they shadow same-named globals for the remainder of the block.
fn collect_block_refs(
    block: &Block,
    globals: &HashSet<String>,
    bound: &HashSet<String>,
    out: &mut Vec<(String, Span)>,
) {
    let mut local = bound.clone();
    for stmt in &block.stmts {
        if let Stmt::Let { pat, value, .. } = stmt {
            collect_expr_refs(value, globals, &local, out);
            for name in pattern_names(pat) {
                local.insert(name);
            }
        } else {
            collect_stmt_refs(stmt, globals, &local, out);
        }
    }
}

fn collect_expr_refs(
    expr: &Expr,
    globals: &HashSet<String>,
    bound: &HashSet<String>,
    out: &mut Vec<(String, Span)>,
) {
    match expr {
        Expr::Ident(name, span) => {
            if !bound.contains(name) && globals.contains(name) {
                out.push((name.clone(), *span));
            }
        }
        Expr::Int(..) | Expr::Float(..) | Expr::Bool(..) | Expr::Null(_) | Expr::SelfExpr(_) => {}
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(inner) = seg {
                    collect_expr_refs(inner, globals, bound, out);
                }
            }
        }
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) | Expr::Field(inner, _, _) => {
            collect_expr_refs(inner, globals, bound, out);
        }
        Expr::Binary(_, l, r, _) | Expr::Index(l, r, _) | Expr::Range(l, r, _) => {
            collect_expr_refs(l, globals, bound, out);
            collect_expr_refs(r, globals, bound, out);
        }
        Expr::Call(callee, args, _) => {
            collect_expr_refs(callee, globals, bound, out);
            for arg in args {
                collect_expr_refs(&arg.expr, globals, bound, out);
            }
        }
        Expr::Closure(params, body, _) => {
            let mut inner = bound.clone();
            for p in params {
                inner.insert(p.name.clone());
            }
            collect_expr_refs(body, globals, &inner, out);
        }
        Expr::Array(items, _) => {
            for item in items {
                collect_expr_refs(item, globals, bound, out);
            }
        }
        Expr::TypeLit(_, fields, _) => {
            for (_, value) in fields {
                collect_expr_refs(value, globals, bound, out);
            }
        }
        Expr::VariantLit(_, _, fields, _) => {
            for (_, value) in fields {
                collect_expr_refs(value, globals, bound, out);
            }
        }
        Expr::If(cond, then, els, _) => {
            collect_expr_refs(cond, globals, bound, out);
            collect_block_refs(then, globals, bound, out);
            if let Some(els) = els {
                collect_expr_refs(els, globals, bound, out);
            }
        }
        Expr::IfLet(pat, scrut, then, els, _) => {
            collect_expr_refs(scrut, globals, bound, out);
            let mut inner = bound.clone();
            for name in pattern_names(pat) {
                inner.insert(name);
            }
            collect_block_refs(then, globals, &inner, out);
            if let Some(els) = els {
                collect_expr_refs(els, globals, bound, out);
            }
        }
        Expr::Match(scrut, arms, _) => {
            collect_expr_refs(scrut, globals, bound, out);
            for arm in arms {
                let mut inner = bound.clone();
                for name in pattern_names(&arm.pattern) {
                    inner.insert(name);
                }
                collect_expr_refs(&arm.body, globals, &inner, out);
            }
        }
        Expr::Block(block, _) => collect_block_refs(block, globals, bound, out),
    }
}

/// Names bound by a pattern. Variant/record destructuring binds its fields.
fn pattern_names(pat: &Pattern) -> Vec<String> {
    let mut names = Vec::new();
    collect_pattern_names(pat, &mut names);
    names
}

fn collect_pattern_names(pat: &Pattern, out: &mut Vec<String>) {
    match pat {
        Pattern::Binding(name, _) => out.push(name.clone()),
        Pattern::Record(_, fields, _) => {
            for field in fields {
                match &field.pat {
                    Some(sub) => collect_pattern_names(sub, out),
                    None => out.push(field.name.clone()),
                }
            }
        }
        Pattern::Array(pats, _) => {
            for p in pats {
                collect_pattern_names(p, out);
            }
        }
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
    }
}
