//! Shared AST traversal used by the type-checking passes. Visits every
//! expression reachable from function bodies, method bodies, and module-level
//! statements, and collects the values a statement-position expression
//! discards ([`discarded_value_spans`]).

use brass_hir::{Program, TypeKind};
use brass_parser::Span;
use brass_parser::ast::*;

/// A pre-order expression visitor: the walk functions call [`Self::visit`] on
/// each expression before descending into its subexpressions.
pub trait ExprVisitor {
    fn visit(&mut self, e: &Expr);

    /// Called by [`walk_program_exprs_in`] before it walks each body, with
    /// the module the body belongs to (names in it resolve in that module's
    /// scope). Visitors that resolve no names ignore it.
    fn enter_module(&mut self, _module: &[String]) {}
}

/// Visit every expression of the function bodies, method bodies and module
/// initializers of the modules `modules` checks, announcing each body's module
/// first ([`ExprVisitor::enter_module`]).
pub(crate) fn walk_program_exprs_in(
    program: &Program,
    modules: crate::AnalysisModules<'_>,
    v: &mut impl ExprVisitor,
) {
    for f in program.functions.values() {
        if !modules.checks(&f.module) || !modules.checks_body(f.decl.span) {
            continue;
        }
        v.enter_module(&f.module);
        walk_block(&f.decl.body, v);
    }
    for t in program.types.values() {
        if !modules.checks(&t.module) {
            continue;
        }
        v.enter_module(&t.module);
        match &t.kind {
            TypeKind::Record { methods, .. } => {
                for m in methods.values() {
                    if !modules.checks_body(m.decl.span) {
                        continue;
                    }
                    if let Some(b) = &m.decl.body {
                        walk_block(b, v);
                    }
                }
            }
            TypeKind::Sum { variants } => {
                for vi in variants {
                    for m in vi.methods.values() {
                        if !modules.checks_body(m.decl.span) {
                            continue;
                        }
                        if let Some(b) = &m.decl.body {
                            walk_block(b, v);
                        }
                    }
                }
            }
        }
    }
    for init in &program.inits {
        if !modules.checks(&init.path) {
            continue;
        }
        v.enter_module(&init.path);
        for s in &init.stmts {
            walk_stmt(s, v);
        }
    }
}

pub fn walk_block(b: &Block, v: &mut impl ExprVisitor) {
    for s in &b.stmts {
        walk_stmt(s, v);
    }
}

pub fn walk_stmt(s: &Stmt, v: &mut impl ExprVisitor) {
    match s {
        Stmt::Let {
            value: Some(value), ..
        } => walk_expr(value, v),
        Stmt::Let { value: None, .. } => {}
        Stmt::Assign { target, value, .. } => {
            walk_expr(target, v);
            walk_expr(value, v);
        }
        Stmt::Expr(e) => walk_expr(e, v),
        Stmt::While { cond, body, .. } => {
            walk_expr(cond, v);
            walk_block(body, v);
        }
        Stmt::For { iter, body, .. } => {
            walk_expr(iter, v);
            walk_block(body, v);
        }
        Stmt::Return(Some(e), _) => walk_expr(e, v),
        _ => {}
    }
}

pub fn walk_expr(e: &Expr, v: &mut impl ExprVisitor) {
    v.visit(e);
    match e {
        Expr::Unary(_, a, _) | Expr::ErrorProp(a, _) | Expr::Field(a, _, _) => walk_expr(a, v),
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
            walk_expr(a, v);
            walk_expr(b, v);
        }
        Expr::Call(f, args, _) => {
            walk_expr(f, v);
            for a in args {
                walk_expr(&a.expr, v);
            }
        }
        Expr::Closure(_, body, _) => walk_expr(body, v),
        Expr::Array(es, _) => es.iter().for_each(|e| walk_expr(e, v)),
        Expr::TypeLit(_, fs, _) | Expr::VariantLit(_, _, fs, _) => {
            fs.iter().for_each(|(_, e)| walk_expr(e, v))
        }
        Expr::Str(segs, _) => {
            for s in segs {
                if let StrSeg::Expr(e) = s {
                    walk_expr(e, v);
                }
            }
        }
        Expr::If(c, t, els, _) => {
            walk_expr(c, v);
            walk_block(t, v);
            if let Some(e) = els {
                walk_expr(e, v);
            }
        }
        Expr::IfLet(_, scrut, t, els, _) => {
            walk_expr(scrut, v);
            walk_block(t, v);
            if let Some(e) = els {
                walk_expr(e, v);
            }
        }
        Expr::Match(scrut, arms, _) => {
            walk_expr(scrut, v);
            for a in arms {
                walk_expr(&a.body, v);
            }
        }
        Expr::Block(b, _) => walk_block(b, v),
        Expr::TypeTest(subject, _, _, _) => walk_expr(subject, v),
        _ => {}
    }
}

/// The spans of the values a statement-position `e` discards: `e` itself and,
/// through `if`/`if let`/`match` arms and blocks, each arm's trailing
/// expression -- the value of an arm is the value of the whole statement.
pub(crate) fn discarded_value_spans(e: &Expr, out: &mut Vec<Span>) {
    fn block_tail(b: &Block, out: &mut Vec<Span>) {
        if let Some(Stmt::Expr(tail)) = b.stmts.last() {
            discarded_value_spans(tail, out);
        }
    }
    out.push(e.span());
    match e {
        Expr::If(_, then, els, _) | Expr::IfLet(_, _, then, els, _) => {
            block_tail(then, out);
            if let Some(els) = els {
                discarded_value_spans(els, out);
            }
        }
        Expr::Match(_, arms, _) => {
            for arm in arms {
                discarded_value_spans(&arm.body, out);
            }
        }
        Expr::Block(b, _) => block_tail(b, out),
        _ => {}
    }
}
