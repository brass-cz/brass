//! Shared AST traversal used by the type-checking passes. Visits every
//! expression reachable from function bodies, method bodies, and module-level
//! statements.

use brass_hir::{Program, TypeKind};
use brass_parser::ast::*;

pub trait ExprVisitor {
    fn visit(&mut self, e: &Expr);
}

pub fn walk_program_exprs(program: &Program, v: &mut impl ExprVisitor) {
    walk_program_exprs_in(program, crate::AnalysisModules::all(), v);
}

pub(crate) fn walk_program_exprs_in(
    program: &Program,
    modules: crate::AnalysisModules<'_>,
    v: &mut impl ExprVisitor,
) {
    for f in program.functions.values() {
        if !modules.checks(&f.module) {
            continue;
        }
        walk_block(&f.decl.body, v);
    }
    for t in program.types.values() {
        if !modules.checks(&t.module) {
            continue;
        }
        match &t.kind {
            TypeKind::Record { methods, .. } => {
                for m in methods.values() {
                    if let Some(b) = &m.decl.body {
                        walk_block(b, v);
                    }
                }
            }
            TypeKind::Sum { variants } => {
                for vi in variants {
                    for m in vi.methods.values() {
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
        Expr::TypeTest(subject, _, _) => walk_expr(subject, v),
        _ => {}
    }
}
