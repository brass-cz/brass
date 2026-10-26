//! Which closure bindings are generalized: let-polymorphism with a value
//! restriction.
//!
//! A `let`/`const` binding is *generalized* when it binds a plain name with
//! no annotation, its initializer is a closure literal with at least one
//! unannotated parameter, and no assignment anywhere in its body (nested
//! closures included) targets that name. Such a
//! binding behaves like a local generic function: the checker gives it a type
//! scheme instantiated afresh at every use, and MIR lowering builds the
//! closure value afresh at every use so each use is compiled at its own
//! instantiation. Every other closure value -- a reassigned binding, a
//! parameter, a closure stored in a field or array, a returned closure -- is
//! monomorphic. A closure whose parameters are all annotated has its type
//! fixed by them, so it stays one value (it keeps its identity under `==`).
//!
//! The rule is purely syntactic so the checker and the lowering decide it
//! identically from the HIR alone. It is conservative by name: an assignment
//! to *any* binding of the same name in the body (or, for a module-level
//! binding, anywhere in the program, since functions may assign globals)
//! keeps the binding monomorphic, which only ever makes the checker stricter.

use fxhash::FxHashSet as HashSet;

use brass_parser::Span;
use brass_parser::ast::{Block, Expr, Pattern, Stmt, StrSeg};

use crate::{Program, TypeKind};

/// The binding spans (the span of the bound name in `let name = ...`) of
/// every generalized closure binding in `program`: in free functions,
/// methods and module initializers, at any nesting depth.
pub fn generalized_closure_bindings(program: &Program) -> HashSet<Span> {
    let mut bodies: Vec<&Block> = program.functions.values().map(|f| &f.decl.body).collect();
    for info in program.types.values() {
        match &info.kind {
            TypeKind::Record { methods, .. } => {
                bodies.extend(methods.values().filter_map(|m| m.decl.body.as_ref()));
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    bodies.extend(v.methods.values().filter_map(|m| m.decl.body.as_ref()));
                }
            }
        }
    }
    let mut out = HashSet::default();
    // A module-level binding is a global any function may assign, so the
    // initializers judge their bindings against every assignment in the
    // program.
    let mut program_assigned = HashSet::default();
    for body in &bodies {
        let mut assigned = HashSet::default();
        each_stmt_in_block(body, &mut |s| collect_assigned(s, &mut assigned));
        each_stmt_in_block(body, &mut |s| collect_generalized(s, &assigned, &mut out));
        program_assigned.extend(assigned);
    }
    for init in &program.inits {
        for s in &init.stmts {
            each_stmt(s, &mut |s| collect_assigned(s, &mut program_assigned));
        }
    }
    for init in &program.inits {
        for s in &init.stmts {
            each_stmt(s, &mut |s| {
                collect_generalized(s, &program_assigned, &mut out)
            });
        }
    }
    out
}

/// Record the name a plain `name = ...` / `name += ...` assignment rebinds.
fn collect_assigned(s: &Stmt, assigned: &mut HashSet<String>) {
    if let Stmt::Assign {
        target: Expr::Ident(name, _),
        ..
    } = s
    {
        assigned.insert(name.clone());
    }
}

/// Record `s` when it is a generalized closure binding.
fn collect_generalized(s: &Stmt, assigned: &HashSet<String>, out: &mut HashSet<Span>) {
    if let Stmt::Let {
        pat: Pattern::Binding(name, None, span),
        ty: None,
        value: Some(Expr::Closure(params, _, _)),
        ..
    } = s
        && params.iter().any(|p| p.ty.is_none())
        && !assigned.contains(name)
    {
        out.insert(*span);
    }
}

/// Visit every statement in `b`, including those nested in blocks, loops,
/// branches, match arms and closure bodies.
fn each_stmt_in_block(b: &Block, f: &mut impl FnMut(&Stmt)) {
    for s in &b.stmts {
        each_stmt(s, f);
    }
}

fn each_stmt(s: &Stmt, f: &mut impl FnMut(&Stmt)) {
    f(s);
    match s {
        Stmt::Let { value, .. } => {
            if let Some(v) = value {
                each_stmt_in_expr(v, f);
            }
        }
        Stmt::Assign { target, value, .. } => {
            each_stmt_in_expr(target, f);
            each_stmt_in_expr(value, f);
        }
        Stmt::Expr(e) => each_stmt_in_expr(e, f),
        Stmt::While { cond, body, .. } => {
            each_stmt_in_expr(cond, f);
            each_stmt_in_block(body, f);
        }
        Stmt::For { iter, body, .. } => {
            each_stmt_in_expr(iter, f);
            each_stmt_in_block(body, f);
        }
        Stmt::Return(Some(e), _) => each_stmt_in_expr(e, f),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

fn each_stmt_in_expr(e: &Expr, f: &mut impl FnMut(&Stmt)) {
    match e {
        Expr::Unary(_, a, _) | Expr::ErrorProp(a, _) | Expr::Field(a, _, _) => {
            each_stmt_in_expr(a, f)
        }
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
            each_stmt_in_expr(a, f);
            each_stmt_in_expr(b, f);
        }
        Expr::Call(callee, args, _) => {
            each_stmt_in_expr(callee, f);
            for a in args {
                each_stmt_in_expr(&a.expr, f);
            }
        }
        Expr::Closure(_, body, _) => each_stmt_in_expr(body, f),
        Expr::Array(es, _) => es.iter().for_each(|e| each_stmt_in_expr(e, f)),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            fields.iter().for_each(|(_, e)| each_stmt_in_expr(e, f))
        }
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(e) = seg {
                    each_stmt_in_expr(e, f);
                }
            }
        }
        Expr::If(cond, then, els, _) => {
            each_stmt_in_expr(cond, f);
            each_stmt_in_block(then, f);
            if let Some(e) = els {
                each_stmt_in_expr(e, f);
            }
        }
        Expr::IfLet(_, scrut, then, els, _) => {
            each_stmt_in_expr(scrut, f);
            each_stmt_in_block(then, f);
            if let Some(e) = els {
                each_stmt_in_expr(e, f);
            }
        }
        Expr::Match(scrut, arms, _) => {
            each_stmt_in_expr(scrut, f);
            for arm in arms {
                each_stmt_in_expr(&arm.body, f);
            }
        }
        Expr::Block(b, _) => each_stmt_in_block(b, f),
        Expr::TypeTest(subject, _, _, _) => each_stmt_in_expr(subject, f),
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spans_of(src: &str) -> Vec<String> {
        let ast = brass_parser::parse(src).expect("parse");
        let (program, errors) = crate::lower(&[crate::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty(), "lower errors: {errors:?}");
        let mut names: Vec<String> = generalized_closure_bindings(&program)
            .into_iter()
            .map(|span| src[span.lo..span.hi].to_string())
            .collect();
        names.sort();
        names
    }

    /// Only unannotated, never-assigned bindings of a closure with an
    /// unannotated parameter generalize; an assignment anywhere in the body
    /// (a nested closure included) keeps the binding monomorphic, as does an
    /// annotation, fully annotated parameters, or a non-closure value.
    #[test]
    fn generalizes_unassigned_unannotated_closure_bindings() {
        let names = spans_of(
            "fun main() {\n    let id = (x) -> x\n    const k = (x, y: int32) -> 1\n    \
             let f = (x) -> x\n    let g = () -> {\n        f = (x) -> x\n    }\n    \
             let a = (x: int32) -> x\n    \
             let h: (int32) -> int32 = (x) -> x\n    let n = 5\n}\n",
        );
        assert_eq!(names, vec!["id".to_string(), "k".to_string()]);
    }

    /// A module-level closure binding is judged against assignments in every
    /// function, since any of them may assign the global.
    #[test]
    fn module_level_binding_sees_assignments_in_functions() {
        let names =
            spans_of("let a = (x) -> x\nlet b = (x) -> x\nfun main() {\n    b = (x) -> x\n}\n");
        assert_eq!(names, vec!["a".to_string()]);
    }
}
