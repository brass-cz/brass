//! Completed concrete checks of closed numeric closure bodies.
//!
//! Syntax certification excludes external reads, calls, control flow and
//! reference modes. A concrete signature then has no external solver read
//! dependencies: allocating or rolling back unrelated variables cannot
//! invalidate it. Entries belong to one checker/program lifetime and retain
//! the saved body's identity and enclosing instance. Context seeds never
//! export this cache.

use super::*;
use std::hash::{Hash, Hasher};

#[derive(Clone)]
struct BodyIdentity(Rc<ClosureBody>);

impl PartialEq for BodyIdentity {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for BodyIdentity {}

impl Hash for BodyIdentity {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state);
    }
}

/// A concrete check within one saved lexical body and enclosing instance.
/// Keeping the Rc prevents address reuse from conflating different bodies.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct ClosureMemoKey {
    body: BodyIdentity,
    args: Vec<Type>,
    expected_return: Option<Type>,
    instance: Option<instances::TagRef>,
    layout: Option<brass_hir::NumericLayout>,
}

/// Whether a type has the primitive, mode-free numeric representation.
pub(super) fn primitive_numeric(ty: &Type) -> bool {
    matches!(ty, Type::Int(_) | Type::Float(_))
}

/// Certify lexical independence without inferring types. Annotations are
/// declined because resolving them can read nominal or contextual tables.
/// Every read and assignment must refer to a parameter or an earlier local
/// declaration; initializers are checked before their new binding is added.
pub(super) fn closed_numeric_body(expr: &Expr) -> bool {
    let Expr::Closure(params, body, _) = expr else {
        return false;
    };
    let mut locals = HashSet::default();
    for param in params {
        if param.ty.is_some() || (param.name != "_" && !locals.insert(param.name.as_str())) {
            return false;
        }
    }
    let Expr::Block(block, _) = &**body else {
        return numeric_expr(body, &locals);
    };
    let Some((Stmt::Return(Some(result), _), statements)) = block.stmts.split_last() else {
        return false;
    };
    for stmt in statements {
        let admitted = match stmt {
            Stmt::Let {
                pat: Pattern::Binding(name, None, _),
                ty: None,
                value: Some(value),
                ..
            } => numeric_expr(value, &locals) && locals.insert(name.as_str()),
            Stmt::Assign {
                target: Expr::Ident(name, _),
                value,
                ..
            } => locals.contains(name.as_str()) && numeric_expr(value, &locals),
            Stmt::Expr(expr) => numeric_expr(expr, &locals),
            _ => false,
        };
        if !admitted {
            return false;
        }
    }
    numeric_expr(result, &locals)
}

fn numeric_expr(expr: &Expr, locals: &HashSet<&str>) -> bool {
    match expr {
        Expr::Int(..) | Expr::Float(..) => true,
        Expr::Ident(name, _) => locals.contains(name.as_str()),
        Expr::Unary(UnaryOp::Neg | UnaryOp::BitNot, inner, _) => numeric_expr(inner, locals),
        Expr::Binary(
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Rem
            | BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor
            | BinOp::Shl
            | BinOp::Shr,
            left,
            right,
            _,
        ) => numeric_expr(left, locals) && numeric_expr(right, locals),
        _ => false,
    }
}

impl Checker<'_> {
    /// Admit only a completed numeric signature with no contextual solver
    /// reads. Open enclosing-instance tags decline instead of capturing a
    /// substitution that could change after rollback or a later statement.
    pub(super) fn closure_memo_key(
        &self,
        body: &Rc<ClosureBody>,
        args: &[Type],
        ret: &Type,
    ) -> Option<ClosureMemoKey> {
        if !self.errors.is_empty()
            || self.closure_memo_disabled
            || !body.numeric_replay
            || self.co_checking
            || self.static_divergence
            || self.fixed_array_binding
            || self.branch_expectation.is_some()
            || self.speculation_depth != 0
            || self.application_probe.is_some()
            || !self.type_test_holes.is_empty()
            || !args.iter().all(primitive_numeric)
            || !matches!(&body.expr, Expr::Closure(params, _, _) if params.len() == args.len())
        {
            return None;
        }
        if self.numeric.probing {
            return None;
        }
        let expected_return = body.explicit_return.then(|| self.resolve(ret));
        if expected_return
            .as_ref()
            .is_some_and(|ty| !primitive_numeric(ty))
        {
            return None;
        }
        let instance = self.current_instance();
        if instance
            .as_ref()
            .is_some_and(|tag| !tag.args.iter().all(brass_hir::is_fully_known))
        {
            return None;
        }
        Some(ClosureMemoKey {
            layout: match &body.expr {
                Expr::Closure(_, expr, _) => self.numeric_layout_for(expr.span()),
                _ => None,
            },
            body: BodyIdentity(Rc::clone(body)),
            args: args.to_vec(),
            expected_return,
            instance,
        })
    }
}

#[cfg(test)]
mod tests;
