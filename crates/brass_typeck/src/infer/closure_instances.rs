//! Concrete closure identities shared with MIR capture ordering.

use super::*;

impl Checker<'_> {
    /// Enter a closure at its physical capture types followed by its parameters.
    pub(super) fn enter_closure_instance(
        &mut self,
        params: &[Param],
        body: &Expr,
        args: &[Type],
        scopes: &ScopeStack,
    ) {
        let mut captures = Vec::new();
        self.closure_instance_captures(params, body, scopes, &mut captures);
        captures.extend_from_slice(args);
        let span = body.span();
        self.enter_instance(
            brass_hir::InstanceCallable::Closure {
                lo: span.lo,
                hi: span.hi,
            },
            &captures,
        );
        let layout = self.numeric_layout_for(span);
        if !self.numeric.probing && self.discarded_walks == 0 {
            self.record_numeric_call(span, layout.clone(), self.current_instance());
        }
        self.settle_numeric_instance(layout);
    }

    fn closure_instance_captures(
        &self,
        params: &[Param],
        body: &Expr,
        scopes: &ScopeStack,
        out: &mut Vec<Type>,
    ) {
        let block = match body {
            Expr::Block(block, _) => block.clone(),
            body => Block {
                stmts: vec![Stmt::Expr(body.clone())],
                span: body.span(),
            },
        };
        for name in brass_hir::captures::free_vars_of(params, &block) {
            let Some(ty) = scopes
                .iter()
                .skip(1)
                .rev()
                .find_map(|scope| scope.get(&name))
            else {
                continue;
            };
            let resolved = self.resolve(ty);
            let generalized = brass_hir::type_vars(&resolved)
                .iter()
                .any(|var| self.closure_schemes.contains_key(var));
            if generalized
                && let Type::Fun(args, ret) = &resolved
                && let Some(saved) = self.saved_closure_body(args, ret)
                && let Expr::Closure(params, body, _) = &saved.expr
            {
                self.closure_instance_captures(params, body, &saved.scopes, out);
            } else {
                out.push(resolved);
            }
        }
    }
}
