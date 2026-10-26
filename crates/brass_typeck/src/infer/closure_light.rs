//! Concrete closure results for the speculative light walk.

use super::*;

impl Checker<'_> {
    /// Infer a saved closure's result at the light call's argument types.
    /// Keep contextual return contracts and roll back parameter bindings so
    /// this approximation cannot commit a monomorphic closure's signature.
    pub(super) fn infer_callable_light(
        &mut self,
        callee: &Type,
        arguments: &[Type],
    ) -> Option<Type> {
        let Type::Fun(params, ret) = self.resolve_head(callee) else {
            return None;
        };
        let fallback = self.resolve(&ret);
        let Some(closure) = self.saved_closure_body(&params, &ret) else {
            return Some(fallback);
        };
        if closure.explicit_return || params.len() != arguments.len() {
            return Some(fallback);
        }
        let Expr::Closure(decl_params, body, span) = &closure.expr else {
            unreachable!("only closures have saved callable bodies");
        };
        let key = format!("light-closure:{}", span.lo);
        if !self.instantiating.insert(key.clone()) {
            return Some(fallback);
        }
        let snapshot = self.solver.snapshot();
        for (param, arg) in params.iter().zip(arguments) {
            if !brass_hir::is_fully_known(&self.resolve(param)) {
                let _ = self.solver.unify(param, arg);
            }
        }
        let concrete: Vec<_> = params.iter().map(|ty| self.resolve(ty)).collect();
        let result = if concrete.iter().all(brass_hir::is_fully_known) {
            let mut env = closure.scopes.clone();
            env.push(Scope::new(
                decl_params
                    .iter()
                    .zip(concrete)
                    .map(|(param, ty)| (param.name.clone(), ty))
                    .collect(),
            ));
            let saved_module = std::mem::replace(&mut self.current_module, closure.module.clone());
            let saved_self = std::mem::replace(&mut self.self_type, closure.self_type.clone());
            let saved_variant =
                std::mem::replace(&mut self.self_variant, closure.self_variant.clone());
            let mut props = LightProps::default();
            let ret = self.infer_expr_light(body, &env, &mut props);
            let ret = if props.errors.is_empty() {
                ret
            } else {
                self.result_from_payloads(Some(ret), &props.errors, false)
            };
            let ret = super::precompute::wrap_null_propagated_return(ret, &props.nulls);
            self.current_module = saved_module;
            self.self_type = saved_self;
            self.self_variant = saved_variant;
            self.resolve(&ret)
        } else {
            fallback
        };
        self.solver.rollback(snapshot);
        self.instantiating.remove(&key);
        Some(result)
    }
}
