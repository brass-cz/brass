//! Observe committed call edges around the authoritative elaboration routine.

use super::FunctionCall;
use crate::infer::Checker;
use brass_hir::{ParamInfo, Type};
use brass_parser::ast::Block;

impl Checker<'_> {
    /// Type a call of the free function `symbol` (defined in `module`) at
    /// `arg_types` by re-elaborating `body` at them, and return the call's
    /// result: the declared return when there is one, else the return this
    /// instantiation's body produces. A recursive call is typed against the
    /// elaboration in progress instead, and a call past the depth or budget
    /// limits (see `elaboration_allowed`) gets `fallback_ret`. A clean
    /// elaboration is memoized and, for an unannotated function with fully
    /// known inputs and return, published as an instance return
    /// (`Inference::instance_returns`).
    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn instantiate_function_call(
        &mut self,
        symbol: &str,
        module: &[String],
        params: &[ParamInfo],
        body: &Block,
        declared_ret: Option<Type>,
        fallback_ret: Type,
        arg_types: &[Type],
        span: brass_parser::Span,
    ) -> Type {
        let observation = (self.completion.active
            && self.speculation_depth == 0
            && !self.numeric.probing
            && !self.numeric_enabled
            && !self.co_checking)
            .then(|| {
                let caller = self.current_instance()?;
                if caller.numeric_layout.is_some() {
                    return None;
                }
                let caller = brass_hir::InstanceKey::new(
                    self.program,
                    caller.callable.clone(),
                    &caller.args,
                )?;
                let args: Vec<_> = arg_types.iter().map(|ty| self.resolve(ty)).collect();
                let callee = brass_hir::InstanceKey::function(self.program, symbol, &args)?;
                Some((caller, callee, self.depth_capped))
            })
            .flatten();
        let result = self.instantiate_function_call_inner(FunctionCall {
            symbol,
            module,
            params,
            body,
            declared_ret,
            fallback_ret,
            arg_types,
            span,
        });
        if let Some((caller, callee, before)) = observation {
            self.completion
                .observe(&caller, &callee, self.depth_capped != before);
        }
        result
    }
}
