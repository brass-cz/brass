//! Prepare implicit user renderers at their concrete receiver types.

use super::{LocalId, Monomorphizer, Operand, Type};
use crate::render::{RenderForm, renderer_dependencies};

impl Monomorphizer<'_, '_> {
    /// Instantiate every user method the shared renderer traversal can call.
    /// Each custom renderer owns its children and ordinary recursive calls.
    pub(super) fn prepare_rendering(
        &mut self,
        ty: &Type,
        form: RenderForm,
        cur_sym: &str,
        cur_ret: &Option<Type>,
    ) -> Result<bool, String> {
        let mut ready = true;
        for (receiver, method) in renderer_dependencies(self.program, ty, form) {
            match self.method_call_type(
                method,
                &[Operand::Local(LocalId(0))],
                cur_sym,
                cur_ret,
                &[Some(receiver.clone())],
            )? {
                None => ready = false,
                Some(Type::Str) => {}
                Some(other) => {
                    return Err(format!(
                        "`{method}` on `{}` must return `string`, found `{}`",
                        receiver.display(),
                        other.display()
                    ));
                }
            }
        }
        Ok(ready)
    }
}
