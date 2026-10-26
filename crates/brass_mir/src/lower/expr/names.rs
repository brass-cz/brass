//! Value names share one lexical precedence for references and calls.

use super::*;

/// The value namespace selected before lowering a reference or ordinary call.
pub(super) enum ValueName {
    Local,
    Global,
    Function,
    Unresolved,
}

impl FnLower<'_, '_> {
    /// Classify a name with the checker's local, global, then function order.
    pub(super) fn value_name(&self, name: &str) -> ValueName {
        if self.is_bound(name) {
            ValueName::Local
        } else if self.ctx.is_global_name(&self.module, name) {
            ValueName::Global
        } else if self.ctx.resolve_fn_symbol(&self.module, name).is_some() {
            ValueName::Function
        } else {
            ValueName::Unresolved
        }
    }

    /// Lower a bound value or a visible function used as a value.
    pub(crate) fn lower_ident(&mut self, name: &str) -> Operand {
        self.lower_ident_at(name, None)
    }

    /// Lower a source reference, preserving the checker's per-use closure type.
    pub(crate) fn lower_ident_at(&mut self, name: &str, span: Option<Span>) -> Operand {
        match self.value_name(name) {
            ValueName::Local => {
                if let Some(template) = self.lookup_template(name) {
                    return self.instantiate_template(&template, span);
                }
                let local = self.lookup(name).expect("local value binding");
                if self.is_cell(name) {
                    self.b.emit(Rvalue::Load(Place::projected(
                        local,
                        vec![Projection::Index(Operand::Const(Literal::Int(0)))],
                    )))
                } else {
                    Operand::Local(local)
                }
            }
            ValueName::Function => {
                let arity = self
                    .ctx
                    .function_arity(&self.module, name)
                    .expect("resolved function");
                self.lower_fn_value(name, arity, span)
            }
            ValueName::Global | ValueName::Unresolved => {
                let symbol = self.ctx.global_symbol(&self.module, name);
                match self.instantiate_global_template(&symbol, span) {
                    Some(value) => value,
                    None => self.b.emit(Rvalue::Global(symbol)),
                }
            }
        }
    }

    /// Whether this reference builds a fresh generalized closure value.
    pub(super) fn is_closure_template_use(&self, e: &Expr) -> bool {
        let Expr::Ident(name, _) = e else {
            return false;
        };
        match self.value_name(name) {
            ValueName::Local => self.lookup_template(name).is_some(),
            ValueName::Global => self
                .ctx
                .tables
                .global_templates
                .contains_key(&self.ctx.global_symbol(&self.module, name)),
            ValueName::Function | ValueName::Unresolved => false,
        }
    }
}
