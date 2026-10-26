//! Functions named as values whose trailing parameters are optional.
//!
//! A direct call may omit a function's trailing nullable parameters; a
//! function used as a value has the arity its use needs, from its required
//! parameters up to all of them (`["x", "y"].map(greet)` with `fun
//! greet(name: string, title: string?)` applies a one-parameter function,
//! the omitted `title` being `null`). Such a value is typed by an inference
//! variable that its first application or expected function type fixes to
//! the matching prefix of the signature; MIR lowering builds the forwarding
//! closure with that many parameters (it reads the arity back from the
//! value's checked type) and the forwarded call fills the rest with `null`.

use super::*;

/// The signature of a function used as a value with optional trailing
/// parameters.
#[derive(Clone)]
pub(super) struct FunctionValue {
    /// The source name, for diagnostics.
    name: String,
    /// The declared parameter types.
    params: Vec<Type>,
    /// The declared return type.
    ret: Type,
    /// How many leading parameters a use must supply.
    required: usize,
    /// The occurrence of the name.
    span: Span,
}

impl Checker<'_> {
    /// The type of the free function `name` used as a value at `span`: its
    /// signature when every parameter is required, an inference variable
    /// standing for "the signature at the arity its use needs" when trailing
    /// ones are optional, `None` when the signature does not fix the value's
    /// type (see `annotated_function_value_type`).
    pub(super) fn function_value_type(&mut self, name: &str, span: Span) -> Option<Type> {
        let fun = self.annotated_function_value_type(name)?;
        let required = helpers::required_arg_count(
            self.program,
            &self.lookup_function(name)?.signature.params,
        );
        let Type::Fun(params, ret) = &fun else {
            return Some(fun);
        };
        if required == params.len() {
            return Some(fun);
        }
        let var = self.fresh_unknown();
        let Type::Unknown(id) = var else {
            unreachable!("fresh_unknown is a variable");
        };
        self.function_values.insert(
            id,
            FunctionValue {
                name: name.to_string(),
                params: params.clone(),
                ret: (**ret).clone(),
                required,
                span,
            },
        );
        Some(var)
    }

    /// Apply the function value standing behind inference variable `id` (see
    /// [`Self::function_value_type`]) to `args`: the number of arguments picks
    /// the arity, each argument is checked against its declared parameter,
    /// and the value is fixed to that prefix of the signature. `None` when
    /// `id` stands for no such value.
    pub(super) fn apply_function_value(
        &mut self,
        id: u32,
        args: &[Arg],
        span: Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        let value = self.function_values.get(&id)?.clone();
        if args.len() < value.required || args.len() > value.params.len() {
            self.check_arg_count_range_counts(
                &value.name,
                value.required,
                value.params.len(),
                args.len(),
                span,
            );
        }
        for (arg, param) in args.iter().zip(&value.params) {
            self.check_expr_against(&arg.expr, param, scopes);
        }
        for arg in args.iter().skip(value.params.len()) {
            self.check_expr(&arg.expr, scopes);
        }
        let arity = args.len().clamp(value.required, value.params.len());
        let fixed = Type::Fun(value.params[..arity].to_vec(), Box::new(value.ret.clone()));
        let _ = self.solver.unify(&Type::Unknown(id), &fixed);
        Some(value.ret)
    }

    /// Fix the function value `got` (when it is one, see
    /// [`Self::function_value_type`]) to the arity of the function type `want`
    /// it is checked against, reporting at `span` a use whose arity or types
    /// the signature cannot serve. Returns whether `got` was such a value.
    pub(super) fn expect_function_value(&mut self, got: &Type, want: &Type, span: Span) -> bool {
        let Type::Unknown(id) = self.resolve_head(got) else {
            return false;
        };
        let Some(value) = self.function_values.remove(&id) else {
            return false;
        };
        let Type::Fun(params, _) = self.resolve(want) else {
            // Not a function position: the whole signature is the value.
            let full = Type::Fun(value.params.clone(), Box::new(value.ret.clone()));
            let _ = self.solver.unify(&Type::Unknown(id), &full);
            return true;
        };
        let arity = params.len();
        if arity < value.required || arity > value.params.len() {
            let full = Type::Fun(value.params.clone(), Box::new(value.ret.clone()));
            self.errors.push(TypeError {
                message: format!(
                    "cannot use function `{}` of type `{}` where `{}` is required",
                    value.name,
                    full.display(),
                    self.resolve(want).display()
                ),
                span,
            });
            let _ = self.solver.unify(&Type::Unknown(id), &full);
            return true;
        }
        let fixed = Type::Fun(value.params[..arity].to_vec(), Box::new(value.ret.clone()));
        let _ = self.solver.unify(&Type::Unknown(id), &fixed);
        true
    }

    /// Settle every function value with optional parameters once all bodies
    /// are checked: one its uses fixed must have an arity between its required
    /// and declared parameter counts and accept its declared parameters and
    /// result where the use's function type puts them; one no use fixed takes
    /// the whole signature.
    pub(super) fn settle_function_values(&mut self) {
        let values: Vec<(u32, FunctionValue)> = self.function_values.drain().collect();
        for (id, value) in values {
            let full = Type::Fun(value.params.clone(), Box::new(value.ret.clone()));
            match self.resolve(&Type::Unknown(id)) {
                Type::Unknown(_) => {
                    let _ = self.solver.unify(&Type::Unknown(id), &full);
                }
                Type::Fun(params, ret) => {
                    let fits = params.len() >= value.required
                        && params.len() <= value.params.len()
                        && params
                            .iter()
                            .zip(&value.params)
                            .all(|(used, declared)| self.can_unify(used, declared))
                        && self.can_unify(&ret, &value.ret);
                    if fits {
                        for (used, declared) in params.iter().zip(&value.params) {
                            let _ = self.solver.unify(used, declared);
                        }
                        let _ = self.solver.unify(&ret, &value.ret);
                    } else {
                        self.errors.push(TypeError {
                            message: format!(
                                "cannot use function `{}` of type `{}` where `{}` is required",
                                value.name,
                                full.display(),
                                self.resolve(&Type::Fun(params, ret)).display()
                            ),
                            span: value.span,
                        });
                    }
                }
                other => {
                    self.errors.push(TypeError {
                        message: format!(
                            "cannot use function `{}` of type `{}` where `{}` is required",
                            value.name,
                            full.display(),
                            other.display()
                        ),
                        span: value.span,
                    });
                }
            }
        }
    }
}
