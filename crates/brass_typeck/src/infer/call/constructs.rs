//! Language constructs keep their meaning in call position.

use super::*;

impl Checker<'_> {
    /// Type reflection and error constructs, and diagnose function bindings
    /// whose names denote constructs. Concurrency typing lives in builtins.
    pub(super) fn check_construct_call(
        &mut self,
        name: &str,
        args: &[Arg],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
        call_expected: Option<&Type>,
    ) -> Option<Type> {
        // Ownership inserts acquisitions with an empty closure span. They
        // do not call a source binding named `with`, so only written calls
        // need the function-binding diagnostic.
        let generated_acquire = name == "with"
            && matches!(
                args.get(1).map(|arg| &arg.expr),
                Some(Expr::Closure(_, _, closure_span)) if closure_span.lo == closure_span.hi
            );
        if !generated_acquire {
            self.check_construct_binding(name, span, scopes);
        }
        if name == "fields" {
            self.errors.push(TypeError {
                message: "`fields(..)` is a compile-time construct, usable only as a \
                      `for` loop iterable"
                    .to_string(),
                span,
            });
            return Some(self.fresh_unknown());
        }
        // `typeof(x)` in value position: a compile-time string constant, the
        // source name of x's static type (the same construct also names a
        // type in type/receiver position; see `resolve_annotation_scoped`
        // and `static_qualifier`). Only the argument is checked here: the name
        // itself is derived per monomorphic instance by the back ends
        // (`Rvalue::TypeName`), never recorded by span -- a generic body is
        // re-checked once per instantiation at the same span, and a
        // span-keyed name would leak the last instance's answer into all.
        if name == "typeof" {
            if args.len() != 1 {
                self.errors.push(TypeError {
                    message: format!("`typeof` takes 1 argument, found {}", args.len()),
                    span,
                });
            }
            let saved = std::mem::replace(&mut self.type_only_read, true);
            for a in args {
                self.check_expr(&a.expr, scopes);
            }
            self.type_only_read = saved;
            return Some(Type::Str);
        }
        // `error(x)` executes the ordinary prelude function, but its TYPE
        // is special-cased so the fully-known result can be seeded: the
        // Ok payload comes from the call's required position (nothing in
        // the expression itself can constrain it -- see the prelude's
        // `-> infer!`), and the Err payload is the prelude `Error` record
        // wrapping the argument's type, mirroring what the body builds.
        // `error` is a reserved callee name: a local binding (a match's
        // `Err { error }` payload) never shadows it in call position.
        if name == "error" {
            let signature_params = self
                .lookup_function(name)
                .map(|info| info.signature.params.clone());
            let value_ty = if let Some(params) = signature_params {
                // The specialized result construction below changes only the
                // return type. The ordinary signature still owns arity and the
                // explicit trailing Location argument's type.
                self.check_arg_count_range(name, &params, args.len(), span);
                let arg_types = self.check_signature_args_collect(&params, args, scopes);
                self.elaborate_error_body(&params, &arg_types, span);
                arg_types.into_iter().next().unwrap_or(Type::Void)
            } else {
                // A program without the prelude (unit tests, embedders)
                // has no signature to check the arguments against.
                let value_ty = args
                    .first()
                    .map(|a| self.check_expr(&a.expr, scopes))
                    .unwrap_or(Type::Void);
                for a in args.iter().skip(1) {
                    self.check_expr(&a.expr, scopes);
                }
                value_ty
            };
            // Without the prelude `Error` record the Err payload is the raw
            // argument.
            let err_ty = match self.program.prelude_type("Error") {
                Some(err_info) => {
                    let mut err = NominalType::new(err_info.id, &err_info.name);
                    err.substitution.insert("value", self.resolve(&value_ty));
                    Type::Record(err)
                }
                None => self.resolve(&value_ty),
            };
            let ok_ty = call_expected
                .and_then(|want| {
                    self.resolve(want)
                        .result_payloads()
                        .map(|(ok, _)| ok.clone())
                })
                .filter(brass_hir::is_fully_known)
                .unwrap_or_else(|| self.fresh_unknown());
            return Some(Type::result(ok_ty, err_ty));
        }
        None
    }
}
