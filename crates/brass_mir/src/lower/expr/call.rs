//! Call routing and argument lowering.

use super::names::ValueName;
use super::*;

impl FnLower<'_, '_> {
    /// Build the rvalue for a call, routing it structurally (free function,
    /// method, static call, builtin or function value). Side-effecting
    /// sub-expressions (receiver, args) are evaluated here in source order.
    pub(crate) fn lower_call(&mut self, callee: &Expr, args: &[Arg], span: Span) -> Rvalue {
        let value = self.lower_call_inner(callee, args, span);
        match value {
            Rvalue::Call(inner @ (Callee::Method(_) | Callee::Static { .. }), args)
                if self
                    .ctx
                    .numeric_calls
                    .iter()
                    .any(|((site, _), _)| *site == span) =>
            {
                Rvalue::Call(
                    Callee::Numeric {
                        inner: Box::new(inner),
                        site: span,
                    },
                    args,
                )
            }
            other => other,
        }
    }

    fn lower_call_inner(&mut self, callee: &Expr, args: &[Arg], span: Span) -> Rvalue {
        // `typeof(x)` in value position: the reflection builtin (the checker
        // reserves the name before any user binding). The operand is lowered
        // for its effects and the type NAME is left to the back ends, which
        // derive it from the operand's per-instance monomorphized type
        // (`Rvalue::TypeName`) -- baking a name here would fix one shared
        // answer across every instance of a generic body.
        if matches!(callee, Expr::Ident(n, _) if n == "typeof") {
            let op = self
                .lower_args(args)
                .into_iter()
                .next()
                .unwrap_or_else(Operand::void);
            return Rvalue::TypeName(op);
        }
        // `recv.method(args)` or `Type.method(args)`.
        if let Expr::Field(base, method, _) = callee
            && !callee.span().is_parenthesized()
        {
            // `typeof(v).method(args)`: a static call on v's type, whose name the
            // checker resolved into the type-name channel keyed by the inner
            // `typeof(v)` span. Route it exactly like a written `Type.method`.
            if let Expr::Call(c, operands, tspan) = &**base
                && matches!(&**c, Expr::Ident(n, _) if n == "typeof")
                && let Some(tname) = self.ctx.type_names.get(tspan)
            {
                let tn = tname.clone();
                // A compound operand (a call, an element read) runs for its
                // effects before the call, like any receiver; a name reads
                // nothing.
                if operands
                    .iter()
                    .any(|operand| !matches!(operand.expr, Expr::Ident(..) | Expr::SelfExpr(_)))
                {
                    self.lower_args(operands);
                }
                // A primitive type's `default()` folds to its zero value, as
                // the written `int64.default()` does.
                if let Some(lit) = primitive_default_literal(&tn, method) {
                    self.lower_args(args);
                    return Rvalue::Use(Operand::Const(lit));
                }
                if method == "from" && self.ctx.has_structural_from(&self.module, &tn) {
                    let source = self
                        .lower_args(args)
                        .into_iter()
                        .next()
                        .unwrap_or_else(Operand::void);
                    return Rvalue::RecordFrom { ty: tn, source };
                }
                return self.lower_static_call(&tn, method, args, span);
            }
            // `T.default()` for a primitive type word folds to its zero
            // value (the `Default` protocol's builtin implementations).
            if let Expr::Ident(tname, _) = &**base
                && !self.is_bound(tname)
                && let Some(lit) = primitive_default_literal(tname, method)
            {
                return Rvalue::Use(Operand::Const(lit));
            }
            if let Expr::Ident(tname, _) = &**base
                && !self.is_bound(tname)
                && self.ctx.is_type_word_in(&self.module, tname)
            {
                let tn = self.resolve_self_name(tname);
                // `T.from(v)` for a structure type `T`: a fallible structural
                // conversion. The result is `T?` -- the record built from `v`'s
                // fields when the (monomorphized) `v` has all of `T`'s, else null.
                // The back ends read the fields and make the presence decision per
                // instance, so the lowering only carries the target type and source.
                if method == "from" && self.ctx.has_structural_from(&self.module, &tn) {
                    let source = self
                        .lower_args(args)
                        .into_iter()
                        .next()
                        .unwrap_or_else(Operand::void);
                    return Rvalue::RecordFrom { ty: tn, source };
                }
                return self.lower_static_call(&tn, method, args, span);
            }
            // A sum variant qualifier is a static receiver, including aliases
            // and module markers; evaluating it as a value loses its type. A
            // UNIT variant calling an instance method is the exception: the
            // variant is a value of its sum and receives the call
            // (`L.Nil.size()`), so it falls through to the instance path.
            if let Expr::Field(sum, variant, _) = &**base
                && let Expr::Ident(type_name, _) = &**sum
                && !self.is_bound(type_name)
                && let Some(info) = self
                    .ctx
                    .program
                    .resolve_type_or_alias(&self.module, &self.resolve_self_name(type_name))
                && let Some(var) = info.variant(variant)
                && !(var.fields.is_empty()
                    && var
                        .methods
                        .get(method.as_str())
                        .is_some_and(|m| m.decl.params.first().is_some_and(|p| p.name == "self")))
            {
                let ty = info.symbol.clone();
                let defaults = self.ctx.static_call_defaults(&self.module, &ty, method);
                let mut ops = self.lower_args(args);
                self.complete_call_args(defaults.as_deref(), &mut ops, span);
                return Rvalue::Call(
                    Callee::Static {
                        ty,
                        method: method.clone(),
                    },
                    ops,
                );
            }
            // `method` names a *method*: omitted trailing arguments are
            // completed from the signature the checker resolved for this
            // receiver (see `lower_method_call`), never by looking the name up
            // as a free function, whose same-named signature is unrelated.
            let recv = self.lower_expr(base);
            let recv = self.hold(recv, &assigned_names(args.iter().map(|a| &a.expr)));
            // A FIELD call -- `a.func(4)` loads the function-typed field and
            // calls it indirectly -- where the checker resolved the call to a
            // field (whatever methods of that name other types declare), or,
            // lowering without a checked program, where no type's method
            // table (nor the primitive-method table) knows the name. A call
            // the instantiations of a generic body resolve both ways
            // branches on the receiver's type, which every instance folds.
            let field_call = match self.ctx.field_calls.get(&span) {
                Some(Some(receivers)) => {
                    let receivers = receivers.clone();
                    return self.lower_field_or_method_call(recv, method, args, span, &receivers);
                }
                Some(None) => true,
                None => !self.ctx.method_name_exists(method),
            };
            if field_call {
                let obj = self.b.make_local(recv);
                let ops = self.lower_args(args);
                return self.field_call(obj, method, ops);
            }
            let mut ops = vec![recv];
            ops.extend(self.lower_args(args));
            // A keyed call whose instances dispatch to different
            // specializations names its site; monomorphization picks the
            // specialization per instance. The specializations of one call
            // share their signature shape, so any one decides the omitted
            // trailing arguments (a specialization takes its caller's
            // `Location`).
            if let Some(per_instance) = self.ctx.instance_dispatch.get(&span) {
                let mut targets: Vec<&String> = per_instance.values().collect();
                targets.sort();
                let defaults = targets
                    .first()
                    .and_then(|target| self.ctx.instance_call_defaults(span, target));
                self.complete_call_args(defaults.as_deref(), &mut ops, span);
                return Rvalue::Call(
                    Callee::Keyed {
                        method: method.clone(),
                        site: span,
                    },
                    ops,
                );
            }
            // A keyed call dispatches to its generated specialization, whose
            // signature (not the template's) decides the omitted trailing
            // arguments: a specialization takes its caller's `Location`.
            let method = self
                .ctx
                .keyed_dispatch
                .get(&span)
                .cloned()
                .unwrap_or_else(|| method.clone());
            return self.lower_method_call(method, ops, span);
        }
        if let Expr::Ident(name, _) = callee {
            // Local and global callable bindings are called indirectly.
            // Construct calls bypass value bindings, including module globals.
            if !matches!(name.as_str(), "error" | "spawn" | "with")
                && matches!(self.value_name(name), ValueName::Local | ValueName::Global)
            {
                // Read the value the way any use of the name reads it: a
                // binding promoted to a shared cell holds the closure in the
                // cell's element 0, not in the cell local itself, and a
                // generalized closure binding builds this use's own closure.
                let value = self.lower_ident_at(name, Some(callee.span()));
                let callee = self.hold(value, &assigned_names(args.iter().map(|a| &a.expr)));
                let ops = self.lower_args(args);
                return Rvalue::Call(Callee::Indirect(callee), ops);
            }
            // A known free function resolves to its storage symbol. An argument
            // the checker recorded as view-convertible (an anonymous structural
            // value fitting an eligible parameter's row) is converted into that
            // parameter's view at the call boundary, so every argument shape
            // with the same view selects one callee instance.
            if !matches!(name.as_str(), "spawn" | "with")
                && let Some(symbol) = self.ctx.resolve_fn_symbol(&self.module, name)
            {
                let exprs: Vec<&Expr> = args.iter().map(|a| &a.expr).collect();
                let later = later_assigned(&exprs);
                let mut ops = Vec::with_capacity(args.len());
                for (i, a) in args.iter().enumerate() {
                    let v = self.lower_expr(&a.expr);
                    let v = self.hold(v, &later[i]);
                    if self.ctx.is_view_arg(a.expr.span()) {
                        ops.push(self.b.emit(Rvalue::RecordView {
                            callee: symbol.clone(),
                            param: i,
                            source: v,
                        }));
                    } else {
                        ops.push(v);
                    }
                }
                let defaults = self.ctx.free_call_defaults(&self.module, name);
                self.complete_call_args(defaults.as_deref(), &mut ops, span);
                let callee = if self
                    .ctx
                    .numeric_calls
                    .iter()
                    .any(|((site, _), flavor)| *site == span && flavor.is_some())
                {
                    Callee::NumericFree {
                        base: symbol,
                        site: span,
                    }
                } else {
                    Callee::Free(symbol)
                };
                return Rvalue::Call(callee, ops);
            }
            // A program lowered without the prelude (unit tests, embedders)
            // has no `error` function to resolve to; the builtin desugar
            // still constructs the Err there.
            if name == "error" {
                let payload = match args.first() {
                    Some(a) => self.lower_expr(&a.expr),
                    None => Operand::void(),
                };
                return Rvalue::Variant {
                    ty: "Result".to_string(),
                    variant: "Err".to_string(),
                    fields: vec![("error".to_string(), payload)],
                };
            }
            // `with(c, (x) -> ..)` hands the closure the shared object
            // itself: its parameter is the guarded value, so a closure
            // literal there borrows its parameter instead of copying it.
            if name == "with"
                && let [
                    cown,
                    Arg {
                        expr: Expr::Closure(params, body, span),
                    },
                ] = args
            {
                let cown = self.lower_expr(&cown.expr);
                let f = self.lower_closure_passing(params, body, ParamPassing::Borrow, Some(*span));
                return Rvalue::Call(Callee::Builtin(name.clone()), vec![cown, f]);
            }
            // Otherwise it is a runtime builtin.
            let ops = self.lower_args(args);
            return Rvalue::Call(Callee::Builtin(name.clone()), ops);
        }
        // Any other callee expression evaluates to a closure/function value.
        let clo = self.lower_expr(callee);
        let clo = self.hold(clo, &assigned_names(args.iter().map(|a| &a.expr)));
        let ops = self.lower_args(args);
        Rvalue::Call(Callee::Indirect(clo), ops)
    }

    /// Build the `Location` record for the call at `span` (the implicit
    /// caller-location argument).
    pub(super) fn location_operand(&mut self, span: Span) -> Operand {
        let (file, line, col) = self.ctx.call_location(span);
        self.b.emit(Rvalue::Record {
            ty: self
                .ctx
                .program
                .prelude_type("Location")
                .map(|info| info.symbol.clone())
                .unwrap_or_else(|| "Location".into()),
            fields: vec![
                ("file".to_string(), Operand::Const(Literal::Str(file))),
                (
                    "line".to_string(),
                    Operand::Const(Literal::Int(line as i128)),
                ),
                ("col".to_string(), Operand::Const(Literal::Int(col as i128))),
            ],
        })
    }

    /// Lower call arguments left to right (see [`Self::lower_in_order`]).
    pub(super) fn lower_args(&mut self, args: &[Arg]) -> Vec<Operand> {
        self.lower_in_order(&args.iter().map(|a| &a.expr).collect::<Vec<_>>())
    }

    /// Fill every omitted optional parameter from one resolved signature.
    /// Nullable defaults and the implicit caller location may be interleaved in
    /// the trailing optional run accepted by the checker.
    pub(super) fn complete_call_args(
        &mut self,
        defaults: Option<&[crate::lower::CallDefault]>,
        ops: &mut Vec<Operand>,
        span: Span,
    ) {
        let Some(defaults) = defaults else {
            return;
        };
        for default in defaults.iter().skip(ops.len()) {
            match default {
                crate::lower::CallDefault::Nullable => ops.push(Operand::Const(Literal::Null)),
                crate::lower::CallDefault::Location => {
                    let location = self.location_operand(span);
                    ops.push(location);
                }
                crate::lower::CallDefault::Required => break,
            }
        }
    }
}
