//! Expression lowering: flattening to three-address form and the value-bearing
//! control-flow constructs (`&&`/`||`/`if`/`if let`/`match`/`expr!`).
//!
//! Every [`FnLower::lower_expr`] returns an [`Operand`] naming the result. Plain
//! computations emit one assignment to a fresh temporary; branching constructs
//! allocate a result local that each arm writes before jumping to the merge
//! block. Call routing, field/element reads, literals, and constructors mirror
//! the AST-walking codegen so the two stay behaviorally equivalent.

use brass_hir::Type;
use brass_parser::Span;
use brass_parser::ast::{Arg, BinOp, Block, Expr, Param, Stmt, StrSeg};

use crate::analysis::free_vars_of;
use crate::cfg::{MirStmt, Terminator};
use crate::ids::{BlockId, LocalId};
use crate::lower::{FnLower, ProgramCtx};
use crate::program::MirClosure;
use crate::value::{Callee, Literal, Operand, Place, Projection, Rvalue};

/// Whether a checker-resolved call result is worth seeding onto its result
/// local: a record/sum whose field types the back end could otherwise fail to
/// infer for a witness-free constructor (the array fields inside are seeded from
/// the record's substitution). Bare arrays/scalars/strings the back end always
/// re-derives from how the value is built and used, so they keep an inferred
/// `Var` -- seeding them is unnecessary and perturbs value ownership.
fn is_seedable_result(ty: &Type) -> bool {
    matches!(ty, Type::Record(_) | Type::Sum(_))
}

/// Whether a checker-resolved array-literal type must be seeded onto its result
/// local: a slice/array whose *element representation* the back end would
/// re-derive differently from the element values alone. A nullable element is a
/// heap cell, not the bare value; a non-default numeric element (`int64[]`,
/// `uint8[]`, `float32[]`) has a different width than the literal's int32 /
/// float64 default -- either way the buffer built at the re-derived type would
/// be reinterpreted at the annotated one and corrupt every element. Literals
/// whose element matches the derived representation keep an inferred `Var`
/// (see [`is_seedable_result`] for why seeding is otherwise avoided).
fn array_element_needs_seed(ty: &Type) -> bool {
    use brass_hir::{FloatKind, IntKind};
    let elem = match ty {
        Type::Slice(e) | Type::Array(e, _) => e,
        _ => return false,
    };
    match elem.as_ref() {
        Type::Nullable(_) => true,
        Type::Int(k) => *k != IntKind::I32,
        Type::Float(f) => *f != FloatKind::F64,
        _ => false,
    }
}

/// The zero value `T.default()` folds to for a primitive type word.
fn primitive_default_literal(tname: &str, method: &str) -> Option<Literal> {
    if method != "default" {
        return None;
    }
    if brass_hir::IntKind::from_name(tname).is_some() {
        return Some(Literal::Int(0));
    }
    match tname {
        "float32" | "float64" => Some(Literal::Float(0.0)),
        "bool" => Some(Literal::Bool(false)),
        "string" => Some(Literal::Str(String::new())),
        _ => None,
    }
}

impl<'a, 'p> FnLower<'a, 'p> {
    /// Lower an expression to an operand naming its value; a value the checker
    /// accepted as a declared sum subtype at this expression is then rebuilt
    /// as the parent sum (see [`Self::apply_sum_view`]).
    pub(crate) fn lower_expr(&mut self, e: &Expr) -> Operand {
        let op = self.lower_expr_inner(e);
        if let Some(target) = self.ctx.sum_view_target(e.span()) {
            let target = target.clone();
            return self.apply_sum_view(&target, op);
        }
        op
    }

    fn lower_expr_inner(&mut self, e: &Expr) -> Operand {
        match e {
            Expr::Int(v, _) => Operand::Const(Literal::Int(*v)),
            Expr::Float(v, _) => Operand::Const(Literal::Float(*v)),
            Expr::Bool(b, _) => Operand::Const(Literal::Bool(*b)),
            Expr::Null(_) => Operand::Const(Literal::Null),
            Expr::Str(segs, _) => self.lower_string(segs),
            Expr::Ident(name, _) => self.lower_ident(name),
            Expr::SelfExpr(_) => self.lower_ident("self"),
            Expr::Unary(op, a, _) => {
                let v = self.lower_expr(a);
                self.b.emit(Rvalue::Un(*op, v))
            }
            Expr::Binary(op, a, b, _) => self.lower_binary(*op, a, b),
            Expr::Call(callee, args, span) => {
                let rv = self.lower_call(callee, args, *span);
                // A call whose checker-resolved result is a constructed aggregate
                // (a record/sum/array) seeds its result local `Known`, so the back
                // end follows the instance type the caller fixed -- the path a
                // witness-free constructor (`HashMap.new()`) depends on. Other
                // calls keep an inferred `Var` local.
                match self.ctx.expr_type(*span) {
                    Some(ty) if is_seedable_result(ty) => self.b.emit_known(rv, ty.clone()),
                    _ => self.b.emit(rv),
                }
            }
            Expr::Field(base, name, _) => self.lower_field(base, name),
            Expr::Index(base, idx, _) => self.lower_index(base, idx),
            Expr::ErrorProp(inner, span) => self.lower_error_prop(inner, *span),
            Expr::Closure(params, body, _) => self.lower_closure(params, body),
            Expr::Array(es, span) => self.lower_array(es, *span),
            Expr::Range(lo, hi, span) => self.lower_range(lo, hi, *span),
            Expr::TypeLit(name, fields, span) => self.lower_record(name, fields, *span),
            Expr::VariantLit(ty, variant, fields, _) => self.lower_variant(ty, variant, fields),
            Expr::If(cond, then, els, _) => self.lower_if(cond, then, els.as_deref()),
            Expr::IfLet(pat, scrut, then, els, _) => {
                self.lower_iflet(pat, scrut, then, els.as_deref())
            }
            Expr::Match(scrut, arms, _) => self.lower_match(scrut, arms),
            Expr::Block(b, _) => self.lower_block_value(b),
        }
    }

    /// Rebuild `source` (a value of a declared sum subtype) as its parent sum
    /// `target`: test the value's variant, load the parent's fields for that
    /// variant (variant-scoped projections, tag-safe under the test), and
    /// construct the parent's variant from them. The child may carry extra
    /// (width) fields; the rebuild drops them, which is what declared sum
    /// subtyping means at a flow point -- identity flow would misread the
    /// unboxed layout. The result local is seeded with the parent instance
    /// the checker resolved, so monomorphization follows it in any position.
    fn apply_sum_view(&mut self, target: &Type, source: Operand) -> Operand {
        let Type::Sum(n) = target else {
            return source;
        };
        let Some(info) = self.ctx.program.type_by_id(n.id) else {
            return source;
        };
        let brass_hir::TypeKind::Sum { variants } = &info.kind else {
            return source;
        };
        let symbol = info.symbol.clone();
        let variants: Vec<(String, Vec<String>)> = variants
            .iter()
            .map(|v| {
                (
                    v.name.clone(),
                    v.fields.iter().map(|f| f.name.clone()).collect(),
                )
            })
            .collect();
        let src = self.b.make_local(source);
        let res = if brass_hir::is_fully_known(target) {
            self.b.fresh_local_typed(None, target.clone())
        } else {
            self.b.fresh_local(None)
        };
        let merge_bb = self.b.new_block();
        for (vname, fields) in &variants {
            let arm_bb = self.b.new_block();
            let next_bb = self.b.new_block();
            let cond = self.b.emit(Rvalue::Call(
                Callee::Builtin("value_matches".into()),
                vec![
                    Operand::Local(src),
                    Operand::Const(Literal::Str(vname.clone())),
                ],
            ));
            self.b.terminate(Terminator::CondBranch {
                cond,
                then: arm_bb,
                els: next_bb,
            });
            self.b.switch_to(arm_bb);
            let built: Vec<(String, Operand)> = fields
                .iter()
                .map(|f| {
                    let key = format!("{vname}.{f}");
                    let load =
                        Rvalue::Load(Place::projected(src, vec![Projection::Field(key.clone())]));
                    // Seed the loaded payload with the target instance's own
                    // type for this slot: an arm the value never takes (the
                    // guard above proves it) has no inferable type of its own,
                    // and the target instance is what the rebuild constructs.
                    let v = match n
                        .substitution
                        .get(&key)
                        .filter(|t| brass_hir::is_fully_known(t))
                    {
                        Some(ft) => self.b.emit_known(load, ft.clone()),
                        None => self.b.emit(load),
                    };
                    (f.clone(), v)
                })
                .collect();
            let rebuild = Rvalue::Variant {
                ty: symbol.clone(),
                variant: vname.clone(),
                fields: built,
            };
            // The construction IS the target instance; seed it so the arm
            // types without an enclosing-return Result to borrow from.
            let v = if brass_hir::is_fully_known(target) {
                self.b.emit_known(rebuild, target.clone())
            } else {
                self.b.emit(rebuild)
            };
            self.b.push(MirStmt::Assign(res, Rvalue::Use(v)));
            self.b.terminate(Terminator::Goto(merge_bb));
            self.b.switch_to(next_bb);
        }
        // The checker enforced variant-set equality at the declaration, so the
        // value is always one of the parent's variants.
        self.b.push(MirStmt::Eval(Rvalue::Call(
            Callee::Builtin("panic".into()),
            vec![Operand::Const(Literal::Str(
                "unreachable: sum subtype coercion saw an unknown variant".into(),
            ))],
        )));
        self.b.terminate(Terminator::Unreachable);
        self.b.switch_to(merge_bb);
        Operand::Local(res)
    }

    /// A bare identifier: a bound local, otherwise a module global read.
    pub(crate) fn lower_ident(&mut self, name: &str) -> Operand {
        // A cell-promoted name reads element 0 of its one-element cell array.
        if self.is_cell(name)
            && let Some(local) = self.lookup(name)
        {
            let zero = Operand::Const(Literal::Int(0));
            return self.b.emit(Rvalue::Load(Place::projected(
                local,
                vec![Projection::Index(zero)],
            )));
        }
        match self.lookup(name) {
            Some(local) => Operand::Local(local),
            // A bare reference to a top-level function (not a local, not a global
            // binding) is a first-class function value: eta-expand it into a
            // forwarding closure so it lowers exactly like the closure a caller
            // could write by hand, and the back ends need no dedicated fn-value.
            None => match self.ctx.function_arity(&self.module, name) {
                Some(arity) => self.lower_fn_value(name, arity),
                // Global storage is keyed per defining module, so the read
                // resolves the bare name to that module's key.
                None => self
                    .b
                    .emit(Rvalue::Global(self.ctx.global_symbol(&self.module, name))),
            },
        }
    }

    /// Eta-expand a bare reference to top-level function `name` of `arity`
    /// parameters into the forwarding closure `(a0, .., a{n-1}) -> name(a0, ..,
    /// a{n-1})`. Reuses closure lowering, so the value is an ordinary closure the
    /// monomorphizer and both back ends already handle.
    fn lower_fn_value(&mut self, name: &str, arity: usize) -> Operand {
        use brass_parser::ast::{Arg, Param};
        let span = brass_parser::Span::new(0, 0);
        let names: Vec<String> = (0..arity).map(|i| format!("__eta{i}")).collect();
        let params: Vec<Param> = names
            .iter()
            .map(|n| Param {
                name: n.clone(),
                ty: None,
                span,
            })
            .collect();
        let args: Vec<Arg> = names
            .iter()
            .map(|n| Arg {
                expr: Expr::Ident(n.clone(), span),
            })
            .collect();
        let body = Expr::Call(Box::new(Expr::Ident(name.to_string(), span)), args, span);
        self.lower_closure(&params, &body)
    }

    fn lower_binary(&mut self, op: BinOp, a: &Expr, b: &Expr) -> Operand {
        match op {
            // `&&`/`||` short-circuit and so become control flow.
            BinOp::And | BinOp::Or => self.lower_logical(op, a, b),
            _ => {
                let la = self.lower_expr(a);
                let lb = self.lower_expr(b);
                self.b.emit(Rvalue::Bin(op, la, lb))
            }
        }
    }

    /// `a && b` / `a || b`: evaluate `b` only when `a` does not already decide
    /// the result. The result local holds the boolean outcome.
    fn lower_logical(&mut self, op: BinOp, a: &Expr, b: &Expr) -> Operand {
        let res = self.b.fresh_local(None);
        let la = self.lower_expr(a);
        let rhs_bb = self.b.new_block();
        let skip_bb = self.b.new_block();
        let merge_bb = self.b.new_block();
        // And: a true -> evaluate rhs, else short-circuit false.
        // Or:  a true -> short-circuit true, else evaluate rhs.
        let (then, els) = match op {
            BinOp::And => (rhs_bb, skip_bb),
            _ => (skip_bb, rhs_bb),
        };
        self.b.terminate(Terminator::CondBranch {
            cond: la,
            then,
            els,
        });

        self.b.switch_to(rhs_bb);
        let rb = self.lower_expr(b);
        self.b.push(MirStmt::Assign(res, Rvalue::Use(rb)));
        self.b.terminate(Terminator::Goto(merge_bb));

        self.b.switch_to(skip_bb);
        let short = matches!(op, BinOp::Or);
        self.b.push(MirStmt::Assign(
            res,
            Rvalue::Use(Operand::Const(Literal::Bool(short))),
        ));
        self.b.terminate(Terminator::Goto(merge_bb));

        self.b.switch_to(merge_bb);
        Operand::Local(res)
    }

    /// `if cond { then } else { els }` as a value: each arm writes the result.
    fn lower_if(&mut self, cond: &Expr, then: &Block, els: Option<&Expr>) -> Operand {
        let res = self.b.fresh_local(None);
        let c = self.lower_expr(cond);
        let then_bb = self.b.new_block();
        let else_bb = self.b.new_block();
        let merge_bb = self.b.new_block();
        self.b.terminate(Terminator::CondBranch {
            cond: c,
            then: then_bb,
            els: else_bb,
        });

        let mut reached = false;
        self.b.switch_to(then_bb);
        let tv = self.lower_block_value(then);
        if !self.b.terminated() {
            self.b.push(MirStmt::Assign(res, Rvalue::Use(tv)));
            self.b.terminate(Terminator::Goto(merge_bb));
            reached = true;
        }

        self.b.switch_to(else_bb);
        let ev = match els {
            Some(e) => self.lower_expr(e),
            None => Operand::void(),
        };
        if !self.b.terminated() {
            self.b.push(MirStmt::Assign(res, Rvalue::Use(ev)));
            self.b.terminate(Terminator::Goto(merge_bb));
            reached = true;
        }

        self.b.switch_to(merge_bb);
        self.seal_value_merge(res, reached)
    }

    /// Finalize a value-producing construct (`if`/`if let`/`match`) at its merge
    /// block: when no arm reached the merge (all diverged), the merge is dead, so
    /// give the result local a value -- keeping it typeable -- and terminate the
    /// block, so a trailing implicit return never reads an unassigned local.
    fn seal_value_merge(&mut self, res: LocalId, reached: bool) -> Operand {
        if !reached {
            self.b
                .push(MirStmt::Assign(res, Rvalue::Use(Operand::void())));
            self.b.terminate(Terminator::Unreachable);
        }
        Operand::Local(res)
    }

    /// `if let pat = scrut { then } else { els }`: test the pattern, bind on the
    /// success arm, and merge like an ordinary `if`.
    fn lower_iflet(
        &mut self,
        pat: &brass_parser::ast::Pattern,
        scrut: &Expr,
        then: &Block,
        els: Option<&Expr>,
    ) -> Operand {
        let res = self.b.fresh_local(None);
        let subj = self.lower_expr(scrut);
        let subj = self.b.make_local(subj);
        // A plain (non-variant) binding in `if let` is a *presence* test, not the
        // catch-all it is in `match`: `if let x = e` runs the then-arm only when `e`
        // is present. The test is the `__present` builtin over the subject -- a
        // nullable tests non-null, while ANY non-nullable value is an irrefutable
        // bind that folds to always-then (including a `false` bool, which a plain
        // truthiness condition would wrongly branch on). This is what lets
        // `if let p = T.from(v)` (whose result is `T?`) take the else arm when the
        // conversion yields null. Other patterns test as usual.
        let cond = match pat {
            brass_parser::ast::Pattern::Binding(name, _) if !self.is_variant_name(name) => {
                self.b.emit(Rvalue::Call(
                    Callee::Builtin("__present".into()),
                    vec![Operand::Local(subj)],
                ))
            }
            _ => self.lower_pattern_cond(pat, subj),
        };
        let then_bb = self.b.new_block();
        let else_bb = self.b.new_block();
        let merge_bb = self.b.new_block();
        self.b.terminate(Terminator::CondBranch {
            cond,
            then: then_bb,
            els: else_bb,
        });

        let mut reached = false;
        self.b.switch_to(then_bb);
        self.push_scope();
        // A plain binding on a nullable scrutinee binds the *unwrapped* value (the
        // then-arm has proven it non-null), so `p` has the value type rather than
        // the nullable -- `__nonnull` narrows it (and is the identity for a
        // non-nullable). Other patterns bind their parts as usual.
        match pat {
            brass_parser::ast::Pattern::Binding(name, _) if !self.is_variant_name(name) => {
                let nn = self.b.emit(Rvalue::Call(
                    Callee::Builtin("__nonnull".into()),
                    vec![Operand::Local(subj)],
                ));
                self.bind_value(name, nn);
            }
            _ => self.lower_pattern_bind(pat, subj),
        }
        let tv = self.lower_block_value(then);
        self.pop_scope();
        if !self.b.terminated() {
            self.b.push(MirStmt::Assign(res, Rvalue::Use(tv)));
            self.b.terminate(Terminator::Goto(merge_bb));
            reached = true;
        }

        self.b.switch_to(else_bb);
        let ev = match els {
            Some(e) => self.lower_expr(e),
            None => Operand::void(),
        };
        if !self.b.terminated() {
            self.b.push(MirStmt::Assign(res, Rvalue::Use(ev)));
            self.b.terminate(Terminator::Goto(merge_bb));
            reached = true;
        }

        self.b.switch_to(merge_bb);
        self.seal_value_merge(res, reached)
    }

    /// `match scrut { pat => body, ... }`: a linear chain of pattern tests, each
    /// arm binding then writing the result. Falling off the end panics, so the
    /// post-match merge is reached only by a matching arm.
    fn lower_match(&mut self, scrut: &Expr, arms: &[brass_parser::ast::MatchArm]) -> Operand {
        let res = self.b.fresh_local(None);
        let subj = self.lower_expr(scrut);
        let subj = self.b.make_local(subj);
        let merge_bb = self.b.new_block();
        let mut reached = false;
        for arm in arms {
            let arm_bb = self.b.new_block();
            let next_bb = self.b.new_block();
            let cond = self.lower_pattern_cond(&arm.pattern, subj);
            self.b.terminate(Terminator::CondBranch {
                cond,
                then: arm_bb,
                els: next_bb,
            });
            self.b.switch_to(arm_bb);
            self.push_scope();
            self.lower_pattern_bind(&arm.pattern, subj);
            let v = self.lower_expr(&arm.body);
            self.pop_scope();
            if !self.b.terminated() {
                self.b.push(MirStmt::Assign(res, Rvalue::Use(v)));
                self.b.terminate(Terminator::Goto(merge_bb));
                reached = true;
            }
            self.b.switch_to(next_bb);
        }
        // No arm matched: panic and diverge.
        self.b.push(MirStmt::Eval(Rvalue::Call(
            Callee::Builtin("panic".into()),
            vec![Operand::Const(Literal::Str(
                "no match arm matched the value".into(),
            ))],
        )));
        self.b.terminate(Terminator::Unreachable);
        self.b.switch_to(merge_bb);
        self.seal_value_merge(res, reached)
    }

    /// `expr!`: unwrap a `Result.Ok` -- or, for a nullable operand (a span the
    /// checker recorded in `null_props`), unwrap the non-null value. The
    /// failure arm returns the error `Result` unchanged -- or, for a nullable
    /// operand, returns `null` itself (the enclosing callable's return type is
    /// then nullable) -- or aborts the program when this body is an entry
    /// point (`abort_error_prop`). Expressed as an explicit branch (MIR
    /// lowering: error propagation lives in the CFG, not in a codegen
    /// heuristic).
    fn lower_error_prop(&mut self, inner: &Expr, span: brass_parser::Span) -> Operand {
        let nullable = self.ctx.is_null_prop(span);
        let v = self.lower_expr(inner);
        let v = self.b.make_local(v);
        let res = self.b.fresh_local(None);
        // A nullable operand succeeds on presence; a Result succeeds on `Ok`.
        let test = if nullable {
            "__present"
        } else {
            "result_is_ok"
        };
        let is_ok = self.b.emit(Rvalue::Call(
            Callee::Builtin(test.into()),
            vec![Operand::Local(v)],
        ));
        let ok_bb = self.b.new_block();
        let err_bb = self.b.new_block();
        let cont_bb = self.b.new_block();
        self.b.terminate(Terminator::CondBranch {
            cond: is_ok,
            then: ok_bb,
            els: err_bb,
        });

        self.b.switch_to(ok_bb);
        let val = if nullable {
            // Narrow the proven-non-null value (same shape as `if let`).
            self.b.emit(Rvalue::Call(
                Callee::Builtin("__nonnull".into()),
                vec![Operand::Local(v)],
            ))
        } else {
            self.b.emit(Rvalue::Load(Place::projected(
                v,
                vec![Projection::Field("value".into())],
            )))
        };
        self.b.push(MirStmt::Assign(res, Rvalue::Use(val)));
        self.b.terminate(Terminator::Goto(cont_bb));

        self.b.switch_to(err_bb);
        if self.abort_error_prop {
            self.abort_failed_prop(v, nullable);
        } else if nullable {
            // A nullable's null is returned as-is: the enclosing callable's
            // return type is nullable (`T?`, or `Result<..>?` when the body
            // also raises errors).
            self.b
                .terminate(Terminator::Return(Operand::Const(Literal::Null)));
        } else if self.ctx.lift_errs.contains(&span) {
            // The checker marked this propagation as LIFTING: the payload is
            // re-raised wrapped into the prelude `Error`, gaining this site's
            // position (the abort path above keeps the original payload, so a
            // never-wrapped chain renders as before).
            let lifted = self.lift_propagated_err(v, span);
            self.b.terminate(Terminator::Return(lifted));
        } else {
            // Propagate the error Result unchanged.
            self.b.terminate(Terminator::Return(Operand::Local(v)));
        }

        self.b.switch_to(cont_bb);
        Operand::Local(res)
    }

    /// Rebuild a propagated Err whose payload the checker marked for lifting:
    /// `Err { error: Error { value: <old payload>, location: <this site>,
    /// frames: [] } }`, mirroring what `error(..)` builds.
    fn lift_propagated_err(&mut self, v: LocalId, span: brass_parser::Span) -> Operand {
        let old = self.b.emit(Rvalue::Load(Place::projected(
            v,
            vec![Projection::Field("error".into())],
        )));
        let loc = self.location_operand(span);
        let frames = match self
            .ctx
            .concrete_nominal_ref(&self.module, "Frame")
            .map(|t| Type::Slice(Box::new(t)))
        {
            Some(t) => self.b.fresh_local_typed(None, t),
            None => self.b.fresh_local(None),
        };
        self.b
            .push(MirStmt::Assign(frames, Rvalue::Array(Vec::new())));
        let err = self.b.emit(Rvalue::Record {
            ty: "Error".to_string(),
            fields: vec![
                ("value".to_string(), old),
                ("location".to_string(), loc),
                ("frames".to_string(), Operand::Local(frames)),
            ],
        });
        self.b.emit(Rvalue::Variant {
            ty: "Result".to_string(),
            variant: "Err".to_string(),
            fields: vec![("error".to_string(), err)],
        })
    }

    /// Rebuild a forwarded Result so its Err arm carries the LIFTED payload
    /// (see [`Self::lift_propagated_err`]); the Ok arm passes through. The
    /// ERR block is created first on purpose: the merged result local takes
    /// its type from the first assignment monomorphization sees, and the Err
    /// arm's construction is the one carrying the callable's lifted Result.
    pub(crate) fn wrap_forwarded_err(
        &mut self,
        source: Operand,
        span: brass_parser::Span,
    ) -> Operand {
        let src = self.b.make_local(source);
        let res = self.b.fresh_local(None);
        let cond = self.b.emit(Rvalue::Call(
            Callee::Builtin("result_is_ok".into()),
            vec![Operand::Local(src)],
        ));
        let err_bb = self.b.new_block();
        let ok_bb = self.b.new_block();
        let merge_bb = self.b.new_block();
        self.b.terminate(Terminator::CondBranch {
            cond,
            then: ok_bb,
            els: err_bb,
        });
        self.b.switch_to(err_bb);
        let lifted = self.lift_propagated_err(src, span);
        self.b.push(MirStmt::Assign(res, Rvalue::Use(lifted)));
        self.b.terminate(Terminator::Goto(merge_bb));
        self.b.switch_to(ok_bb);
        self.b
            .push(MirStmt::Assign(res, Rvalue::Use(Operand::Local(src))));
        self.b.terminate(Terminator::Goto(merge_bb));
        self.b.switch_to(merge_bb);
        Operand::Local(res)
    }

    /// The failure arm of an `expr!` at an entry point (the entry `main` or a
    /// module init's top level), where there is no caller to propagate to:
    /// abort the program with a non-zero exit. A nullable operand's null
    /// aborts with a fixed message; an `Err` aborts with its rendered
    /// payload.
    fn abort_failed_prop(&mut self, v: LocalId, nullable: bool) {
        if nullable {
            self.b.push(MirStmt::Eval(Rvalue::Call(
                Callee::Builtin("panic".into()),
                vec![Operand::Const(Literal::Str(
                    "unhandled error: null value propagated by `!`".into(),
                ))],
            )));
            self.b.terminate(Terminator::Unreachable);
            return;
        }
        let err = self.b.emit(Rvalue::Load(Place::projected(
            v,
            vec![Projection::Field("error".into())],
        )));
        // The prelude renders the payload: an `Error` prints its trace, any
        // other payload the plain `unhandled error:` prefix form (see
        // core/error.cz `_render_unhandled`).
        let msg = match self
            .ctx
            .resolve_fn_symbol(&self.module, "_render_unhandled")
        {
            Some(render) => self.b.emit(Rvalue::Call(Callee::Free(render), vec![err])),
            // Lowering without the prelude (tests): keep the prefix form.
            None => {
                let rendered = self
                    .b
                    .emit(Rvalue::Call(Callee::Builtin("to_string".into()), vec![err]));
                self.b.emit(Rvalue::Call(
                    Callee::Builtin("_string_concat".into()),
                    vec![
                        Operand::Const(Literal::Str("unhandled error: ".into())),
                        rendered,
                    ],
                ))
            }
        };
        self.b.push(MirStmt::Eval(Rvalue::Call(
            Callee::Builtin("_panic".into()),
            vec![msg],
        )));
        self.b.terminate(Terminator::Unreachable);
    }

    fn lower_field(&mut self, base: &Expr, name: &str) -> Operand {
        // `Type.Variant` with no fields is a compile-time unit-variant value.
        if let Expr::Ident(tname, _) = base
            && self.lookup(tname).is_none()
        {
            let tn = self.resolve_self_name(tname);
            if let Some(info) = self.ctx.program.resolve_type(&self.module, &tn)
                && let Some(var) = info.variant(name)
                && var.fields.is_empty()
            {
                return self.b.emit(Rvalue::Variant {
                    ty: tn,
                    variant: name.to_string(),
                    fields: Vec::new(),
                });
            }
        }
        let recv = self.lower_expr(base);
        let recv = self.b.make_local(recv);
        self.b.emit(Rvalue::Load(Place::projected(
            recv,
            vec![Projection::Field(name.to_string())],
        )))
    }

    fn lower_index(&mut self, base: &Expr, idx: &Expr) -> Operand {
        let arr = self.lower_expr(base);
        let arr = self.b.make_local(arr);
        let i = self.lower_expr(idx);
        self.b.emit(Rvalue::Load(Place::projected(
            arr,
            vec![Projection::Index(i)],
        )))
    }

    fn lower_array(&mut self, es: &[Expr], span: Span) -> Operand {
        let mut ops = Vec::with_capacity(es.len());
        for e in es {
            let v = self.lower_expr(e);
            ops.push(v);
        }
        let rv = Rvalue::Array(ops);
        // A literal whose checked element representation differs from what the
        // back end would re-derive (a nullable cell, a non-default numeric
        // width) carries that type onto its result local, so the elements are
        // built at the annotated representation from the start. An EMPTY
        // literal has no elements to derive from at all, so any recorded
        // checked type (the channel only records fully-known ones for it) is
        // its only source and is always carried.
        match self.ctx.expr_type(span) {
            Some(ty) if array_element_needs_seed(ty) || es.is_empty() => {
                self.b.emit_known(rv, ty.clone())
            }
            _ => self.b.emit(rv),
        }
    }

    /// The checker-resolved element type of a range expression, when its
    /// non-default representation was recorded (the expr_types channel). The
    /// counting locals must carry it: monomorphization would otherwise
    /// re-derive the literal bound's default width, and a counter narrower
    /// than the checked type wraps before a wide `hi` bound is reached.
    pub(crate) fn range_elem_type(&self, span: Span) -> Option<Type> {
        match self.ctx.expr_type(span) {
            Some(Type::Slice(e)) => Some((**e).clone()),
            _ => None,
        }
    }

    /// Materialize `op` into a local carrying the checker-resolved type when
    /// one is known; a bare [`crate::builder::BodyBuilder::make_local`] otherwise.
    pub(crate) fn make_local_seeded(&mut self, op: Operand, ty: Option<&Type>) -> LocalId {
        match ty {
            Some(t) => {
                let id = self.b.fresh_local_typed(None, t.clone());
                self.b.push(MirStmt::Assign(id, Rvalue::Use(op)));
                id
            }
            None => self.b.make_local(op),
        }
    }

    /// Lower `[lo..hi]` to an index loop that fills a fresh array with the
    /// half-open integer range: `arr = []; i = lo; while i < hi { arr.push(i);
    /// i += 1 }`. The element type follows the checker's range type when it
    /// was recorded (a non-default width); otherwise it is inferred from the
    /// push.
    fn lower_range(&mut self, lo: &Expr, hi: &Expr, span: Span) -> Operand {
        let elem = self.range_elem_type(span);
        let arr_op = match &elem {
            Some(t) => self
                .b
                .emit_known(Rvalue::Array(Vec::new()), Type::Slice(Box::new(t.clone()))),
            None => self.b.emit(Rvalue::Array(Vec::new())),
        };
        let arr = self.b.make_local(arr_op);
        let lo_op = self.lower_expr(lo);
        let i = self.make_local_seeded(lo_op, elem.as_ref());
        let hi_op = self.lower_expr(hi);
        let end = self.make_local_seeded(hi_op, elem.as_ref());

        let cond_bb = self.b.new_block();
        let body_bb = self.b.new_block();
        let incr_bb = self.b.new_block();
        let end_bb = self.b.new_block();
        self.b.terminate(Terminator::Goto(cond_bb));

        self.b.switch_to(cond_bb);
        let c = self.b.emit(Rvalue::Bin(
            BinOp::Lt,
            Operand::Local(i),
            Operand::Local(end),
        ));
        self.b.terminate(Terminator::CondBranch {
            cond: c,
            then: body_bb,
            els: end_bb,
        });

        self.b.switch_to(body_bb);
        self.b.emit(Rvalue::Call(
            Callee::Method("push".into()),
            vec![Operand::Local(arr), Operand::Local(i)],
        ));
        self.b.terminate(Terminator::Goto(incr_bb));

        self.b.switch_to(incr_bb);
        let next = self.b.emit(Rvalue::Bin(
            BinOp::Add,
            Operand::Local(i),
            Operand::Const(Literal::Int(1)),
        ));
        self.b.push(MirStmt::Assign(i, Rvalue::Use(next)));
        self.b.terminate(Terminator::Goto(cond_bb));

        self.b.switch_to(end_bb);
        Operand::Local(arr)
    }

    fn lower_record(&mut self, name: &str, fields: &[(String, Expr)], span: Span) -> Operand {
        let ty = self.resolve_self_name(name);
        let fields = self.lower_named_fields(fields);
        let rv = Rvalue::Record { ty, fields };
        // The checker-resolved instance type seeds the literal's result local
        // exactly like a constructor call's: the substitution carries the
        // per-instance types of inferred fields -- in particular the signature
        // of an unannotated function-typed field, which the back end cannot
        // derive from the closure operand alone (the closure takes its
        // parameter types FROM that seed).
        match self.ctx.expr_type(span) {
            Some(t) if is_seedable_result(t) => self.b.emit_known(rv, t.clone()),
            _ => self.b.emit(rv),
        }
    }

    fn lower_variant(&mut self, ty: &str, variant: &str, fields: &[(String, Expr)]) -> Operand {
        let ty = self.resolve_self_name(ty);
        let fields = self.lower_named_fields(fields);
        self.b.emit(Rvalue::Variant {
            ty,
            variant: variant.to_string(),
            fields,
        })
    }

    fn lower_named_fields(&mut self, fields: &[(String, Expr)]) -> Vec<(String, Operand)> {
        let mut out = Vec::with_capacity(fields.len());
        for (n, e) in fields {
            let v = self.lower_expr(e);
            out.push((n.clone(), v));
        }
        out
    }

    /// A string literal with interpolation: constant text stays a single
    /// constant; an interpolated segment is stringified and concatenated with
    /// `+` (resolved to string concat later by type).
    fn lower_string(&mut self, segs: &[StrSeg]) -> Operand {
        if segs.iter().all(|s| matches!(s, StrSeg::Lit(_))) {
            let mut text = String::new();
            for s in segs {
                if let StrSeg::Lit(t) = s {
                    text.push_str(t);
                }
            }
            return Operand::Const(Literal::Str(text));
        }
        let mut acc = Operand::Const(Literal::Str(String::new()));
        for seg in segs {
            let piece = match seg {
                StrSeg::Lit(t) => Operand::Const(Literal::Str(t.clone())),
                StrSeg::Expr(e) => {
                    let v = self.lower_expr(e);
                    self.b
                        .emit(Rvalue::Call(Callee::Builtin("to_string".into()), vec![v]))
                }
            };
            acc = self.b.emit(Rvalue::Bin(BinOp::Add, acc, piece));
        }
        acc
    }

    /// Build the rvalue for a call, routing it structurally (same decisions as
    /// `codegen::gen_call`). Side-effecting sub-expressions (receiver, args) are
    /// evaluated here in source order.
    pub(crate) fn lower_call(&mut self, callee: &Expr, args: &[Arg], span: Span) -> Rvalue {
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
        if let Expr::Field(base, method, _) = callee {
            // `typeof(v).method(args)`: a static call on v's type, whose name the
            // checker resolved into the type-name channel keyed by the inner
            // `typeof(v)` span. Route it exactly like a written `Type.method`.
            if let Expr::Call(c, _, tspan) = &**base
                && matches!(&**c, Expr::Ident(n, _) if n == "typeof")
                && let Some(tname) = self.ctx.type_names.get(tspan)
            {
                let tn = tname.clone();
                if method == "from" && self.ctx.record_field_names(&self.module, &tn).is_some() {
                    let source = self
                        .lower_args(args)
                        .into_iter()
                        .next()
                        .unwrap_or_else(Operand::void);
                    return Rvalue::RecordFrom { ty: tn, source };
                }
                let qualifier = self.ctx.static_qualifier(&self.module, &tn);
                let ops = self.lower_args(args);
                return Rvalue::Call(
                    Callee::Static {
                        ty: qualifier,
                        method: method.clone(),
                    },
                    ops,
                );
            }
            // `T.default()` for a primitive type word folds to its zero
            // value (the `Default` protocol's builtin implementations).
            if let Expr::Ident(tname, _) = &**base
                && self.lookup(tname).is_none()
                && let Some(lit) = primitive_default_literal(tname, method)
            {
                return Rvalue::Use(Operand::Const(lit));
            }
            if let Expr::Ident(tname, _) = &**base
                && self.lookup(tname).is_none()
                && self.ctx.is_type_word_in(&self.module, tname)
            {
                let tn = self.resolve_self_name(tname);
                // `T.from(v)` for a structure type `T`: a fallible structural
                // conversion. The result is `T?` -- the record built from `v`'s
                // fields when the (monomorphized) `v` has all of `T`'s, else null.
                // The back ends read the fields and make the presence decision per
                // instance, so the lowering only carries the target type and source.
                if method == "from" && self.ctx.record_field_names(&self.module, &tn).is_some() {
                    let source = self
                        .lower_args(args)
                        .into_iter()
                        .next()
                        .unwrap_or_else(Operand::void);
                    return Rvalue::RecordFrom { ty: tn, source };
                }
                let qualifier = self.ctx.static_qualifier(&self.module, &tn);
                let ops = self.lower_args(args);
                return Rvalue::Call(
                    Callee::Static {
                        ty: qualifier,
                        method: method.clone(),
                    },
                    ops,
                );
            }
            // No trailing-nullable padding here: `method` names a *method*, whose
            // arity the checker enforces in full. Looking the name up as a free
            // function (as free calls below do) would pad from an unrelated
            // same-named function's signature and corrupt the argument list.
            let recv = self.lower_expr(base);
            // A name no type's method table (nor the primitive-method table)
            // knows is a FIELD call: `a.func(4)` loads the function-typed field
            // and calls it indirectly (the checker already resolved the name to
            // a field). A field sharing its name with an unrelated type's
            // method still routes as a method -- a limitation of this
            // structural, type-free routing.
            if !self.ctx.method_name_exists(method) {
                let obj = self.b.make_local(recv);
                let f = self.b.emit(Rvalue::Load(Place::projected(
                    obj,
                    vec![Projection::Field(method.clone())],
                )));
                let ops = self.lower_args(args);
                return Rvalue::Call(Callee::Indirect(f), ops);
            }
            let mut ops = vec![recv];
            ops.extend(self.lower_args(args));
            // A method call may omit the callee's trailing `Location`
            // parameter; complete it with the call site.
            if let Some(full) = self.ctx.method_wants_location(method)
                && ops.len() + 1 == full
            {
                let loc = self.location_operand(span);
                ops.push(loc);
            }
            return Rvalue::Call(Callee::Method(method.clone()), ops);
        }
        if let Expr::Ident(name, _) = callee {
            // A local holding a closure/function value is called indirectly.
            // `error` is a reserved callee name: a local binding (a match's
            // `Err { error }` payload) never shadows the prelude function in
            // call position.
            if name != "error"
                && let Some(local) = self.lookup(name)
            {
                let ops = self.lower_args(args);
                return Rvalue::Call(Callee::Indirect(Operand::Local(local)), ops);
            }
            // A known free function resolves to its storage symbol. An argument
            // the checker recorded as view-convertible (an anonymous structural
            // value fitting an eligible parameter's row) is converted into that
            // parameter's view at the call boundary, so every argument shape
            // with the same view selects one callee instance.
            if let Some(symbol) = self.ctx.resolve_fn_symbol(&self.module, name) {
                let mut ops = Vec::with_capacity(args.len());
                for (i, a) in args.iter().enumerate() {
                    let v = self.lower_expr(&a.expr);
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
                self.pad_trailing_nullable(name, &mut ops);
                // A call may omit the callee's trailing `Location` parameter;
                // complete it with the call site.
                if let Some(full) = self.ctx.free_fn_wants_location(&self.module, name)
                    && ops.len() + 1 == full
                {
                    let loc = self.location_operand(span);
                    ops.push(loc);
                }
                return Rvalue::Call(Callee::Free(symbol), ops);
            }
            // A module GLOBAL holding a closure/function value is called
            // indirectly, exactly like a local: `let inc = (n: int32) -> n + 1`
            // at top level, then `inc(1)` anywhere in the module.
            if self.ctx.is_global_name(&self.module, name) {
                let g = self
                    .b
                    .emit(Rvalue::Global(self.ctx.global_symbol(&self.module, name)));
                let ops = self.lower_args(args);
                return Rvalue::Call(Callee::Indirect(g), ops);
            }
            // A program lowered without the prelude (unit tests, embedders)
            // has no `error` function to resolve to; keep the legacy builtin
            // desugar so such programs still construct the Err.
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
            // Otherwise it is a runtime builtin.
            let ops = self.lower_args(args);
            return Rvalue::Call(Callee::Builtin(name.clone()), ops);
        }
        // Any other callee expression evaluates to a closure/function value.
        let clo = self.lower_expr(callee);
        let ops = self.lower_args(args);
        Rvalue::Call(Callee::Indirect(clo), ops)
    }

    /// Build the `Location` record for the call at `span` (the implicit
    /// caller-location argument).
    fn location_operand(&mut self, span: Span) -> Operand {
        let (file, line, col) = self.ctx.call_location(span);
        self.b.emit(Rvalue::Record {
            ty: "Location".to_string(),
            fields: vec![
                ("file".to_string(), Operand::Const(Literal::Str(file))),
                (
                    "line".to_string(),
                    Operand::Const(Literal::Int(line as i64)),
                ),
                ("col".to_string(), Operand::Const(Literal::Int(col as i64))),
            ],
        })
    }

    fn lower_args(&mut self, args: &[Arg]) -> Vec<Operand> {
        let mut ops = Vec::with_capacity(args.len());
        for a in args {
            let v = self.lower_expr(&a.expr);
            ops.push(v);
        }
        ops
    }

    /// Pad a free-function call's argument list with `null` for each omitted
    /// trailing nullable parameter of `name`, so a call may leave them off. The
    /// type checker has already verified the omitted parameters are nullable;
    /// padding stops at the first non-nullable one.
    fn pad_trailing_nullable(&self, name: &str, ops: &mut Vec<Operand>) {
        let Some(nullable) = self.ctx.fn_param_nullability(&self.module, name) else {
            return;
        };
        for &is_nullable in nullable.iter().skip(ops.len()) {
            if !is_nullable {
                break;
            }
            ops.push(Operand::Const(Literal::Null));
        }
    }

    /// Lower a closure: capture the free variables in scope, lower its body into
    /// its own MIR, register it in the program-wide table, and yield a closure
    /// value naming the captured operands.
    fn lower_closure(&mut self, params: &[Param], body: &Expr) -> Operand {
        let block = closure_block(body);
        let free = free_vars_of(params, &block);
        let mut capture_names = Vec::new();
        let mut capture_ops = Vec::new();
        let mut cell_captures = Vec::new();
        for n in &free {
            if let Some(local) = self.lookup(n) {
                capture_names.push(n.clone());
                // A cell-promoted capture is the shared cell array (its local holds
                // the array pointer); the closure body accesses it through element 0.
                capture_ops.push(Operand::Local(local));
                if self.is_cell(n) {
                    cell_captures.push(n.clone());
                }
            }
        }
        let id = self.ctx.fresh_closure_id();
        let closure = lower_closure_body(
            self.ctx,
            self.module.clone(),
            self.self_type.clone(),
            id,
            &capture_names,
            &cell_captures,
            params,
            body,
        );
        self.ctx.closures.borrow_mut().push(closure);
        self.b.emit(Rvalue::Closure {
            id,
            captures: capture_ops,
        })
    }
}

/// View a closure body as a block (an expression body becomes a one-statement
/// block whose value is returned).
fn closure_block(body: &Expr) -> Block {
    match body {
        Expr::Block(b, _) => b.clone(),
        other => Block {
            stmts: vec![Stmt::Expr(other.clone())],
            span: other.span(),
        },
    }
}

/// Lower a closure body into its own [`MirClosure`]. Captures are bound first
/// (the closure environment), then parameters; the body returns its value.
#[allow(clippy::too_many_arguments)]
fn lower_closure_body(
    ctx: &ProgramCtx,
    module: Vec<String>,
    self_type: Option<String>,
    id: crate::ids::ClosureId,
    capture_names: &[String],
    cell_captures: &[String],
    params: &[Param],
    body: &Expr,
) -> MirClosure {
    let mut fl = FnLower::new(ctx, module.clone(), self_type);
    // Cell candidates local to this closure: its own captured-and-mutated
    // bindings (for nested closures). As in `lower_callable`, each binder
    // decides for its own binding, so a parameter binds plainly (shadowing any
    // same-named captured cell) while a `let` of a candidate name is promoted.
    fl.cells = crate::analysis::cell_promotions(&closure_block(body));
    let captures: Vec<_> = capture_names
        .iter()
        .map(|n| {
            let l = fl.b.fresh_local(Some(n.clone()));
            // A capture that is a shared cell in the enclosing body stays a
            // cell binding here: its local holds the cell array, and the body
            // reads/writes it through element 0.
            fl.bind_as(n, l, cell_captures.contains(n));
            l
        })
        .collect();
    // Closure parameters are borrowed (never deep-copied on entry): the copy
    // inference targets named functions and methods, and closure callbacks
    // (`map`/`filter`/`fold`) read their arguments rather than mutating them.
    let no_copies = vec![false; params.len()];
    let param_locals = fl.bind_params(params, &no_copies);
    match body {
        // Block body: explicit returns drive control flow; a falling-off tail
        // returns void.
        Expr::Block(b, _) => {
            fl.lower_body_stmts(&b.stmts);
            if !fl.b.terminated() {
                fl.b.terminate(Terminator::Return(Operand::void()));
            }
        }
        // Expression body: its value is the closure result.
        other => {
            let v = fl.lower_expr(other);
            if !fl.b.terminated() {
                fl.b.terminate(Terminator::Return(v));
            }
        }
    }
    let mir_body = fl.b.finish(param_locals.clone(), BlockId(0));
    MirClosure {
        id,
        params: param_locals,
        captures,
        capture_names: capture_names.to_vec(),
        module,
        body: mir_body,
    }
}
