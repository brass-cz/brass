//! Expression lowering: flattening to three-address form and the value-bearing
//! control-flow constructs (`&&`/`||`/`if`/`if let`/`match`/`expr!`).
//!
//! Every [`FnLower::lower_expr`] returns an [`Operand`] naming the result. Plain
//! computations emit one assignment to a fresh temporary; branching constructs
//! allocate a result local that each arm writes before jumping to the merge
//! block. Call routing, field/element reads, literals, and constructors are
//! resolved by name and scope; the type-dependent choices come from the
//! checker's channels (the span-keyed tables on `ProgramCtx`).

mod call;
mod names;

use brass_hir::Type;
use brass_parser::Span;
use brass_parser::ast::{Arg, BinOp, Block, Expr, StrSeg};

use crate::cfg::{MirStmt, Terminator};
use crate::ids::{BlockId, LocalId};
use crate::lower::FnLower;
use crate::lower::closure::ParamPassing;
use crate::lower::order::{assigned_names, later_assigned};
use crate::value::{Callee, Literal, Operand, Place, Projection, Rvalue};

/// Whether a checker-resolved call result is worth seeding onto its result
/// local: a record/sum whose field types the back end could otherwise fail to
/// infer for a witness-free constructor (the array fields inside are seeded from
/// the record's substitution). Bare arrays/scalars/strings the back end always
/// re-derives from how the value is built and used, so they keep an inferred
/// `Var` -- seeding them is unnecessary and perturbs value ownership.
fn is_seedable_result(ty: &Type) -> bool {
    matches!(ty, Type::Record(_) | Type::Sum(_))
        || matches!(ty, Type::Nullable(inner) if matches!(inner.as_ref(), Type::Record(_) | Type::Sum(_)))
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
        let numeric = |ty: &Type| matches!(ty, Type::Int(_) | Type::Float(_));
        let shared = self.ctx.expr_type(e.span()).filter(|ty| numeric(ty));
        let per_instance = self
            .ctx
            .instance_seeds
            .get(&e.span())
            .is_some_and(|seeds| seeds.values().any(numeric));
        if shared.is_some() || per_instance {
            return self
                .b
                .emit_seeded(Rvalue::Use(op), e.span(), shared.cloned());
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
            Expr::Ident(name, span) => self.lower_ident_at(name, Some(*span)),
            Expr::SelfExpr(_) => self.lower_ident("self"),
            // A negated numeric literal is ONE constant (the checker types
            // `-1` by its value, and lets `-0.5` adapt like `0.5`), so the
            // operand rule sees a literal here too instead of a computed
            // temporary.
            Expr::Unary(..) if let Some(v) = e.int_literal_value() => {
                Operand::Const(Literal::Int(v))
            }
            Expr::Unary(brass_parser::ast::UnaryOp::Neg, inner, _)
                if let Expr::Float(v, _) = &**inner =>
            {
                Operand::Const(Literal::Float(-*v))
            }
            Expr::Unary(op, a, _) => {
                let v = self.lower_expr(a);
                self.b.emit(Rvalue::Un(*op, v))
            }
            Expr::Binary(op, a, b, _) => self.lower_binary(*op, a, b),
            Expr::Call(callee, args, span) => {
                if let Expr::Field(base, method, _) = &**callee
                    && !callee.span().is_parenthesized()
                    && method == "context"
                    && self.ctx.nullable_receiver_inner(*span).is_some()
                {
                    return self.lower_nullable_context(base, args, *span);
                }
                let rv = self.lower_call(callee, args, *span);
                // A call whose checker-resolved result is a constructed aggregate
                // (a record/sum/array) seeds its result local, so the back end
                // follows the instance type the caller fixed -- the path a
                // witness-free constructor (`HashMap.new()`) depends on. The
                // seed shared by every instance is carried here; per-instance
                // seeds are looked up by the call's span.
                let shared = self
                    .ctx
                    .expr_type(*span)
                    .filter(|ty| is_seedable_result(ty))
                    .cloned();
                self.b.emit_seeded(rv, *span, shared)
            }
            Expr::Field(base, name, _) => self.lower_field(base, name),
            Expr::Index(base, idx, _) => self.lower_index(base, idx),
            Expr::ErrorProp(inner, span) => self.lower_error_prop(inner, *span),
            Expr::Closure(params, body, span) => self.lower_closure(params, body, *span),
            Expr::Array(es, span) => self.lower_array(es, *span),
            Expr::Range(lo, hi, span) => self.lower_range(lo, hi, *span),
            Expr::TypeLit(name, fields, span) => self.lower_record(name, fields, *span),
            Expr::VariantLit(ty, variant, fields, _) => self.lower_variant(ty, variant, fields),
            // A type test folds to a constant bool per monomorphized instance
            // (the back ends match the operand's type against the pattern);
            // the subject is still evaluated like any operand. `lower_if`
            // handles negation by swapping successors, so MIR tests stay
            // positive. The pattern is the checker-resolved channel entry; a
            // body no instantiation ever decided falls back to the syntactic
            // annotation with every hole a wildcard -- such a body is never
            // monomorphized, the fallback only keeps the shared lowering total.
            Expr::TypeTest(subject, te, _, span) => {
                let subj = self.lower_expr(subject);
                let pattern = self.ctx.type_tests.get(span).cloned().unwrap_or_else(|| {
                    let program = self.ctx.program;
                    brass_hir::resolve(te, |n| {
                        program
                            .resolve_type(&self.module, n)
                            .map(|info| match &info.kind {
                                brass_hir::TypeKind::Record { .. } => {
                                    brass_hir::NominalInfo::record(info.id)
                                }
                                brass_hir::TypeKind::Sum { .. } => {
                                    brass_hir::NominalInfo::sum(info.id)
                                }
                            })
                    })
                    .unwrap_or(Type::Unknown(brass_hir::INFER_VAR))
                });
                self.b
                    .emit_known(Rvalue::TypeTest(subj, pattern), Type::Bool)
            }
            Expr::If(cond, then, els, span) => {
                self.lower_if(cond, then, els.as_deref(), true, *span)
            }
            Expr::IfLet(pat, scrut, then, els, span) => {
                self.lower_iflet(pat, scrut, then, els.as_deref(), true, *span)
            }
            Expr::Match(scrut, arms, span) => self.lower_match(scrut, arms, true, *span),
            Expr::Block(b, _) => self.lower_block_value(b),
        }
    }

    /// Expand nullable context into explicit control flow. The missing arm
    /// calls the prelude `error` function so its Error construction and caller
    /// location stay canonical; the present Result arm calls the unchanged
    /// `Result.context`, preserving its frame-append policy.
    fn lower_nullable_context(&mut self, base: &Expr, args: &[Arg], span: Span) -> Operand {
        let base = self.lower_expr(base);
        let base = self.hold(base, &assigned_names(args.iter().map(|a| &a.expr)));
        let receiver = self.b.make_local(base);
        let lowered_args = self.lower_args(args);
        let message = lowered_args.first().cloned().unwrap_or_else(Operand::void);
        let location = lowered_args
            .get(1)
            .cloned()
            .unwrap_or_else(|| self.location_operand(span));
        let shared = self
            .ctx
            .expr_type(span)
            .filter(|ty| is_seedable_result(ty))
            .cloned();
        let result = self.b.fresh_seeded_local(span, shared);
        let present = self.b.emit(Rvalue::Call(
            Callee::Builtin("__nullable_context_present".into()),
            vec![Operand::Local(receiver)],
        ));
        let value_bb = self.b.new_block();
        let missing_bb = self.b.new_block();
        let merge_bb = self.b.new_block();
        self.b.terminate(Terminator::CondBranch {
            cond: present,
            then: value_bb,
            els: missing_bb,
        });

        self.b.switch_to(value_bb);
        let value = self.b.emit(Rvalue::Call(
            Callee::Builtin("__nonnull".into()),
            vec![Operand::Local(receiver)],
        ));
        let result_pattern = Type::Sum(brass_hir::NominalType::new(
            brass_hir::RESULT_TYPE_ID,
            brass_hir::RESULT_TYPE_NAME,
        ));
        let is_result = self.b.emit(Rvalue::TypeTest(value.clone(), result_pattern));
        let result_bb = self.b.new_block();
        let plain_bb = self.b.new_block();
        self.b.terminate(Terminator::CondBranch {
            cond: is_result,
            then: result_bb,
            els: plain_bb,
        });

        self.b.switch_to(result_bb);
        let contextualized = self.b.emit(Rvalue::Call(
            Callee::Method("context".into()),
            vec![value.clone(), message.clone(), location.clone()],
        ));
        self.b
            .push(MirStmt::Assign(result, Rvalue::Use(contextualized)));
        self.b.terminate(Terminator::Goto(merge_bb));

        // The Ok wrap is built straight into the result local, so it takes
        // the whole expression's `Result` type: a separate temporary would be
        // typed on its own and fall back to the enclosing function's return
        // type, whose Ok payload is another type.
        self.b.switch_to(plain_bb);
        self.b.push(MirStmt::Assign(
            result,
            Rvalue::Variant {
                ty: "Result".to_string(),
                variant: "Ok".to_string(),
                fields: vec![("value".to_string(), value)],
            },
        ));
        self.b.terminate(Terminator::Goto(merge_bb));

        self.b.switch_to(missing_bb);
        let missing_result = match self.ctx.resolve_fn_symbol(&self.module, "error") {
            Some(error) => self
                .b
                .emit(Rvalue::Call(Callee::Free(error), vec![message, location])),
            None => self.b.emit(Rvalue::Variant {
                ty: "Result".to_string(),
                variant: "Err".to_string(),
                fields: vec![("error".to_string(), message)],
            }),
        };
        self.b
            .push(MirStmt::Assign(result, Rvalue::Use(missing_result)));
        self.b.terminate(Terminator::Goto(merge_bb));

        self.b.switch_to(merge_bb);
        Operand::Local(result)
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

    fn lower_binary(&mut self, op: BinOp, a: &Expr, b: &Expr) -> Operand {
        match op {
            // `&&`/`||` short-circuit and so become control flow.
            BinOp::And | BinOp::Or => self.lower_logical(op, a, b),
            // Each use of a generalized closure binding builds its own
            // closure value, and function values compare by identity, so
            // such a use equals no other value -- itself included (types.md,
            // Equality). The comparison is decided without building the
            // closure, which nothing else would type; the other operand
            // still runs for its effects.
            BinOp::Eq | BinOp::Ne
                if self.is_closure_template_use(a) || self.is_closure_template_use(b) =>
            {
                for operand in [a, b] {
                    if !self.is_closure_template_use(operand) {
                        self.lower_expr(operand);
                    }
                }
                Operand::Const(Literal::Bool(op == BinOp::Ne))
            }
            _ => {
                let la = self.lower_expr(a);
                let la = self.hold(la, &assigned_names([b]));
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

    /// The local an `if`/`if let`/`match` value at `span` is written into:
    /// a join of the branch values, or -- when the checker joined them at a
    /// numeric type their literal branches adapted to (the `expr_types`
    /// channel) -- a local of that type, so each literal branch is built at it.
    fn branch_result_local(&mut self, span: Span) -> LocalId {
        let adapted = self.ctx.expr_type(span).filter(|ty| {
            matches!(ty, Type::Int(_) | Type::Float(_))
                || matches!(ty, Type::Nullable(inner) if matches!(**inner, Type::Int(_) | Type::Float(_)))
        });
        match adapted {
            Some(ty) => self.b.fresh_local_typed(None, ty.clone()),
            None => self.b.fresh_join_local(),
        }
    }

    /// `if cond { then } else { els }`. As a value (`value`) each arm writes
    /// the result; as a statement the arms run for their effects only and
    /// their trailing values are discarded, so arms of different types (or a
    /// value-yielding arm without an `else`) never meet in one result.
    pub(super) fn lower_if(
        &mut self,
        cond: &Expr,
        then: &Block,
        els: Option<&Expr>,
        value: bool,
        span: Span,
    ) -> Operand {
        let res = value.then(|| self.branch_result_local(span));
        let c = self.lower_expr(cond);
        let then_bb = self.b.new_block();
        let else_bb = self.b.new_block();
        let merge_bb = self.b.new_block();
        // Keep MIR's test positive so compile-time pruning sees it directly.
        let negated = matches!(cond, Expr::TypeTest(_, _, true, _));
        self.b.terminate(Terminator::CondBranch {
            cond: c,
            then: if negated { else_bb } else { then_bb },
            els: if negated { then_bb } else { else_bb },
        });

        let mut reached = false;
        self.b.switch_to(then_bb);
        let tv = self.lower_arm_block(then, value);
        reached |= self.close_arm(res, tv, merge_bb);

        self.b.switch_to(else_bb);
        let ev = match els {
            Some(e) => self.lower_arm_expr(e, value),
            None => Some(Operand::void()),
        };
        reached |= self.close_arm(res, ev, merge_bb);

        self.b.switch_to(merge_bb);
        self.seal_value_merge(res, reached)
    }

    /// Lower an arm block of a branching expression: its value when the
    /// expression yields one, else its statements alone (`None`).
    fn lower_arm_block(&mut self, b: &Block, value: bool) -> Option<Operand> {
        if value {
            Some(self.lower_block_value(b))
        } else {
            self.lower_block_stmts(b);
            None
        }
    }

    /// As [`Self::lower_arm_block`], for an arm written as an expression (an
    /// `else` chain, a `match` arm body).
    fn lower_arm_expr(&mut self, e: &Expr, value: bool) -> Option<Operand> {
        if value {
            Some(self.lower_expr(e))
        } else {
            self.lower_expr_stmt(e);
            None
        }
    }

    /// End an arm that falls through: write its value `v` into the result
    /// `res` (when the expression yields one) and jump to `merge`. Returns
    /// whether the arm reached the merge (it did not when it diverged).
    fn close_arm(&mut self, res: Option<LocalId>, v: Option<Operand>, merge: BlockId) -> bool {
        if self.b.terminated() {
            return false;
        }
        if let (Some(res), Some(v)) = (res, v) {
            self.b.push(MirStmt::Assign(res, Rvalue::Use(v)));
        }
        self.b.terminate(Terminator::Goto(merge));
        true
    }

    /// Finalize a branching construct (`if`/`if let`/`match`) at its merge
    /// block: when no arm reached the merge (all diverged), the merge is dead, so
    /// give the result local (if the construct yields a value) a value --
    /// keeping it typeable -- and terminate the block, so a trailing implicit
    /// return never reads an unassigned local. A statement yields `void`.
    fn seal_value_merge(&mut self, res: Option<LocalId>, reached: bool) -> Operand {
        if !reached {
            if let Some(res) = res {
                self.b
                    .push(MirStmt::Assign(res, Rvalue::Use(Operand::void())));
            }
            self.b.terminate(Terminator::Unreachable);
        }
        res.map_or_else(Operand::void, Operand::Local)
    }

    /// `if let pat = scrut { then } else { els }`: test the pattern, bind on the
    /// success arm, and merge like an ordinary `if` (as a value or, without
    /// `value`, as a statement).
    pub(super) fn lower_iflet(
        &mut self,
        pat: &brass_parser::ast::Pattern,
        scrut: &Expr,
        then: &Block,
        els: Option<&Expr>,
        value: bool,
        span: Span,
    ) -> Operand {
        let res = value.then(|| self.branch_result_local(span));
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
            brass_parser::ast::Pattern::Binding(name, None, _) if !self.is_variant_name(name) => {
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
            brass_parser::ast::Pattern::Binding(name, None, _) if !self.is_variant_name(name) => {
                let nn = self.b.emit(Rvalue::Call(
                    Callee::Builtin("__nonnull".into()),
                    vec![Operand::Local(subj)],
                ));
                self.bind_value(name, nn);
            }
            _ => self.lower_pattern_bind(pat, subj),
        }
        let tv = self.lower_arm_block(then, value);
        self.pop_scope();
        reached |= self.close_arm(res, tv, merge_bb);

        self.b.switch_to(else_bb);
        let ev = match els {
            Some(e) => self.lower_arm_expr(e, value),
            None => Some(Operand::void()),
        };
        reached |= self.close_arm(res, ev, merge_bb);

        self.b.switch_to(merge_bb);
        self.seal_value_merge(res, reached)
    }

    /// `match scrut { pat => body, ... }`: a linear chain of pattern tests, each
    /// arm binding then writing the result (when `value`; as a statement the
    /// arms' values are discarded). Falling off the end panics, so the
    /// post-match merge is reached only by a matching arm.
    pub(super) fn lower_match(
        &mut self,
        scrut: &Expr,
        arms: &[brass_parser::ast::MatchArm],
        value: bool,
        span: Span,
    ) -> Operand {
        let res = value.then(|| self.branch_result_local(span));
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
            let v = self.lower_arm_expr(&arm.body, value);
            self.pop_scope();
            reached |= self.close_arm(res, v, merge_bb);
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
            // This marker is reserved for compiler-generated propagation. A
            // user-written `if let ... else { return null }` uses `__present`
            // and must remain an ordinary nullable return in inference.
            "__null_prop_present"
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
        // Propagating returns from the callable, ending every enclosing
        // iteration (an aborting entry point has no caller to observe it).
        if !self.abort_error_prop {
            self.emit_exit_writebacks();
        }
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
            // chain that never wraps renders that payload).
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
            .program
            .prelude_type("Frame")
            .map(brass_hir::TypeInfo::type_ref)
            .map(|t| Type::Slice(Box::new(t)))
        {
            Some(t) => self.b.fresh_local_typed(None, t),
            None => self.b.fresh_local(None),
        };
        self.b
            .push(MirStmt::Assign(frames, Rvalue::Array(Vec::new())));
        let err = self.b.emit(Rvalue::Record {
            ty: self
                .ctx
                .program
                .prelude_type("Error")
                .map(|info| info.symbol.clone())
                .unwrap_or_else(|| "Error".into()),
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
            && !self.is_bound(tname)
        {
            let tn = self.resolve_self_name(tname);
            if let Some(info) = self.ctx.program.resolve_type_or_alias(&self.module, &tn)
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
        let arr = self.hold(arr, &assigned_names([idx]));
        let arr = self.b.make_local(arr);
        let i = self.lower_expr(idx);
        self.b.emit(Rvalue::Load(Place::projected(
            arr,
            vec![Projection::Index(i)],
        )))
    }

    /// The call of the function value field `name` of the record `obj`
    /// holds, with `ops` as its arguments.
    fn field_call(&mut self, obj: LocalId, name: &str, ops: Vec<Operand>) -> Rvalue {
        let f = self.b.emit(Rvalue::Load(Place::projected(
            obj,
            vec![Projection::Field(name.to_string())],
        )));
        Rvalue::Call(Callee::Indirect(f), ops)
    }

    /// The instance method call `method(ops)` (receiver first) at `span`,
    /// with its omitted trailing arguments completed from the resolved
    /// method's signature. When the call's instances resolve `method` on
    /// different owners whose signatures complete it differently (a generic
    /// body calling `x.describe()` on a `Dog` and on a `Cat`), the receiver
    /// is tested against each owner in turn and every arm calls with its
    /// owner's completion; each instance folds the tests by its receiver's
    /// type, so it compiles exactly its own call.
    fn lower_method_call(&mut self, method: String, mut ops: Vec<Operand>, span: Span) -> Rvalue {
        let Some(owners) = self.ctx.owner_defaults(span, &method) else {
            let defaults = self.ctx.instance_call_defaults(span, &method);
            self.complete_call_args(defaults.as_deref(), &mut ops, span);
            return Rvalue::Call(Callee::Method(method), ops);
        };
        // The defaults that fill this call's omitted arguments: the run of
        // optional parameters after the written arguments.
        let given = ops.len();
        let completion = |defaults: &Option<Vec<super::CallDefault>>| {
            defaults.as_ref().map(|defaults| {
                defaults
                    .iter()
                    .skip(given)
                    .take_while(|d| **d != super::CallDefault::Required)
                    .copied()
                    .collect::<Vec<_>>()
            })
        };
        let first = completion(&owners[0].1);
        if owners
            .iter()
            .all(|(_, defaults)| completion(defaults) == first)
        {
            self.complete_call_args(owners[0].1.as_deref(), &mut ops, span);
            return Rvalue::Call(Callee::Method(method), ops);
        }
        let recv = self.b.make_local(ops[0].clone());
        ops[0] = Operand::Local(recv);
        let result = self.b.fresh_join_local();
        let merge_bb = self.b.new_block();
        let last = owners.len() - 1;
        for (i, (owner, defaults)) in owners.into_iter().enumerate() {
            let next_bb = (i < last).then(|| {
                let test = self
                    .b
                    .emit_known(Rvalue::TypeTest(Operand::Local(recv), owner), Type::Bool);
                let call_bb = self.b.new_block();
                let next_bb = self.b.new_block();
                self.b.terminate(Terminator::CondBranch {
                    cond: test,
                    then: call_bb,
                    els: next_bb,
                });
                self.b.switch_to(call_bb);
                next_bb
            });
            let mut arm_ops = ops.clone();
            self.complete_call_args(defaults.as_deref(), &mut arm_ops, span);
            let value = self
                .b
                .emit(Rvalue::Call(Callee::Method(method.clone()), arm_ops));
            self.b.push(MirStmt::Assign(result, Rvalue::Use(value)));
            self.b.terminate(Terminator::Goto(merge_bb));
            if let Some(next_bb) = next_bb {
                self.b.switch_to(next_bb);
            }
        }
        self.b.switch_to(merge_bb);
        Rvalue::Use(Operand::Local(result))
    }

    /// Lower `recv.name(args)` where some instantiations of the body call
    /// the function-valued field `name` (the receivers matching
    /// `field_receivers`) and the others a method `name`: the arguments are
    /// evaluated once, then a type test on the receiver selects the field
    /// call or the method call. Each instance folds the test by its
    /// receiver's type, so only its own arm is typed and compiled.
    fn lower_field_or_method_call(
        &mut self,
        recv: Operand,
        name: &str,
        args: &[Arg],
        span: Span,
        field_receivers: &[Type],
    ) -> Rvalue {
        let obj = self.b.make_local(recv);
        let ops = self.lower_args(args);
        let result = self.b.fresh_join_local();
        let field_bb = self.b.new_block();
        let method_bb = self.b.new_block();
        let merge_bb = self.b.new_block();
        for pattern in field_receivers {
            let test = self.b.emit_known(
                Rvalue::TypeTest(Operand::Local(obj), pattern.clone()),
                Type::Bool,
            );
            let next = self.b.new_block();
            self.b.terminate(Terminator::CondBranch {
                cond: test,
                then: field_bb,
                els: next,
            });
            self.b.switch_to(next);
        }
        self.b.terminate(Terminator::Goto(method_bb));

        self.b.switch_to(field_bb);
        let call = self.field_call(obj, name, ops.clone());
        let value = self.b.emit(call);
        self.b.push(MirStmt::Assign(result, Rvalue::Use(value)));
        self.b.terminate(Terminator::Goto(merge_bb));

        self.b.switch_to(method_bb);
        let mut method_ops = vec![Operand::Local(obj)];
        method_ops.extend(ops);
        let call = self.lower_method_call(name.to_string(), method_ops, span);
        let value = self.b.emit(call);
        self.b.push(MirStmt::Assign(result, Rvalue::Use(value)));
        self.b.terminate(Terminator::Goto(merge_bb));

        self.b.switch_to(merge_bb);
        Rvalue::Use(Operand::Local(result))
    }

    fn lower_array(&mut self, es: &[Expr], span: Span) -> Operand {
        let ops = self.lower_in_order(&es.iter().collect::<Vec<_>>());
        let rv = Rvalue::Array(ops);
        // A literal whose checked element representation differs from what the
        // back end would re-derive (`brass_hir::array_literal_needs_seed`)
        // carries that type onto its result local, so the elements are built
        // at the checked representation from the start; other literals keep
        // an inferred `Var` (see [`is_seedable_result`]). An EMPTY
        // literal has no elements to derive from at all, so any recorded
        // checked type (the channel only records fully-known ones for it) is
        // its only source and is always carried.
        let shared = self
            .ctx
            .expr_type(span)
            .filter(|ty| brass_hir::array_literal_needs_seed(ty) || es.is_empty())
            .cloned();
        self.b.emit_seeded(rv, span, shared)
    }

    /// The checker-resolved element type of a range expression (the
    /// expr_types channel records every range whose instantiations agree on
    /// it). The counting locals must carry it: monomorphization would
    /// otherwise type the counter from `lo` alone, and a counter narrower than
    /// the range's type (`[lo..256]` with `lo: uint8`) wraps before `hi` is
    /// reached.
    pub(crate) fn range_elem_type(&self, span: Span) -> Option<Type> {
        match self.ctx.expr_type(span) {
            Some(Type::Slice(e)) => Some((**e).clone()),
            _ => None,
        }
    }

    /// Lower a range's bounds into its counter (holding `lo`) and its end
    /// (holding `hi`). With the checker's element type both carry it. Without
    /// one (a generic body whose instantiations disagree on it) the counter
    /// is a join local written `hi` and then `lo`: the `hi` write is
    /// immediately overwritten, but it makes monomorphization type the counter
    /// as the join of both bounds -- the operator rule's type for them -- so
    /// a narrow `lo` with a wider `hi` still counts up to `hi`.
    pub(crate) fn range_bounds(
        &mut self,
        lo: &Expr,
        hi: &Expr,
        elem: Option<&Type>,
    ) -> (LocalId, LocalId) {
        let lo_op = self.lower_expr(lo);
        if elem.is_some() {
            let i = self.make_local_seeded(lo_op, elem);
            let hi_op = self.lower_expr(hi);
            let end = self.make_local_seeded(hi_op, elem);
            return (i, end);
        }
        // `lo` is read before `hi` is evaluated, as written; a constant keeps
        // its literal value for the join.
        let lo_op = match lo_op {
            Operand::Local(_) => self.b.emit(Rvalue::Use(lo_op)),
            constant => constant,
        };
        let hi_op = self.lower_expr(hi);
        let i = self.b.fresh_join_local();
        self.b.push(MirStmt::Assign(i, Rvalue::Use(hi_op.clone())));
        self.b.push(MirStmt::Assign(i, Rvalue::Use(lo_op)));
        let end = self.make_local_seeded(hi_op, None);
        (i, end)
    }

    /// Copy `op` into a FRESH local, carrying the checker-resolved type when
    /// one is known. A range's counter and bound use this: the counter is
    /// advanced in place, and the bound is the value at evaluation time, so
    /// neither may share a slot with a variable the bound expression named
    /// (`[x..n]` must neither advance `x` nor follow a later `n = ..`).
    pub(crate) fn make_local_seeded(&mut self, op: Operand, ty: Option<&Type>) -> LocalId {
        let id = match ty {
            Some(t) => self.b.fresh_local_typed(None, t.clone()),
            None => self.b.fresh_local(None),
        };
        self.b.push(MirStmt::Assign(id, Rvalue::Use(op)));
        id
    }

    /// Lower `[lo..hi]` to an index loop that fills a fresh array with the
    /// half-open integer range: `arr = []; i = lo; while i < hi { arr.push(i);
    /// i += 1 }`. The element type is the checker's range type when it was
    /// recorded, else the bounds' join (see [`Self::range_bounds`]).
    fn lower_range(&mut self, lo: &Expr, hi: &Expr, span: Span) -> Operand {
        let elem = self.range_elem_type(span);
        let arr_op = match &elem {
            Some(t) => self
                .b
                .emit_known(Rvalue::Array(Vec::new()), Type::Slice(Box::new(t.clone()))),
            None => self.b.emit(Rvalue::Array(Vec::new())),
        };
        let arr = self.b.make_local(arr_op);
        let (i, end) = self.range_bounds(lo, hi, elem.as_ref());

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
        // An anonymous literal the checker accepted into a slot of a declared
        // record (its fields are exactly the record's), and a literal written
        // through a `type A = R { .. }` alias, are built AS that record; the
        // checker recorded the record's symbol for the literal's span in the
        // type-name channel.
        let ty = match self.ctx.type_names.get(&span) {
            Some(symbol) => symbol.clone(),
            None => self.resolve_self_name(name),
        };
        let fields = self.lower_named_fields(fields);
        let rv = Rvalue::Record { ty, fields };
        // The checker-resolved instance type seeds the literal's result local
        // exactly like a constructor call's: the substitution carries the
        // per-instance types of inferred fields -- in particular the signature
        // of an unannotated function-typed field, which the back end cannot
        // derive from the closure operand alone (the closure takes its
        // parameter types FROM that seed).
        let shared = self
            .ctx
            .expr_type(span)
            .filter(|ty| is_seedable_result(ty))
            .cloned();
        self.b.emit_seeded(rv, span, shared)
    }

    /// A static call `T.method(args)` on the type named `tn` (a type word or
    /// the name a `typeof(v)` receiver resolved to). `string.from(x)` is the
    /// rendering of `x` exactly as `"{x}"` and `print` show it -- a declared
    /// `display` included -- so it lowers to the same `to_string` builtin as
    /// an interpolation segment.
    fn lower_static_call(&mut self, tn: &str, method: &str, args: &[Arg], span: Span) -> Rvalue {
        let qualifier = self.ctx.static_qualifier(&self.module, tn);
        let mut ops = self.lower_args(args);
        if qualifier == "string" && method == "from" && ops.len() == 1 {
            return Rvalue::Call(Callee::Builtin("to_string".into()), ops);
        }
        let defaults = self.ctx.static_call_defaults(&self.module, tn, method);
        self.complete_call_args(defaults.as_deref(), &mut ops, span);
        Rvalue::Call(
            Callee::Static {
                ty: qualifier,
                method: method.to_string(),
            },
            ops,
        )
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
        let values = self.lower_in_order(&fields.iter().map(|(_, e)| e).collect::<Vec<_>>());
        fields.iter().map(|(n, _)| n.clone()).zip(values).collect()
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
}
