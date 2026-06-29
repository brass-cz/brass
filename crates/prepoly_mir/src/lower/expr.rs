//! Expression lowering: flattening to three-address form and the value-bearing
//! control-flow constructs (`&&`/`||`/`if`/`if let`/`match`/`expr!`).
//!
//! Every [`FnLower::lower_expr`] returns an [`Operand`] naming the result. Plain
//! computations emit one assignment to a fresh temporary; branching constructs
//! allocate a result local that each arm writes before jumping to the merge
//! block. Call routing, field/element reads, literals, and constructors mirror
//! the AST-walking codegen so the two stay behaviorally equivalent.

use prepoly_parser::ast::{Arg, BinOp, Block, Expr, Param, Stmt, StrSeg};

use crate::analysis::free_vars_of;
use crate::cfg::{MirStmt, Terminator};
use crate::ids::{BlockId, LocalId};
use crate::lower::{FnLower, ProgramCtx};
use crate::program::MirClosure;
use crate::value::{Callee, Literal, Operand, Place, Projection, Rvalue};

impl<'a, 'p> FnLower<'a, 'p> {
    /// Lower an expression to an operand naming its value.
    pub(crate) fn lower_expr(&mut self, e: &Expr) -> Operand {
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
            Expr::Call(callee, args, _) => {
                let rv = self.lower_call(callee, args);
                self.b.emit(rv)
            }
            Expr::Field(base, name, _) => self.lower_field(base, name),
            Expr::Index(base, idx, _) => self.lower_index(base, idx),
            Expr::ErrorProp(inner, _) => self.lower_error_prop(inner),
            Expr::Closure(params, body, _) => self.lower_closure(params, body),
            Expr::Array(es, _) => self.lower_array(es),
            Expr::TypeLit(name, fields, _) => self.lower_record(name, fields),
            Expr::VariantLit(ty, variant, fields, _) => self.lower_variant(ty, variant, fields),
            Expr::If(cond, then, els, _) => self.lower_if(cond, then, els.as_deref()),
            Expr::IfLet(pat, scrut, then, els, _) => {
                self.lower_iflet(pat, scrut, then, els.as_deref())
            }
            Expr::Match(scrut, arms, _) => self.lower_match(scrut, arms),
            Expr::Block(b, _) => self.lower_block_value(b),
        }
    }

    /// A bare identifier: a bound local, otherwise a module global read.
    fn lower_ident(&mut self, name: &str) -> Operand {
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
            None => self.b.emit(Rvalue::Global(name.to_string())),
        }
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
        pat: &prepoly_parser::ast::Pattern,
        scrut: &Expr,
        then: &Block,
        els: Option<&Expr>,
    ) -> Operand {
        let res = self.b.fresh_local(None);
        let subj = self.lower_expr(scrut);
        let subj = self.b.make_local(subj);
        let cond = self.lower_pattern_cond(pat, subj);
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
        self.lower_pattern_bind(pat, subj);
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
    fn lower_match(&mut self, scrut: &Expr, arms: &[prepoly_parser::ast::MatchArm]) -> Operand {
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

    /// `expr!`: unwrap a `Result.Ok`, or return the `Result.Err` from the
    /// enclosing callable. Expressed as an explicit branch (PLAN_MIR: error
    /// propagation lives in the CFG, not in a codegen heuristic).
    fn lower_error_prop(&mut self, inner: &Expr) -> Operand {
        let v = self.lower_expr(inner);
        let v = self.b.make_local(v);
        let res = self.b.fresh_local(None);
        let is_ok = self.b.emit(Rvalue::Call(
            Callee::Builtin("result_is_ok".into()),
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
        let val = self.b.emit(Rvalue::Load(Place::projected(
            v,
            vec![Projection::Field("value".into())],
        )));
        self.b.push(MirStmt::Assign(res, Rvalue::Use(val)));
        self.b.terminate(Terminator::Goto(cont_bb));

        self.b.switch_to(err_bb);
        // Propagate the error Result unchanged.
        self.b.terminate(Terminator::Return(Operand::Local(v)));

        self.b.switch_to(cont_bb);
        Operand::Local(res)
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

    fn lower_array(&mut self, es: &[Expr]) -> Operand {
        let mut ops = Vec::with_capacity(es.len());
        for e in es {
            let v = self.lower_expr(e);
            ops.push(v);
        }
        self.b.emit(Rvalue::Array(ops))
    }

    fn lower_record(&mut self, name: &str, fields: &[(String, Expr)]) -> Operand {
        let ty = self.resolve_self_name(name);
        let fields = self.lower_named_fields(fields);
        self.b.emit(Rvalue::Record { ty, fields })
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
    pub(crate) fn lower_call(&mut self, callee: &Expr, args: &[Arg]) -> Rvalue {
        // `recv.method(args)` or `Type.method(args)`.
        if let Expr::Field(base, method, _) = callee {
            if let Expr::Ident(tname, _) = &**base
                && self.lookup(tname).is_none()
                && self.ctx.is_type_word(tname)
            {
                let tn = self.resolve_self_name(tname);
                // `T.from(v)` for a structure type `T`: build a `T` record by reading
                // each of `T`'s declared fields from `v` (the front end checks `v`
                // has them all). A record literal reuses construction/layout.
                if method == "from"
                    && let Some(field_names) = self.ctx.record_field_names(&self.module, &tn)
                {
                    let v = self
                        .lower_args(args)
                        .into_iter()
                        .next()
                        .unwrap_or_else(Operand::void);
                    let subj = self.b.make_local(v);
                    let fields = field_names
                        .into_iter()
                        .map(|name| {
                            let load = self.b.emit(Rvalue::Load(Place::projected(
                                subj,
                                vec![Projection::Field(name.clone())],
                            )));
                            (name, load)
                        })
                        .collect();
                    return Rvalue::Record { ty: tn, fields };
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
            let recv = self.lower_expr(base);
            let mut ops = vec![recv];
            ops.extend(self.lower_args(args));
            self.pad_trailing_nullable(method, &mut ops);
            return Rvalue::Call(Callee::Method(method.clone()), ops);
        }
        if let Expr::Ident(name, _) = callee {
            // `error(x)` desugars to the builtin `Result.Err { error: x }` and is
            // never a user function (DESIGN.md 5.6).
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
            // A local holding a closure/function value is called indirectly.
            if let Some(local) = self.lookup(name) {
                let ops = self.lower_args(args);
                return Rvalue::Call(Callee::Indirect(Operand::Local(local)), ops);
            }
            // A known free function resolves to its storage symbol.
            if let Some(symbol) = self.ctx.resolve_fn_symbol(&self.module, name) {
                let mut ops = self.lower_args(args);
                self.pad_trailing_nullable(name, &mut ops);
                self.copy_nonref_args(name, &mut ops);
                return Rvalue::Call(Callee::Free(symbol), ops);
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

    fn lower_args(&mut self, args: &[Arg]) -> Vec<Operand> {
        let mut ops = Vec::with_capacity(args.len());
        for a in args {
            let v = self.lower_expr(&a.expr);
            ops.push(v);
        }
        ops
    }

    /// Deep-copy each argument whose parameter is a non-reference heap aggregate
    /// (the default for a non-`ref` heap type), so the callee mutates its own copy.
    /// A `ref(...)` parameter is left as a shared borrow. The `__deep_copy` builtin
    /// is type-directed at codegen (an aggregate is copied, anything else is passed
    /// through with its reference count balanced).
    fn copy_nonref_args(&mut self, name: &str, ops: &mut [Operand]) {
        let Some(copies) = self.ctx.fn_param_copies(&self.module, name) else {
            return;
        };
        for (op, needs) in ops.iter_mut().zip(copies.iter()) {
            if *needs {
                *op = self
                    .b
                    .emit(Rvalue::Call(Callee::Builtin("__deep_copy".into()), vec![op.clone()]));
            }
        }
    }

    /// Pad a call's argument list with `null` for each omitted trailing nullable
    /// parameter of `name` (a free function or UFCS method), so a call may leave
    /// them off (DESIGN.md 5.6). The type checker has already verified the omitted
    /// parameters are nullable; padding stops at the first non-nullable one.
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
    // Cells in this closure: its own captured-and-mutated locals (for nested
    // closures), plus the captures that are shared cells in the enclosing body --
    // both are accessed through the cell array's element 0.
    fl.cells = crate::analysis::cell_promotions(&closure_block(body));
    for c in cell_captures {
        fl.cells.insert(c.clone());
    }
    // Parameters are not cells (like `lower_callable`): a parameter has no binder
    // that wraps it, and inside the closure its name shadows any same-named
    // captured cell. Leaving a captured-and-mutated parameter in the set would
    // bind it as a plain scalar that read/write/capture sites then index as a
    // cell array.
    for p in params {
        fl.cells.remove(&p.name);
    }
    let captures: Vec<_> = capture_names
        .iter()
        .map(|n| {
            let l = fl.b.fresh_local(Some(n.clone()));
            fl.bind(n, l);
            l
        })
        .collect();
    let param_locals = fl.bind_params(params);
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
