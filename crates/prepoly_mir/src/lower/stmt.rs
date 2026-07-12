//! Statement and control-flow lowering.
//!
//! All branching constructs decompose into basic blocks here. The result of a
//! value-producing construct (`if`/`match`/`if let`/`&&`/`||`/`expr!`) is held
//! in a dedicated result local that each arm writes and the merge block reads;
//! because MIR locals are mutable slots this needs no phi nodes (see
//! [`crate::cfg`]). Loop targets are tracked so `break`/`continue` jump to the
//! right blocks.

use prepoly_hir::{FloatKind, IntKind, Type};
use prepoly_parser::ast::{AssignOp, Block, Expr, Pattern, Stmt, TypeExpr};

use crate::cfg::{MirStmt, Terminator};
use crate::ids::LocalId;
use crate::lower::{FnLower, compound_op};
use crate::value::{Literal, Operand, Place, Projection, Rvalue};

/// Resolve a `let` annotation to a concrete type when it is built from primitives
/// (numbers, `bool`, `string`, nullable, array, function). Nominal names return
/// `None` so the binding stays inferred (monomorphization recovers them from use);
/// this preserves annotations the initializer or call site alone is ambiguous
/// about, such as `int32?` for a `null` (a `let`, or a nullable parameter).
pub(crate) fn resolve_simple_type(te: &TypeExpr) -> Option<Type> {
    match te {
        TypeExpr::Named(name, _) => primitive_type(name),
        TypeExpr::Nullable(inner, _) => Some(Type::Nullable(Box::new(resolve_simple_type(inner)?))),
        TypeExpr::Array(inner, len, _) => {
            let e = resolve_simple_type(inner)?;
            Some(match len {
                Some(n) => Type::Array(Box::new(e), *n),
                None => Type::Slice(Box::new(e)),
            })
        }
        TypeExpr::Fun(params, ret, _) => {
            let ps = params
                .iter()
                .map(resolve_simple_type)
                .collect::<Option<Vec<_>>>()?;
            Some(Type::Fun(ps, Box::new(resolve_simple_type(ret)?)))
        }
        // `T!` (a Result) carries no simple, fully-known local hint; the engine
        // infers the local's type from its initializer/uses. (`infer`/`infer[]`
        // likewise resolve to no hint via `primitive_type`.)
        TypeExpr::Fallible(_, _) => None,
        TypeExpr::Tuple(elems, _) => {
            let ts = elems
                .iter()
                .map(resolve_simple_type)
                .collect::<Option<Vec<_>>>()?;
            Some(Type::Tuple(ts))
        }
        TypeExpr::Anonymous(fields, _) => {
            let mut resolved = Vec::with_capacity(fields.len());
            for (name, fty) in fields {
                resolved.push((name.clone(), resolve_simple_type(fty)?));
            }
            Some(prepoly_hir::structural_record(resolved))
        }
        // Mutability and reference-ness are front-end concepts; the back end sees
        // the plain `T` (a reference is a pointer, the same as the value handle).
        TypeExpr::Mut(inner, _) | TypeExpr::Ref(inner, _) => resolve_simple_type(inner),
        // `typeof(v)` is not a "simple" type here (it needs the checker's
        // inference); the binding stays inferred and monomorphization recovers
        // its type from the value / use, or from the recorded uninit-let type.
        TypeExpr::TypeOf(..) => None,
        // A refinement / slot reference is a nominal instance whose concrete
        // layout the checker resolves; the binding stays inferred here.
        TypeExpr::Refine(..) | TypeExpr::SelfField(..) | TypeExpr::TypeSlot(..) => None,
    }
}

fn primitive_type(name: &str) -> Option<Type> {
    if let Some(k) = IntKind::from_name(name) {
        return Some(Type::Int(k));
    }
    match name {
        "bool" => Some(Type::Bool),
        "float32" => Some(Type::Float(FloatKind::F32)),
        "float64" => Some(Type::Float(FloatKind::F64)),
        "string" => Some(Type::Str),
        "void" => Some(Type::Void),
        _ => None,
    }
}

/// Where an assignment target resolves to.
enum PlaceTarget {
    Local(LocalId),
    Global(String),
    Projected(Place),
    /// An unsupported target shape; assignment is a no-op (matches codegen,
    /// which silently ignores non-place targets).
    Discard,
}

impl FnLower<'_, '_> {
    /// Lower a callable/closure top-level statement sequence: each statement
    /// runs for effect (expression statements discard their value, matching the
    /// rule that functions need an explicit `return`). Stops at the first block
    /// terminator.
    pub(crate) fn lower_body_stmts(&mut self, stmts: &[Stmt]) {
        for s in stmts {
            if self.b.terminated() {
                break;
            }
            self.lower_stmt(s);
        }
    }

    /// Lower a block used as an expression: open a scope, run the statements
    /// keeping the trailing expression's value, and return it (or `void`).
    pub(crate) fn lower_block_value(&mut self, b: &Block) -> Operand {
        self.push_scope();
        let mut last = Operand::void();
        for s in &b.stmts {
            if self.b.terminated() {
                break;
            }
            match s {
                Stmt::Expr(e) => last = self.lower_expr(e),
                _ => self.lower_stmt(s),
            }
        }
        self.pop_scope();
        last
    }

    /// Lower one statement, possibly emitting control flow.
    pub(crate) fn lower_stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Let { pat, ty, value, .. } => match value {
                Some(value) => self.lower_let(pat, ty.as_ref(), value),
                None => self.lower_let_uninit(pat, ty.as_ref()),
            },
            Stmt::Assign {
                target, op, value, ..
            } => self.lower_assign(target, *op, value),
            Stmt::Expr(e) => self.lower_expr_stmt(e),
            Stmt::While { cond, body, .. } => self.lower_while(cond, body),
            Stmt::For {
                pat,
                iter,
                body,
                span,
            } => {
                // A fields-loop the checker approved unrolls into one copy per
                // field; the copies are the same expansion the checker typed. Only
                // a plain loop variable can be a fields-loop (see
                // `fields_loop_target`), so its name is available here.
                if let Some(fields) = self.ctx.fields_loops.get(span)
                    && let Pattern::Binding(var, _) = pat
                {
                    let fields = fields.clone();
                    for (i, field) in fields.iter().enumerate() {
                        let expanded = prepoly_hir::expand_fields_body(body, var, field, i);
                        self.push_scope();
                        for stmt in &expanded.stmts {
                            if self.b.terminated() {
                                break;
                            }
                            self.lower_stmt(stmt);
                        }
                        self.pop_scope();
                    }
                    return;
                }
                self.lower_for(pat, iter, body)
            }
            Stmt::Return(opt, _) => {
                let v = match opt {
                    Some(e) => self.lower_expr(e),
                    None => Operand::void(),
                };
                self.b.terminate(Terminator::Return(v));
            }
            // `break`/`continue` end the current iteration, so a pending `for`
            // write-back must run on these edges too, not only on the body's
            // fall-through tail.
            Stmt::Break(_) => {
                if let Some(brk) = self.loops.last().map(|f| f.brk) {
                    self.emit_loop_writeback();
                    self.b.terminate(Terminator::Goto(brk));
                }
            }
            Stmt::Continue(_) => {
                if let Some(cont) = self.loops.last().map(|f| f.cont) {
                    self.emit_loop_writeback();
                    self.b.terminate(Terminator::Goto(cont));
                }
            }
        }
    }

    /// An expression used as a statement: evaluate for side effects, discard the
    /// result. A bare call emits an `eval` (no junk temporary); everything else
    /// reuses the value-producing path and drops the operand.
    fn lower_expr_stmt(&mut self, e: &Expr) {
        match e {
            Expr::Call(callee, args, _) => {
                let rv = self.lower_call(callee, args);
                self.b.push(MirStmt::Eval(rv));
            }
            _ => {
                let _ = self.lower_expr(e);
            }
        }
    }

    /// The concrete slot type for a `let` annotation: the checker-resolved type
    /// for a `typeof`-bearing annotation (which the scope-free
    /// [`resolve_simple_type`] cannot handle), else the simple resolution.
    fn slot_type(&self, ty: &TypeExpr) -> Option<Type> {
        if let Some(t) = self.ctx.typeof_types.get(&ty.span()) {
            return Some(t.clone());
        }
        resolve_simple_type(ty)
    }

    fn lower_let(&mut self, pat: &Pattern, ty: Option<&TypeExpr>, value: &Expr) {
        match pat {
            // The common case: a single name binds the value directly into its
            // own slot. A resolvable annotation fixes the slot's type so an
            // annotation the initializer cannot express (e.g. `int32?` for `null`)
            // survives into monomorphization.
            Pattern::Binding(name, _) => {
                let v = self.lower_expr(value);
                // A captured-and-mutated binding is heap-promoted to a shared cell
                // by `bind_value`; the scalar type annotation does not apply to the
                // cell array, so the cell case takes precedence over it.
                if self.is_cell(name) {
                    self.bind_value(name, v);
                } else {
                    match ty.and_then(|t| self.slot_type(t)) {
                        Some(t) => {
                            let local = self.b.fresh_local_typed(Some(name.clone()), t);
                            self.b.push(MirStmt::Assign(local, Rvalue::Use(v)));
                            self.bind(name, local);
                        }
                        None => self.bind_value(name, v),
                    }
                }
            }
            // `let _ = e`: evaluate for effects, bind nothing.
            Pattern::Wildcard(_) => {
                let _ = self.lower_expr(value);
            }
            // Destructuring `let`: bind the value to a subject local and walk the
            // pattern. Top-level `let` patterns are irrefutable, so no condition
            // is tested.
            _ => {
                let v = self.lower_expr(value);
                let subj = self.b.make_local(v);
                self.lower_pattern_bind(pat, subj);
            }
        }
    }

    /// Lower `let x: T` (no initializer). The slot is declared with its
    /// annotated type; a record (or other aggregate) additionally gets a
    /// default-valued skeleton so field-by-field initialization has a target
    /// allocation. The checker's definite-assignment pass rejects any read
    /// before full initialization, so a default value is never observed.
    fn lower_let_uninit(&mut self, pat: &Pattern, ty: Option<&TypeExpr>) {
        let Pattern::Binding(name, _) = pat else {
            // The checker rejects uninitialized wildcard/destructuring lets.
            return;
        };
        // Nominal annotations (records, sums) are not "simple" types; resolve
        // them against the program's types for the slot type and, for records,
        // the skeleton's field list.
        if let Some(TypeExpr::Named(type_name, _)) = ty {
            let sym = self.resolve_self_name(type_name);
            if let Some(info) = self.ctx.type_info(&sym) {
                let slot_ty = info.type_ref();
                let local = self
                    .b
                    .fresh_local_typed(Some(name.clone()), slot_ty.clone());
                if let Some(op) = self.default_operand(&slot_ty, &mut Vec::new()) {
                    self.b.push(MirStmt::Assign(local, Rvalue::Use(op)));
                }
                self.bind(name, local);
                return;
            }
        }
        match ty.and_then(resolve_simple_type) {
            Some(t) => {
                let local = self.b.fresh_local_typed(Some(name.clone()), t.clone());
                if let Some(op) = self.default_operand(&t, &mut Vec::new()) {
                    self.b.push(MirStmt::Assign(local, Rvalue::Use(op)));
                }
                self.bind(name, local);
            }
            None => {
                // No resolvable annotation (the checker already required one);
                // bind an untyped slot so later whole assignments type it.
                let local = self.b.fresh_local(Some(name.clone()));
                self.bind(name, local);
            }
        }
    }

    /// A default-valued operand for `t`, or `None` when the type has no
    /// constructible default (sums, function values, records containing one).
    /// Emits the statements that build aggregate defaults. `visiting` guards
    /// against infinitely recursive record skeletons (`type A = { b: B }`,
    /// `type B = { a: A }`), which have no constructible value at all.
    fn default_operand(&mut self, t: &Type, visiting: &mut Vec<i32>) -> Option<Operand> {
        match t {
            Type::Int(_) => Some(Operand::Const(Literal::Int(0))),
            Type::Float(_) => Some(Operand::Const(Literal::Float(0.0))),
            Type::Bool => Some(Operand::Const(Literal::Bool(false))),
            Type::Str => Some(Operand::Const(Literal::Str(String::new()))),
            Type::Nullable(_) => Some(Operand::Const(Literal::Null)),
            // Aggregate defaults seed their temp local with the full type: an
            // empty `[]` (or a zero literal element) carries no element type of
            // its own, and monomorphization must not re-derive a narrower one.
            Type::Slice(_) => Some(self.b.emit_known(Rvalue::Array(Vec::new()), t.clone())),
            Type::Array(e, n) => {
                let elems = (0..*n)
                    .map(|_| self.default_operand(e, visiting))
                    .collect::<Option<Vec<_>>>()?;
                Some(self.b.emit_known(Rvalue::Array(elems), t.clone()))
            }
            Type::Tuple(ts) => {
                let elems = ts
                    .iter()
                    .map(|t| self.default_operand(t, visiting))
                    .collect::<Option<Vec<_>>>()?;
                Some(self.b.emit_known(Rvalue::Array(elems), t.clone()))
            }
            Type::Record(n) => {
                if visiting.contains(&n.id) {
                    return None;
                }
                visiting.push(n.id);
                let info = self.ctx.type_info_by_id(n.id)?;
                let field_infos = match &info.kind {
                    prepoly_hir::TypeKind::Record { fields, .. } => fields.clone(),
                    _ => return None,
                };
                let ty_sym = info.symbol.clone();
                let ty_name = info.name.clone();
                let mut fields = Vec::with_capacity(field_infos.len());
                // The declared field types also seed the result as a known
                // substitution, so a literal default (`Int(0)`) is laid out at
                // the field's width instead of the literal's default kind.
                let mut subst = prepoly_hir::Substitution::empty();
                for f in &field_infos {
                    let ft = f.resolved_ty.as_ref()?;
                    fields.push((f.name.clone(), self.default_operand(ft, visiting)?));
                    subst.insert(f.name.clone(), ft.clone());
                }
                visiting.pop();
                let known = Type::Record(prepoly_hir::NominalType::with_substitution(
                    n.id, ty_name, subst,
                ));
                Some(
                    self.b
                        .emit_known(Rvalue::Record { ty: ty_sym, fields }, known),
                )
            }
            _ => None,
        }
    }

    // ----- assignment -----

    fn lower_assign(&mut self, target: &Expr, op: AssignOp, value: &Expr) {
        let rhs = self.lower_expr(value);
        let place = self.lower_place(target);
        let new_value = if op == AssignOp::Eq {
            rhs
        } else {
            let cur = self.load_target(&place);
            self.b.emit(Rvalue::Bin(compound_op(op), cur, rhs))
        };
        self.store_target(place, new_value);
    }

    /// Resolve an assignment target, evaluating any base/index sub-expressions
    /// exactly once.
    fn lower_place(&mut self, target: &Expr) -> PlaceTarget {
        match target {
            // A cell-promoted name writes element 0 of its one-element cell array --
            // but only when it is actually a local here. A module global that a
            // closure captures and mutates is in the cell set yet has no local slot;
            // it is written as a global, mirroring the read path in `lower_ident`
            // (which is why this must guard on `lookup`, not `expect` it).
            Expr::Ident(name, _) if self.is_cell(name) && self.lookup(name).is_some() => {
                let local = self.lookup(name).unwrap();
                let zero = Operand::Const(Literal::Int(0));
                PlaceTarget::Projected(Place::projected(local, vec![Projection::Index(zero)]))
            }
            Expr::Ident(name, _) => match self.lookup(name) {
                Some(local) => PlaceTarget::Local(local),
                // Module-qualified, matching the read path in `lower_ident`.
                None => PlaceTarget::Global(self.ctx.global_symbol(&self.module, name)),
            },
            Expr::Field(base, field, _) => {
                let recv = self.lower_expr(base);
                let recv = self.b.make_local(recv);
                PlaceTarget::Projected(Place::projected(
                    recv,
                    vec![Projection::Field(field.clone())],
                ))
            }
            Expr::Index(base, idx, _) => {
                let arr = self.lower_expr(base);
                let arr = self.b.make_local(arr);
                let i = self.lower_expr(idx);
                PlaceTarget::Projected(Place::projected(arr, vec![Projection::Index(i)]))
            }
            _ => PlaceTarget::Discard,
        }
    }

    fn load_target(&mut self, place: &PlaceTarget) -> Operand {
        match place {
            PlaceTarget::Local(id) => Operand::Local(*id),
            PlaceTarget::Global(name) => self.b.emit(Rvalue::Global(name.clone())),
            PlaceTarget::Projected(p) => self.b.emit(Rvalue::Load(p.clone())),
            PlaceTarget::Discard => Operand::void(),
        }
    }

    fn store_target(&mut self, place: PlaceTarget, v: Operand) {
        match place {
            PlaceTarget::Local(id) => self.b.push(MirStmt::Assign(id, Rvalue::Use(v))),
            PlaceTarget::Global(name) => self.b.push(MirStmt::SetGlobal(name, v)),
            PlaceTarget::Projected(p) => self.b.push(MirStmt::Store(p, v)),
            PlaceTarget::Discard => {}
        }
    }

    // ----- loops -----

    fn lower_while(&mut self, cond: &Expr, body: &Block) {
        let cond_bb = self.b.new_block();
        let body_bb = self.b.new_block();
        let end_bb = self.b.new_block();
        self.b.terminate(Terminator::Goto(cond_bb));

        self.b.switch_to(cond_bb);
        let c = self.lower_expr(cond);
        self.b.terminate(Terminator::CondBranch {
            cond: c,
            then: body_bb,
            els: end_bb,
        });

        self.b.switch_to(body_bb);
        self.loops.push(crate::lower::LoopFrame {
            cont: cond_bb,
            brk: end_bb,
            writeback: None,
        });
        let _ = self.lower_block_value(body);
        if !self.b.terminated() {
            self.b.terminate(Terminator::Goto(cond_bb));
        }
        self.loops.pop();
        self.b.switch_to(end_bb);
    }

    /// Emit the innermost loop's pending element write-back, if any: a `for`
    /// body that reassigns its loop variable binds the element by reference, so
    /// the variable's current value is stored back into the array slot on every
    /// edge that ends the iteration.
    fn emit_loop_writeback(&mut self) {
        let Some((arr, idx, var)) = self.loops.last().and_then(|f| f.writeback.clone()) else {
            return;
        };
        let e = self.lower_ident(&var);
        self.b.push(MirStmt::Store(
            Place::projected(arr, vec![Projection::Index(Operand::Local(idx))]),
            e,
        ));
    }

    /// `for v in iter` desugars to an index loop over the iterable's length,
    /// matching codegen: `i = 0; while i < len(iter) { v = iter[i]; body; i+=1 }`.
    ///
    /// A literal range iterable never escapes the loop, so it skips the array
    /// materialization entirely and counts in place.
    fn lower_for(&mut self, pat: &Pattern, iter: &Expr, body: &Block) {
        // A range counts through a single variable; the checker rejects a
        // destructuring pattern over one.
        if let Expr::Range(lo, hi, span) = iter
            && let Pattern::Binding(var, _) = pat
        {
            return self.lower_for_range(var, lo, hi, *span, body);
        }
        let arr = self.lower_expr(iter);
        let arr = self.b.make_local(arr);
        let i = self.b.fresh_local(None);
        self.b.push(MirStmt::Assign(
            i,
            Rvalue::Use(Operand::Const(crate::value::Literal::Int(0))),
        ));

        let cond_bb = self.b.new_block();
        let body_bb = self.b.new_block();
        let incr_bb = self.b.new_block();
        let end_bb = self.b.new_block();
        self.b.terminate(Terminator::Goto(cond_bb));

        self.b.switch_to(cond_bb);
        let len = self.b.emit(Rvalue::Call(
            crate::value::Callee::Builtin("array_len".into()),
            vec![Operand::Local(arr)],
        ));
        let c = self.b.emit(Rvalue::Bin(
            prepoly_parser::ast::BinOp::Lt,
            Operand::Local(i),
            len,
        ));
        self.b.terminate(Terminator::CondBranch {
            cond: c,
            then: body_bb,
            els: end_bb,
        });

        self.b.switch_to(body_bb);
        self.push_scope();
        let elem = self.b.emit(Rvalue::Load(Place::projected(
            arr,
            vec![Projection::Index(Operand::Local(i))],
        )));
        // A plain loop variable is bound by reference: a body that reassigns it
        // (`e *= 2`, `e = ...`) writes the new value back into the slot, so the
        // array is mutated in place. (A managed element mutated through its own
        // fields aliases the slot already, so only a bare reassignment needs this.)
        // The write-back is carried on the loop frame so `continue`/`break` edges
        // emit it too.
        //
        // A DESTRUCTURING pattern binds the element's parts, which are values of
        // their own -- there is no single binding to write back through.
        let writeback = match pat {
            Pattern::Binding(var, _) => {
                self.bind_value(var, elem);
                reassigns_var(body, var).then(|| (arr, i, var.to_string()))
            }
            _ => {
                let el = self.b.make_local(elem);
                self.lower_pattern_bind(pat, el);
                None
            }
        };
        self.loops.push(crate::lower::LoopFrame {
            cont: incr_bb,
            brk: end_bb,
            writeback,
        });
        let _ = self.lower_block_value(body);
        if !self.b.terminated() {
            self.emit_loop_writeback();
            self.b.terminate(Terminator::Goto(incr_bb));
        }
        self.loops.pop();
        self.pop_scope();

        self.b.switch_to(incr_bb);
        let next = self.b.emit(Rvalue::Bin(
            prepoly_parser::ast::BinOp::Add,
            Operand::Local(i),
            Operand::Const(crate::value::Literal::Int(1)),
        ));
        self.b.push(MirStmt::Assign(i, Rvalue::Use(next)));
        self.b.terminate(Terminator::Goto(cond_bb));
        self.b.switch_to(end_bb);
    }

    /// `for v in [lo..hi]` counts directly: `i = lo; while i < hi { v = i;
    /// body; i += 1 }`. Materializing the range as an array (the general
    /// [`Self::lower_for`] path) would cost the full range in memory and one
    /// push per element for a value the program can never observe. The loop
    /// variable binds a COPY of the counter, so a body that reassigns it
    /// neither skews iteration nor needs the array write-back -- the same
    /// visible behavior as writing into the discarded range array. The
    /// counter carries the checker's range element type when one was recorded
    /// (see `range_elem_type`), so counting matches the checked width.
    fn lower_for_range(
        &mut self,
        var: &str,
        lo: &Expr,
        hi: &Expr,
        span: prepoly_parser::Span,
        body: &Block,
    ) {
        let elem = self.range_elem_type(span);
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
            prepoly_parser::ast::BinOp::Lt,
            Operand::Local(i),
            Operand::Local(end),
        ));
        self.b.terminate(Terminator::CondBranch {
            cond: c,
            then: body_bb,
            els: end_bb,
        });

        self.b.switch_to(body_bb);
        self.push_scope();
        let elem = self.b.emit(Rvalue::Use(Operand::Local(i)));
        self.bind_value(var, elem);
        self.loops.push(crate::lower::LoopFrame {
            cont: incr_bb,
            brk: end_bb,
            writeback: None,
        });
        let _ = self.lower_block_value(body);
        if !self.b.terminated() {
            self.b.terminate(Terminator::Goto(incr_bb));
        }
        self.loops.pop();
        self.pop_scope();

        self.b.switch_to(incr_bb);
        let next = self.b.emit(Rvalue::Bin(
            prepoly_parser::ast::BinOp::Add,
            Operand::Local(i),
            Operand::Const(crate::value::Literal::Int(1)),
        ));
        self.b.push(MirStmt::Assign(i, Rvalue::Use(next)));
        self.b.terminate(Terminator::Goto(cond_bb));
        self.b.switch_to(end_bb);
    }
}

/// Whether `block` reassigns the whole binding `var` (`var = ...` / `var op= ...`),
/// as opposed to mutating a field/element of it. Such a reassignment of a `for`
/// loop variable is the signal that the element must be written back to the array.
fn reassigns_var(block: &Block, var: &str) -> bool {
    block.stmts.iter().any(|s| stmt_reassigns_var(s, var))
}

fn stmt_reassigns_var(stmt: &Stmt, var: &str) -> bool {
    match stmt {
        Stmt::Assign { target, .. } => matches!(target, Expr::Ident(n, _) if n == var),
        Stmt::While { body, .. } => reassigns_var(body, var),
        // A nested `for` that rebinds the same name shadows it, so stop there.
        Stmt::For { pat, body, .. } => {
            !pat.bound_names().contains(&var) && reassigns_var(body, var)
        }
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => expr_reassigns_var(e, var),
        Stmt::Let { value, .. } => value.as_ref().is_some_and(|v| expr_reassigns_var(v, var)),
        _ => false,
    }
}

fn expr_reassigns_var(e: &Expr, var: &str) -> bool {
    match e {
        Expr::Block(b, _) => reassigns_var(b, var),
        Expr::If(_, t, els, _) | Expr::IfLet(_, _, t, els, _) => {
            reassigns_var(t, var) || els.as_ref().is_some_and(|e| expr_reassigns_var(e, var))
        }
        Expr::Match(_, arms, _) => arms.iter().any(|a| expr_reassigns_var(&a.body, var)),
        _ => false,
    }
}
