//! Statement lowering: blocks, `let` (annotated slots, and the default
//! skeleton of an uninitialized `let x: T`), assignment places, and the loops.
//!
//! `while` and `for` decompose into basic blocks here (a `for` over a literal
//! range counts in place; a `for` whose body reassigns its variable writes
//! the element back on every edge leaving the iteration). Loop targets are
//! tracked so `break`/`continue` jump to the right blocks. The
//! value-producing branching constructs live in the `expr` module.

use brass_hir::{FloatKind, IntKind, Type};
use brass_parser::ast::{AssignOp, Block, Expr, Pattern, Stmt, TypeExpr};

use crate::cfg::{MirStmt, Terminator};
use crate::ids::LocalId;
use crate::lower::order::{assigned_names, assigned_names_block};
use crate::lower::{FnLower, compound_op};
use crate::value::{Literal, Operand, Place, Projection, Rvalue};

/// Resolve a `let` annotation to a concrete type when it is built from primitives
/// (numbers, `bool`, `string`, nullable, array, function). Nominal names return
/// `None` so the binding stays inferred (monomorphization recovers them from use);
/// this preserves annotations the initializer or call site alone is ambiguous
/// about, such as `int32?` for a `null` (a `let`, or a nullable parameter).
pub fn resolve_simple_type(te: &TypeExpr) -> Option<Type> {
    match te {
        TypeExpr::Named(name, _) => primitive_type(name),
        TypeExpr::Nullable(inner, _) => Some(Type::nullable(resolve_simple_type(inner)?)),
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
            for (name, fty, _) in fields {
                resolved.push((name.clone(), resolve_simple_type(fty)?));
            }
            Some(brass_hir::structural_record(resolved))
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
    /// A target that is not a place. The checker rejects such an assignment
    /// ("invalid assignment target"); lowering keeps it a no-op.
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

    /// Lower a block in statement position: open a scope and run its
    /// statements, the trailing one included as a statement.
    pub(crate) fn lower_block_stmts(&mut self, b: &Block) {
        self.push_scope();
        self.lower_body_stmts(&b.stmts);
        self.pop_scope();
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

    /// Unroll one checked field sequence, preserving the loop's control flow.
    fn lower_fields_body(
        &mut self,
        body: &Block,
        var: &str,
        fields: &[String],
        exit: crate::BlockId,
    ) {
        for (i, field) in fields.iter().enumerate() {
            let next = self.b.new_block();
            let expanded = brass_hir::expand_fields_body(body, var, field, i);
            self.push_scope();
            // The compile-time copies form one logical loop. A
            // `break` leaves the whole sequence, while `continue`
            // advances to the next expanded field.
            self.loops.push(crate::lower::LoopFrame {
                cont: next,
                brk: exit,
                writeback: None,
            });
            for stmt in &expanded.stmts {
                if self.b.terminated() {
                    break;
                }
                self.lower_stmt(stmt);
            }
            if !self.b.terminated() {
                self.b.terminate(Terminator::Goto(next));
            }
            self.loops.pop();
            self.pop_scope();
            self.b.switch_to(next);
        }
        if !self.b.terminated() {
            self.b.terminate(Terminator::Goto(exit));
        }
    }

    /// Lower one statement, possibly emitting control flow.
    pub(crate) fn lower_stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Let { pat, ty, value, .. } => match value {
                // A generalized closure binding builds no value here: every
                // use builds its own (see `lower::closure`).
                Some(Expr::Closure(params, body, _))
                    if let Pattern::Binding(name, None, span) = pat
                        && self.ctx.tables.generalized.contains(span) =>
                {
                    self.bind_closure_template(name, params, body)
                }
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
                    && let Pattern::Binding(var, _, _) = pat
                {
                    let fields = fields.clone();
                    if let Some(instances) = self.ctx.instance_fields.get(span) {
                        let mut alternatives: Vec<_> = instances.values().cloned().collect();
                        alternatives.sort();
                        alternatives.dedup();
                        let exit = self.b.new_block();
                        for fields in alternatives {
                            let selected = self.b.new_block();
                            let other = self.b.new_block();
                            let cond = self.b.emit_known(
                                Rvalue::FieldsTest {
                                    site: *span,
                                    fields: fields.clone(),
                                },
                                Type::Bool,
                            );
                            self.b.terminate(Terminator::CondBranch {
                                cond,
                                then: selected,
                                els: other,
                            });
                            self.b.switch_to(selected);
                            self.lower_fields_body(body, var, &fields, exit);
                            self.b.switch_to(other);
                        }
                        // A checked live loop always has a selected expansion.
                        self.b.terminate(Terminator::Unreachable);
                        self.b.switch_to(exit);
                    } else {
                        let exit = self.b.new_block();
                        self.lower_fields_body(body, var, &fields, exit);
                        self.b.switch_to(exit);
                    }
                    return;
                }
                self.lower_for(pat, iter, body)
            }
            Stmt::Return(opt, _) => {
                let v = match opt {
                    Some(e) => {
                        let v = self.lower_expr(e);
                        // A forwarded Result whose payload the checker marked
                        // for lifting is rebuilt with its Err arm wrapped
                        // (`!` sites lift in their own propagation arm).
                        if !matches!(e, Expr::ErrorProp(..))
                            && self.ctx.lift_errs.contains(&e.span())
                        {
                            self.wrap_forwarded_err(v, e.span())
                        } else {
                            v
                        }
                    }
                    None => Operand::void(),
                };
                // Returning ends every enclosing iteration of this body.
                self.emit_exit_writebacks();
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

    /// Lower an expression used as a statement: evaluate it for its side
    /// effects and discard the result. A bare call emits an `eval` (no junk
    /// temporary). A branching expression yields no value at all -- its arms
    /// run for their effects and their trailing values are dropped --
    /// matching the checker, which does not join the arms of a statement
    /// `if`/`if let`/`match`. Everything else reuses the value-producing path
    /// and drops the operand.
    pub(super) fn lower_expr_stmt(&mut self, e: &Expr) {
        match e {
            // An `error(..)` statement's Result is kept in a local: the
            // callable's error type joins its payload (see
            // `analysis::fallible_block`), which monomorphization reads from
            // the call's result.
            Expr::Call(callee, args, span) if matches!(&**callee, Expr::Ident(name, _) if name == "error") =>
            {
                let rv = self.lower_call(callee, args, *span);
                let _ = self.b.emit(rv);
            }
            Expr::Call(callee, args, span) => {
                let rv = self.lower_call(callee, args, *span);
                self.b.push(MirStmt::Eval(rv));
            }
            Expr::If(cond, then, els, span) => {
                self.lower_if(cond, then, els.as_deref(), false, *span);
            }
            Expr::IfLet(pat, scrut, then, els, span) => {
                self.lower_iflet(pat, scrut, then, els.as_deref(), false, *span);
            }
            Expr::Match(scrut, arms, span) => {
                self.lower_match(scrut, arms, false, *span);
            }
            Expr::Block(b, _) => self.lower_block_stmts(b),
            _ => {
                let _ = self.lower_expr(e);
            }
        }
    }

    /// The concrete slot type for a `let` annotation: the checker-resolved type
    /// for a `typeof`-bearing annotation (which the scope-free
    /// [`resolve_simple_type`] cannot handle), else the simple resolution.
    pub(super) fn slot_type(&self, ty: &TypeExpr) -> Option<Type> {
        if let Some(t) = self.ctx.typeof_types.get(&ty.span()) {
            return Some(t.clone());
        }
        if let Some(t) = resolve_simple_type(ty) {
            return Some(t);
        }
        // A fully-concrete nominal annotation (`let frames: Frame[] = []`)
        // seeds too; generic nominals stay inferred (see
        // `ProgramCtx::concrete_nominal_ref`).
        self.resolve_concrete_annotation(ty)
    }

    fn resolve_concrete_annotation(&self, te: &TypeExpr) -> Option<Type> {
        match te {
            TypeExpr::Named(name, _) => self.ctx.concrete_nominal_ref(&self.module, name),
            TypeExpr::Nullable(inner, _) => {
                Some(Type::nullable(self.resolve_concrete_annotation(inner)?))
            }
            TypeExpr::Array(inner, len, _) => {
                let e = resolve_simple_type(inner)
                    .or_else(|| self.resolve_concrete_annotation(inner))?;
                Some(match len {
                    Some(n) => Type::Array(Box::new(e), *n),
                    None => Type::Slice(Box::new(e)),
                })
            }
            _ => None,
        }
    }

    fn lower_let(&mut self, pat: &Pattern, ty: Option<&TypeExpr>, value: &Expr) {
        match pat {
            // The common case: a single name binds the value directly into its
            // own slot. A resolvable annotation fixes the slot's type so an
            // annotation the initializer cannot express (e.g. `int32?` for `null`)
            // survives into monomorphization.
            // A captured-and-mutated binding is heap-promoted to a shared
            // cell; the annotation then types the cell's element, so
            // `let total: int64 = 0` keeps an `int64` cell however its
            // initializer is written.
            Pattern::Binding(name, _, span) => {
                let v = self.lower_expr(value);
                if let Some(annotation) = ty {
                    let shared = self.slot_type(annotation);
                    let local = self.annotation_local(name, Some(annotation), shared);
                    self.b.push(MirStmt::Assign(local, Rvalue::Use(v)));
                    // Promotion derives its element type from the seeded local,
                    // which may have a different type in each instance.
                    self.bind_value(name, Operand::Local(local));
                } else if self.ctx.expr_types.contains_key(span)
                    || self.ctx.instance_seeds.contains_key(span)
                {
                    let shared = self.ctx.expr_type(*span).cloned();
                    let local = self.b.fresh_seeded_local(*span, shared);
                    self.b.push(MirStmt::Assign(local, Rvalue::Use(v)));
                    self.bind_value(name, Operand::Local(local));
                } else {
                    self.bind_value(name, v);
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
        let Pattern::Binding(name, _, _) = pat else {
            // The checker rejects uninitialized wildcard/destructuring lets.
            return;
        };
        // A concrete refinement alias must keep its instance substitution for
        // the skeleton; resolving only its base declaration would recover the
        // open field types the alias concretized.
        if let Some(slot_ty @ Type::Record(_)) = ty.and_then(|ty| self.slot_type(ty)) {
            let local = self.annotation_local(name, ty, Some(slot_ty.clone()));
            if let Some(op) = self.default_operand(&slot_ty, &mut Vec::new()) {
                self.b.push(MirStmt::Assign(local, Rvalue::Use(op)));
            }
            self.bind_typed_slot(name, local, &slot_ty);
            return;
        }
        // Other nominal annotations are not "simple" types; resolve them
        // against the program's types for the slot type and, for records, the
        // skeleton's field list.
        if let Some(TypeExpr::Named(type_name, _)) = ty {
            let info = brass_hir::generated_type_id(type_name)
                .and_then(|id| self.ctx.type_info_by_id(id))
                .or_else(|| {
                    let sym = self.resolve_self_name(type_name);
                    self.ctx.type_info(&self.module, &sym)
                });
            if let Some(info) = info {
                let slot_ty = info.type_ref();
                let local = self.annotation_local(name, ty, Some(slot_ty.clone()));
                if let Some(op) = self.default_operand(&slot_ty, &mut Vec::new()) {
                    self.b.push(MirStmt::Assign(local, Rvalue::Use(op)));
                }
                self.bind_typed_slot(name, local, &slot_ty);
                return;
            }
        }
        match ty.and_then(|ty| self.slot_type(ty)) {
            Some(t) => {
                let local = self.annotation_local(name, ty, Some(t.clone()));
                if let Some(op) = self.default_operand(&t, &mut Vec::new()) {
                    self.b.push(MirStmt::Assign(local, Rvalue::Use(op)));
                }
                self.bind_typed_slot(name, local, &t);
            }
            None => {
                // No resolvable annotation (the checker already required one);
                // bind an untyped slot so later whole assignments type it.
                let local = self.annotation_local(name, ty, None);
                self.bind(name, local);
            }
        }
    }

    fn annotation_local(
        &mut self,
        name: &str,
        annotation: Option<&TypeExpr>,
        shared: Option<Type>,
    ) -> LocalId {
        match annotation {
            Some(annotation) => {
                // A source-declared type is not an observed instance seed.
                // Only scope-dependent annotations need the checker channel.
                if let Some(ty) = resolve_simple_type(annotation)
                    .or_else(|| self.resolve_concrete_annotation(annotation))
                {
                    self.b.fresh_local_typed(None, ty)
                } else {
                    self.b.fresh_seeded_local(annotation.span(), shared)
                }
            }
            None => self.b.fresh_local(Some(name.to_string())),
        }
    }

    /// Bind the annotated slot `local` of type `ty` to `name`, promoting it
    /// to a shared cell of `ty` elements when a closure shares later
    /// mutations. An uninitialized slot already contains the type's hidden
    /// default whenever one is constructible, so copying it into the cell
    /// preserves the declared element representation without exposing the
    /// value to source code.
    fn bind_typed_slot(&mut self, name: &str, local: LocalId, ty: &Type) {
        if self.cells.contains(name) {
            let cell = self.b.emit_known(
                Rvalue::Array(vec![Operand::Local(local)]),
                Type::Slice(Box::new(ty.clone())),
            );
            let cell_local = self.b.make_local(cell);
            self.bind_as(name, cell_local, true);
        } else {
            self.bind(name, local);
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
                    brass_hir::TypeKind::Record { fields, .. } => fields.clone(),
                    _ => return None,
                };
                let ty_sym = info.symbol.clone();
                let ty_name = info.name.clone();
                let mut fields = Vec::with_capacity(field_infos.len());
                // The declared field types also seed the result as a known
                // substitution, so a literal default (`Int(0)`) is laid out at
                // the field's width instead of the literal's default kind.
                let mut subst = brass_hir::Substitution::empty();
                for f in &field_infos {
                    let ft = n.substitution.get(&f.name).or(f.resolved_ty.as_ref())?;
                    fields.push((f.name.clone(), self.default_operand(ft, visiting)?));
                    subst.insert(f.name.clone(), ft.clone());
                }
                visiting.pop();
                let known = Type::Record(brass_hir::NominalType::with_substitution(
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

    /// `place = value` / `place op= value`. The place's subexpressions (its
    /// receiver and index) are evaluated first, left to right, then -- for a
    /// compound assignment -- the place's current value is read, then the
    /// right-hand side runs, and finally the store happens. Each part keeps
    /// the value it was evaluated with even when the right-hand side rebinds
    /// a variable it named (see [`crate::lower::order`]).
    fn lower_assign(&mut self, target: &Expr, op: AssignOp, value: &Expr) {
        let later = assigned_names([value]);
        let place = self.lower_place(target, &later);
        let new_value = if op == AssignOp::Eq {
            self.lower_expr(value)
        } else {
            let cur = self.load_target(&place);
            let cur = self.hold(cur, &later);
            let rhs = self.lower_expr(value);
            self.b.emit(Rvalue::Bin(compound_op(op), cur, rhs))
        };
        self.store_target(place, new_value);
    }

    /// Resolve an assignment target, evaluating any base/index sub-expressions
    /// exactly once. `later` names the variables the code that runs between
    /// this evaluation and the store (the right-hand side) may rebind; a base
    /// or index naming one of them is held at its current value.
    fn lower_place(&mut self, target: &Expr, later: &fxhash::FxHashSet<String>) -> PlaceTarget {
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
                let recv = self.hold(recv, later);
                let recv = self.b.make_local(recv);
                PlaceTarget::Projected(Place::projected(
                    recv,
                    vec![Projection::Field(field.clone())],
                ))
            }
            Expr::Index(base, idx, _) => {
                let arr = self.lower_expr(base);
                let mut before_store = assigned_names([&**idx]);
                before_store.extend(later.iter().cloned());
                let arr = self.hold(arr, &before_store);
                let arr = self.b.make_local(arr);
                let i = self.lower_expr(idx);
                let i = self.hold(i, later);
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
        if let Some(wb) = self.loops.last().and_then(|f| f.writeback) {
            self.emit_writeback(wb);
        }
    }

    /// Emit the write-back of EVERY enclosing loop, innermost first: the edge
    /// being built (a `return`, or a failed `!` propagating out of the
    /// callable) leaves all of them at once.
    pub(crate) fn emit_exit_writebacks(&mut self) {
        let pending: Vec<crate::lower::LoopWriteBack> = self
            .loops
            .iter()
            .rev()
            .filter_map(|f| f.writeback)
            .collect();
        for wb in pending {
            self.emit_writeback(wb);
        }
    }

    fn emit_writeback(&mut self, wb: crate::lower::LoopWriteBack) {
        let value = if wb.cell {
            self.b.emit(Rvalue::Load(Place::projected(
                wb.var,
                vec![Projection::Index(Operand::Const(Literal::Int(0)))],
            )))
        } else {
            Operand::Local(wb.var)
        };
        self.b.push(MirStmt::Store(
            Place::projected(wb.arr, vec![Projection::Index(Operand::Local(wb.idx))]),
            value,
        ));
    }

    /// `for v in iter` desugars to an index loop over the iterable's length:
    /// `i = 0; while i < len(iter) { v = iter[i]; body; i+=1 }`.
    ///
    /// A literal range iterable never escapes the loop, so it skips the array
    /// materialization entirely and counts in place.
    fn lower_for(&mut self, pat: &Pattern, iter: &Expr, body: &Block) {
        // A range counts through a single variable; the checker rejects a
        // destructuring pattern over one.
        if let Expr::Range(lo, hi, span) = iter
            && let Pattern::Binding(var, _, _) = pat
        {
            return self.lower_for_range(var, lo, hi, *span, body);
        }
        // The iterable is evaluated once: a body rebinding the variable it
        // named iterates (and writes back into) the original array.
        let arr = self.lower_expr(iter);
        let arr = self.hold(arr, &assigned_names_block(body));
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
            brass_parser::ast::BinOp::Lt,
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
            Pattern::Binding(var, _, _) => {
                self.bind_value(var, elem);
                let (local, cell) = self
                    .local_binding(var)
                    .expect("the loop variable was just bound");
                reassigns_var(body, var).then_some(crate::lower::LoopWriteBack {
                    arr,
                    idx: i,
                    var: local,
                    cell,
                })
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
            brass_parser::ast::BinOp::Add,
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
        span: brass_parser::Span,
        body: &Block,
    ) {
        let elem = self.range_elem_type(span);
        let (i, end) = self.range_bounds(lo, hi, elem.as_ref());

        let cond_bb = self.b.new_block();
        let body_bb = self.b.new_block();
        let incr_bb = self.b.new_block();
        let end_bb = self.b.new_block();
        self.b.terminate(Terminator::Goto(cond_bb));

        self.b.switch_to(cond_bb);
        let c = self.b.emit(Rvalue::Bin(
            brass_parser::ast::BinOp::Lt,
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
            brass_parser::ast::BinOp::Add,
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
    for stmt in &block.stmts {
        if stmt_reassigns_var(stmt, var) {
            return true;
        }
        // A `let` shadows from its declaration to the end of this lexical
        // block. Its initializer still sees the outer loop element and was
        // scanned above.
        if matches!(stmt, Stmt::Let { pat, .. } if pat.bound_names().contains(&var)) {
            return false;
        }
    }
    false
}

fn stmt_reassigns_var(stmt: &Stmt, var: &str) -> bool {
    match stmt {
        Stmt::Assign { target, value, .. } => {
            matches!(target, Expr::Ident(n, _) if n == var)
                || expr_reassigns_var(target, var)
                || expr_reassigns_var(value, var)
        }
        Stmt::While { cond, body, .. } => expr_reassigns_var(cond, var) || reassigns_var(body, var),
        // A nested `for` that rebinds the same name shadows it, so stop there.
        Stmt::For {
            pat, iter, body, ..
        } => {
            expr_reassigns_var(iter, var)
                || (!pat.bound_names().contains(&var) && reassigns_var(body, var))
        }
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => expr_reassigns_var(e, var),
        Stmt::Let { value, .. } => value.as_ref().is_some_and(|v| expr_reassigns_var(v, var)),
        _ => false,
    }
}

fn expr_reassigns_var(e: &Expr, var: &str) -> bool {
    match e {
        Expr::Unary(_, inner, _) | Expr::Field(inner, _, _) | Expr::ErrorProp(inner, _) => {
            expr_reassigns_var(inner, var)
        }
        Expr::Binary(_, left, right, _)
        | Expr::Index(left, right, _)
        | Expr::Range(left, right, _) => {
            expr_reassigns_var(left, var) || expr_reassigns_var(right, var)
        }
        Expr::Call(callee, args, _) => {
            expr_reassigns_var(callee, var)
                || args.iter().any(|arg| expr_reassigns_var(&arg.expr, var))
        }
        Expr::Closure(params, body, _) => {
            !params.iter().any(|param| param.name == var) && expr_reassigns_var(body, var)
        }
        Expr::Array(items, _) => items.iter().any(|item| expr_reassigns_var(item, var)),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => fields
            .iter()
            .any(|(_, value)| expr_reassigns_var(value, var)),
        Expr::Str(segments, _) => segments.iter().any(
            |segment| matches!(segment, brass_parser::ast::StrSeg::Expr(e) if expr_reassigns_var(e, var)),
        ),
        Expr::Block(b, _) => reassigns_var(b, var),
        Expr::If(cond, then, els, _) => {
            expr_reassigns_var(cond, var)
                || reassigns_var(then, var)
                || els.as_ref().is_some_and(|e| expr_reassigns_var(e, var))
        }
        Expr::IfLet(pat, subject, then, els, _) => {
            expr_reassigns_var(subject, var)
                || (!pat.bound_names().contains(&var) && reassigns_var(then, var))
                || els.as_ref().is_some_and(|e| expr_reassigns_var(e, var))
        }
        Expr::TypeTest(subject, _, _, _) => expr_reassigns_var(subject, var),
        Expr::Match(subject, arms, _) => {
            expr_reassigns_var(subject, var)
                || arms.iter().any(|arm| {
                    !arm.pattern.bound_names().contains(&var)
                        && expr_reassigns_var(&arm.body, var)
                })
        }
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(..)
        | Expr::Ident(..)
        | Expr::SelfExpr(..) => false,
    }
}
