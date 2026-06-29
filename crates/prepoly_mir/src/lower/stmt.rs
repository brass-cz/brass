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
            Stmt::Let { pat, ty, value, .. } => self.lower_let(pat, ty.as_ref(), value),
            Stmt::Assign {
                target, op, value, ..
            } => self.lower_assign(target, *op, value),
            Stmt::Expr(e) => self.lower_expr_stmt(e),
            Stmt::While { cond, body, .. } => self.lower_while(cond, body),
            Stmt::For {
                var, iter, body, ..
            } => self.lower_for(var, iter, body),
            Stmt::Return(opt, _) => {
                let v = match opt {
                    Some(e) => self.lower_expr(e),
                    None => Operand::void(),
                };
                self.b.terminate(Terminator::Return(v));
            }
            Stmt::Break(_) => {
                if let Some((_, brk)) = self.loops.last().copied() {
                    self.b.terminate(Terminator::Goto(brk));
                }
            }
            Stmt::Continue(_) => {
                if let Some((cont, _)) = self.loops.last().copied() {
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
                    match ty.and_then(resolve_simple_type) {
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
                None => PlaceTarget::Global(name.clone()),
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
        self.loops.push((cond_bb, end_bb));
        let _ = self.lower_block_value(body);
        if !self.b.terminated() {
            self.b.terminate(Terminator::Goto(cond_bb));
        }
        self.loops.pop();
        self.b.switch_to(end_bb);
    }

    /// `for v in iter` desugars to an index loop over the iterable's length,
    /// matching codegen: `i = 0; while i < len(iter) { v = iter[i]; body; i+=1 }`.
    fn lower_for(&mut self, var: &str, iter: &Expr, body: &Block) {
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
        self.bind_value(var, elem);
        self.loops.push((incr_bb, end_bb));
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
