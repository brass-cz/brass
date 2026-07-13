//! Closure typing for the monomorphizer: recovering a closure's concrete
//! parameter types from how the closure is *used* -- a direct in-body call, a
//! pass to a higher-order callee (probed by lightly inferring the callee's
//! body), a store into a function-typed record field, its own annotations
//! (an escaping closure), or an indirect call through a typed capture in its
//! own body -- and instantiating the closure body once per
//! (capture-types, param-types) tuple.

use super::*;

use crate::mono::scan::{resolve_alias, use_aliases};

impl Monomorphizer<'_, '_> {
    /// The declared parameter types of record `ty`'s field `field` when the
    /// field is annotated with a concrete function type -- the typing source for
    /// a closure stored into that field.
    fn record_field_fun_params(
        &self,
        module: &[String],
        ty: &str,
        field: &str,
    ) -> Option<Vec<Type>> {
        let info = self.program.resolve_type(module, ty)?;
        let TypeKind::Record { fields, .. } = &info.kind else {
            return None;
        };
        let f = fields.iter().find(|f| f.name == field)?;
        match f.resolved_ty.as_ref() {
            Some(Type::Fun(params, _)) if params.iter().all(prepoly_hir::is_fully_known) => {
                Some(params.clone())
            }
            _ => None,
        }
    }

    /// Derive an unannotated closure's parameter types from its OWN body: seed
    /// the capture locals with their (already resolved) types, lightly infer the
    /// body, and read what each parameter is CALLED with. An indirect call
    /// through a typed capture (`(x) -> func(g(x))` where `g: (int32) -> int32`
    /// is captured) pins `x` even though nothing outside the closure calls it.
    /// `None` when any parameter stays unpinned.
    fn closure_params_from_body(&self, id: ClosureId, capture_types: &[Type]) -> Option<Vec<Type>> {
        let clo = self.by_closure.get(&id)?;
        let body = &clo.body;
        let mut seeded: Vec<Option<Type>> = vec![None; body.locals.len()];
        for (cap, t) in clo.captures.iter().zip(capture_types) {
            seeded[cap.index()] = Some(t.clone());
        }
        for p in &body.params {
            if let Some(t) = body.locals[p.index()].ty.as_known() {
                seeded[p.index()] = Some(t.clone());
            }
        }
        let lt = self.probe_local_types(body, seeded);
        let mut out: Vec<Option<Type>> =
            body.params.iter().map(|p| lt[p.index()].clone()).collect();
        for block in &body.blocks {
            for stmt in &block.stmts {
                let (MirStmt::Assign(_, rv) | MirStmt::Eval(rv)) = stmt else {
                    continue;
                };
                if let Rvalue::Call(Callee::Indirect(Operand::Local(g)), args) = rv
                    && let Some(Type::Fun(ps, _)) = lt[g.index()].as_ref()
                {
                    for (a, pty) in args.iter().zip(ps) {
                        if let Operand::Local(al) = a
                            && let Some(slot) = body.params.iter().position(|p| p == al)
                            && out[slot].is_none()
                            && prepoly_hir::is_fully_known(pty)
                        {
                            out[slot] = Some(pty.clone());
                        }
                    }
                }
            }
        }
        out.into_iter().collect()
    }

    /// The type each parameter's own annotation fixes, positionally, `None` for
    /// an unannotated one. Lowering records a closure parameter's annotation on
    /// its local declaration, and a nominal annotation is resolved against the
    /// declaration so the type is self-describing -- exactly what the body is
    /// typed against (see `type_and_store_inner`, where a declared local's type
    /// overrides the seeded argument type). `None` when `id` names no closure.
    fn closure_param_annotations(&self, id: ClosureId) -> Option<Vec<Option<Type>>> {
        let clo = self.by_closure.get(&id)?;
        Some(
            clo.params
                .iter()
                .map(|p| {
                    clo.body.locals[p.index()]
                        .ty
                        .as_known()
                        .map(|t| resolve_nominal(self.program, t))
                })
                .collect(),
        )
    }

    /// The closure's parameter types from its own annotations, when every parameter
    /// is annotated. This types an *escaping* closure (returned, so neither called
    /// in-body nor passed to a function) -- e.g. `make_accumulator`'s returned
    /// `(amount: int32) -> ...`. `None` if any parameter is unannotated.
    fn closure_annotated_params(&self, id: ClosureId) -> Option<Vec<Type>> {
        self.closure_param_annotations(id)?.into_iter().collect()
    }

    /// Type a closure local: its captures come from the creation site and its
    /// parameter types from how it is used -- an in-body call (direct-call
    /// closures), being passed to a higher-order function (the callee's use of
    /// that parameter, recovered by probing), initializing a record field with a
    /// declared function type (the field's signature), or, for an escaping
    /// closure, its own parameter annotations. Also instantiates the closure
    /// body. `None` while any operand type is still unresolved.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn closure_local_type(
        &mut self,
        id: ClosureId,
        captures: &[Operand],
        local: LocalId,
        module: &[String],
        indirect_args: &HashMap<LocalId, Vec<Vec<Operand>>>,
        closure_passes: &HashMap<LocalId, (String, Vec<Operand>, usize)>,
        record_field_closures: &HashMap<LocalId, (LocalId, String, String)>,
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        let mut capture_types = Vec::with_capacity(captures.len());
        for c in captures {
            match self.operand_type(c, local_types)? {
                Some(t) => capture_types.push(t),
                None => return Ok(None),
            }
        }
        // Parameter types: from a direct in-body call, else from a higher-order
        // callee's use of the parameter the closure is passed as.
        let mut param_types = if let Some(call_sites) = indirect_args.get(&local) {
            match self.joined_arg_types(call_sites, local_types)? {
                Some(pt) => pt,
                None => return Ok(None),
            }
        } else if let Some((base, pass_args, idx)) = closure_passes.get(&local) {
            match self.probe_callee_param_types(base, pass_args, *idx, local_types)? {
                Some(pt) => pt,
                // The probe cannot answer (the receiver is still untyped, or
                // the callee never calls the parameter directly -- e.g. it only
                // re-captures it into another closure). A fully annotated
                // closure falls back to its own signature, which the checker
                // has already verified against every use; an unannotated one
                // waits for a later pass.
                None => match self.closure_annotated_params(id) {
                    Some(annotated) => annotated,
                    None => return Ok(None),
                },
            }
        } else if let Some(pt) = record_field_closures
            .get(&local)
            .and_then(|(dest, ty, field)| {
                // The closure initializes a record field: the call contract is the
                // field's declared function signature, or -- for an unannotated
                // field -- the constructed instance's substitution entry when the
                // checker seeded the destination local (`Iter { trans: (x) -> .. }`
                // takes `trans`'s per-instance type from the seed).
                self.record_field_fun_params(module, ty, field).or_else(|| {
                    match local_types[dest.index()].as_ref() {
                        Some(Type::Record(n)) => match n.substitution.get(field) {
                            Some(Type::Fun(params, _))
                                if params.iter().all(prepoly_hir::is_fully_known) =>
                            {
                                Some(params.clone())
                            }
                            _ => None,
                        },
                        _ => None,
                    }
                })
            })
        {
            pt
        } else if let Some(annotated) = self.closure_annotated_params(id) {
            // An escaping closure (returned): type it from its own parameter
            // annotations rather than a call/pass site.
            annotated
        } else if let Some(pt) = self.closure_params_from_body(id, &capture_types) {
            // Derived from the closure's OWN body: an indirect call through a
            // typed capture pins the parameter it is called with.
            pt
        } else {
            return Err(format!(
                "closure _{} is neither called nor passed to a function nor fully \
                 annotated; unsupported on the typed backend",
                local.index()
            ));
        };
        // A parameter's own annotation is authoritative, and the use site does
        // not have to agree with it: the checker accepts a `string` argument for
        // a `(s: string?)` parameter, widening it. The body is typed against the
        // annotation, so the closure's `Fun` type -- which the call site coerces
        // its arguments to, and which keys the instance symbol -- has to carry
        // the annotation too. Otherwise a bare `string` reaches a `string?`
        // parameter unwrapped and the body reads the value as a nullable cell.
        // The annotation loses no information the argument type has: it is the
        // very type the instance ends up with either way.
        if let Some(annotations) = self.closure_param_annotations(id) {
            for (pt, annotated) in param_types.iter_mut().zip(annotations) {
                if let Some(t) = annotated {
                    *pt = t;
                }
            }
        }
        let ret = self.instantiate_closure(id, &capture_types, &param_types)?;
        Ok(Some(Type::Fun(param_types, Box::new(ret))))
    }

    /// Recover the parameter types of a closure passed to free function `base` as
    /// argument `idx`: seed the callee's other parameters from the call's
    /// arguments, lightly infer its local types, and read what the closure
    /// parameter is called with inside the callee -- following, when the callee
    /// only FORWARDS the parameter, the call it forwards it into. `None` if not
    /// yet resolvable.
    fn probe_callee_param_types(
        &self,
        base: &str,
        pass_args: &[Operand],
        idx: usize,
        caller_local_types: &[Option<Type>],
    ) -> Result<Option<Vec<Type>>, String> {
        // The hop budget bounds a forwarding CHAIN (`g` hands the closure to `h`
        // hands it to `f`); mutual recursion between forwarders would otherwise
        // never terminate. Real chains are short, so a small budget loses nothing.
        self.probe_callee_param_types_within(base, pass_args, idx, caller_local_types, 8)
    }

    fn probe_callee_param_types_within(
        &self,
        base: &str,
        pass_args: &[Operand],
        idx: usize,
        caller_local_types: &[Option<Type>],
        hops: u32,
    ) -> Result<Option<Vec<Type>>, String> {
        // `base` is the callee name. For a stdlib primitive/array method passed a
        // closure (`arr.map(f)`), its body lives under the class-qualified symbol;
        // for a user METHOD (`iter.map_lazy(f)`) it lives in the method table
        // keyed by the receiver's type symbol. Both are recovered from the
        // receiver argument (the first call operand).
        let (body, callee_module) = match self.by_fn.get(base) {
            Some(f) => (&f.body, f.module.as_slice()),
            None => {
                let recv_ty = pass_args
                    .first()
                    .and_then(|a| self.operand_type(a, caller_local_types).ok().flatten());
                let prim = recv_ty
                    .as_ref()
                    .and_then(|t| t.primitive_class())
                    .and_then(|class| {
                        self.program
                            .primitive_methods
                            .get(&(class.to_string(), base.to_string()))
                    })
                    .and_then(|s| self.by_fn.get(s.as_str()))
                    .map(|f| (&f.body, f.module.as_slice()));
                let user = recv_ty
                    .as_ref()
                    .map(unwrap_nullable)
                    .and_then(|t| match t {
                        Type::Record(n) | Type::Sum(n) => self.program.type_by_id(n.id),
                        _ => None,
                    })
                    .and_then(|info| self.by_method.get(&(info.symbol.as_str(), base)))
                    .map(|m| (&m.body, m.module.as_slice()));
                match prim.or(user) {
                    Some(b) => b,
                    None => return Ok(None),
                }
            }
        };
        let mut seeded: Vec<Option<Type>> = vec![None; body.locals.len()];
        for (i, p) in body.params.iter().enumerate() {
            if i == idx {
                continue;
            }
            if let Some(arg) = pass_args.get(i) {
                seeded[p.index()] = self.operand_type(arg, caller_local_types)?;
            }
        }
        let lt = self.probe_local_types(body, seeded);
        let Some(p_local) = body.params.get(idx) else {
            return Ok(None);
        };
        let indirect = collect_indirect_args(body);
        if let Some(call_sites) = indirect.get(p_local) {
            return self.joined_arg_types(call_sites, &lt);
        }
        // The callee never calls the parameter itself. If it FORWARDS it to
        // another function or method (`fun g(handler) { f(handler) }`), the call
        // contract lives one call further on: recurse into that callee, with the
        // forwarding call's arguments typed by this body's lightly-inferred
        // locals. Without the hop, a merely-forwarding wrapper left the closure
        // with no parameter types at all.
        if hops == 0 {
            return Ok(None);
        }
        let alias = use_aliases(body);
        for block in &body.blocks {
            for stmt in &block.stmts {
                let (MirStmt::Assign(_, rv) | MirStmt::Eval(rv)) = stmt else {
                    continue;
                };
                match rv {
                    Rvalue::Call(Callee::Free(next) | Callee::Method(next), args) => {
                        for (i, a) in args.iter().enumerate() {
                            let Operand::Local(g) = a else { continue };
                            if resolve_alias(&alias, *g) != *p_local {
                                continue;
                            }
                            if let Some(pt) =
                                self.probe_callee_param_types_within(next, args, i, &lt, hops - 1)?
                            {
                                return Ok(Some(pt));
                            }
                        }
                    }
                    // The callee STORES the parameter into a record field
                    // (`register` builds `RequestHandler { handler: handler }`):
                    // the field's declared function type is the call contract, the
                    // same source a closure stored into a literal directly takes
                    // (`record_field_closures`) -- just one call boundary away.
                    Rvalue::Record { ty, fields } | Rvalue::Variant { ty, fields, .. } => {
                        for (fname, op) in fields {
                            let Operand::Local(g) = op else { continue };
                            if resolve_alias(&alias, *g) != *p_local {
                                continue;
                            }
                            if let Some(pt) = self.record_field_fun_params(callee_module, ty, fname)
                            {
                                return Ok(Some(pt));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        Ok(None)
    }

    /// The type of each parameter position across the call sites: one closure
    /// parameter has one type, so the sites' argument types are joined (`null`
    /// at one site and a `P` at another give `P?`).
    ///
    /// A site whose arguments are not all typed yet is skipped rather than
    /// deferring the whole answer, because it may never type on its own: an
    /// argument that is the closure's *own* result (`g(g(v))`) waits on the
    /// return type this very call is needed to infer. `None` only when no site
    /// contributes, which leaves the closure for a later pass. A zero-argument
    /// closure has no positions, so it types immediately.
    fn joined_arg_types(
        &self,
        call_sites: &[Vec<Operand>],
        local_types: &[Option<Type>],
    ) -> Result<Option<Vec<Type>>, String> {
        let mut joined: Vec<Type> = Vec::new();
        let mut any = false;
        for args in call_sites {
            let mut site = Vec::with_capacity(args.len());
            for a in args {
                match self.operand_type(a, local_types)? {
                    Some(t) => site.push(t),
                    None => break,
                }
            }
            if site.len() != args.len() {
                continue;
            }
            any = true;
            for (i, t) in site.into_iter().enumerate() {
                match joined.get_mut(i) {
                    Some(cur) => *cur = merge_return_types(cur, &t),
                    None => joined.push(t),
                }
            }
        }
        if !any && !call_sites.is_empty() {
            return Ok(None);
        }
        Ok(Some(joined))
    }

    /// A lightweight, non-instantiating fixpoint that resolves local types from
    /// simple rvalues (uses, binary ops, field/element loads). Used to probe a
    /// callee body without the side effects of full instantiation.
    fn probe_local_types(&self, body: &MirBody, seeded: Vec<Option<Type>>) -> Vec<Option<Type>> {
        let mut lt = seeded;
        loop {
            let mut changed = false;
            for block in &body.blocks {
                for stmt in &block.stmts {
                    if let MirStmt::Assign(local, rv) = stmt
                        && lt[local.index()].is_none()
                        && let Some(t) = self.probe_rvalue_type(rv, &lt)
                    {
                        lt[local.index()] = Some(t);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        lt
    }

    /// The type of a simple rvalue during a probe (no calls/constructions).
    fn probe_rvalue_type(&self, rv: &Rvalue, lt: &[Option<Type>]) -> Option<Type> {
        match rv {
            Rvalue::Use(op) => self.operand_type(op, lt).ok().flatten(),
            Rvalue::Bin(op, a, _) if is_comparison(*op) => {
                // A comparison's operands must be resolvable for the result bool
                // to be meaningful here.
                self.operand_type(a, lt).ok().flatten()?;
                Some(Type::Bool)
            }
            Rvalue::Bin(_, a, b) => self.binary_operand_type(a, b, lt).ok().flatten(),
            Rvalue::Load(place) => match place.proj.as_slice() {
                [Projection::Field(field)] => {
                    match unwrap_nullable(lt.get(place.local.index())?.as_ref()?) {
                        Type::Record(n) => self.record_field_type(n, field).ok().flatten(),
                        Type::Sum(n) => self.sum_field_type(n, field).ok().flatten(),
                        _ => None,
                    }
                }
                [Projection::Index(_)] => {
                    match unwrap_nullable(lt.get(place.local.index())?.as_ref()?) {
                        Type::Slice(elem) | Type::Array(elem, _) => Some((**elem).clone()),
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Instantiate a closure body for one (capture-types, param-types) tuple
    /// (memoized), returning its return type.
    fn instantiate_closure(
        &mut self,
        id: ClosureId,
        capture_types: &[Type],
        param_types: &[Type],
    ) -> Result<Type, String> {
        let clo = *self
            .by_closure
            .get(&id)
            .ok_or_else(|| format!("unknown closure {}", id.index()))?;
        let sym = closure_symbol(id, capture_types, param_types);
        tracing::debug!(
            closure = id.index(),
            captures = ?capture_types.iter().map(|t| t.display()).collect::<Vec<_>>(),
            params = ?param_types.iter().map(|t| t.display()).collect::<Vec<_>>(),
            declared_captures = self.by_closure.get(&id).map(|c| c.captures.len()),
            "instantiating closure"
        );
        if let Some(inst) = self.instances.get(&sym) {
            return Ok(inst.ret.clone());
        }
        if self.in_progress.contains_key(&sym) {
            return Err("recursive closures are unsupported on the typed backend".into());
        }
        let capture_seed: Vec<(LocalId, Type)> = clo
            .captures
            .iter()
            .copied()
            .zip(capture_types.iter().cloned())
            .collect();
        let stored = self.type_and_store(
            sym,
            &clo.body,
            &clo.module,
            param_types.to_vec(),
            None,
            None,
            None,
            &capture_seed,
            clo.captures.clone(),
            true,
            false,
        )?;
        Ok(self.instances[&stored].ret.clone())
    }
}
