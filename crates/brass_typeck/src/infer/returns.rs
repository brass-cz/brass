//! Reconciling the values that leave one callable body -- its `return`s and
//! its error payloads -- into one type, through the shared value join
//! ([`brass_typesys::join_values`]), and reporting the instantiations whose
//! values have no join.
//!
//! The definitional pass, every per-call-site re-elaboration and
//! monomorphization all reconcile with the same join, so an instance's return
//! type is never decided by which `return` was visited first.
//!
//! The module also settles a self-recursive instantiation's return, and owns
//! the values nothing reads: an expression whose value is discarded (a `!`
//! there only propagates), a statement-position `if`/`if let`/`match` (no
//! value, its arms not joined), and the Ok payload of a call that only
//! returns errors (never readable).

use super::*;
use brass_typesys::{JoinConflict, JoinOperand, NumericLiteral, join_values};

/// The call that created the instantiation being re-elaborated, carried while
/// its body's returns are reconciled so a conflict that only this
/// instantiation has is reported with the call that caused it.
#[derive(Clone, Debug)]
pub(super) struct InstanceSite {
    /// The callable as the user names it (`pick`, `Box.pick`).
    pub(super) callee: String,
    /// The call site that instantiated it.
    pub(super) call_span: Span,
    /// The instantiation's identity -- the callable and its resolved
    /// receiver/argument types -- so each instantiation is reported once
    /// however many call sites (or re-elaborations) reach it.
    pub(super) key: (String, Vec<Type>),
}

impl Checker<'_> {
    /// Include a callable's end in its return join: a reachable end contributes
    /// `void`, while a body with no returns and an unreachable end is `never`.
    /// Called once the body's inputs are known, so static branch choices are
    /// the choices of this instance.
    pub(super) fn collect_body_end(
        &mut self,
        body: &Block,
        diverges: bool,
        collected: &mut Vec<(Type, Span)>,
    ) {
        let span = Span::new(body.span.hi.saturating_sub(1), body.span.hi);
        if diverges {
            if collected.is_empty() {
                collected.push((Type::Never, span));
            }
        } else if !collected.is_empty() {
            collected.push((Type::Void, span));
            // Forwarded Results join by their success payload; an error-only
            // return contributes no success value to conflict with fallthrough.
            self.report_instance_return_conflict(collected, true);
        }
    }

    /// Remember that the value collected for a `return` at `span` is the
    /// literal `expr` (when it is one), so the join can let it adapt. Spans are
    /// unique per source position and the literal is syntactic, so the entry
    /// stays valid across every pass that collects the same `return`.
    pub(super) fn note_return_literal(&mut self, span: Span, expr: &Expr) {
        if let Some(literal) = NumericLiteral::of_expr(expr) {
            self.return_literals.insert(span, literal);
        }
    }

    /// The join of collected `(type, span)` values when every type is fully
    /// known, else `None` -- an open set (the definitional pass of a generic
    /// body) is reconciled leniently by the caller, since the types its open
    /// variables stand for are only decided per instantiation.
    pub(super) fn join_known_values(
        &self,
        values: &[(Type, Span)],
    ) -> Option<Result<Option<Type>, JoinConflict>> {
        let resolved: Vec<Type> = values.iter().map(|(ty, _)| self.resolve(ty)).collect();
        if !resolved.iter().all(brass_hir::is_fully_known) {
            return None;
        }
        let operands: Vec<JoinOperand> = resolved
            .into_iter()
            .zip(values)
            .map(|(ty, (_, span))| JoinOperand {
                ty,
                literal: self.return_literals.get(span).copied(),
            })
            .collect();
        Some(join_values(self.program, &operands))
    }

    /// Report a conflict found while joining `values` (`what` is "return
    /// types" or "error payloads"). Inside an instantiation's re-elaboration
    /// (see [`Self::conflict_site`]) the message names the instantiation and
    /// the call that created it; otherwise it is the definition's own
    /// conflict.
    pub(super) fn report_join_conflict(
        &mut self,
        what: &str,
        values: &[(Type, Span)],
        conflict: JoinConflict,
    ) {
        let first = self.resolve(&values[conflict.first].0);
        let second = self.resolve(&values[conflict.second].0);
        let message = match &self.conflict_site {
            Some(site) => format!(
                "incompatible {what} `{}` and `{}` in this instantiation of `{}` \
                 (instantiated at {})",
                first.display(),
                second.display(),
                site.callee,
                crate::source_location(site.call_span),
            ),
            None => format!(
                "incompatible {what}: `{}` and `{}`",
                first.display(),
                second.display()
            ),
        };
        self.report_conflict_once(what, message, values[conflict.second].1);
    }

    /// Report a conflict among a body's `what` ("return types" or "error
    /// payloads") at `span`, unless one is already reported at that site. A
    /// body whose inputs are all known conflicts identically in its definition
    /// and in each instantiation's re-elaboration -- the one at the returned
    /// value, the other at its `return` statement, so a site is any span that
    /// contains the other; the first report stands for it.
    pub(super) fn report_conflict_once(&mut self, what: &str, message: String, span: Span) {
        let prefix = format!("incompatible {what}");
        let same_site = |other: Span| {
            (other.lo <= span.lo && span.hi <= other.hi)
                || (span.lo <= other.lo && other.hi <= span.hi)
        };
        if self
            .errors
            .iter()
            .any(|e| same_site(e.span) && e.message.starts_with(&prefix))
        {
            return;
        }
        self.errors.push(TypeError { message, span });
    }

    /// Record the rebuilds a joined return type needs: when the returns of a
    /// body join at a parent sum because some of them are a declared subtype
    /// of it, each subtype value is rebuilt as the parent where it is
    /// returned (the back ends never reinterpret one sum's layout as
    /// another's), and each value already of the parent is recorded as
    /// needing none -- so a generic body whose instantiations disagree at the
    /// same `return` is rejected rather than rebuilt for all of them.
    pub(super) fn record_return_rebuilds(&mut self, collected: &[(Type, Span)], joined: &Type) {
        let joined = self.resolve(joined);
        let target = match &joined {
            Type::Nullable(inner) => (**inner).clone(),
            other => other.clone(),
        };
        let Type::Sum(parent) = &target else {
            return;
        };
        let subtype_of_parent = |ty: &Type| {
            matches!(ty, Type::Sum(n) if n.id != parent.id
                && crate::structural::declares_sum_parent(self.program, n.id, parent.id, 0))
        };
        let resolved: Vec<(Type, Span)> = collected
            .iter()
            .map(|(ty, span)| (self.resolve(ty), *span))
            .collect();
        if !resolved.iter().any(|(ty, _)| subtype_of_parent(ty)) {
            return;
        }
        for (ty, span) in &resolved {
            let Some(value_span) = self.return_value_spans.get(span).copied() else {
                continue;
            };
            if subtype_of_parent(ty) {
                self.record_sum_view(ty, &target, value_span);
            } else if matches!(ty, Type::Sum(n) if n.id == parent.id) {
                self.record_sum_view_identity(value_span);
            }
        }
    }

    /// The return a recursive call inside the instantiation `key` at
    /// `arg_types` reads while [`Self::settle_recursive_return`] re-elaborates
    /// that instantiation, if it is the one being settled.
    pub(super) fn recursion_assumption(&self, key: &str, arg_types: &[Type]) -> Option<Type> {
        let (args, ret) = self.recursion_assumptions.get(key)?;
        (args.len() == arg_types.len()
            && args
                .iter()
                .zip(arg_types)
                .all(|(assumed, arg)| *assumed == self.resolve(arg)))
        .then(|| ret.clone())
    }

    /// Settle the return of an instantiation whose body called itself.
    ///
    /// A recursive call reads the callable's shared definitional return (the
    /// instantiation is still being elaborated), which approximates what one
    /// instantiation returns: a generic `sum(xs, i)` whose `return 0` is
    /// `int32` until a float array's instantiation joins it with the
    /// recursive sum to `float64`. When that approximation is a concrete type
    /// that does not even unify with the instantiation's real return, the
    /// body is elaborated again with its recursive calls reading the real
    /// return, until the two agree -- so every type recorded inside (the
    /// seeds the back ends type the body with) describes this instantiation.
    /// Returns the settled return, and the return the last re-elaboration's
    /// recursive calls read when there was one.
    pub(super) fn settle_recursive_return(
        &mut self,
        key: &str,
        arg_types: &[Type],
        fallback: &Type,
        mut ret: Type,
        mut elaborate: impl FnMut(&mut Self) -> Type,
    ) -> (Type, Option<Type>) {
        // Each round re-reads a strictly different concrete return; a chain
        // that keeps changing is left at its last answer.
        const MAX_ROUNDS: usize = 4;
        let args: Vec<Type> = arg_types.iter().map(|ty| self.resolve(ty)).collect();
        let mut assumed = self.resolve(fallback);
        let mut read = None;
        for _ in 0..MAX_ROUNDS {
            let current = self.resolve(&ret);
            if !brass_hir::is_fully_known(&assumed)
                || !brass_hir::is_fully_known(&current)
                || self.can_unify(&assumed, &current)
            {
                break;
            }
            self.recursion_assumptions
                .insert(key.to_string(), (args.clone(), current.clone()));
            ret = elaborate(self);
            self.recursion_assumptions.remove(key);
            read = Some(current.clone());
            assumed = current;
        }
        (ret, read)
    }

    /// The site to report an instantiation's conflicts against: present only
    /// when every input of the instantiation is fully known (a conflict among
    /// open types is the definitional pass's business) and this instantiation
    /// has not been reported yet.
    pub(super) fn instance_site(
        &self,
        callee: String,
        call_span: Span,
        callable: String,
        inputs: impl IntoIterator<Item = Type>,
    ) -> Option<InstanceSite> {
        let inputs: Vec<Type> = inputs.into_iter().map(|ty| self.resolve(&ty)).collect();
        if !inputs.iter().all(brass_hir::is_fully_known) {
            return None;
        }
        let key = (callable, inputs);
        (!self.reported_instances.contains(&key)).then_some(InstanceSite {
            callee,
            call_span,
            key,
        })
    }

    /// Report the conflict, if any, among an instantiation's returns as the
    /// full check collected them: the values its live paths hand back (a
    /// pruned type-test arm or statically dead code contributes none). In a
    /// fallible body the bare values are Ok payloads and a forwarded `Result`
    /// is compared by its Ok payload; the error-only `Result`s that
    /// `return error(..)` produces carry no Ok value and are left out.
    pub(super) fn report_instance_return_conflict(
        &mut self,
        collected: &[(Type, Span)],
        fallible: bool,
    ) {
        let values: Vec<(Type, Span)> = collected
            .iter()
            .filter_map(|(ty, span)| {
                let resolved = self.resolve(ty);
                if !fallible {
                    return Some((resolved, *span));
                }
                match resolved.result_payloads() {
                    Some((ok, _)) if ok.is_unknown() => None,
                    Some((ok, _)) => Some((self.resolve(ok), *span)),
                    None => Some((resolved, *span)),
                }
            })
            .collect();
        if let Some(Err(conflict)) = self.join_known_values(&values) {
            self.report_join_conflict("return types", &values, conflict);
        }
    }
}

impl Checker<'_> {
    /// Whether `ty` is still the Ok payload of a call that can only fail (an
    /// instantiation whose every live path returns an error): a type no value
    /// ever has.
    fn is_error_only_ok(&self, ty: &Type) -> bool {
        matches!(
            self.resolve(ty),
            Type::Unknown(id) if self.solver.kind_of(id) == Some(InferenceVarKind::UninhabitedOk)
        )
    }

    /// Reject reading `name`, a binding of the Ok payload of a call that only
    /// returns errors (`Ok { value } => println(value)` on such a Result):
    /// the arm may be written, but the payload never exists. `typeof(..)`
    /// reads only the type and stays allowed.
    pub(super) fn reject_error_only_binding_read(&mut self, name: &str, ty: &Type, span: Span) {
        if self.type_only_read || !self.is_error_only_ok(ty) {
            return;
        }
        self.errors.push(TypeError {
            message: format!(
                "`{name}` is the Ok payload of a call that only returns errors: it never holds \
                 a value, so it cannot be read"
            ),
            span,
        });
    }

    /// Reject a `!` whose Ok payload comes from a call that only returns
    /// errors when its value is used: the `!` always propagates, so there is
    /// no value. As a statement, a returned value (which hands the same
    /// uninhabited payload on) or a `let` initializer (whose binding carries
    /// it, and is rejected when read) it only propagates and is allowed.
    pub(super) fn reject_error_only_unwrap(&mut self, ok: &Type, span: Span) {
        if self.type_only_read
            || self.discarded_values.contains(&span)
            || !self.is_error_only_ok(ok)
        {
            return;
        }
        self.errors.push(TypeError {
            message: "this `!` unwraps the Ok payload of a call that only returns errors: it \
                      always propagates, so it has no value to use (use it as a statement, or \
                      `match` the Result)"
                .to_string(),
            span,
        });
    }

    /// Check `e`, whose value is discarded (a statement, or a returned value
    /// handed on whole), so a `!` in its value positions only propagates.
    pub(super) fn check_discarded_expr(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        let mut spans = Vec::new();
        crate::walk::discarded_value_spans(e, &mut spans);
        let added: Vec<Span> = spans
            .into_iter()
            .filter(|span| self.discarded_values.insert(*span))
            .collect();
        let ty = self.check_expr(e, scopes);
        for span in added {
            self.discarded_values.remove(&span);
        }
        ty
    }

    /// Check the expression statement `e` (not the trailing value of a block
    /// in expression position): its value is discarded, and an
    /// `if`/`if let`/`match` there -- or in the trailing position of one of
    /// its arms -- yields no value, so its arms are not joined (see
    /// [`Self::statement_branch_type`]).
    pub(super) fn check_statement_expr(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        let added = self.mark_statement_values(e);
        let ty = self.check_discarded_expr(e, scopes);
        for span in added {
            self.statement_values.remove(&span);
        }
        ty
    }

    /// Check a closure's block body `body` (the `Expr::Block` holding
    /// `block`). The closure yields only what it `return`s, so the trailing
    /// expression is a statement like every other one -- its value discarded,
    /// its branches not joined -- as MIR lowering treats it.
    pub(super) fn check_closure_block_body(
        &mut self,
        body: &Expr,
        block: &Block,
        scopes: &mut ScopeStack,
    ) -> Type {
        let Some(Stmt::Expr(tail)) = block.stmts.last() else {
            return self.check_expr(body, scopes);
        };
        let statement = self.mark_statement_values(tail);
        let mut spans = Vec::new();
        crate::walk::discarded_value_spans(tail, &mut spans);
        let discarded: Vec<Span> = spans
            .into_iter()
            .filter(|span| self.discarded_values.insert(*span))
            .collect();
        let ty = self.check_expr(body, scopes);
        for span in discarded {
            self.discarded_values.remove(&span);
        }
        for span in statement {
            self.statement_values.remove(&span);
        }
        ty
    }

    /// Mark the statement `e` and its arms' trailing expressions as values
    /// nothing reads (see `Checker::statement_values`), returning the spans
    /// newly marked so the caller unmarks exactly those afterwards.
    fn mark_statement_values(&mut self, e: &Expr) -> Vec<Span> {
        let mut spans = Vec::new();
        crate::walk::discarded_value_spans(e, &mut spans);
        spans
            .into_iter()
            .filter(|span| self.statement_values.insert(*span))
            .collect()
    }

    /// The type of the branching expression at `span` when it stands in
    /// statement position: `None` in value position (the caller joins the
    /// branches). As a statement it has no value, whatever its arms leave as
    /// their trailing values: `void`, or `never` when every arm diverges, so
    /// the enclosing block still knows the statement always leaves.
    pub(super) fn statement_branch_type<'t>(
        &self,
        span: Span,
        branches: impl IntoIterator<Item = &'t Type>,
    ) -> Option<Type> {
        if !self.statement_values.contains(&span) {
            return None;
        }
        let diverges = branches
            .into_iter()
            .all(|ty| matches!(self.resolve(ty), Type::Never));
        Some(if diverges { Type::Never } else { Type::Void })
    }
}
