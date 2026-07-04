//! Compile-time expansion of `for f in fields(x)` loops.
//!
//! `fields(x)` is a compile-time construct, legal only as a `for` iterable:
//! the loop is unrolled during checking and lowering, once per field of `x`'s
//! record type, in declaration order. In each unrolled copy the loop variable
//! decays to the field's NAME as a string constant everywhere except the
//! indexing form `v[f]`, which becomes the field projection `v.<name>`.
//!
//! Both the checker (which type-checks each copy) and MIR lowering (which
//! emits each copy) run the same transform, so no side channel needs to carry
//! per-copy types. Every span in a copy is shifted by a per-iteration delta so
//! span-keyed sidecars (`expr_types`, literal kinds) stay distinct across
//! copies; a shifted span is mapped back to its source position with
//! [`unshift_span`] when it surfaces in a diagnostic.

use prepoly_lexer::Span;
use prepoly_parser::ast::*;

/// The per-iteration span-shift unit. Real source offsets stay below this, so
/// `offset % SPAN_SHIFT_UNIT` recovers the source position no matter how many
/// nested expansions shifted it. Sources are capped at 16 MiB by construction
/// (far above any real module) and the total shift stays within a 32-bit
/// usize for the wasm build as long as nested unrolls stay below 256 copies.
pub const SPAN_SHIFT_UNIT: usize = 1 << 24;

/// The `(loop var, fields(..) argument)` of a fields-loop statement, if `stmt`
/// is one. Recognizes `for v in fields(x)` and `for v in fields(x)!` (the `!`
/// marks the arm-killing bail-out once `fields` can fail per instance).
pub fn fields_loop_target(stmt: &Stmt) -> Option<(&str, &Expr, &Block)> {
    let Stmt::For {
        var, iter, body, ..
    } = stmt
    else {
        return None;
    };
    let call = match iter {
        Expr::ErrorProp(inner, _) => inner,
        other => other,
    };
    let Expr::Call(callee, args, _) = call else {
        return None;
    };
    if !matches!(&**callee, Expr::Ident(name, _) if name == "fields") {
        return None;
    }
    let [arg] = args.as_slice() else { return None };
    Some((var, &arg.expr, body))
}

/// Whether a return annotation is the keyed form `-> infer!`: the method's
/// result type is fixed per CALL SITE by the caller's expectation, and its
/// body is elaborated (and lowered) once per requested key. Only the fallible
/// form is keyed -- viability folds need the error channel.
pub fn keyed_return(ret: Option<&TypeExpr>) -> bool {
    matches!(ret, Some(TypeExpr::Fallible(inner, _))
        if matches!(&**inner, TypeExpr::Named(n, _) if n == "infer"))
}

/// Map a possibly-shifted span offset back to its source position.
pub fn unshift_span(span: Span) -> Span {
    Span::new(span.lo % SPAN_SHIFT_UNIT, span.hi % SPAN_SHIFT_UNIT)
}

/// One unrolled copy of a fields-loop body: the loop variable `var` decays to
/// the string constant `field` except in `v[var]`, which becomes `v.<field>`;
/// every span is shifted by `iteration + 1` shift units.
pub fn expand_fields_body(body: &Block, var: &str, field: &str, iteration: usize) -> Block {
    let cx = Expander {
        var,
        field,
        delta: (iteration + 1) * SPAN_SHIFT_UNIT,
    };
    cx.block(body)
}

struct Expander<'a> {
    var: &'a str,
    field: &'a str,
    delta: usize,
}

impl Expander<'_> {
    fn span(&self, s: Span) -> Span {
        Span::new(s.lo + self.delta, s.hi + self.delta)
    }

    fn block(&self, b: &Block) -> Block {
        Block {
            stmts: b.stmts.iter().map(|s| self.stmt(s)).collect(),
            span: self.span(b.span),
        }
    }

    fn stmt(&self, s: &Stmt) -> Stmt {
        match s {
            Stmt::Let {
                pat,
                ty,
                value,
                is_const,
                span,
            } => Stmt::Let {
                pat: self.pattern(pat),
                ty: ty.as_ref().map(|t| self.type_expr(t)),
                value: value.as_ref().map(|v| self.expr(v)),
                is_const: *is_const,
                span: self.span(*span),
            },
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => Stmt::Assign {
                target: self.expr(target),
                op: *op,
                value: self.expr(value),
                span: self.span(*span),
            },
            Stmt::Expr(e) => Stmt::Expr(self.expr(e)),
            Stmt::While { cond, body, span } => Stmt::While {
                cond: self.expr(cond),
                body: self.block(body),
                span: self.span(*span),
            },
            Stmt::For {
                var,
                iter,
                body,
                span,
            } => Stmt::For {
                var: var.clone(),
                iter: self.expr(iter),
                body: self.block(body),
                span: self.span(*span),
            },
            Stmt::Return(e, span) => {
                Stmt::Return(e.as_ref().map(|e| self.expr(e)), self.span(*span))
            }
            Stmt::Break(span) => Stmt::Break(self.span(*span)),
            Stmt::Continue(span) => Stmt::Continue(self.span(*span)),
        }
    }

    fn expr(&self, e: &Expr) -> Expr {
        match e {
            // The descriptor decays to the field name as a string constant...
            Expr::Ident(name, span) if name == self.var => {
                Expr::Str(vec![StrSeg::Lit(self.field.to_string())], self.span(*span))
            }
            // ...except as an index, where it projects the field.
            Expr::Index(base, idx, span) if matches!(&**idx, Expr::Ident(name, _) if name == self.var) => {
                Expr::Field(
                    Box::new(self.expr(base)),
                    self.field.to_string(),
                    self.span(*span),
                )
            }
            Expr::Int(v, span) => Expr::Int(*v, self.span(*span)),
            Expr::Float(v, span) => Expr::Float(*v, self.span(*span)),
            Expr::Bool(v, span) => Expr::Bool(*v, self.span(*span)),
            Expr::Null(span) => Expr::Null(self.span(*span)),
            Expr::Ident(name, span) => Expr::Ident(name.clone(), self.span(*span)),
            Expr::SelfExpr(span) => Expr::SelfExpr(self.span(*span)),
            Expr::Str(segs, span) => Expr::Str(
                segs.iter()
                    .map(|seg| match seg {
                        StrSeg::Lit(s) => StrSeg::Lit(s.clone()),
                        StrSeg::Expr(e) => StrSeg::Expr(Box::new(self.expr(e))),
                    })
                    .collect(),
                self.span(*span),
            ),
            Expr::Unary(op, inner, span) => {
                Expr::Unary(*op, Box::new(self.expr(inner)), self.span(*span))
            }
            Expr::Binary(op, l, r, span) => Expr::Binary(
                *op,
                Box::new(self.expr(l)),
                Box::new(self.expr(r)),
                self.span(*span),
            ),
            Expr::Call(callee, args, span) => Expr::Call(
                Box::new(self.expr(callee)),
                args.iter()
                    .map(|a| Arg {
                        expr: self.expr(&a.expr),
                    })
                    .collect(),
                self.span(*span),
            ),
            Expr::Field(base, name, span) => {
                Expr::Field(Box::new(self.expr(base)), name.clone(), self.span(*span))
            }
            Expr::Index(base, idx, span) => Expr::Index(
                Box::new(self.expr(base)),
                Box::new(self.expr(idx)),
                self.span(*span),
            ),
            Expr::ErrorProp(inner, span) => {
                Expr::ErrorProp(Box::new(self.expr(inner)), self.span(*span))
            }
            Expr::Closure(params, body, span) => {
                Expr::Closure(params.clone(), Box::new(self.expr(body)), self.span(*span))
            }
            Expr::Array(es, span) => {
                Expr::Array(es.iter().map(|e| self.expr(e)).collect(), self.span(*span))
            }
            Expr::Range(lo, hi, span) => Expr::Range(
                Box::new(self.expr(lo)),
                Box::new(self.expr(hi)),
                self.span(*span),
            ),
            Expr::TypeLit(name, fields, span) => Expr::TypeLit(
                name.clone(),
                fields
                    .iter()
                    .map(|(n, e)| (n.clone(), self.expr(e)))
                    .collect(),
                self.span(*span),
            ),
            Expr::VariantLit(ty, variant, fields, span) => Expr::VariantLit(
                ty.clone(),
                variant.clone(),
                fields
                    .iter()
                    .map(|(n, e)| (n.clone(), self.expr(e)))
                    .collect(),
                self.span(*span),
            ),
            Expr::If(cond, then, els, span) => Expr::If(
                Box::new(self.expr(cond)),
                self.block(then),
                els.as_ref().map(|e| Box::new(self.expr(e))),
                self.span(*span),
            ),
            Expr::IfLet(pat, scrut, then, els, span) => Expr::IfLet(
                self.pattern(pat),
                Box::new(self.expr(scrut)),
                self.block(then),
                els.as_ref().map(|e| Box::new(self.expr(e))),
                self.span(*span),
            ),
            Expr::Match(scrut, arms, span) => Expr::Match(
                Box::new(self.expr(scrut)),
                arms.iter()
                    .map(|arm| MatchArm {
                        pattern: self.pattern(&arm.pattern),
                        body: self.expr(&arm.body),
                        span: self.span(arm.span),
                    })
                    .collect(),
                self.span(*span),
            ),
            Expr::Block(b, span) => Expr::Block(self.block(b), self.span(*span)),
        }
    }

    fn pattern(&self, p: &Pattern) -> Pattern {
        match p {
            Pattern::Wildcard(span) => Pattern::Wildcard(self.span(*span)),
            Pattern::Binding(name, span) => Pattern::Binding(name.clone(), self.span(*span)),
            Pattern::Literal(e, span) => Pattern::Literal(Box::new(self.expr(e)), self.span(*span)),
            Pattern::Record(name, fields, span) => Pattern::Record(
                name.clone(),
                fields
                    .iter()
                    .map(|f| FieldPat {
                        name: f.name.clone(),
                        pat: f.pat.as_ref().map(|p| self.pattern(p)),
                        span: self.span(f.span),
                    })
                    .collect(),
                self.span(*span),
            ),
            Pattern::Array(ps, span) => Pattern::Array(
                ps.iter().map(|p| self.pattern(p)).collect(),
                self.span(*span),
            ),
        }
    }

    fn type_expr(&self, t: &TypeExpr) -> TypeExpr {
        match t {
            TypeExpr::Named(name, span) => TypeExpr::Named(name.clone(), self.span(*span)),
            TypeExpr::Array(inner, len, span) => {
                TypeExpr::Array(Box::new(self.type_expr(inner)), *len, self.span(*span))
            }
            TypeExpr::Fun(params, ret, span) => TypeExpr::Fun(
                params.iter().map(|p| self.type_expr(p)).collect(),
                Box::new(self.type_expr(ret)),
                self.span(*span),
            ),
            TypeExpr::Nullable(inner, span) => {
                TypeExpr::Nullable(Box::new(self.type_expr(inner)), self.span(*span))
            }
            TypeExpr::Fallible(inner, span) => {
                TypeExpr::Fallible(Box::new(self.type_expr(inner)), self.span(*span))
            }
            TypeExpr::Tuple(elems, span) => TypeExpr::Tuple(
                elems.iter().map(|t| self.type_expr(t)).collect(),
                self.span(*span),
            ),
            TypeExpr::Anonymous(fields, span) => TypeExpr::Anonymous(
                fields
                    .iter()
                    .map(|(n, t)| (n.clone(), self.type_expr(t)))
                    .collect(),
                self.span(*span),
            ),
            TypeExpr::Mut(inner, span) => {
                TypeExpr::Mut(Box::new(self.type_expr(inner)), self.span(*span))
            }
            TypeExpr::Ref(inner, span) => {
                TypeExpr::Ref(Box::new(self.type_expr(inner)), self.span(*span))
            }
            TypeExpr::TypeOf(e, span) => TypeExpr::TypeOf(Box::new(self.expr(e)), self.span(*span)),
        }
    }
}
