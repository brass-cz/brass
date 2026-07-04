//! Per-key specialization of reflective decoder methods (`fun T.m(self) ->
//! infer!`).
//!
//! A keyed method's body is written generically over an unknown target type
//! (`infer`); each call site fixes the target from the caller's expectation
//! (`let u: User = j.into()!` fixes `User`). Because prepoly monomorphizes to
//! fully concrete code, the generic body is turned into one CONCRETE method per
//! requested key here, before ordinary type checking and lowering see it. The
//! specializer:
//!
//! - substitutes every `infer` annotation with the key (`let ret: infer` ->
//!   `let ret: User`, the return `infer!` -> `User!`);
//! - unrolls a `for f in fields(ret)` loop over the (now concrete) key, so each
//!   field is assigned directly and the recursive `x.into()` inside becomes a
//!   call to the FIELD's own specialization (`x.into__<fieldtype>()`), which is
//!   in turn scheduled for specialization;
//! - resolves `infer.from(x)` by the from/parse partition
//!   (`crate::infer_from`): an identity, a named conversion, or -- when
//!   no conversion exists -- a runtime error (the arm is not viable for this
//!   key, e.g. a JSON number decoded as a record);
//! - turns `return null` into a runtime error when the key is not nullable.
//!
//! The result is a set of concrete methods keyed by mangled name; the driver
//! injects them, rewrites the keyed call sites to their specializations, and
//! runs the normal pipeline over the fully concrete program.

use std::collections::HashMap;

use prepoly_parser::ast::*;

use prepoly_hir::{Program, Type, TypeKind};

/// The width of each specialization's span band, in `SPAN_SHIFT_UNIT`s. Wider
/// than any record's field count, so a fields-loop unroll inside one
/// specialization (which shifts each copy by `(i+1) * SPAN_SHIFT_UNIT`) stays
/// within that specialization's band.
const SPAN_BAND: usize = 4096;

/// A pure span-shift of a block by `delta` (a multiple of `SPAN_SHIFT_UNIT`):
/// reuses the fields-loop expander with a variable that matches nothing, so it
/// rewrites spans without substituting anything.
fn shift_spans(b: &Block, delta: usize) -> Block {
    debug_assert!(delta.is_multiple_of(prepoly_hir::SPAN_SHIFT_UNIT));
    let iteration = delta / prepoly_hir::SPAN_SHIFT_UNIT;
    // `expand_fields_body` shifts by `(iteration + 1) * SPAN_SHIFT_UNIT`; the
    // sentinel variable name cannot appear in source, so no ident is rewritten.
    prepoly_hir::expand_fields_body(b, "\u{0}shift", "", iteration.saturating_sub(1))
}

/// A requested specialization: method `method` on receiver type `recv`,
/// targeting result type `key`.
#[derive(Clone)]
pub struct KeyedNeed {
    pub recv: String,
    pub method: String,
    pub key: Type,
}

/// The mangled method name of a specialization (`into__int64`,
/// `into__rec5x2_...`). Deterministic and collision-free (see
/// [`prepoly_hir::type_key`]); a valid identifier, so the injected method parses and
/// dispatches like any other.
pub fn mangled_name(method: &str, key: &Type) -> String {
    format!("{method}__{}", prepoly_hir::type_key(key))
}

/// Generate every concrete method reachable from `roots` (transitively: a
/// record key pulls in a specialization per field type). Returns each as
/// `(defining module, FunDecl)` for the driver to inject, or an error naming a
/// construct the specializer cannot handle.
pub fn specialize_all(
    program: &Program,
    roots: &[KeyedNeed],
) -> Result<Vec<(Vec<String>, FunDecl)>, String> {
    let mut out = Vec::new();
    let mut done: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut work: Vec<KeyedNeed> = roots.to_vec();
    // Bounded by the distinct (recv, method, key) triples the program's type
    // graph can reach -- finite -- so the worklist drains.
    while let Some(need) = work.pop() {
        let sym = format!(
            "{}.{}:{}",
            need.recv,
            need.method,
            prepoly_hir::type_key(&need.key)
        );
        if !done.insert(sym) {
            continue;
        }
        let (mut decl, module) = specialize_one(program, &need, &mut work)?;
        // Every specialization is a clone of one template, so their statements
        // share the template's source spans. Span-keyed inference state (literal
        // kinds, expr types) would then collide across specializations. Shift
        // each into its own span band, wide enough to also clear the fields-loop
        // unroll's own per-field shifts inside it; a diagnostic maps back with
        // `unshift_span` (`% SPAN_SHIFT_UNIT`).
        let base = (out.len() + 1) * SPAN_BAND * prepoly_hir::SPAN_SHIFT_UNIT;
        decl.body = shift_spans(&decl.body, base);
        out.push((module, decl));
    }
    Ok(out)
}

fn specialize_one(
    program: &Program,
    need: &KeyedNeed,
    work: &mut Vec<KeyedNeed>,
) -> Result<(FunDecl, Vec<String>), String> {
    let info = program
        .types
        .values()
        .find(|i| i.name == need.recv)
        .ok_or_else(|| format!("unknown receiver type `{}`", need.recv))?;
    let method = match &info.kind {
        TypeKind::Record { methods, .. } => methods.get(&need.method),
        TypeKind::Sum { variants } => variants.iter().find_map(|v| v.methods.get(&need.method)),
    }
    .ok_or_else(|| format!("`{}` has no method `{}`", need.recv, need.method))?;
    let src = &method.decl;
    let mut cx = Specializer {
        program,
        recv: &need.recv,
        method: &need.method,
        key: &need.key,
        scrutinee: info.type_ref(),
        work,
    };
    let body = cx.block(&src.body.clone().ok_or("keyed method has no body")?);
    let decl = FunDecl {
        name: mangled_name(&need.method, &need.key),
        recv: Some(TypeExpr::Named(need.recv.clone(), src.span)),
        params: src.params.clone(),
        // The concrete result: `key!` (a fallible decode).
        ret: Some(TypeExpr::Fallible(
            Box::new(type_to_expr(&need.key, src.span)),
            src.span,
        )),
        body,
        span: src.span,
    };
    Ok((decl, info.module.clone()))
}

struct Specializer<'a> {
    program: &'a Program,
    recv: &'a str,
    method: &'a str,
    key: &'a Type,
    /// The type of `self` (the receiver), the scrutinee of the top match.
    scrutinee: Type,
    work: &'a mut Vec<KeyedNeed>,
}

/// Per-arm variable-to-type bindings (a match pattern binds variant fields).
type Bindings = HashMap<String, Type>;

impl Specializer<'_> {
    fn block(&mut self, b: &Block) -> Block {
        Block {
            stmts: b
                .stmts
                .iter()
                .flat_map(|s| self.stmt(s, &HashMap::new()))
                .collect(),
            span: b.span,
        }
    }

    fn block_in(&mut self, b: &Block, binds: &Bindings) -> Block {
        Block {
            stmts: b.stmts.iter().flat_map(|s| self.stmt(s, binds)).collect(),
            span: b.span,
        }
    }

    fn stmt(&mut self, s: &Stmt, binds: &Bindings) -> Vec<Stmt> {
        match s {
            // `let ret: infer` -> `let ret: <key>`; other lets keep their (infer-
            // substituted) annotation.
            Stmt::Let {
                pat,
                ty,
                value,
                is_const,
                span,
            } => vec![Stmt::Let {
                pat: pat.clone(),
                ty: ty.as_ref().map(|t| self.subst_type(t)),
                value: value.as_ref().map(|v| self.expr(v, binds)),
                is_const: *is_const,
                span: *span,
            }],
            // `for f in fields(ret)`: unroll over the key's fields (the key is
            // the type of `ret`). A non-record key cannot iterate -- the arm is
            // not viable, so the whole loop is dropped and a later `return ret`
            // is unreachable; but a non-record key only reaches here in an arm
            // that also folds elsewhere, so this stays a faithful unroll.
            Stmt::For {
                var,
                iter,
                body,
                span,
            } if is_fields_over(iter, "ret") => {
                // A non-record key cannot iterate fields: the whole arm is not
                // viable, so fold it to a runtime decode error. The subsequent
                // `return ret` is then unreachable.
                let Type::Record(n) = self.key else {
                    return vec![self.error_return(*span)];
                };
                let Some(info) = self.program.type_by_id(n.id) else {
                    return vec![self.error_return(*span)];
                };
                let TypeKind::Record { fields, .. } = &info.kind else {
                    return vec![self.error_return(*span)];
                };
                let mut out = Vec::new();
                for (i, f) in fields.iter().enumerate() {
                    let fty = f.resolved_ty.clone().unwrap_or(Type::Void);
                    // Reuse the fields-loop expansion (field name decay + v[f]
                    // projection), then rewrite the recursive keyed call to the
                    // field's specialization.
                    let expanded = prepoly_hir::expand_fields_body(body, var, &f.name, i);
                    for st in &expanded.stmts {
                        out.push(self.rewrite_recursive(st, &fty, binds));
                    }
                }
                out
            }
            Stmt::Return(Some(e), span) => {
                // `return null` at a non-nullable key is not viable: emit a
                // runtime decode error instead.
                if matches!(e, Expr::Null(_)) && !matches!(self.key, Type::Nullable(_)) {
                    return vec![self.error_return(*span)];
                }
                vec![Stmt::Return(Some(self.expr(e, binds)), *span)]
            }
            Stmt::Return(None, span) => vec![Stmt::Return(None, *span)],
            Stmt::Expr(e) => vec![Stmt::Expr(self.expr(e, binds))],
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => vec![Stmt::Assign {
                target: self.expr(target, binds),
                op: *op,
                value: self.expr(value, binds),
                span: *span,
            }],
            Stmt::While { cond, body, span } => vec![Stmt::While {
                cond: self.expr(cond, binds),
                body: self.block_in(body, binds),
                span: *span,
            }],
            Stmt::For {
                var,
                iter,
                body,
                span,
            } => vec![Stmt::For {
                var: var.clone(),
                iter: self.expr(iter, binds),
                body: self.block_in(body, binds),
                span: *span,
            }],
            Stmt::Break(s) => vec![Stmt::Break(*s)],
            Stmt::Continue(s) => vec![Stmt::Continue(*s)],
        }
    }

    /// Rewrite the recursive keyed call `x.into()` (the method being
    /// specialized) inside a field assignment to the field's own
    /// specialization `x.into__<fty>()`, and schedule that specialization.
    fn rewrite_recursive(&mut self, s: &Stmt, fty: &Type, binds: &Bindings) -> Stmt {
        // Register the field's specialization need.
        self.work.push(KeyedNeed {
            recv: self.recv.to_string(),
            method: self.method.to_string(),
            key: fty.clone(),
        });
        let mangled = mangled_name(self.method, fty);
        let rewritten = self.rewrite_into_calls(s, &mangled);
        // Then apply the ordinary infer substitution to whatever remains.
        match self.stmt(&rewritten, binds).into_iter().next() {
            Some(st) => st,
            None => rewritten,
        }
    }

    fn expr(&mut self, e: &Expr, binds: &Bindings) -> Expr {
        match e {
            // `infer.from(x)`: resolve by the from/parse partition.
            Expr::Call(callee, args, span)
                if is_static_call(callee, "infer", "from") && args.len() == 1 =>
            {
                self.infer_from(&args[0].expr, binds, *span)
            }
            Expr::Match(scrut, arms, span) => {
                let scrut_e = self.expr(scrut, binds);
                let arms = arms
                    .iter()
                    .map(|arm| {
                        let arm_binds = self.arm_bindings(&arm.pattern, scrut);
                        MatchArm {
                            pattern: arm.pattern.clone(),
                            body: self.expr(&arm.body, &arm_binds),
                            span: arm.span,
                        }
                    })
                    .collect();
                Expr::Match(Box::new(scrut_e), arms, *span)
            }
            Expr::Block(b, span) => Expr::Block(self.block_in(b, binds), *span),
            Expr::If(c, t, els, span) => Expr::If(
                Box::new(self.expr(c, binds)),
                self.block_in(t, binds),
                els.as_ref().map(|e| Box::new(self.expr(e, binds))),
                *span,
            ),
            Expr::IfLet(pat, scrut, t, els, span) => Expr::IfLet(
                pat.clone(),
                Box::new(self.expr(scrut, binds)),
                self.block_in(t, binds),
                els.as_ref().map(|e| Box::new(self.expr(e, binds))),
                *span,
            ),
            Expr::Call(callee, args, span) => Expr::Call(
                Box::new(self.expr(callee, binds)),
                args.iter()
                    .map(|a| Arg {
                        expr: self.expr(&a.expr, binds),
                    })
                    .collect(),
                *span,
            ),
            Expr::Field(b, n, span) => Expr::Field(Box::new(self.expr(b, binds)), n.clone(), *span),
            Expr::Index(b, i, span) => Expr::Index(
                Box::new(self.expr(b, binds)),
                Box::new(self.expr(i, binds)),
                *span,
            ),
            Expr::ErrorProp(i, span) => Expr::ErrorProp(Box::new(self.expr(i, binds)), *span),
            Expr::Unary(op, i, span) => Expr::Unary(*op, Box::new(self.expr(i, binds)), *span),
            Expr::Binary(op, l, r, span) => Expr::Binary(
                *op,
                Box::new(self.expr(l, binds)),
                Box::new(self.expr(r, binds)),
                *span,
            ),
            Expr::Str(segs, span) => Expr::Str(
                segs.iter()
                    .map(|seg| match seg {
                        StrSeg::Lit(s) => StrSeg::Lit(s.clone()),
                        StrSeg::Expr(e) => StrSeg::Expr(Box::new(self.expr(e, binds))),
                    })
                    .collect(),
                *span,
            ),
            Expr::Array(es, span) => {
                Expr::Array(es.iter().map(|e| self.expr(e, binds)).collect(), *span)
            }
            Expr::Range(l, r, span) => Expr::Range(
                Box::new(self.expr(l, binds)),
                Box::new(self.expr(r, binds)),
                *span,
            ),
            Expr::TypeLit(n, fs, span) => Expr::TypeLit(
                n.clone(),
                fs.iter()
                    .map(|(k, e)| (k.clone(), self.expr(e, binds)))
                    .collect(),
                *span,
            ),
            Expr::VariantLit(t, v, fs, span) => Expr::VariantLit(
                t.clone(),
                v.clone(),
                fs.iter()
                    .map(|(k, e)| (k.clone(), self.expr(e, binds)))
                    .collect(),
                *span,
            ),
            Expr::Closure(ps, b, span) => {
                Expr::Closure(ps.clone(), Box::new(self.expr(b, binds)), *span)
            }
            other => other.clone(),
        }
    }

    /// Resolve `infer.from(arg)` at the current key. `arg` must have a
    /// determinable type (a pattern-bound variable, whose type comes from the
    /// enclosing arm).
    fn infer_from(&mut self, arg: &Expr, binds: &Bindings, span: prepoly_hir::Span) -> Expr {
        let Some(src) = self.arg_type(arg, binds) else {
            // Unknown source type: leave `infer.from` as an unresolved call so
            // the checker reports it clearly rather than the specializer.
            return Expr::Call(
                Box::new(Expr::Field(
                    Box::new(Expr::Ident("infer".into(), span)),
                    "from".into(),
                    span,
                )),
                vec![Arg { expr: arg.clone() }],
                span,
            );
        };
        match crate::infer_from(self.program, &src, self.key) {
            // Identity: the argument already is the target value.
            crate::InferFrom::Identity => arg.clone(),
            // A named conversion `Q.from(arg)`.
            crate::InferFrom::Static { qualifier, .. } => Expr::Call(
                Box::new(Expr::Field(
                    Box::new(Expr::Ident(qualifier, span)),
                    "from".into(),
                    span,
                )),
                vec![Arg { expr: arg.clone() }],
                span,
            ),
            // No conversion: this variant cannot produce the key -- a runtime
            // decode error (e.g. a JSON string decoded as an int).
            crate::InferFrom::Absent(_) => self.error_call(span),
        }
    }

    fn arm_bindings(&self, pat: &Pattern, scrut: &Expr) -> Bindings {
        let mut binds = HashMap::new();
        // Only the top match on `self` is typed here (the scrutinee is the
        // receiver); nested matches contribute no field types.
        if (matches!(scrut, Expr::SelfExpr(_)) || matches!(scrut, Expr::Ident(n, _) if n == "self"))
            && let Pattern::Record(type_variant, fields, _) = pat
        {
            {
                let variant = type_variant.rsplit('.').next().unwrap_or(type_variant);
                if let Type::Sum(n) = &self.scrutinee
                    && let Some(info) = self.program.type_by_id(n.id)
                    && let Some(v) = info.variant(variant)
                {
                    for fp in fields {
                        if let Some(fi) = v.fields.iter().find(|fi| fi.name == fp.name) {
                            let name = match &fp.pat {
                                Some(Pattern::Binding(b, _)) => b.clone(),
                                _ => fp.name.clone(),
                            };
                            if let Some(t) = &fi.resolved_ty {
                                binds.insert(name, t.clone());
                            }
                        }
                    }
                }
            }
        }
        binds
    }

    fn arg_type(&self, arg: &Expr, binds: &Bindings) -> Option<Type> {
        match arg {
            Expr::Ident(n, _) => binds.get(n).cloned(),
            _ => None,
        }
    }

    fn subst_type(&self, t: &TypeExpr) -> TypeExpr {
        match t {
            TypeExpr::Named(n, span) if n == "infer" => type_to_expr(self.key, *span),
            TypeExpr::Named(..) => t.clone(),
            TypeExpr::Array(i, len, span) => {
                TypeExpr::Array(Box::new(self.subst_type(i)), *len, *span)
            }
            TypeExpr::Nullable(i, span) => TypeExpr::Nullable(Box::new(self.subst_type(i)), *span),
            TypeExpr::Fallible(i, span) => TypeExpr::Fallible(Box::new(self.subst_type(i)), *span),
            other => other.clone(),
        }
    }

    /// A `return error("...")` for a non-viable arm/branch at this key.
    fn error_return(&self, span: prepoly_hir::Span) -> Stmt {
        Stmt::Return(Some(self.error_call(span)), span)
    }

    fn error_call(&self, span: prepoly_hir::Span) -> Expr {
        Expr::Call(
            Box::new(Expr::Ident("error".into(), span)),
            vec![Arg {
                expr: Expr::Str(
                    vec![StrSeg::Lit(format!(
                        "cannot decode this value as `{}`",
                        self.key.type_name()
                    ))],
                    span,
                ),
            }],
            span,
        )
    }

    /// Rewrite `<x>.into()` calls (the method being specialized) to
    /// `<x>.into__<mangle>()` inside a statement.
    fn rewrite_into_calls(&self, s: &Stmt, mangled: &str) -> Stmt {
        RewriteInto {
            method: self.method,
            mangled,
        }
        .stmt(s)
    }
}

/// A minimal AST walk that renames `recv.<method>()` calls to `recv.<mangled>()`.
struct RewriteInto<'a> {
    method: &'a str,
    mangled: &'a str,
}

impl RewriteInto<'_> {
    fn stmt(&self, s: &Stmt) -> Stmt {
        match s {
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => Stmt::Assign {
                target: self.expr(target),
                op: *op,
                value: self.expr(value),
                span: *span,
            },
            Stmt::Return(Some(e), span) => Stmt::Return(Some(self.expr(e)), *span),
            Stmt::Expr(e) => Stmt::Expr(self.expr(e)),
            Stmt::Let {
                pat,
                ty,
                value,
                is_const,
                span,
            } => Stmt::Let {
                pat: pat.clone(),
                ty: ty.clone(),
                value: value.as_ref().map(|v| self.expr(v)),
                is_const: *is_const,
                span: *span,
            },
            other => other.clone(),
        }
    }

    fn expr(&self, e: &Expr) -> Expr {
        match e {
            Expr::Call(callee, args, span) => {
                let new_callee = match &**callee {
                    Expr::Field(base, m, fspan) if m == self.method => {
                        Expr::Field(Box::new(self.expr(base)), self.mangled.to_string(), *fspan)
                    }
                    other => self.expr(other),
                };
                Expr::Call(
                    Box::new(new_callee),
                    args.iter()
                        .map(|a| Arg {
                            expr: self.expr(&a.expr),
                        })
                        .collect(),
                    *span,
                )
            }
            Expr::ErrorProp(i, span) => Expr::ErrorProp(Box::new(self.expr(i)), *span),
            Expr::Field(b, n, span) => Expr::Field(Box::new(self.expr(b)), n.clone(), *span),
            Expr::Index(b, i, span) => {
                Expr::Index(Box::new(self.expr(b)), Box::new(self.expr(i)), *span)
            }
            Expr::Binary(op, l, r, span) => {
                Expr::Binary(*op, Box::new(self.expr(l)), Box::new(self.expr(r)), *span)
            }
            other => other.clone(),
        }
    }
}

fn is_fields_over(iter: &Expr, var: &str) -> bool {
    let call = match iter {
        Expr::ErrorProp(inner, _) => inner,
        other => other,
    };
    matches!(call, Expr::Call(c, args, _)
        if matches!(&**c, Expr::Ident(n, _) if n == "fields")
            && matches!(args.as_slice(), [a] if matches!(&a.expr, Expr::Ident(n, _) if n == var)))
}

fn is_static_call(callee: &Expr, ty: &str, method: &str) -> bool {
    matches!(callee, Expr::Field(base, m, _)
        if m == method && matches!(&**base, Expr::Ident(n, _) if n == ty))
}

/// Render a concrete type back to a `TypeExpr` for use in a synthesized
/// annotation. Covers the types a decoder targets.
pub fn type_to_expr(t: &Type, span: prepoly_hir::Span) -> TypeExpr {
    match t {
        Type::Record(n) | Type::Sum(n) => TypeExpr::Named(n.name.clone(), span),
        Type::Nullable(i) => TypeExpr::Nullable(Box::new(type_to_expr(i, span)), span),
        Type::Slice(i) => TypeExpr::Array(Box::new(type_to_expr(i, span)), None, span),
        Type::Array(i, k) => TypeExpr::Array(Box::new(type_to_expr(i, span)), Some(*k), span),
        Type::ConstOf(i) | Type::Mut(i) | Type::Ref(i) => type_to_expr(i, span),
        _ => TypeExpr::Named(t.type_name(), span),
    }
}
