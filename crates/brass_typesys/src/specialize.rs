//! Per-key specialization of reflective decoder methods (`fun T.m(self) ->
//! infer!`).
//!
//! A keyed method's body is written generically over an unknown target type
//! (`infer`); each call site fixes the target from the caller's expectation
//! (`let u: User = j.into()!` fixes `User`). Because Brass monomorphizes to
//! fully concrete code, the generic body is turned into one CONCRETE method per
//! requested key here, which is then checked and lowered like source code. The
//! specializer:
//!
//! - substitutes every `infer` annotation with the key (`let ret: infer` ->
//!   `let ret: User`, the return `infer!` -> `User!`);
//! - unrolls the record walk -- a `for f in fields(x)` loop over a binding
//!   declared `let x: infer`, whatever its name -- over the (now concrete) key,
//!   so each field is assigned directly and the recursive `x.into()` inside
//!   becomes a call to the FIELD's own specialization (`x.into__<fieldtype>()`),
//!   which is in turn scheduled for specialization. A nullable key `T?` walks
//!   `T`'s fields (the walked binding is typed `T`, and the `T` it builds
//!   promotes into the `T?` result);
//! - resolves `infer.from(x)` by the from/parse partition
//!   (`crate::convert::infer_from`): an identity, a named conversion, or -- when
//!   no conversion exists -- a runtime error (the arm is not viable for this
//!   key, e.g. a JSON number decoded as a record). A source the template does
//!   not type (anything but a variant-pattern binding) is resolved per instance
//!   by a type-test dispatch over the same partition (see `conversion`). At a
//!   nullable key a fallible conversion is unwrapped with `!`, so its value
//!   promotes into the result;
//! - turns `return null` into a runtime error when the key is not nullable.
//!
//! Every runtime error the specializer itself generates is raised at the
//! location of the decoder call that could not produce its key: the concrete
//! method takes the caller's position through an implicit trailing `Location`
//! parameter (filled at each call site, like `error`'s own).
//!
//! The result is a set of concrete methods keyed by mangled name. The driver
//! takes the keys from the checker's keyed-call channels, lowers the
//! generated methods into the program (`brass_hir::lower_generated_into`),
//! checks each of them, and has MIR lowering call the specialization at every
//! keyed call site (per instance where the enclosing body's instances key the
//! call differently); keyed calls inside generated bodies repeat the step.

use fxhash::FxHashMap as HashMap;

use brass_parser::ast::*;

use brass_hir::{Program, Type, TypeKind};

mod conversion;
mod walk;

use walk::{fields_loop_binding, fields_walked_bindings};

/// A pure span-shift of a block by `delta` (a multiple of `SPAN_SHIFT_UNIT`):
/// reuses the fields-loop expander with a variable that matches nothing, so it
/// rewrites spans without substituting anything.
fn shift_spans(b: &Block, delta: usize) -> Block {
    debug_assert!(delta.is_multiple_of(brass_hir::SPAN_SHIFT_UNIT));
    let iteration = delta / brass_hir::SPAN_SHIFT_UNIT;
    // `expand_fields_body` shifts by `(iteration + 1) * SPAN_SHIFT_UNIT`; the
    // sentinel variable name cannot appear in source, so no ident is rewritten.
    brass_hir::expand_fields_body(b, "\u{0}shift", "", iteration.saturating_sub(1))
}

/// The largest synthetic offset and absolute high coordinate in a generated
/// block. Field-loop expansion may already have shifted nested copies before a
/// specialization receives its own band.
fn span_metrics(b: &Block) -> (usize, usize) {
    fn observe(span: brass_hir::Span, max_shift: &mut usize, max_hi: &mut usize) {
        let source = span.source_span();
        *max_shift = (*max_shift).max(
            span.lo
                .saturating_sub(source.lo)
                .max(span.hi.saturating_sub(source.hi)),
        );
        *max_hi = (*max_hi).max(span.hi);
    }

    fn expr(e: &Expr, max_shift: &mut usize, max_hi: &mut usize) {
        observe(e.span(), max_shift, max_hi);
        match e {
            Expr::Unary(_, inner, _)
            | Expr::ErrorProp(inner, _)
            | Expr::Field(inner, _, _)
            | Expr::TypeTest(inner, _, _, _) => expr(inner, max_shift, max_hi),
            Expr::Binary(_, left, right, _)
            | Expr::Index(left, right, _)
            | Expr::Range(left, right, _) => {
                expr(left, max_shift, max_hi);
                expr(right, max_shift, max_hi);
            }
            Expr::Call(callee, args, _) => {
                expr(callee, max_shift, max_hi);
                for arg in args {
                    expr(&arg.expr, max_shift, max_hi);
                }
            }
            Expr::Str(segments, _) => {
                for segment in segments {
                    if let StrSeg::Expr(inner) = segment {
                        expr(inner, max_shift, max_hi);
                    }
                }
            }
            Expr::Closure(_, body, _) => expr(body, max_shift, max_hi),
            Expr::Array(items, _) => {
                for item in items {
                    expr(item, max_shift, max_hi);
                }
            }
            Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
                for (_, value) in fields {
                    expr(value, max_shift, max_hi);
                }
            }
            Expr::If(cond, then, els, _) => {
                expr(cond, max_shift, max_hi);
                block(then, max_shift, max_hi);
                if let Some(els) = els {
                    expr(els, max_shift, max_hi);
                }
            }
            Expr::IfLet(_, scrutinee, then, els, _) => {
                expr(scrutinee, max_shift, max_hi);
                block(then, max_shift, max_hi);
                if let Some(els) = els {
                    expr(els, max_shift, max_hi);
                }
            }
            Expr::Match(scrutinee, arms, _) => {
                expr(scrutinee, max_shift, max_hi);
                for arm in arms {
                    observe(arm.span, max_shift, max_hi);
                    expr(&arm.body, max_shift, max_hi);
                }
            }
            Expr::Block(inner, _) => block(inner, max_shift, max_hi),
            Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(_)
            | Expr::Ident(..)
            | Expr::SelfExpr(_) => {}
        }
    }

    fn block(b: &Block, max_shift: &mut usize, max_hi: &mut usize) {
        observe(b.span, max_shift, max_hi);
        for stmt in &b.stmts {
            observe(stmt.span(), max_shift, max_hi);
            match stmt {
                Stmt::Let {
                    value: Some(value), ..
                } => expr(value, max_shift, max_hi),
                Stmt::Let { value: None, .. } => {}
                Stmt::Assign { target, value, .. } => {
                    expr(target, max_shift, max_hi);
                    expr(value, max_shift, max_hi);
                }
                Stmt::Expr(value) | Stmt::Return(Some(value), _) => expr(value, max_shift, max_hi),
                Stmt::While { cond, body, .. } => {
                    expr(cond, max_shift, max_hi);
                    block(body, max_shift, max_hi);
                }
                Stmt::For { iter, body, .. } => {
                    expr(iter, max_shift, max_hi);
                    block(body, max_shift, max_hi);
                }
                Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
            }
        }
    }

    let mut max_shift = 0;
    let mut max_hi = 0;
    block(b, &mut max_shift, &mut max_hi);
    (max_shift, max_hi)
}

/// A requested specialization: method `method` on the receiver's canonical HIR
/// symbol `recv`, targeting result type `key`. The symbol, unlike the source
/// display name, is unique when modules declare same-named types.
#[derive(Clone)]
pub struct KeyedNeed {
    pub recv: String,
    pub method: String,
    pub key: Type,
}

/// The mangled method name of a specialization (`into__int64`,
/// `into__rec5x2_...`). Deterministic and collision-free (see
/// [`brass_hir::type_key`]); a valid identifier, so the injected method parses and
/// dispatches like any other.
pub fn mangled_name(method: &str, key: &Type) -> String {
    format!("{method}__{}", brass_hir::type_key(key))
}

/// One generated specialization, retained outside the parsed module graph.
pub type Generated = brass_hir::GeneratedDecl;

/// The name of the implicit trailing `Location` parameter every generated
/// specialization declares. Source text cannot spell it, so it never collides
/// with a template's own bindings.
const LOCATION_PARAM: &str = "\u{0}location";

/// Generate every concrete method reachable from `roots` (transitively: a
/// record key pulls in a specialization per field type), or an error when a
/// need names no method with a body on its receiver or the synthetic span
/// space runs out.
pub fn specialize_all(program: &Program, roots: &[KeyedNeed]) -> Result<Vec<Generated>, String> {
    let mut out = Vec::new();
    let mut done: fxhash::FxHashSet<String> = fxhash::FxHashSet::default();
    let mut work: Vec<KeyedNeed> = roots.to_vec();
    // One shift unit separates an unexpanded body from its first fields-loop
    // copy. Each generated body reserves only the lanes it actually used, so
    // the first specialization remains representable on 32-bit targets.
    let mut next_span_base = brass_hir::SPAN_SHIFT_UNIT;
    // Bounded by the distinct (recv, method, key) triples the program's type
    // graph can reach -- finite -- so the worklist drains.
    while let Some(need) = work.pop() {
        let sym = format!(
            "{}.{}:{}",
            need.recv,
            need.method,
            brass_hir::type_key(&need.key)
        );
        if !done.insert(sym) {
            continue;
        }
        let (mut decl, module) = specialize_one(program, &need, &mut work)?;
        // Every specialization cloned from one template retains the same source
        // provenance, so it still needs a distinct synthetic coordinate band.
        // Provenance itself separates different templates; within a template,
        // reserve the exact field-expansion extent instead of assuming a fixed
        // record-size ceiling or a 64-bit `usize`.
        let (inner_shift, max_hi) = span_metrics(&decl.body);
        if !inner_shift.is_multiple_of(brass_hir::SPAN_SHIFT_UNIT) {
            return Err("reflective specialization produced a misaligned synthetic span".into());
        }
        let extent = inner_shift
            .checked_add(brass_hir::SPAN_SHIFT_UNIT)
            .ok_or_else(|| {
                "reflective specialization exhausted synthetic span space".to_string()
            })?;
        let base = next_span_base;
        max_hi.checked_add(base).ok_or_else(|| {
            "reflective specialization exhausted synthetic span space".to_string()
        })?;
        next_span_base = next_span_base.checked_add(extent).ok_or_else(|| {
            "reflective specialization exhausted synthetic span space".to_string()
        })?;
        decl.body = shift_spans(&decl.body, base);
        out.push(Generated {
            module,
            receiver: program
                .types
                .get(&need.recv)
                .expect("specialization receiver was resolved above")
                .name
                .clone(),
            template: need.method.clone(),
            decl,
            key: need.key.clone(),
        });
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
        .get(&need.recv)
        .ok_or_else(|| format!("unknown receiver type `{}`", need.recv))?;
    let method = match &info.kind {
        TypeKind::Record { methods, .. } => methods.get(&need.method),
        TypeKind::Sum { variants } => variants.iter().find_map(|v| v.methods.get(&need.method)),
    }
    .ok_or_else(|| format!("`{}` has no method `{}`", info.name, need.method))?;
    let src = &method.decl;
    let template_body = src.body.as_ref().ok_or("keyed method has no body")?;
    // A program lowered without the prelude (unit tests, embedders) has no
    // `Location`; its generated errors then fall back to `error`'s own
    // implicit position.
    let location = program
        .prelude_type("Location")
        .map(brass_hir::TypeInfo::type_ref);
    let mut cx = Specializer {
        program,
        recv: &need.recv,
        method: &need.method,
        key: &need.key,
        scrutinee: info.type_ref(),
        work,
        walked: fields_walked_bindings(template_body),
        walk_targets: fxhash::FxHashSet::default(),
        located: location.is_some(),
        dispatch_stride: walk_width(program, &need.key) + 1,
    };
    let body = cx.block(template_body);
    let mut params = src.params.clone();
    if let Some(location) = &location {
        params.push(Param {
            name: LOCATION_PARAM.to_string(),
            ty: Some(type_to_expr(location, src.span)),
            span: src.span,
        });
    }
    let decl = FunDecl {
        name: mangled_name(&need.method, &need.key),
        name_span: src.name_span,
        recv: Some(TypeExpr::Named(info.name.clone(), src.span)),
        params,
        // The concrete result: `key!` (a fallible decode).
        ret: Some(TypeExpr::Fallible(
            Box::new(type_to_expr(&need.key, src.span)),
            src.span,
        )),
        body,
        span: src.span,
        doc: src.doc.clone(),
    };
    Ok((decl, info.module.clone()))
}

/// How many copies a record walk at `key` unrolls: the record key's field
/// count (a nullable key walks its payload), zero for any other key.
fn walk_width(program: &Program, key: &Type) -> usize {
    let key = match key {
        Type::Nullable(inner) => inner,
        other => other,
    };
    match key {
        Type::Record(n) => program.type_by_id(n.id).map_or(0, |info| match &info.kind {
            TypeKind::Record { fields, .. } => fields.len(),
            TypeKind::Sum { .. } => 0,
        }),
        _ => 0,
    }
}

struct Specializer<'a> {
    program: &'a Program,
    recv: &'a str,
    method: &'a str,
    key: &'a Type,
    /// The type of `self` (the receiver), the scrutinee of the top match.
    scrutinee: Type,
    work: &'a mut Vec<KeyedNeed>,
    /// Every binding name the template iterates with `fields(..)`.
    walked: fxhash::FxHashSet<String>,
    /// The `let x: infer` bindings among `walked`: the record walk's targets,
    /// typed (and unrolled) as [`Self::record_key`].
    walk_targets: fxhash::FxHashSet<String>,
    /// Whether the generated method declares the implicit `Location`
    /// parameter its generated errors are raised at.
    located: bool,
    /// The shift-lane spacing of an `infer.from` dispatch's arms: one more
    /// than the copies the record walk unrolls (see `lane_span`).
    dispatch_stride: usize,
}

/// Per-arm variable-to-type bindings (a match pattern binds variant fields).
type Bindings = HashMap<String, Type>;

impl<'a> Specializer<'a> {
    fn block(&mut self, b: &Block) -> Block {
        Block {
            stmts: b
                .stmts
                .iter()
                .flat_map(|s| self.stmt(s, &HashMap::default()))
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

    /// The key the record walk builds: the key itself, or the payload of a
    /// nullable key (a present value decodes as the payload, which promotes
    /// into the nullable result).
    fn record_key(&self) -> &'a Type {
        match self.key {
            Type::Nullable(inner) => inner,
            other => other,
        }
    }

    fn stmt(&mut self, s: &Stmt, binds: &Bindings) -> Vec<Stmt> {
        match s {
            // The record walk's target `let x: infer` (a binding a `fields(x)`
            // loop iterates) -> `let x: <record key>`; every other let keeps
            // its (infer-substituted) annotation, so `let y: infer` is the key.
            Stmt::Let {
                pat,
                ty,
                value,
                is_const,
                span,
            } => {
                let walk_target = match (pat, ty) {
                    (Pattern::Binding(name, None, _), Some(TypeExpr::Named(t, _)))
                        if t == "infer" && self.walked.contains(name) =>
                    {
                        Some(name)
                    }
                    _ => None,
                };
                let ty = match walk_target {
                    Some(name) => {
                        self.walk_targets.insert(name.clone());
                        ty.as_ref()
                            .map(|t| type_to_expr(self.record_key(), t.span()))
                    }
                    None => ty.as_ref().map(|t| self.subst_type(t, binds)),
                };
                vec![Stmt::Let {
                    pat: pat.clone(),
                    ty,
                    value: value.as_ref().map(|v| self.expr(v, binds)),
                    is_const: *is_const,
                    span: *span,
                }]
            }
            // The record walk `for f in fields(x)` over a walk target: unroll
            // over the record key's fields.
            Stmt::For {
                pat: Pattern::Binding(var, _, _),
                iter,
                body,
                span,
            } if fields_loop_binding(iter).is_some_and(|x| self.walk_targets.contains(x)) => {
                // A non-record key cannot iterate fields: the whole arm is not
                // viable, so fold it to a runtime decode error. The subsequent
                // `return` of the walked binding is then unreachable.
                let Type::Record(n) = self.record_key() else {
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
                    let fty = n
                        .substitution
                        .get(&f.name)
                        .cloned()
                        .or_else(|| f.resolved_ty.clone())
                        .unwrap_or(Type::Void);
                    // Reuse the fields-loop expansion (field name decay + v[f]
                    // projection), then rewrite the recursive keyed call to the
                    // field's specialization.
                    let expanded = brass_hir::expand_fields_body(body, var, &f.name, i);
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
                pat,
                iter,
                body,
                span,
            } => vec![Stmt::For {
                pat: pat.clone(),
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
            Expr::TypeTest(subject, te, negated, span) => Expr::TypeTest(
                Box::new(self.expr(subject, binds)),
                self.subst_type(te, binds),
                *negated,
                *span,
            ),
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

    fn arm_bindings(&self, pat: &Pattern, scrut: &Expr) -> Bindings {
        let mut binds = HashMap::default();
        // Only a match on `self` is typed here (its scrutinee is the
        // receiver); a match on anything else contributes no field types.
        if (matches!(scrut, Expr::SelfExpr(_)) || matches!(scrut, Expr::Ident(n, _) if n == "self"))
            && let Pattern::Record(type_variant, _, fields, _) = pat
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
                                Some(Pattern::Binding(b, _, _)) => b.clone(),
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

    fn subst_type(&mut self, t: &TypeExpr, binds: &Bindings) -> TypeExpr {
        match t {
            TypeExpr::Named(n, span) if n == "infer" => type_to_expr(self.key, *span),
            TypeExpr::Named(..) => t.clone(),
            TypeExpr::Array(i, len, span) => {
                TypeExpr::Array(Box::new(self.subst_type(i, binds)), *len, *span)
            }
            TypeExpr::Fun(params, ret, span) => TypeExpr::Fun(
                params
                    .iter()
                    .map(|param| self.subst_type(param, binds))
                    .collect(),
                Box::new(self.subst_type(ret, binds)),
                *span,
            ),
            TypeExpr::Nullable(i, span) => {
                TypeExpr::Nullable(Box::new(self.subst_type(i, binds)), *span)
            }
            TypeExpr::Fallible(i, span) => {
                TypeExpr::Fallible(Box::new(self.subst_type(i, binds)), *span)
            }
            TypeExpr::Tuple(items, span) => TypeExpr::Tuple(
                items
                    .iter()
                    .map(|item| self.subst_type(item, binds))
                    .collect(),
                *span,
            ),
            TypeExpr::Anonymous(fields, span) => TypeExpr::Anonymous(
                fields
                    .iter()
                    .map(|(name, ty, name_span)| {
                        (name.clone(), self.subst_type(ty, binds), *name_span)
                    })
                    .collect(),
                *span,
            ),
            TypeExpr::Mut(i, span) => TypeExpr::Mut(Box::new(self.subst_type(i, binds)), *span),
            TypeExpr::Ref(i, span) => TypeExpr::Ref(Box::new(self.subst_type(i, binds)), *span),
            TypeExpr::TypeOf(expr, span) => {
                TypeExpr::TypeOf(Box::new(self.expr(expr, binds)), *span)
            }
            TypeExpr::Refine(base, fields, span) => TypeExpr::Refine(
                Box::new(self.subst_type(base, binds)),
                fields
                    .iter()
                    .map(|(name, ty, name_span)| {
                        (name.clone(), self.subst_type(ty, binds), *name_span)
                    })
                    .collect(),
                *span,
            ),
            TypeExpr::TypeSlot(_) | TypeExpr::SelfField(..) => t.clone(),
        }
    }

    /// A `return error("...")` for a non-viable arm/branch at this key.
    fn error_return(&self, span: brass_hir::Span) -> Stmt {
        Stmt::Return(Some(self.error_call(span)), span)
    }

    /// `error("cannot decode this value as `<key>`", <location>)`: raised at
    /// the decoder call's position, which the generated method receives as
    /// its implicit `Location` parameter.
    fn error_call(&self, span: brass_hir::Span) -> Expr {
        let mut args = vec![Arg {
            expr: Expr::Str(
                vec![StrSeg::Lit(format!(
                    "cannot decode this value as `{}`",
                    self.key.type_name()
                ))],
                span,
            ),
        }];
        if self.located {
            args.push(Arg {
                expr: Expr::Ident(LOCATION_PARAM.into(), span),
            });
        }
        Expr::Call(Box::new(Expr::Ident("error".into(), span)), args, span)
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

/// A recursive AST walk that renames `recv.<method>()` calls to
/// `recv.<mangled>()` wherever an expanded fields-loop body may contain them.
struct RewriteInto<'a> {
    method: &'a str,
    mangled: &'a str,
}

impl RewriteInto<'_> {
    fn block(&self, b: &Block) -> Block {
        Block {
            stmts: b.stmts.iter().map(|stmt| self.stmt(stmt)).collect(),
            span: b.span,
        }
    }

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
            Stmt::Return(None, span) => Stmt::Return(None, *span),
            Stmt::Expr(e) => Stmt::Expr(self.expr(e)),
            Stmt::Let {
                pat,
                ty,
                value,
                is_const,
                span,
            } => Stmt::Let {
                pat: self.pattern(pat),
                ty: ty.as_ref().map(|ty| self.type_expr(ty)),
                value: value.as_ref().map(|v| self.expr(v)),
                is_const: *is_const,
                span: *span,
            },
            Stmt::While { cond, body, span } => Stmt::While {
                cond: self.expr(cond),
                body: self.block(body),
                span: *span,
            },
            Stmt::For {
                pat,
                iter,
                body,
                span,
            } => Stmt::For {
                pat: self.pattern(pat),
                iter: self.expr(iter),
                body: self.block(body),
                span: *span,
            },
            Stmt::Break(span) => Stmt::Break(*span),
            Stmt::Continue(span) => Stmt::Continue(*span),
        }
    }

    fn expr(&self, e: &Expr) -> Expr {
        match e {
            Expr::Call(callee, args, span) => {
                let new_callee = match self.expr(callee) {
                    Expr::Field(base, m, fspan) if m == self.method => {
                        Expr::Field(base, self.mangled.to_string(), fspan)
                    }
                    other => other,
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
            Expr::Int(value, span) => Expr::Int(*value, *span),
            Expr::Float(value, span) => Expr::Float(*value, *span),
            Expr::Bool(value, span) => Expr::Bool(*value, *span),
            Expr::Null(span) => Expr::Null(*span),
            Expr::Ident(name, span) => Expr::Ident(name.clone(), *span),
            Expr::SelfExpr(span) => Expr::SelfExpr(*span),
            Expr::Str(segments, span) => Expr::Str(
                segments
                    .iter()
                    .map(|segment| match segment {
                        StrSeg::Lit(value) => StrSeg::Lit(value.clone()),
                        StrSeg::Expr(expr) => StrSeg::Expr(Box::new(self.expr(expr))),
                    })
                    .collect(),
                *span,
            ),
            Expr::Unary(op, inner, span) => Expr::Unary(*op, Box::new(self.expr(inner)), *span),
            Expr::ErrorProp(i, span) => Expr::ErrorProp(Box::new(self.expr(i)), *span),
            Expr::Field(b, n, span) => Expr::Field(Box::new(self.expr(b)), n.clone(), *span),
            Expr::Index(b, i, span) => {
                Expr::Index(Box::new(self.expr(b)), Box::new(self.expr(i)), *span)
            }
            Expr::Binary(op, l, r, span) => {
                Expr::Binary(*op, Box::new(self.expr(l)), Box::new(self.expr(r)), *span)
            }
            Expr::Closure(params, body, span) => Expr::Closure(
                params.iter().map(|param| self.param(param)).collect(),
                Box::new(self.expr(body)),
                *span,
            ),
            Expr::Array(items, span) => {
                Expr::Array(items.iter().map(|item| self.expr(item)).collect(), *span)
            }
            Expr::Range(lo, hi, span) => {
                Expr::Range(Box::new(self.expr(lo)), Box::new(self.expr(hi)), *span)
            }
            Expr::TypeLit(name, fields, span) => Expr::TypeLit(
                name.clone(),
                fields
                    .iter()
                    .map(|(name, value)| (name.clone(), self.expr(value)))
                    .collect(),
                *span,
            ),
            Expr::VariantLit(ty, variant, fields, span) => Expr::VariantLit(
                ty.clone(),
                variant.clone(),
                fields
                    .iter()
                    .map(|(name, value)| (name.clone(), self.expr(value)))
                    .collect(),
                *span,
            ),
            Expr::If(cond, then, els, span) => Expr::If(
                Box::new(self.expr(cond)),
                self.block(then),
                els.as_ref().map(|els| Box::new(self.expr(els))),
                *span,
            ),
            Expr::IfLet(pattern, scrutinee, then, els, span) => Expr::IfLet(
                self.pattern(pattern),
                Box::new(self.expr(scrutinee)),
                self.block(then),
                els.as_ref().map(|els| Box::new(self.expr(els))),
                *span,
            ),
            Expr::TypeTest(subject, ty, negated, span) => Expr::TypeTest(
                Box::new(self.expr(subject)),
                self.type_expr(ty),
                *negated,
                *span,
            ),
            Expr::Match(scrutinee, arms, span) => Expr::Match(
                Box::new(self.expr(scrutinee)),
                arms.iter()
                    .map(|arm| MatchArm {
                        pattern: self.pattern(&arm.pattern),
                        body: self.expr(&arm.body),
                        span: arm.span,
                    })
                    .collect(),
                *span,
            ),
            Expr::Block(block, span) => Expr::Block(self.block(block), *span),
        }
    }

    fn pattern(&self, pattern: &Pattern) -> Pattern {
        match pattern {
            Pattern::Wildcard(span) => Pattern::Wildcard(*span),
            Pattern::Binding(name, qualifier, span) => {
                Pattern::Binding(name.clone(), qualifier.clone(), *span)
            }
            Pattern::Literal(expr, span) => Pattern::Literal(Box::new(self.expr(expr)), *span),
            Pattern::Record(name, qualifier, fields, span) => Pattern::Record(
                name.clone(),
                qualifier.clone(),
                fields
                    .iter()
                    .map(|field| FieldPat {
                        name: field.name.clone(),
                        pat: field.pat.as_ref().map(|pat| self.pattern(pat)),
                        span: field.span,
                    })
                    .collect(),
                *span,
            ),
            Pattern::Array(patterns, span) => Pattern::Array(
                patterns
                    .iter()
                    .map(|pattern| self.pattern(pattern))
                    .collect(),
                *span,
            ),
        }
    }

    fn param(&self, param: &Param) -> Param {
        Param {
            name: param.name.clone(),
            ty: param.ty.as_ref().map(|ty| self.type_expr(ty)),
            span: param.span,
        }
    }

    fn type_expr(&self, ty: &TypeExpr) -> TypeExpr {
        match ty {
            TypeExpr::Named(name, span) => TypeExpr::Named(name.clone(), *span),
            TypeExpr::Array(inner, len, span) => {
                TypeExpr::Array(Box::new(self.type_expr(inner)), *len, *span)
            }
            TypeExpr::Fun(params, ret, span) => TypeExpr::Fun(
                params.iter().map(|param| self.type_expr(param)).collect(),
                Box::new(self.type_expr(ret)),
                *span,
            ),
            TypeExpr::Nullable(inner, span) => {
                TypeExpr::Nullable(Box::new(self.type_expr(inner)), *span)
            }
            TypeExpr::Fallible(inner, span) => {
                TypeExpr::Fallible(Box::new(self.type_expr(inner)), *span)
            }
            TypeExpr::Tuple(items, span) => TypeExpr::Tuple(
                items.iter().map(|item| self.type_expr(item)).collect(),
                *span,
            ),
            TypeExpr::Anonymous(fields, span) => TypeExpr::Anonymous(
                fields
                    .iter()
                    .map(|(name, ty, name_span)| (name.clone(), self.type_expr(ty), *name_span))
                    .collect(),
                *span,
            ),
            TypeExpr::Mut(inner, span) => TypeExpr::Mut(Box::new(self.type_expr(inner)), *span),
            TypeExpr::Ref(inner, span) => TypeExpr::Ref(Box::new(self.type_expr(inner)), *span),
            TypeExpr::TypeOf(expr, span) => TypeExpr::TypeOf(Box::new(self.expr(expr)), *span),
            TypeExpr::TypeSlot(span) => TypeExpr::TypeSlot(*span),
            TypeExpr::SelfField(name, span) => TypeExpr::SelfField(name.clone(), *span),
            TypeExpr::Refine(base, fields, span) => TypeExpr::Refine(
                Box::new(self.type_expr(base)),
                fields
                    .iter()
                    .map(|(name, ty, name_span)| (name.clone(), self.type_expr(ty), *name_span))
                    .collect(),
                *span,
            ),
        }
    }
}

fn is_static_call(callee: &Expr, ty: &str, method: &str) -> bool {
    matches!(callee, Expr::Field(base, m, _)
        if m == method && matches!(&**base, Expr::Ident(n, _) if n == ty))
}

/// Render a concrete type back to a `TypeExpr` for use in a synthesized
/// annotation. Covers the types a decoder targets. A declared record or sum
/// is named by its id ([`brass_hir::generated_type_name`]), so the annotation
/// denotes that declaration whatever names the template's module can see.
pub fn type_to_expr(t: &Type, span: brass_hir::Span) -> TypeExpr {
    match t {
        Type::Record(n) | Type::Sum(n) if n.id >= 0 => {
            TypeExpr::Named(brass_hir::generated_type_name(n.id), span)
        }
        Type::Record(n) | Type::Sum(n) => TypeExpr::Named(n.name.clone(), span),
        Type::Nullable(i) => TypeExpr::Nullable(Box::new(type_to_expr(i, span)), span),
        Type::Slice(i) => TypeExpr::Array(Box::new(type_to_expr(i, span)), None, span),
        Type::Array(i, k) => TypeExpr::Array(Box::new(type_to_expr(i, span)), Some(*k), span),
        Type::ConstOf(i) | Type::Mut(i) | Type::Ref(i) => type_to_expr(i, span),
        _ => TypeExpr::Named(t.type_name(), span),
    }
}

#[cfg(test)]
mod tests;
