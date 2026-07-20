//! Hindley-Milner type inference (Algorithm W) over function and method bodies,
//! run as a type-checking pass before monomorphization.
//!
//! The checker builds a global environment of function schemes, then infers each
//! function and method body under its parameters: every sub-expression gets a
//! principal type through unification, `let` bindings are generalized so a
//! polymorphic value (notably a closure such as `(x) -> x`) can be used at
//! several types, and each use instantiates a binding's scheme to fresh
//! variables. A unification conflict is a type error.
//!
//! Coverage is the functional core (literals with contextual numeric kinds,
//! identifiers, closures, calls, conditionals, operators, `let`/`return`/loops)
//! plus records (field access + construction), sum types (variant construction +
//! common-field access), methods, `match`/`if let` pattern binding, indexing,
//! typed errors, and the built-in numeric/string conversions. Value flow uses
//! structural subtyping (a wider record satisfies a narrower one). Positions it
//! cannot pin -- an unannotated function used only at call sites, a builtin/UFCS
//! call -- infer to a fresh variable rather than being rejected.
//!
//! This pass runs *alongside* the call-site-re-elaboration checker in `infer.rs`,
//! which remains authoritative for calls: Brass's numeric literals are
//! contextual and the back end monomorphizes per call, so a single HM scheme
//! cannot capture `fun add1(x){ x+1 }` being usable at both `int32` and `int64`
//! (it would pin the literal). The two checkers are complementary -- this one
//! contributes principled let-polymorphism and structural reconciliation, kept
//! permissive where it cannot be certain so it never rejects a valid program.

use std::collections::BTreeMap;

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use brass_hir::{
    FloatKind, FunInfo, IntKind, MethodInfo, Program, Type, TypeInfo, TypeKind, int_literal_kind,
};
use brass_parser::Span;
use brass_parser::ast::{BinOp, Block, Expr, Pattern, Stmt, StrSeg, UnaryOp};
use brass_typesys::{numeric_flows_into, strip_nullable};

use crate::TypeError;
use crate::infer::helpers::{const_index, numeric_literal_repr};
use crate::solver::{InferenceVarKind, Scheme, Solver};

/// Type-check `program` with Algorithm W, returning the inferred type errors.
/// Intended to run before monomorphization so concrete types are settled first.
pub fn check(program: &Program) -> Vec<TypeError> {
    let mut hm = Hm::new(program);
    hm.build_globals();
    // Deterministic order: all callables share one solver, so a var that leaks
    // across bodies would otherwise make diagnostics depend on HashMap order.
    let mut symbols: Vec<String> = program.functions.keys().cloned().collect();
    symbols.sort();
    for symbol in symbols {
        hm.check_function(&symbol);
    }
    hm.check_methods();
    hm.errors
}

struct Hm<'p> {
    program: &'p Program,
    solver: Solver,
    /// Function storage symbol -> its generalized scheme.
    globals: HashMap<String, Scheme>,
    /// Lexical scopes of local bindings (innermost last).
    scopes: Vec<HashMap<String, Scheme>>,
    /// The module of the function currently being checked (for name resolution).
    module: Vec<String>,
    /// The current function's return type, unified against every `return`.
    ret: Type,
    /// The receiver type while checking a method body, so `self` (a `SelfExpr` or
    /// the `self` parameter) is typed; `None` in a free function.
    self_type: Option<Type>,
    /// When the current function is fallible (it uses `error(x)` or `expr!`), its
    /// inferred `Result` payloads: `ok` is the success type a bare `return v`
    /// targets (auto-wrapped as `Ok { value: v }`), `err` the error type every
    /// `error(x)` and propagated `!` must reconcile to.
    fallible: bool,
    ok: Type,
    err: Type,
    /// Numeric-literal variables to finalize: `(id, default, span)`. A literal
    /// stays a fresh variable so context can pin its exact kind; afterwards it
    /// must have resolved to the right numeric class, or defaults to `default`
    /// (int32/int64 by the literal's magnitude, float64).
    lit_vars: Vec<(u32, Type, Span)>,
    errors: Vec<TypeError>,
}

impl<'p> Hm<'p> {
    fn new(program: &'p Program) -> Self {
        Self {
            program,
            solver: {
                // Seed past the HIR-embedded ids (see `Program::next_infer_var`);
                // a colliding local variable aliases an unrelated signature type.
                let mut s = Solver::new();
                s.seed_var_counter(program.next_infer_var);
                s
            },
            globals: HashMap::default(),
            scopes: Vec::new(),
            module: Vec::new(),
            ret: Type::Void,
            self_type: None,
            fallible: false,
            ok: Type::Void,
            err: Type::Void,
            lit_vars: Vec::new(),
            errors: Vec::new(),
        }
    }

    /// Build a scheme for every program function from its (already annotation-
    /// resolved) signature, so calls can be checked against a stable type.
    fn build_globals(&mut self) {
        // Sorted: `signature_type` allocates fresh solver variables for
        // unannotated positions, so an unordered walk would shift every later
        // variable id and make the shared-solver check order-dependent.
        let mut symbols: Vec<&String> = self.program.functions.keys().collect();
        symbols.sort();
        let mut schemes = Vec::new();
        for symbol in symbols {
            let f = &self.program.functions[symbol];
            let ty = self.signature_type(f);
            schemes.push((symbol.clone(), ty));
        }
        for (symbol, ty) in schemes {
            // Annotated signatures have no inference variables, so generalizing
            // over an empty environment quantifies any unannotated positions.
            let scheme = self.solver.generalize(&HashSet::default(), &ty);
            self.globals.insert(symbol, scheme);
        }
    }

    /// The `Fun` type of a function signature; unannotated positions become fresh
    /// variables.
    fn signature_type(&mut self, f: &FunInfo) -> Type {
        let params = f
            .signature
            .params
            .iter()
            .map(|p| self.or_fresh(p.resolved_ty.clone()))
            .collect();
        // Freshen the shared INFER_VAR sentinel in a `T!` return so this
        // function's scheme owns a distinct error variable -- otherwise every
        // fallible function's scheme shares one var and their error payloads
        // collide when one is later constrained to a non-`string` type.
        let ret = match f.signature.ret_ty.clone() {
            Some(t) => {
                brass_hir::freshen_infer(t, &mut || self.solver.fresh(InferenceVarKind::Source))
            }
            None => self.solver.fresh(InferenceVarKind::Source),
        };
        Type::Fun(params, Box::new(ret))
    }

    fn or_fresh(&mut self, ty: Option<Type>) -> Type {
        ty.unwrap_or_else(|| self.solver.fresh(InferenceVarKind::Source))
    }

    /// If a bracket literal's elements describe a tuple, return their types; else
    /// `None` (an array). A rolled-back probe decides: if every element's type can
    /// be unified to one shared type the literal is an array, and if not the
    /// differing types make it a fixed-length tuple. The probe uses each element's
    /// *representative* type -- a numeric literal stands in as its default kind
    /// rather than its still-open inference variable, so `[1, "s"]` is not misread
    /// as unifiable (an unconstrained variable unifies with anything). A tuple
    /// returns the elements' actual types (literals keep their open variable, so an
    /// annotation can still fix the integer width).
    fn tuple_of_elements(&mut self, elems: &[Expr], elem_tys: &[Type]) -> Option<Vec<Type>> {
        if elems.len() < 2 {
            return None;
        }
        // Null elements are excluded from the probe: a null unifies with any
        // element type (the sequence's element just becomes nullable), so only
        // the non-null elements decide array-vs-tuple.
        let reps: Vec<Type> = elems
            .iter()
            .zip(elem_tys)
            .filter(|(e, _)| !matches!(e, Expr::Null(_)))
            .map(|(e, t)| numeric_literal_repr(e).unwrap_or_else(|| self.solver.resolve(t)))
            .collect();
        let (first, rest) = reps.split_first()?;
        let snap = self.solver.snapshot();
        let unifiable = rest.iter().all(|t| self.solver.unify(first, t).is_ok());
        self.solver.rollback(snap);
        if unifiable {
            None
        } else {
            Some(elem_tys.iter().map(|t| self.solver.resolve(t)).collect())
        }
    }

    fn check_function(&mut self, symbol: &str) {
        let f = &self.program.functions[symbol];
        let module = f.module.clone();
        let params: Vec<(String, Type)> = f
            .signature
            .params
            .iter()
            .map(|p| (p.name.clone(), self.or_fresh(p.resolved_ty.clone())))
            .collect();
        let decl_params = f.decl.params.clone();
        let body = f.decl.body.clone();
        let ret_ty = f.signature.ret_ty.clone();
        let span = f.signature.span;
        let context = format!("function `{}`", f.signature.name);
        // A function whose first parameter is `self` is a method implemented with
        // `fun T.m(...)` (the stdlib primitive-method form). Its `self` carries the
        // receiver type so `self` in the body type-checks as a method's would.
        let self_ty = params
            .first()
            .filter(|(name, _)| name == "self")
            .map(|(_, ty)| ty.clone());
        self.check_callable(
            module,
            self_ty,
            params,
            &decl_params,
            &body,
            ret_ty,
            span,
            &context,
        );
    }

    /// Check every method body. A record method's `self` is its record type, so
    /// `self.field`/`self.m()` are checked. A sum-variant method's `self` is left
    /// open (a variant's own fields are not on the sum, so typing `self` as the
    /// sum would wrongly reject `self.variantField`); its parameters and return
    /// are still checked.
    fn check_methods(&mut self) {
        let mut jobs: Vec<(Option<Type>, Vec<String>, MethodInfo)> = Vec::new();
        for info in self.program.types.values() {
            match &info.kind {
                TypeKind::Record { methods, .. } => {
                    for m in methods.values() {
                        if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                            continue;
                        }
                        jobs.push((Some(info.type_ref()), info.module.clone(), m.clone()));
                    }
                }
                TypeKind::Sum { variants } => {
                    for v in variants {
                        for m in v.methods.values() {
                            if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                                continue;
                            }
                            jobs.push((None, info.module.clone(), m.clone()));
                        }
                    }
                }
            }
        }
        // Deterministic order (shared solver; see `check`).
        jobs.sort_by(|a, b| a.2.decl.name.cmp(&b.2.decl.name));
        for (recv, module, m) in jobs {
            self.check_method(recv, module, &m);
        }
    }

    fn check_method(&mut self, recv: Option<Type>, module: Vec<String>, m: &MethodInfo) {
        let Some(body) = m.decl.body.clone() else {
            return; // interface method declaration: no body to check
        };
        let recv = recv.unwrap_or_else(|| self.solver.fresh(InferenceVarKind::Source));
        // Bind parameters; the leading `self` param takes the concrete receiver
        // type (so a body referring to `self` by name resolves too).
        let params: Vec<(String, Type)> = m
            .signature
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let ty = if i == 0 && p.name == "self" {
                    recv.clone()
                } else {
                    self.or_fresh(p.resolved_ty.clone())
                };
                (p.name.clone(), ty)
            })
            .collect();
        let decl_params = m.decl.params.clone();
        self.check_callable(
            module,
            Some(recv),
            params,
            &decl_params,
            &body,
            m.signature.ret_ty.clone(),
            m.signature.span,
            "method",
        );
    }

    /// Check one callable body: bind its parameters (and, for a method, its
    /// receiver as `self`), detect fallibility, then infer the body and reconcile
    /// returns against the (possibly `Result`) return type.
    #[allow(clippy::too_many_arguments)]
    fn check_callable(
        &mut self,
        module: Vec<String>,
        self_ty: Option<Type>,
        params: Vec<(String, Type)>,
        decl_params: &[brass_parser::ast::Param],
        body: &Block,
        ret_ty: Option<Type>,
        span: Span,
        context: &str,
    ) {
        self.module = module;
        self.self_type = self_ty;
        self.scopes = vec![HashMap::default()];
        self.lit_vars.clear();
        // Isolate this body's transient inference: a function's public type is
        // its (pre-built) global scheme, and a method's is re-derived per call
        // from its signature, so nothing outside depends on the variables bound
        // while checking THIS body. Rolling them back at the end keeps each
        // callable's error/inference variables from leaking into the next
        // through the shared solver.
        let body_snapshot = self.solver.snapshot();
        for (name, ty) in &params {
            self.bind_mono(name, ty.clone());
        }
        self.check_duplicate_params(decl_params, context);
        self.ok = self.solver.fresh(InferenceVarKind::Source);
        self.err = self.solver.fresh(InferenceVarKind::Source);
        // A `T!` return resolves to `Result<T, Unknown(INFER_VAR)>` with the
        // shared INFER_VAR sentinel; freshen it so each fallible callable gets
        // its OWN error variable. Without this every `T!` callable aliases one
        // error var -- harmless only while every error payload is `string`, but
        // a spurious conflict the moment two differ.
        let declared = match ret_ty {
            Some(t) => {
                brass_hir::freshen_infer(t, &mut || self.solver.fresh(InferenceVarKind::Source))
            }
            None => self.solver.fresh(InferenceVarKind::Source),
        };
        // A callable returns `Result<ok, err>` -- so a bare `return v` is the `Ok`
        // payload and every error site reconciles to `err` -- when its body uses
        // `error(x)`/`expr!`, OR its declared return is already a `Result` (a `T!`
        // annotation, or an explicit Result). The latter makes a bare value unify
        // with `Result.Ok { value: v }` even when the body raises no error.
        // Only an explicit `error(...)` construction (or a `Result`-shaped
        // annotation) makes a body fallible here. A bare `expr!` does not: a
        // nullable-operand `!` returns null (a nullable, not a Result), the
        // entry `main` aborts, and a Result-operand `!` in an inferred-return
        // function is typed authoritatively by the infer pass -- forcing a
        // `Result` shape here from syntax alone would wrongly reject the
        // nullable cases.
        self.fallible = block_constructs_error(body) || is_result(&self.solver.resolve(&declared));
        tracing::debug!(context, fallible = self.fallible, "checking callable body");
        if self.fallible {
            let inferred = self.scoped_result(self.ok.clone(), self.err.clone());
            self.unify(&declared, &inferred, span);
            self.ret = inferred;
        } else {
            self.ret = declared;
        }
        self.infer_block(body);
        self.finalize_literals();
        // Discard this body's transient bindings (see the snapshot above); its
        // diagnostics are already recorded in `self.errors`.
        self.solver.rollback(body_snapshot);
    }

    // ----- environment -----

    fn bind_mono(&mut self, name: &str, ty: Type) {
        self.scopes
            .last_mut()
            .expect("a scope is open")
            .insert(name.to_string(), Scheme::mono(ty));
    }

    fn bind_scheme(&mut self, name: &str, scheme: Scheme) {
        self.scopes
            .last_mut()
            .expect("a scope is open")
            .insert(name.to_string(), scheme);
    }

    fn lookup(&self, name: &str) -> Option<&Scheme> {
        self.scopes.iter().rev().find_map(|s| s.get(name))
    }

    /// The inference variables free in the current environment; generalization
    /// must not quantify these (they are shared with bindings still in scope).
    fn env_free(&self) -> HashSet<u32> {
        let mut out = HashSet::default();
        for scope in &self.scopes {
            for scheme in scope.values() {
                // Only the non-quantified part of a scheme is "free" in the env.
                let quantified: HashSet<u32> = scheme.vars.iter().copied().collect();
                for v in self.solver.free_vars(&scheme.ty) {
                    if !quantified.contains(&v) {
                        out.insert(v);
                    }
                }
            }
        }
        out
    }

    /// Record a type error at `span`.
    fn error(&mut self, message: String, span: Span) {
        self.errors.push(TypeError { message, span });
    }

    /// Report a parameter name that appears twice in `params`.
    fn check_duplicate_params(&mut self, params: &[brass_parser::ast::Param], context: &str) {
        let mut seen = HashSet::default();
        for p in params {
            if !seen.insert(p.name.as_str()) {
                self.error(
                    format!("duplicate parameter `{}` in {context}", p.name),
                    p.span,
                );
            }
        }
    }

    /// Unify two types in a value-flow context, recording a type error on
    /// failure. Uses Brass's flow leniency (see [`Hm::flow_unify`]).
    fn unify(&mut self, a: &Type, b: &Type, span: Span) {
        if self.flow_unify(a, b) {
            return;
        }
        let ra = self.solver.resolve(a);
        let rb = self.solver.resolve(b);
        let message =
            self.solver.unify(&ra, &rb).err().unwrap_or_else(|| {
                format!("cannot unify `{}` with `{}`", ra.display(), rb.display())
            });
        self.errors.push(TypeError { message, span });
    }

    /// Unify with Brass's value-flow leniency, returning whether it
    /// succeeded. The rule itself is `brass_typesys::flow_unify`, shared
    /// with the JIT-time MIR checker so the two can never drift.
    fn flow_unify(&mut self, a: &Type, b: &Type) -> bool {
        brass_typesys::flow_unify(&mut self.solver, a, b)
    }

    /// Check that a value of type `have` may flow into a `want` position
    /// (assignment, argument, field, return). This is directional: HM flow
    /// unification first, then *structural subtyping* -- a wider record is usable
    /// where a narrower one is required, but not the reverse.
    fn flow_into(&mut self, have: &Type, want: &Type, span: Span) {
        if self.flow_unify(have, want) {
            return;
        }
        let h = self.solver.resolve(have);
        let w = self.solver.resolve(want);
        // A bracket literal with differing element types was classified a tuple
        // (`[4, null, 6]` -- plain values mixed with `null`), but it still flows
        // into a sequence position when every element flows into the element type
        // (`int32?[]` here): the sequence annotation re-checks the literal
        // element-wise, mirroring the other engine's bidirectional array rule.
        // Rolled back on failure so a genuine mismatch reports the original types.
        if let Type::Tuple(ts) = &h {
            let elem = match &w {
                Type::Slice(e) => Some((**e).clone()),
                Type::Array(e, n) if ts.len() == *n => Some((**e).clone()),
                _ => None,
            };
            if let Some(elem) = elem {
                let snap = self.solver.snapshot();
                if ts.iter().all(|t| self.flow_unify(t, &elem)) {
                    return;
                }
                self.solver.rollback(snap);
            }
        }
        // Automatic numeric conversion: a numeric value flows into a numeric
        // position of another type (int widths/signedness, int -> float). The
        // nullable wrapper on the *want* side is stripped (the converted value is
        // wrapped into the nullable), but a nullable value itself does not flow
        // into a non-nullable numeric position. float -> int stays explicit.
        if !matches!(h, Type::Nullable(_)) && numeric_flows_into(&h, &strip_nullable(w.clone())) {
            return;
        }
        // Unification failed; the value only flows if structural subtyping admits
        // it (a wider record into a narrower position). Trace this fallback: it is
        // where a too-permissive structural rule would let an unsound flow through.
        tracing::debug!(have = %h.display(), want = %w.display(), "flow_into falling back to structural subtyping");
        if crate::structural::types_compatible(self.program, &h, &w) {
            return;
        }
        let (h, w) = brass_hir::mismatch_display(&h, &w);
        self.errors.push(TypeError {
            message: format!("cannot use `{h}` where `{w}` is required"),
            span,
        });
    }

    /// Reconcile an error payload `t` with this function's error type, combining
    /// the two perspectives the design requires: first HM unification (`error(x)`
    /// at one type, a propagated `!` at the same type, etc. unify to one error
    /// type), then -- when the payloads are distinct record types that do not
    /// unify -- structural subtyping, accepting them when one error record is
    /// usable as the other. Truly unrelated error
    /// types are a type error.
    /// The `Result` the fallibility sugar builds in the current module's scope
    /// (see `Program::scoped_result_instance`). A shadow with the wrong shape
    /// falls back to the built-in Result silently here; the authoritative
    /// infer pass reports it.
    fn scoped_result(&self, ok: Type, err: Type) -> Type {
        self.program
            .scoped_result_instance(&self.module, &ok, &err)
            .unwrap_or_else(|_| Type::result(ok, err))
    }

    fn reconcile_err(&mut self, t: &Type, span: Span) {
        let err = self.err.clone();
        if self.flow_unify(t, &err) {
            return;
        }
        let have = self.solver.resolve(t);
        let want = self.solver.resolve(&err);
        if crate::structural::types_compatible(self.program, &have, &want)
            || crate::structural::types_compatible(self.program, &want, &have)
        {
            return;
        }
        self.errors.push(TypeError {
            message: format!(
                "incompatible error types `{}` and `{}`",
                have.display(),
                want.display()
            ),
            span,
        });
    }

    // ----- statements -----

    fn infer_block(&mut self, block: &Block) {
        self.scopes.push(HashMap::default());
        for stmt in &block.stmts {
            self.infer_stmt(stmt);
        }
        self.scopes.pop();
    }

    fn infer_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let { pat, ty, value, .. } => {
                // An annotation is the declared (authoritative) type: the value
                // must flow into it, and the binding takes the annotated type
                // (e.g. `let m: int32? = total` binds `m` at `int32?`, so later
                // uses see the nullable, not the promoted `int32` value). An
                // uninitialized `let` has no value; the annotation alone types
                // the binding (definite assignment guards the reads).
                let annot = ty.as_ref().and_then(|a| self.resolve_annotation(a));
                let bound_ty = match (value, annot) {
                    (Some(value), Some(annot_ty)) => {
                        let value_ty = self.infer_expr(value);
                        self.flow_into(&value_ty, &annot_ty, stmt.span());
                        annot_ty
                    }
                    (Some(value), None) => self.infer_expr(value),
                    // A `Self` annotation is resolved positionally by the infer
                    // pass; here it would read as a foreign nominal, so let the
                    // binding's uses pin a fresh variable instead.
                    (None, Some(_)) if matches!(ty.as_ref(), Some(brass_parser::ast::TypeExpr::Named(n, _)) if n == "Self") => {
                        self.solver.fresh(InferenceVarKind::Source)
                    }
                    (None, Some(annot_ty)) => annot_ty,
                    (None, None) => self.solver.fresh(InferenceVarKind::Source),
                };
                // A simple binding is generalized over variables not free in the
                // environment: the HM `let` rule that makes a bound closure
                // polymorphic. Destructuring patterns bind nothing here (the value
                // is still inferred above), staged with the other pattern forms.
                if let Pattern::Binding(name, _) = pat {
                    let env_free = self.env_free();
                    let scheme = self.solver.generalize(&env_free, &bound_ty);
                    self.bind_scheme(name, scheme);
                }
            }
            Stmt::Assign { target, value, .. } => {
                let t = self.infer_expr(target);
                let v = self.infer_expr(value);
                // The value flows into the target (rather than unifying with it),
                // admitting the automatic numeric conversions: `int64_t += int32_v`
                // widens the operand at the write-back, and a plain assignment
                // converts the same way. A compound target's own type is unchanged.
                self.flow_into(&v, &t, stmt.span());
            }
            Stmt::Expr(e) => {
                self.infer_expr(e);
            }
            Stmt::Return(Some(e), span) => {
                let t = self.infer_expr(e);
                // In a fallible function a bare value is the success payload
                // (auto-wrapped as `Ok { value }`); a `Result` value -- or a
                // declared sum subtype of the return's Result, which the flow
                // site coerces -- flows whole.
                let resolved_t = self.solver.resolve(&t);
                let whole = is_result(&resolved_t) || {
                    let ret = self.solver.resolve(&self.ret);
                    let ret_sum = match &ret {
                        Type::Nullable(inner) => inner.as_ref().clone(),
                        other => other.clone(),
                    };
                    matches!((&resolved_t, &ret_sum), (Type::Sum(h), Type::Sum(w))
                        if crate::structural::declares_sum_parent(self.program, h.id, w.id, 0))
                };
                if self.fallible && !whole {
                    let ok = self.ok.clone();
                    self.flow_into(&t, &ok, *span);
                } else {
                    // A forwarded Result's error is re-raised lifted into the
                    // prelude `Error` (the infer pass records the rebuild);
                    // flow the lifted shape so the error type reconciles.
                    let flowed = match &resolved_t {
                        Type::Sum(n) if n.is_result_type() => {
                            match n.substitution.get(brass_hir::types::RESULT_ERR_ERROR) {
                                Some(err) => {
                                    let lifted = crate::lift_err_payload(
                                        self.program,
                                        self.solver.resolve(err),
                                    );
                                    let mut n = n.clone();
                                    n.substitution
                                        .insert(brass_hir::types::RESULT_ERR_ERROR, lifted);
                                    Type::Sum(n)
                                }
                                None => t.clone(),
                            }
                        }
                        _ => t.clone(),
                    };
                    let ret = self.ret.clone();
                    self.flow_into(&flowed, &ret, *span);
                }
            }
            Stmt::Return(None, span) => {
                if !self.fallible {
                    let ret = self.ret.clone();
                    self.unify(&Type::Void, &ret, *span);
                }
            }
            Stmt::While { cond, body, .. } => {
                self.infer_expr(cond);
                self.infer_block(body);
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                // A fields-loop is expanded and fully checked per field by the
                // infer pass; its body does not type as ordinary code (the loop
                // variable changes meaning per position), so HM skips it.
                if brass_hir::fields_loop_target(stmt).is_some() {
                    return;
                }
                let iter_ty = self.infer_expr(iter);
                // The loop variable is the element type of a slice/array iterable
                // (seeing through reference/mutability wrappers, so iterating a
                // `ref(mut(T[]))` binds `ref(mut(T))` elements); otherwise leave it
                // open (permissive for unmodelled iterables).
                let elem = brass_hir::index_element(&self.solver.resolve(&iter_ty))
                    .unwrap_or_else(|| self.solver.fresh(InferenceVarKind::Source));
                self.scopes.push(HashMap::default());
                self.bind_pattern(pat, &elem);
                for stmt in &body.stmts {
                    self.infer_stmt(stmt);
                }
                self.scopes.pop();
            }
            Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }

    // ----- expressions -----

    fn infer_expr(&mut self, expr: &Expr) -> Type {
        match expr {
            Expr::Int(v, span) => self.literal_var(Type::Int(int_literal_kind(*v)), *span),
            Expr::Float(_, span) => self.literal_var(Type::Float(FloatKind::F64), *span),
            Expr::Bool(_, _) => Type::Bool,
            Expr::Str(segs, _) => {
                for seg in segs {
                    if let StrSeg::Expr(e) = seg {
                        self.infer_expr(e);
                    }
                }
                Type::Str
            }
            Expr::Null(_) => Type::Nullable(Box::new(self.solver.fresh(InferenceVarKind::Source))),
            Expr::Ident(name, _) => self.infer_ident(name),
            Expr::SelfExpr(span) => {
                // A closure may bind `self` as a parameter -- a closure-typed
                // field whose type names the enclosing type (`(self, T) -> U`) --
                // so resolve a `self` in scope before the method receiver.
                if let Some(scheme) = self.lookup("self").cloned() {
                    self.solver.instantiate(&scheme)
                } else {
                    match self.self_type.clone() {
                        Some(t) => t,
                        None => {
                            self.error("`self` is only valid inside a method".into(), *span);
                            self.solver.fresh(InferenceVarKind::Source)
                        }
                    }
                }
            }
            Expr::Unary(op, e, span) => self.infer_unary(*op, e, *span),
            Expr::Binary(op, a, b, span) => self.infer_binary(*op, a, b, *span),
            Expr::Call(callee, args, span) => self.infer_call(callee, args, *span),
            Expr::Closure(params, body, _) => {
                self.check_duplicate_params(params, "closure");
                self.scopes.push(HashMap::default());
                let param_tys: Vec<Type> = params
                    .iter()
                    .map(|p| {
                        let ty = self
                            .resolve_annotation_opt(&p.ty)
                            .unwrap_or_else(|| self.solver.fresh(InferenceVarKind::Source));
                        self.bind_mono(&p.name, ty.clone());
                        ty
                    })
                    .collect();
                // The closure has its own return type: a `return` in its body must
                // bind the closure's result, not the enclosing function's. Swap in
                // a fresh return var for the duration of the body -- and its own
                // fallibility: inside a fallible FUNCTION, a closure's bare
                // `return v` is the closure's result, not the function's Ok
                // payload (leaving the flag set unified a closure's `return 41`
                // with the enclosing `-> T!`'s ok type T). The ok/err slots are
                // swapped alongside so an error site inside the closure cannot
                // reconcile against the enclosing callable's payloads either.
                let saved_ret =
                    std::mem::replace(&mut self.ret, self.solver.fresh(InferenceVarKind::Source));
                let saved_fallible = std::mem::replace(&mut self.fallible, false);
                let saved_ok =
                    std::mem::replace(&mut self.ok, self.solver.fresh(InferenceVarKind::Source));
                let saved_err =
                    std::mem::replace(&mut self.err, self.solver.fresh(InferenceVarKind::Source));
                let cret = self.ret.clone();
                match body.as_ref() {
                    // A block body returns via `return` (binding `cret`); a
                    // trailing expression value, if any, is also the result.
                    Expr::Block(block, _) => {
                        let val = self.infer_block_value(block);
                        // A void tail has no value; a `Never` tail (the block
                        // ends in `return`) already bound the ret via the
                        // return statement itself.
                        if !matches!(self.solver.resolve(&val), Type::Void | Type::Never) {
                            self.unify(&val, &cret, body.span());
                        }
                    }
                    // An expression-bodied closure returns that expression.
                    _ => {
                        let val = self.infer_expr(body);
                        self.unify(&val, &cret, body.span());
                    }
                }
                self.ret = saved_ret;
                self.fallible = saved_fallible;
                self.ok = saved_ok;
                self.err = saved_err;
                self.scopes.pop();
                Type::Fun(param_tys, Box::new(cret))
            }
            Expr::Array(elems, _) => {
                let elem_tys: Vec<Type> = elems.iter().map(|e| self.infer_expr(e)).collect();
                // A bracket literal whose elements are all concrete and not all the
                // same type is a fixed-length tuple; otherwise it is an array whose
                // single element type is the unification of the elements (the empty
                // and homogeneous cases, and any element still being inferred).
                // A `null` element never forces a tuple: null unifies with any
                // element type, and its presence makes the element nullable.
                if let Some(tuple) = self.tuple_of_elements(elems, &elem_tys) {
                    Type::Tuple(tuple)
                } else {
                    let elem = self.solver.fresh(InferenceVarKind::EmptyArrayElem);
                    let mut saw_null = false;
                    for (t, e) in elem_tys.iter().zip(elems) {
                        if matches!(e, Expr::Null(_)) {
                            saw_null = true;
                            continue;
                        }
                        self.unify(&elem, t, e.span());
                    }
                    if saw_null && !matches!(self.solver.resolve(&elem), Type::Nullable(_)) {
                        Type::Slice(Box::new(Type::Nullable(Box::new(elem))))
                    } else {
                        Type::Slice(Box::new(elem))
                    }
                }
            }
            Expr::Range(lo, hi, span) => {
                // `[lo..hi]` builds an array whose element type is the bounds'
                // common integer type, mirroring the full check's range rule: a
                // literal bound adapts to the other bound's width (`[0..a.len()]`
                // is `int64[]`), two typed bounds meet at their common type
                // without unifying (each widens at the flow point), and anything
                // else shares one bound type as before.
                let lo_ty = self.infer_expr(lo);
                let hi_ty = self.infer_expr(hi);
                let (rl, rh) = (self.solver.resolve(&lo_ty), self.solver.resolve(&hi_ty));
                let (ll, lh) = (self.lit_default(&rl), self.lit_default(&rh));
                match (&rl, &rh) {
                    (Type::Unknown(_), Type::Int(_)) if ll.is_some() => {
                        self.unify(&lo_ty, &rh, lo.span());
                        Type::Slice(Box::new(rh))
                    }
                    (Type::Int(_), Type::Unknown(_)) if lh.is_some() => {
                        self.unify(&hi_ty, &rl, hi.span());
                        Type::Slice(Box::new(rl))
                    }
                    (Type::Int(_), Type::Int(_)) => {
                        match brass_typesys::common_numeric_type(&rl, &rh) {
                            Some(c) => Type::Slice(Box::new(c)),
                            None => {
                                self.unify(&lo_ty, &hi_ty, *span);
                                Type::Slice(Box::new(rl))
                            }
                        }
                    }
                    _ => {
                        let int_v = self.literal_var(Type::Int(IntKind::I32), *span);
                        self.unify(&lo_ty, &int_v, lo.span());
                        self.unify(&hi_ty, &int_v, hi.span());
                        Type::Slice(Box::new(int_v))
                    }
                }
            }
            Expr::If(cond, then, els, span) => {
                // A condition may be a bool or a nullable (truthy = non-null), so
                // it is inferred but not constrained to `bool`.
                self.infer_expr(cond);
                let then_ty = self.infer_block_value(then);
                match els {
                    Some(e) => {
                        let else_ty = self.infer_expr(e);
                        self.join_branches(then_ty, else_ty, *span)
                    }
                    None => Type::Void,
                }
            }
            Expr::Block(block, _) => self.infer_block_value(block),
            // Record field access yields the field's declared type. A field on a
            // value whose type is not a known record stays open (a builtin like
            // `int32.from` is a `Field` on a type *name*); a field on a concrete
            // primitive, or a missing record field, is an error.
            Expr::Field(base, field, span) => {
                let bt = self.infer_expr(base);
                // Mode wrappers (`ref`/`mut`/`const`) expose the underlying
                // value's fields; peeling keeps a `ref(mut(T))` base from
                // falling to the permissive arm and skipping the field check.
                let resolved = brass_hir::peel_modes(&self.solver.resolve(&bt)).clone();
                match &resolved {
                    // A known record/sum: the field must exist (a sum field must
                    // be common to all variants). A built-in/unknown nominal (e.g.
                    // `Result`, matched not field-accessed) stays open.
                    Type::Record(_) | Type::Sum(_) if self.type_def(&resolved).is_some() => {
                        // An uncalled DECLARED METHOD is the compile-time
                        // presence value: the method's own name, a truthy
                        // string; a name a sum carries nowhere is the null
                        // presence value (see `Program::member_presence`).
                        if let Some(present) = self.program.member_presence(&resolved, field) {
                            return if present { Type::Str } else { Type::null() };
                        }
                        match self.record_field_type(&resolved, field) {
                            // An unannotated (dynamic) field has no single static
                            // type shared across values; give each access a fresh
                            // open variable so this principled pass does not couple
                            // independent uses. The `infer` pass checks dynamic
                            // fields per value through the nominal substitution.
                            Some(ty) if ty.is_unknown() => {
                                self.solver.fresh(InferenceVarKind::Source)
                            }
                            // A field written over the declaration's type SLOTS
                            // (`items: Self.item[]`) is per-instance the same way:
                            // each access instantiates the slot variables fresh so
                            // independent values are not coupled through the
                            // declaration; the `infer` pass checks per value.
                            Some(ty) => {
                                let slot_vars: Vec<u32> = self
                                    .type_def(&resolved)
                                    .map(|info| info.slots.iter().map(|(_, v)| *v).collect())
                                    .unwrap_or_default();
                                let slot_map: BTreeMap<u32, Type> = slot_vars
                                    .into_iter()
                                    .map(|v| (v, self.solver.fresh(InferenceVarKind::Source)))
                                    .collect();
                                brass_hir::substitute_vars(&ty, &slot_map)
                            }
                            // Accessing a field a structure does not have is not an
                            // error: the access is an inference failure -- typed as
                            // the always-null `never?`, so an `if` on it is
                            // statically false (its then-branch is pruned) and using
                            // it as a non-null value is still rejected. A sum's
                            // non-common field still errors (a real variant mistake).
                            None if matches!(resolved, Type::Record(_)) => Type::null(),
                            None => {
                                self.error(
                                    format!("`{}` has no field `{}`", resolved.display(), field),
                                    *span,
                                );
                                self.solver.fresh(InferenceVarKind::Source)
                            }
                        }
                    }
                    // A concrete primitive has no fields; an uncalled member on
                    // one is the compile-time presence value -- the method's
                    // own name (truthy) or the null absence (falsy). Presence
                    // always answers for a primitive class, so this never
                    // hard-errors.
                    Type::Int(_) | Type::Float(_) | Type::Bool | Type::Str => {
                        match self.program.member_presence(&resolved, field) {
                            Some(true) => Type::Str,
                            Some(false) => Type::null(),
                            None => {
                                self.error(
                                    format!("`{}` has no field `{}`", resolved.display(), field),
                                    *span,
                                );
                                self.solver.fresh(InferenceVarKind::Source)
                            }
                        }
                    }
                    _ => self.solver.fresh(InferenceVarKind::Source),
                }
            }
            // Indexing a slice/array yields its element type; the index is an int.
            // Indexing a concrete scalar (not a collection) is an error.
            Expr::Index(base, idx, span) => {
                let bt = self.infer_expr(base);
                let resolved = self.solver.resolve(&bt);
                // A tuple is indexed by a constant literal, yielding the element
                // type at that position (the only way to read a heterogeneous tuple).
                if let Type::Tuple(elems) = &resolved {
                    let _ = self.infer_expr(idx);
                    match const_index(idx) {
                        Some(k) if (k as usize) < elems.len() => elems[k as usize].clone(),
                        Some(k) => {
                            self.error(
                                format!(
                                    "tuple index {k} out of bounds for `{}`",
                                    resolved.display()
                                ),
                                *span,
                            );
                            self.solver.fresh(InferenceVarKind::Source)
                        }
                        None => {
                            self.error(
                                "a tuple can only be indexed by a constant integer".into(),
                                *span,
                            );
                            self.solver.fresh(InferenceVarKind::Source)
                        }
                    }
                } else {
                    // Any integer width indexes (the int -> int flow rule); only
                    // an open index is pinned to the default index type, and a
                    // concrete non-integer is an error. A strict `int64` unify
                    // here would reject an `int32` index that the flow rules --
                    // and the top-level path -- accept.
                    let it = self.infer_expr(idx);
                    match self.solver.resolve(&it) {
                        Type::Int(_) => {}
                        Type::Unknown(_) => {
                            self.unify(&it, &Type::Int(brass_hir::IntKind::I64), *span)
                        }
                        other => self.error(
                            format!(
                                "cannot index with `{}`; an integer is required",
                                other.display()
                            ),
                            *span,
                        ),
                    }
                    match brass_hir::index_element(&resolved) {
                        Some(elem) => elem,
                        None => {
                            if matches!(
                                resolved,
                                Type::Int(_) | Type::Float(_) | Type::Bool | Type::Void
                            ) {
                                self.error(
                                    format!("`{}` cannot be indexed", resolved.display()),
                                    *span,
                                );
                            }
                            self.solver.fresh(InferenceVarKind::Source)
                        }
                    }
                }
            }
            // `expr!`: the operand is a `Result<o, e>`; the operator yields `o`
            // and propagates `e` into this function's error type. A NULLABLE
            // operand unwraps instead: the null case propagates as the
            // payload-less `Result.Null`, constraining no error type.
            Expr::ErrorProp(e, span) => {
                let et = self.infer_expr(e);
                let resolved = self.solver.resolve(&et);
                if let Type::Nullable(inner) = resolved {
                    return *inner;
                }
                // Operand-driven when the Result is already known: `!` unwraps
                // whatever Result declaration the operand carries (a scope's
                // shadow included), so no constructed nominal is forced on it.
                if let Type::Sum(n) = &resolved
                    && let Some((ok, err)) = n.result_payloads()
                {
                    let (ok, err) = (ok.clone(), err.clone());
                    let err = crate::lift_err_payload(self.program, self.solver.resolve(&err));
                    self.reconcile_err(&err, *span);
                    return ok;
                }
                // A declared subtype of the Result in scope unwraps like a
                // Result: its own payload slots reconcile and yield (the
                // infer pass records the coercion the flow needs).
                if let Type::Sum(h) = &resolved {
                    let scoped = self.scoped_result(Type::Void, Type::Void);
                    if let Type::Sum(w) = &scoped
                        && h.id != w.id
                        && crate::structural::declares_sum_parent(self.program, h.id, w.id, 0)
                    {
                        // The propagated payload lifts like a plain Result's
                        // (the infer pass records the rebuild), so the shared
                        // err var must see the lifted type, not the raw one.
                        let err = crate::structural::sum_field_payload(
                            self.program,
                            h,
                            brass_hir::types::RESULT_ERR_ERROR,
                        )
                        .map(|e| crate::lift_err_payload(self.program, self.solver.resolve(&e)))
                        .unwrap_or_else(|| self.solver.fresh(InferenceVarKind::Source));
                        self.reconcile_err(&err, *span);
                        return crate::structural::sum_field_payload(
                            self.program,
                            h,
                            brass_hir::types::RESULT_OK_VALUE,
                        )
                        .unwrap_or_else(|| self.solver.fresh(InferenceVarKind::Source));
                    }
                }
                let o = self.solver.fresh(InferenceVarKind::Source);
                let e_err = self.solver.fresh(InferenceVarKind::Source);
                let res = self.scoped_result(o.clone(), e_err.clone());
                self.unify(&et, &res, *span);
                self.reconcile_err(&e_err, *span);
                o
            }
            // Record construction `Name { f: v, .. }`: each field value must match
            // the declared field type; the result is that record type.
            Expr::TypeLit(name, fields, span) if name.is_empty() => {
                // Anonymous structure literal `{ f: v, ... }`: a structural record
                // whose field types are the field value types.
                let field_tys: Vec<(String, Type)> = fields
                    .iter()
                    .map(|(fname, e)| (fname.clone(), self.infer_expr(e)))
                    .collect();
                brass_hir::structural_record(field_tys)
            }
            Expr::TypeLit(name, fields, span) => {
                let record = self.named_type(name);
                // The declaration's type SLOTS are per-instance parameters:
                // this literal's fields are constrained against its own
                // instantiation of them (one variable per slot for the whole
                // literal), never the declaration's shared slot variables --
                // through those, the first literal's field values would pin
                // every other literal's slots program-wide.
                let slot_vars: Vec<u32> = record
                    .as_ref()
                    .and_then(|r| self.type_def(r))
                    .map(|info| info.slots.iter().map(|(_, v)| *v).collect())
                    .unwrap_or_default();
                let slot_map: BTreeMap<u32, Type> = slot_vars
                    .into_iter()
                    .map(|v| (v, self.solver.fresh(InferenceVarKind::Source)))
                    .collect();
                for (fname, e) in fields {
                    let vt = self.infer_expr(e);
                    // An unannotated field accepts any value (its type is per-value,
                    // recorded in the substitution by the `infer` pass); only an
                    // annotated field constrains the value here.
                    if let Some(rec) = &record
                        && let Some(fty) = self.record_field_type(rec, fname)
                        && !fty.is_unknown()
                    {
                        let fty = brass_hir::substitute_vars(&fty, &slot_map);
                        self.flow_into(&vt, &fty, *span);
                    }
                }
                record.unwrap_or_else(|| self.solver.fresh(InferenceVarKind::Source))
            }
            // Sum-variant construction `Sum.Variant { f: v }`.
            Expr::VariantLit(name, variant, fields, span) => {
                let sum = self.named_type(name);
                for (fname, e) in fields {
                    let vt = self.infer_expr(e);
                    if let Some(s) = &sum
                        && let Some(fty) = self.variant_field_type(s, variant, fname)
                        && !fty.is_unknown()
                    {
                        self.flow_into(&vt, &fty, *span);
                    }
                }
                sum.unwrap_or_else(|| self.solver.fresh(InferenceVarKind::Source))
            }
            // `match`: every arm's body must agree on one result type, and each
            // arm's pattern is checked/bound against the scrutinee type.
            Expr::Match(scrut, arms, span) => {
                let st = self.infer_expr(scrut);
                let result = self.solver.fresh(InferenceVarKind::Source);
                for arm in arms {
                    self.scopes.push(HashMap::default());
                    self.bind_pattern(&arm.pattern, &st);
                    let body = self.infer_expr(&arm.body);
                    self.scopes.pop();
                    // A diverged arm (it always returns/propagates) constrains
                    // nothing; the value arms agree among themselves.
                    if !matches!(self.solver.resolve(&body), Type::Never) {
                        self.unify(&body, &result, *span);
                    }
                }
                result
            }
            // `if let pat = scrut { .. } else { .. }`: bind the pattern in the
            // then-branch; the branches agree on the value type.
            Expr::IfLet(pat, scrut, then, els, span) => {
                let st = self.infer_expr(scrut);
                self.scopes.push(HashMap::default());
                // A plain binding on a nullable scrutinee narrows to the non-null
                // type on the then-arm (the value is proven present).
                let bind_ty = match (pat, &self.solver.resolve(&st)) {
                    (Pattern::Binding(_, _), Type::Nullable(inner)) => (**inner).clone(),
                    _ => st.clone(),
                };
                self.bind_pattern(pat, &bind_ty);
                let then_ty = self.infer_block_value(then);
                self.scopes.pop();
                match els {
                    Some(e) => {
                        let else_ty = self.infer_expr(e);
                        self.join_branches(then_ty, else_ty, *span)
                    }
                    None => Type::Void,
                }
            }
        }
    }

    /// A numeric literal: a fresh variable recorded for finalization so context
    /// can still choose its exact kind (e.g. `let x: int64 = 5`). `default` is
    /// the type an unconstrained literal falls back to.
    /// The default numeric type of an unresolved literal variable (`0.5` ->
    /// `float64`, `1` -> its magnitude-chosen int kind), or `None` when `ty` is
    /// not one. Lets the binary-operator rules probe a literal at its own
    /// numeric class instead of unifying it into the other operand's -- which
    /// would pin `a + 0.5` to `int32` and reject the float literal.
    fn lit_default(&self, ty: &Type) -> Option<Type> {
        match ty {
            Type::Unknown(id) => self
                .lit_vars
                .iter()
                .find(|(v, _, _)| v == id)
                .map(|(_, d, _)| d.clone()),
            _ => None,
        }
    }

    fn literal_var(&mut self, default: Type, span: Span) -> Type {
        let ty = self.solver.fresh(InferenceVarKind::Source);
        if let Type::Unknown(id) = ty {
            self.lit_vars.push((id, default, span));
        }
        ty
    }

    fn infer_ident(&mut self, name: &str) -> Type {
        if let Some(scheme) = self.lookup(name).cloned() {
            return self.solver.instantiate(&scheme);
        }
        if let Some(symbol) = self.program.resolve_fn_symbol(&self.module, name)
            && let Some(scheme) = self.globals.get(&symbol).cloned()
        {
            return self.solver.instantiate(&scheme);
        }
        // A builtin, stdlib symbol, or type name: leave open (permissive).
        self.solver.fresh(InferenceVarKind::Source)
    }

    fn infer_unary(&mut self, op: UnaryOp, e: &Expr, _span: Span) -> Type {
        let t = self.infer_expr(e);
        match op {
            UnaryOp::Not => Type::Bool,
            UnaryOp::Neg | UnaryOp::BitNot => t,
        }
    }

    fn infer_binary(&mut self, op: BinOp, a: &Expr, b: &Expr, span: Span) -> Type {
        let ta = self.infer_expr(a);
        let tb = self.infer_expr(b);
        match op {
            // Logical connectives take and produce booleans.
            BinOp::And | BinOp::Or => {
                self.unify(&ta, &Type::Bool, a.span());
                self.unify(&tb, &Type::Bool, b.span());
                Type::Bool
            }
            // Comparisons yield a bool. Two operands of differing numeric types are
            // compared via their common type (no unification); otherwise they must
            // unify (same type, or a literal adapting to the other).
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                let (ra, rb) = (self.solver.resolve(&ta), self.solver.resolve(&tb));
                // An unresolved literal probes at its own default class, so
                // `a < 0.5` with an int `a` compares via the common float type
                // instead of pinning the literal to `a`'s int kind.
                let (pa, pb) = (
                    self.lit_default(&ra).unwrap_or_else(|| ra.clone()),
                    self.lit_default(&rb).unwrap_or_else(|| rb.clone()),
                );
                if brass_typesys::common_numeric_type(&pa, &pb).is_none() {
                    self.unify(&ta, &tb, span);
                }
                Type::Bool
            }
            // Arithmetic and bitwise operators relate two operands and return their
            // type. Differing numeric operands implicitly convert to a common type;
            // otherwise the operands unify (same type, a literal adapting, or two
            // `Str` for `+` concatenation).
            _ => {
                let (ra, rb) = (self.solver.resolve(&ta), self.solver.resolve(&tb));
                // As with comparisons: a literal probes at its own default, so
                // int+float mixes convert regardless of which side is the
                // literal. The literal variable is pinned to its default (not
                // the common type): the value keeps its own class and only the
                // RESULT is the common type, exactly like two typed operands.
                let (pa, pb) = (
                    self.lit_default(&ra).unwrap_or_else(|| ra.clone()),
                    self.lit_default(&rb).unwrap_or_else(|| rb.clone()),
                );
                match brass_typesys::common_numeric_type(&pa, &pb) {
                    Some(common) => {
                        if self.lit_default(&ra).is_some() {
                            self.unify(&ta, &pa, a.span());
                        }
                        if self.lit_default(&rb).is_some() {
                            self.unify(&tb, &pb, b.span());
                        }
                        common
                    }
                    None => {
                        self.unify(&ta, &tb, span);
                        ta
                    }
                }
            }
        }
    }

    /// A built-in numeric/string conversion call, type-checked against its fixed
    /// source contract: `string.from(x)` accepts any value and
    /// yields a string; `intN.from`/`floatN.from` take a numeric value; `intN.parse`
    /// /`floatN.parse` take a string. `intN.from`/`.parse` are fallible (a narrowing
    /// or parse can fail) so they yield `Result<intN, string>`; `floatN.from` is a
    /// total widening (`floatN`), `floatN.parse` fallible. Returns `None` if
    /// `type_name.method` is not a recognized conversion (so a user static method
    /// of the same shape still resolves normally).
    fn conversion_call(
        &mut self,
        type_name: &str,
        method: &str,
        args: &[brass_parser::ast::Arg],
        span: Span,
    ) -> Option<Type> {
        // `T.from(v)` for a record type `T`: a *fallible* structural conversion. The
        // result is `T?` -- whether the value actually has every field `T` declares
        // is decided per monomorphized argument type (it yields the record when the
        // concrete argument has the fields, else null), so the front end does not
        // reject a value missing a field: the caller narrows the nullable (an
        // `if`/`if let`) and handles the failure. (Numeric/string `from` is below.)
        if method == "from" {
            let target = self
                .program
                .resolve_type(&self.module, type_name)
                .and_then(|info| match &info.kind {
                    TypeKind::Record { .. } => Some(info.type_ref()),
                    _ => None,
                });
            if let Some(ty) = target {
                if let Some(arg) = args.first() {
                    self.infer_expr(&arg.expr);
                }
                return Some(Type::Nullable(Box::new(ty)));
            }
        }
        let int_kind = IntKind::from_name(type_name);
        let float_kind = match type_name {
            "float32" => Some(FloatKind::F32),
            "float64" => Some(FloatKind::F64),
            _ => None,
        };
        let numeric = int_kind.is_some() || float_kind.is_some();
        let recognized = (type_name == "string" && method == "from")
            || (numeric && matches!(method, "from" | "parse"));
        if !recognized {
            return None;
        }
        // Infer the (single) argument; conversions are unary.
        let arg_ty = args.first().map(|a| self.infer_expr(&a.expr));
        if type_name == "string" {
            return Some(Type::Str);
        }
        let resolved = arg_ty
            .map(|t| self.solver.resolve(&t))
            .unwrap_or(Type::Void);
        // An unknown argument is deferred to the runtime; a concrete one of the
        // wrong value class is an error.
        match method {
            "parse" if !matches!(resolved, Type::Str | Type::Unknown(_)) => self.error(
                format!(
                    "`{type_name}.parse` expects a string, found `{}`",
                    resolved.display()
                ),
                span,
            ),
            "from" if !matches!(resolved, Type::Int(_) | Type::Float(_) | Type::Unknown(_)) => self
                .error(
                    format!(
                        "`{type_name}.from` expects a numeric value, found `{}`",
                        resolved.display()
                    ),
                    span,
                ),
            _ => {}
        }
        Some(match (int_kind, float_kind) {
            (Some(k), _) => Type::result(Type::Int(k), Type::Str),
            (_, Some(k)) if method == "from" => Type::Float(k),
            (_, Some(k)) => Type::result(Type::Float(k), Type::Str),
            _ => unreachable!("numeric conversion has an int or float kind"),
        })
    }

    /// A built-in `_string_*` primitive: check its arity and its
    /// string-typed arguments (leniently -- a still-unknown argument defers to the
    /// runtime, as the conversions do, so a polymorphic caller like
    /// `contains(coll, x)` passing fresh variables is not wrongly constrained),
    /// and yield its result type. The non-string (index/bytes) arguments are left
    /// to the runtime. Returns `None` if `name` is not a string builtin.
    fn string_builtin_call(
        &mut self,
        name: &str,
        args: &[brass_parser::ast::Arg],
        span: Span,
    ) -> Option<Type> {
        let str_t = Type::Str;
        let i64_t = Type::Int(IntKind::I64);
        let bytes_t = Type::Slice(Box::new(Type::Int(IntKind::U8)));
        let (params, ret): (Vec<Type>, Type) = match name {
            "_string_concat" => (vec![str_t.clone(), str_t.clone()], str_t.clone()),
            "_string_slice" => (
                vec![str_t.clone(), i64_t.clone(), i64_t.clone()],
                str_t.clone(),
            ),
            "_string_char_at" => (vec![str_t.clone(), i64_t], str_t.clone()),
            "_string_cmp" => (vec![str_t.clone(), str_t.clone()], Type::Int(IntKind::I32)),
            "_string_find" => (
                vec![str_t.clone(), str_t.clone()],
                Type::Nullable(Box::new(Type::Int(IntKind::I64))),
            ),
            "_string_bytes" => (vec![str_t.clone()], bytes_t),
            "_string_from_bytes" => (vec![bytes_t], Type::result(str_t.clone(), str_t)),
            _ => return None,
        };
        let arg_tys: Vec<Type> = args.iter().map(|a| self.infer_expr(&a.expr)).collect();
        if arg_tys.len() != params.len() {
            self.error(
                format!(
                    "`{name}` expects {} argument(s), found {}",
                    params.len(),
                    arg_tys.len()
                ),
                span,
            );
        }
        for (at, want) in arg_tys.iter().zip(&params) {
            // Only the string-typed positions are enforced; a concrete non-string
            // there is an error, an unknown defers.
            if matches!(want, Type::Str) {
                let resolved = self.solver.resolve(at);
                if !matches!(resolved, Type::Str | Type::Unknown(_)) {
                    self.error(
                        format!("`{name}` expects a string, found `{}`", resolved.display()),
                        span,
                    );
                }
            }
        }
        Some(ret)
    }

    fn infer_call(&mut self, callee: &Expr, args: &[brass_parser::ast::Arg], span: Span) -> Type {
        if let Expr::Ident(name, _) = callee {
            // Mirror the infer pass's `error(x)` typing: the Err is the
            // prelude Error record wrapping the argument, the Ok is fresh per
            // call, and the Error reconciles into this function's error type.
            if name == "error" {
                let value_ty = args
                    .first()
                    .map(|a| self.infer_expr(&a.expr))
                    .unwrap_or(Type::Void);
                for a in args.iter().skip(1) {
                    self.infer_expr(&a.expr);
                }
                // A program without the prelude (unit tests, embedders) keeps
                // the legacy raw payload.
                let err = match self.program.types.get("Error") {
                    Some(err_info) => {
                        let mut err = brass_hir::NominalType::new(err_info.id, &err_info.name);
                        err.substitution
                            .insert("value", self.solver.resolve(&value_ty));
                        Type::Record(err)
                    }
                    None => self.solver.resolve(&value_ty),
                };
                self.reconcile_err(&err, span);
                let ok = self.solver.fresh(InferenceVarKind::Source);
                // The call's type carries this function's SHARED error
                // variable (reconciled just above), so a `return error(..)`
                // unifies with the inferred fallible return trivially.
                return Type::result(ok, self.err.clone());
            }
            // Built-in `_string_*` primitives have fixed string-argument contracts.
            if let Some(ret) = self.string_builtin_call(name, args, span) {
                return ret;
            }
        }
        // Method call `recv.method(args)`: check arguments against the method's
        // signature on the receiver's type, and yield its return type. An unknown
        // method (a builtin like `arr.push`, or a UFCS free function) stays open.
        if let Expr::Field(base, method, _) = callee {
            // Built-in numeric/string conversions `Type.from(x)` / `Type.parse(s)`
            // are calls on a primitive type *name*, with fixed source-value
            // contracts. Recognize them before the user-method
            // path so their argument class is checked.
            if let Expr::Ident(type_name, _) = base.as_ref()
                && let Some(ret) = self.conversion_call(type_name, method, args, span)
            {
                return ret;
            }
            let recv = self.infer_expr(base);
            let arg_tys: Vec<Type> = args.iter().map(|a| self.infer_expr(&a.expr)).collect();
            if let Some((params, ret)) = self.method_sig(&recv, method) {
                for (p, a) in params.iter().zip(&arg_tys) {
                    if let Some(pty) = p {
                        self.flow_into(a, pty, span);
                    }
                }
                // The method's declared return may carry the shared INFER_VAR
                // sentinel (a `T!` open error payload). Freshen it so this call
                // gets its own error variable -- otherwise every `T!` method call
                // in the program aliases one error var and their payloads collide.
                return match ret {
                    Some(t) => brass_hir::freshen_infer(t, &mut || {
                        self.solver.fresh(InferenceVarKind::Source)
                    }),
                    None => self.solver.fresh(InferenceVarKind::Source),
                };
            }
            return self.solver.fresh(InferenceVarKind::Source);
        }
        let callee_ty = self.infer_expr(callee);
        let arg_tys: Vec<Type> = args.iter().map(|a| self.infer_expr(&a.expr)).collect();
        match self.solver.resolve(&callee_ty) {
            // The supplied arguments match, or omit only a trailing run of nullable
            // parameters (each defaults to `null`).
            Type::Fun(params, ret)
                if arg_tys.len() <= params.len()
                    && params[arg_tys.len()..]
                        .iter()
                        .all(|p| matches!(p, Type::Nullable(_))) =>
            {
                // Each argument flows into its parameter individually (directional,
                // structural-subtyping-aware) -- whole-`Fun` unification would be
                // invariant and reject a valid record-superset argument.
                for (p, a) in params.iter().zip(&arg_tys) {
                    self.flow_into(a, p, span);
                }
                *ret
            }
            Type::Fun(params, ret) => {
                // A call may omit a trailing `Location` parameter (the
                // implicit caller-location MIR fills in).
                if params.len() == arg_tys.len() + 1
                    && matches!(params.last(), Some(Type::Record(n)) if n.is_name("Location"))
                {
                    for (p, a) in params.iter().zip(&arg_tys) {
                        self.flow_into(a, p, span);
                    }
                    return *ret;
                }
                self.errors.push(TypeError {
                    message: format!(
                        "expected {} argument(s), found {}",
                        params.len(),
                        arg_tys.len()
                    ),
                    span,
                });
                *ret
            }
            // An unmodelled/permissive callee (a fresh var, a method, a builtin):
            // leave the result open rather than forcing a shape.
            _ => self.solver.fresh(InferenceVarKind::Source),
        }
    }

    /// Infer the value of a block: the trailing statement's type if it is a bare
    /// expression, otherwise `void`. Used for `if`/block expressions.
    ///
    /// A block that LEAVES produces no value at all, so its type is `Never`, which
    /// [`Self::join_branches`] absorbs -- the branch that bails out must not force
    /// the other to `void` (`if { return 1 } else { error("x")! }`). Every way out
    /// counts: `return`, and `break`/`continue` (`if even { x } else { continue }`
    /// used to fail as "cannot unify `int32` with `void`"). So does a trailing
    /// expression that itself diverges, such as a `match` whose every arm returns.
    /// And divergence anywhere in the block counts, not just in its last statement:
    /// whatever follows a `return` is unreachable, so the block still yields
    /// nothing.
    fn infer_block_value(&mut self, block: &Block) -> Type {
        self.scopes.push(HashMap::default());
        let mut value = Type::Void;
        let mut diverges = false;
        for (i, stmt) in block.stmts.iter().enumerate() {
            if i + 1 == block.stmts.len()
                && let Stmt::Expr(e) = stmt
            {
                value = self.infer_expr(e);
                diverges |= matches!(self.solver.resolve(&value), Type::Never);
                continue;
            }
            diverges |= matches!(stmt, Stmt::Return(..) | Stmt::Break(_) | Stmt::Continue(_));
            self.infer_stmt(stmt);
        }
        self.scopes.pop();
        if diverges {
            return Type::Never;
        }
        value
    }

    /// Join two branch values: a diverged branch (`Never` -- it always
    /// returns or propagates) is absorbed by the other; otherwise the
    /// branches must unify.
    fn join_branches(&mut self, then_ty: Type, else_ty: Type, span: Span) -> Type {
        let t = self.solver.resolve(&then_ty);
        let e = self.solver.resolve(&else_ty);
        match (matches!(t, Type::Never), matches!(e, Type::Never)) {
            (true, _) => else_ty,
            (_, true) => then_ty,
            _ => {
                self.unify(&then_ty, &else_ty, span);
                then_ty
            }
        }
    }

    // ----- annotations -----

    fn resolve_annotation_opt(
        &mut self,
        annot: &Option<brass_parser::ast::TypeExpr>,
    ) -> Option<Type> {
        let annot = annot.as_ref()?;
        self.resolve_annotation(annot)
    }

    fn resolve_annotation(&mut self, annot: &brass_parser::ast::TypeExpr) -> Option<Type> {
        let module = self.module.clone();
        let resolved = brass_hir::resolve(annot, |name| {
            self.program.resolve_type(&module, name).map(|t| {
                if t.is_sum() {
                    brass_hir::NominalInfo::sum(t.id)
                } else {
                    brass_hir::NominalInfo::record(t.id)
                }
            })
        })
        .ok()?;
        // `infer` / `T!` left `INFER_VAR` placeholders; mint a fresh solver variable
        // for each so they participate in inference like an unannotated position.
        Some(brass_hir::freshen_infer(resolved, &mut || {
            self.solver.fresh(InferenceVarKind::Source)
        }))
    }

    // ----- type definitions (records, sums, methods) -----

    /// The program type definition `ty` resolves to (a record or sum), if any.
    /// Mode wrappers are peeled so a `ref`/`mut`/`const` view of a record still
    /// resolves to its declaration (member checks must not go silent through a
    /// wrapper).
    fn type_def(&self, ty: &Type) -> Option<&TypeInfo> {
        match brass_hir::peel_modes(&self.solver.resolve(ty)) {
            Type::Record(n) | Type::Sum(n) => self.program.type_by_id(n.id),
            _ => None,
        }
    }

    /// The declared type of `field` accessed on `ty` (cloned), if known. For a
    /// record this is the named field; for a sum it is a field common to *every*
    /// variant (common-field access) -- `None` if any variant
    /// lacks it.
    fn record_field_type(&self, ty: &Type, field: &str) -> Option<Type> {
        match &self.type_def(ty)?.kind {
            TypeKind::Record { fields, .. } => fields
                .iter()
                .find(|f| f.name == field)
                .and_then(|f| f.resolved_ty.clone()),
            // Common-field access: the field must exist in every
            // variant. The principled pass stays permissive about an unannotated
            // (dynamic) common field -- it returns the declared type, which the
            // access path freshens -- and the `infer` pass makes the sound decision
            // (a bare sum with a dynamic variant field is rejected, a refined one is
            // resolved through its substitution).
            TypeKind::Sum { variants } => {
                let mut common = None;
                for v in variants {
                    let f = v.fields.iter().find(|f| f.name == field)?;
                    common = f.resolved_ty.clone();
                }
                common
            }
        }
    }

    /// Method `method` on the type of `ty`: its non-self parameter types and
    /// return type (each cloned; `None` for an unannotated position). Looks at
    /// record methods and, for a sum, the methods on any variant.
    fn method_sig(&self, ty: &Type, method: &str) -> Option<(Vec<Option<Type>>, Option<Type>)> {
        let info = self.type_def(ty)?;
        let m = match &info.kind {
            TypeKind::Record { methods, .. } => methods.get(method)?,
            TypeKind::Sum { variants } => variants.iter().find_map(|v| v.methods.get(method))?,
        };
        let params = m
            .signature
            .params
            .iter()
            .skip(1) // the leading `self`
            .map(|p| p.resolved_ty.clone())
            .collect();
        Some((params, m.signature.ret_ty.clone()))
    }

    /// The declared type of a named field of sum variant `variant` on the sum
    /// type `ty` (cloned), if known.
    fn variant_field_type(&self, ty: &Type, variant: &str, field: &str) -> Option<Type> {
        match &self.type_def(ty)?.kind {
            TypeKind::Sum { variants } => variants
                .iter()
                .find(|v| v.name == variant)?
                .fields
                .iter()
                .find(|f| f.name == field)
                .and_then(|f| f.resolved_ty.clone()),
            TypeKind::Record { .. } => None,
        }
    }

    /// The concrete type a record/sum type *name* (from a literal or pattern)
    /// resolves to in the current module, as a nominal `Type`.
    fn named_type(&self, name: &str) -> Option<Type> {
        self.program
            .resolve_type(&self.module, name)
            .map(TypeInfo::type_ref)
    }

    /// Whether `name` is a variant of the sum type `scrut` resolves to (so a bare
    /// `Binding` pattern is a unit-variant match, not a variable binding).
    fn is_variant_name(&self, scrut: &Type, name: &str) -> bool {
        matches!(
            self.type_def(scrut).map(|t| &t.kind),
            Some(TypeKind::Sum { variants }) if variants.iter().any(|v| v.name == name)
        )
    }

    /// The type of a variant field named in a pattern. The built-in `Result`
    /// carries its `Ok.value`/`Err.error` payloads in the nominal substitution;
    /// user sums look the field up on the variant.
    fn pattern_field_type(&self, scrut: &Type, variant: &str, field: &str) -> Option<Type> {
        let resolved = self.solver.resolve(scrut);
        if let Type::Sum(n) = &resolved
            && let Some((ok, err)) = n.result_payloads()
        {
            return match (variant, field) {
                ("Ok", "value") => Some(ok.clone()),
                ("Err", "error") => Some(err.clone()),
                _ => None,
            };
        }
        self.variant_field_type(&resolved, variant, field)
    }

    /// Bind the variables a pattern introduces, typed from the scrutinee. A
    /// `Binding` that names a variant is a unit-variant test (binds nothing);
    /// record/variant and array patterns bind their sub-patterns from the field
    /// and element types.
    fn bind_pattern(&mut self, pat: &Pattern, scrut: &Type) {
        match pat {
            Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
            Pattern::Binding(name, _) => {
                if !self.is_variant_name(scrut, name) {
                    let t = self.solver.resolve(scrut);
                    self.bind_mono(name, t);
                }
            }
            Pattern::Record(variant, fields, _) => {
                for fp in fields {
                    // An unannotated (dynamic) field binds at a fresh open type per
                    // match, so this pass does not couple independent uses; the
                    // `infer` pass checks dynamic fields per value.
                    let fty = match self.pattern_field_type(scrut, variant, &fp.name) {
                        Some(ty) if ty.is_unknown() => self.solver.fresh(InferenceVarKind::Source),
                        Some(ty) => ty,
                        None => self.solver.fresh(InferenceVarKind::Source),
                    };
                    match &fp.pat {
                        Some(sub) => self.bind_pattern(sub, &fty),
                        None => self.bind_mono(&fp.name, fty),
                    }
                }
            }
            Pattern::Array(pats, _) => {
                let resolved = self.solver.resolve(scrut);
                if let Type::Tuple(elems) = &resolved {
                    // Destructuring a tuple binds each position to its own element
                    // type (`let [i, s] = [1, "s"]`).
                    for (p, ety) in pats.iter().zip(elems) {
                        self.bind_pattern(p, ety);
                    }
                } else if let Some(elem) = brass_hir::index_element(&resolved) {
                    // An array: every position is the element type.
                    for p in pats {
                        self.bind_pattern(p, &elem);
                    }
                } else {
                    // The subject's shape is not modelled here (this pass leaves a
                    // method call's result open, so `m.pairs()` arrives as a bare
                    // variable). Each position gets its OWN variable: coupling them
                    // to one would make `for [k, v] in m.pairs()` claim `k` and `v`
                    // are the same type, and whichever the body constrained first
                    // would reject the other. The `infer` pass, which does resolve
                    // the call, checks them for real.
                    for p in pats {
                        let fresh = self.solver.fresh(InferenceVarKind::Source);
                        self.bind_pattern(p, &fresh);
                    }
                }
            }
        }
    }

    /// A numeric literal must end up at a numeric type of its class; an unresolved
    /// one defaults (int32 / float64). A literal forced to a non-numeric type by
    /// its context is a type error.
    fn finalize_literals(&mut self) {
        let lit_vars = std::mem::take(&mut self.lit_vars);
        for (id, default, span) in lit_vars {
            // See through the transparent reference/mutability wrappers: a literal
            // forced to a `ref(mut(int32))` (an array element behind a mutable
            // reference) is still an integer literal at an integer type.
            let mut resolved = self.solver.resolve(&Type::Unknown(id));
            let resolved = loop {
                match resolved {
                    Type::Ref(inner) | Type::Mut(inner) | Type::ConstOf(inner) => {
                        resolved = self.solver.resolve(&inner);
                    }
                    other => break other,
                }
            };
            let is_int = matches!(default, Type::Int(_));
            match (&resolved, is_int) {
                (Type::Unknown(_), _) => {
                    tracing::debug!(
                        var = id,
                        default = %default.display(),
                        "numeric literal unconstrained, defaulting"
                    );
                    let _ = self.solver.unify(&resolved, &default);
                }
                (Type::Int(_), true) | (Type::Float(_), false) => {}
                // An integer literal in a float context becomes a float (the
                // documented numeric-flow rule); the top-level path already
                // accepts this, so the in-function pass must too.
                (Type::Float(_), true) => {}
                (other, true) => self.errors.push(TypeError {
                    message: format!(
                        "integer literal used where `{}` is required",
                        other.display()
                    ),
                    span,
                }),
                (other, false) => self.errors.push(TypeError {
                    message: format!("float literal used where `{}` is required", other.display()),
                    span,
                }),
            }
        }
    }
}

/// Whether a (resolved) type is the built-in `Result`.
fn is_result(ty: &Type) -> bool {
    matches!(ty, Type::Sum(n) if n.is_result_type())
}

/// Whether a function body is fallible: it constructs an error (`error(x)`) or
/// propagates one (`expr!`). Nested closures are their own callables, so their
/// error use does not make the enclosing function fallible.
/// Whether a body constructs an error `Result` with `error(...)`. A bare
/// `expr!` does not count (see `check_callable`): a nullable-operand `!`
/// returns null rather than a Result, and a Result-operand `!` is typed
/// authoritatively by the infer pass.
fn block_constructs_error(block: &Block) -> bool {
    block.stmts.iter().any(stmt_constructs_error)
}

fn stmt_constructs_error(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Let {
            value: Some(value), ..
        }
        | Stmt::Return(Some(value), _) => expr_constructs_error(value),
        Stmt::Let { value: None, .. } => false,
        Stmt::Assign { target, value, .. } => {
            expr_constructs_error(target) || expr_constructs_error(value)
        }
        Stmt::Expr(e) => expr_constructs_error(e),
        Stmt::While { cond, body, .. } => {
            expr_constructs_error(cond) || block_constructs_error(body)
        }
        Stmt::For { iter, body, .. } => expr_constructs_error(iter) || block_constructs_error(body),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => false,
    }
}

fn expr_constructs_error(e: &Expr) -> bool {
    match e {
        // `error(..)!` immediately unwraps; the construction never escapes as
        // this body's own Result (see the MIR-side scanner).
        Expr::ErrorProp(inner, _) => {
            if let Expr::Call(c, args, _) = &**inner
                && matches!(&**c, Expr::Ident(n, _) if n == "error")
            {
                return args.iter().any(|a| expr_constructs_error(&a.expr));
            }
            expr_constructs_error(inner)
        }
        Expr::Call(callee, args, _) => {
            matches!(&**callee, Expr::Ident(n, _) if n == "error")
                || expr_constructs_error(callee)
                || args.iter().any(|a| expr_constructs_error(&a.expr))
        }
        Expr::Field(b, _, _) | Expr::Index(b, _, _) | Expr::Unary(_, b, _) => {
            expr_constructs_error(b)
        }
        Expr::Binary(_, a, b, _) => expr_constructs_error(a) || expr_constructs_error(b),
        Expr::Block(block, _) => block_constructs_error(block),
        Expr::If(c, t, e, _) => {
            expr_constructs_error(c)
                || block_constructs_error(t)
                || e.as_ref().is_some_and(|e| expr_constructs_error(e))
        }
        Expr::Match(scrut, arms, _) => {
            expr_constructs_error(scrut) || arms.iter().any(|a| expr_constructs_error(&a.body))
        }
        // A nested closure has its own fallibility; do not descend.
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::check;

    fn errors(src: &str) -> Vec<String> {
        let ast = brass_parser::parse(src).expect("parse");
        let (program, lerr) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(lerr.is_empty(), "lower: {lerr:?}");
        check(&program).into_iter().map(|e| e.message).collect()
    }

    #[test]
    fn let_bound_closure_is_polymorphic() {
        // The defining HM property: a `let`-bound `(x) -> x` is generalized, so
        // applying it at `int` and then at `string` does not force one type onto
        // the other. A monomorphic binding would unify the two and fail.
        let errs = errors("fun run() {\n  let id = (x) -> x\n  id(1)\n  id(\"hi\")\n}\n");
        assert!(errs.is_empty(), "polymorphic use should check: {errs:?}");
    }

    #[test]
    fn if_branches_must_agree() {
        let errs = errors(
            "fun run() -> int32 {\n  let x = if true { 1 } else { \"no\" }\n  return 0\n}\n",
        );
        assert!(!errs.is_empty(), "mismatched if branches must error");
    }

    #[test]
    fn function_argument_type_is_checked() {
        // Passing a string to an `int32` parameter is rejected through the call's
        // unification against the callee's scheme.
        let errs = errors(
            "fun takes_int(n: int32) -> int32 { return n }\n\
             fun run() { takes_int(\"hello\") }\n",
        );
        assert!(!errs.is_empty(), "argument mismatch must error: {errs:?}");
    }

    #[test]
    fn integer_literal_takes_its_annotated_kind() {
        // Contextual numeric literals: `5` unifies with the `int64` annotation
        // instead of defaulting to int32, so this is accepted.
        let errs = errors("fun run() {\n  let y: int64 = 5\n}\n");
        assert!(errs.is_empty(), "contextual int literal: {errs:?}");
    }

    #[test]
    fn integer_literal_in_non_numeric_context_errors() {
        let errs = errors("fun run() {\n  let y: string = 5\n}\n");
        assert!(
            errs.iter().any(|m| m.contains("integer literal")),
            "expected a numeric-literal error: {errs:?}"
        );
    }

    #[test]
    fn well_typed_arithmetic_function_has_no_errors() {
        let errs = errors(
            "fun add(a: int32, b: int32) -> int32 { return a + b }\n\
             fun run() -> int32 { return add(2, 3) }\n",
        );
        assert!(errs.is_empty(), "well-typed program: {errs:?}");
    }

    // ----- typed errors (HM inference + structural subtyping) -----

    #[test]
    fn error_sites_of_one_type_reconcile() {
        let errs =
            errors("fun f(a: string) {\n  if true { return error(a) }\n  return error(a)\n}\n");
        assert!(errs.is_empty(), "same error type: {errs:?}");
    }

    #[test]
    fn incompatible_scalar_error_types_are_rejected() {
        // HM: two `error(...)` sites at unrelated scalar types cannot unify.
        let errs = errors(
            "fun f(a: string, b: int32) {\n  if true { return error(a) }\n  return error(b)\n}\n",
        );
        assert!(
            errs.iter().any(|m| m.contains("incompatible error types")),
            "{errs:?}"
        );
    }

    #[test]
    fn structurally_compatible_error_records_reconcile() {
        // Structural subtyping: a wider error record is usable where a narrower
        // one is, so two error sites with related records reconcile cleanly.
        let errs = errors(
            "type Big = {\n  code: int32\n  msg: string\n}\n\
             type Small = {\n  code: int32\n}\n\
             fun f(a: Big, b: Small) {\n  if true { return error(a) }\n  return error(b)\n}\n",
        );
        assert!(errs.is_empty(), "structural error records: {errs:?}");
    }

    #[test]
    fn structurally_unrelated_error_records_are_rejected() {
        let errs = errors(
            "type A = {\n  x: int32\n}\n\
             type B = {\n  y: string\n}\n\
             fun f(a: A, b: B) {\n  if true { return error(a) }\n  return error(b)\n}\n",
        );
        assert!(
            errs.iter().any(|m| m.contains("incompatible error types")),
            "{errs:?}"
        );
    }

    #[test]
    fn error_propagation_unwraps_and_checks() {
        // `expr!` unwraps the Ok payload and propagates the error type; a
        // well-formed propagating function checks clean.
        let errs = errors(
            "fun inner(s: string) {\n  return error(s)\n}\n\
             fun outer() {\n  let x = inner(\"a\")!\n  return x\n}\n",
        );
        assert!(errs.is_empty(), "propagation: {errs:?}");
    }

    // ----- record / method / sum / match coverage -----

    #[test]
    fn record_field_access_has_the_field_type() {
        // `p.x` is `int32`, so returning it where `string` is required errors.
        let errs = errors(
            "type Point = {\n  x: int32\n  y: int32\n}\n\
             fun f(p: Point) -> string {\n  return p.x\n}\n",
        );
        assert!(!errs.is_empty(), "field type must be enforced: {errs:?}");
    }

    #[test]
    fn record_construction_checks_field_types() {
        let errs = errors(
            "type Point = {\n  x: int32\n}\n\
             fun f() -> Point {\n  return Point { x: \"s\" }\n}\n",
        );
        assert!(!errs.is_empty(), "field value type must match: {errs:?}");
    }

    #[test]
    fn method_argument_type_is_checked() {
        let errs = errors(
            "type Counter = {\n  n: int32\n}\n\
             fun Counter.add(self, k: int32) {\n    self.n += k\n  }\n\
             fun f(c: Counter) {\n  c.add(\"hi\")\n}\n",
        );
        assert!(!errs.is_empty(), "method argument must match: {errs:?}");
    }

    #[test]
    fn match_arms_must_agree_on_result_type() {
        let errs = errors(
            "type Color = Red | Blue\n\
             fun f(c: Color) -> int32 {\n  let r = match c { Red => 1, Blue => \"two\" }\n  return 0\n}\n",
        );
        assert!(!errs.is_empty(), "match arms must agree: {errs:?}");
    }

    #[test]
    fn well_typed_record_method_and_match_check_clean() {
        let errs = errors(
            "type Point = {\n  x: int32\n  y: int32\n}\n\
             fun Point.sum(self) -> int32 {\n    return self.x + self.y\n  }\n\
             type Color = Red | Blue\n\
             fun area(p: Point) -> int32 {\n  return p.sum()\n}\n\
             fun pick(c: Color) -> int32 {\n  return match c { Red => 1, Blue => 2 }\n}\n",
        );
        assert!(errs.is_empty(), "well-typed record/method/match: {errs:?}");
    }

    #[test]
    fn index_yields_the_element_type() {
        // `xs[0]` is `int32`; returning it where `string` is required errors.
        let errs = errors("fun f(xs: int32[]) -> string {\n  return xs[0]\n}\n");
        assert!(
            !errs.is_empty(),
            "index element type must be enforced: {errs:?}"
        );
    }

    // ----- builtin numeric/string conversion schemes -----

    #[test]
    fn numeric_parse_requires_a_string() {
        let errs = errors("fun f(n: int32) {\n  let x = int32.parse(n)\n}\n");
        assert!(
            errs.iter().any(|m| m.contains("expects a string")),
            "parse must require a string: {errs:?}"
        );
    }

    #[test]
    fn numeric_from_requires_a_numeric_value() {
        let errs = errors("fun f(s: string) {\n  let x = float64.from(s)\n}\n");
        assert!(
            errs.iter().any(|m| m.contains("expects a numeric")),
            "from must require a number: {errs:?}"
        );
    }

    #[test]
    fn string_from_accepts_any_value() {
        let errs = errors("fun f(n: int32) {\n  let x = string.from(n)\n}\n");
        assert!(errs.is_empty(), "string.from accepts any value: {errs:?}");
    }

    #[test]
    fn well_typed_conversions_check_clean() {
        // `parse` on a string and `from` on a number are well-formed; the results
        // are the conversions' (possibly fallible) types.
        let errs = errors(
            "fun f(s: string, n: int32) {\n  let a = int32.parse(s)\n  let b = float64.from(n)\n}\n",
        );
        assert!(errs.is_empty(), "well-typed conversions: {errs:?}");
    }

    // ----- string builtin schemes (`_string_*`) -----

    #[test]
    fn string_find_requires_string_arguments() {
        // A concrete non-string argument to `_string_find` is rejected.
        let errs = errors("fun f(n: int32) {\n  let x = _string_find(\"a\", n)\n}\n");
        assert!(
            errs.iter().any(|m| m.contains("expects a string")),
            "_string_find must require strings: {errs:?}"
        );
    }

    #[test]
    fn string_find_arity_is_checked() {
        let errs = errors("fun f() {\n  let x = _string_find(\"a\")\n}\n");
        assert!(
            errs.iter().any(|m| m.contains("argument")),
            "_string_find arity must be checked: {errs:?}"
        );
    }

    #[test]
    fn string_find_on_strings_checks_clean_and_is_nullable_int() {
        // Two string arguments are well-formed; the result is `int64?`, so
        // returning it where `string` is required errors (proving the result type).
        let ok = errors("fun f(s: string, t: string) {\n  let x = _string_find(s, t)\n}\n");
        assert!(ok.is_empty(), "string args are well-formed: {ok:?}");
        let bad =
            errors("fun f(s: string, t: string) -> string {\n  return _string_find(s, t)\n}\n");
        assert!(!bad.is_empty(), "result is int64?, not string: {bad:?}");
    }

    #[test]
    fn polymorphic_caller_passing_fresh_args_is_not_constrained() {
        // A caller that forwards unannotated (fresh) values to `_string_find` is
        // not wrongly constrained to strings -- the check defers on unknowns, so
        // this is the pattern `array.contains` relies on.
        let errs = errors("fun forward(a, b) {\n  return _string_find(a, b)\n}\n");
        assert!(errs.is_empty(), "fresh args defer: {errs:?}");
    }
}
