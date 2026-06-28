//! Local static type checks (DESIGN.md 5.2, 5.5, 5.7, 5.9).
//!
//! This pass intentionally remains conservative around genuinely polymorphic or
//! structurally inferred code, but every type that is explicit in source is
//! enforced before execution. It checks annotations, constructor fields,
//! annotated function/method calls, nullable use-before-check, and operators.
//! Unknown values are represented with unification variables so uncertain code
//! can still be deferred to the runtime without accepting contradictions against
//! explicit types.

use std::collections::{HashMap, HashSet};

use prepoly_hir::{
    CallableSignature, Constness, FloatKind, IntKind, NominalType, ParamInfo, Program,
    Substitution, Type, TypeKind, TypedProgram,
};
use prepoly_lexer::Span;
use prepoly_parser::ast::*;

use crate::TypeError;
use crate::constraint::ShapeConstraint;
use crate::narrow;
use crate::solver::{InferenceVarKind, Solver};
use crate::unify::Subst;

type ScopeStack = Vec<HashMap<String, Type>>;

struct MethodCall<'a> {
    owner: &'a str,
    self_type: &'a str,
    name: &'a str,
    method: &'a Method,
    signature_params: &'a [ParamInfo],
    receiver_ty: Option<Type>,
    declared_ret: Option<Type>,
    fallback_ret: Type,
    arg_types: &'a [Type],
}

#[derive(Clone)]
struct ResolvedMethod {
    qualifier: String,
    self_type: String,
    signature: CallableSignature,
    method: Method,
}

#[derive(Clone)]
enum ReturnContext {
    Inferred,
    Explicit(Type),
}

pub fn check(program: &Program) -> Vec<TypeError> {
    analyze(program).errors
}

pub struct Inference {
    pub errors: Vec<TypeError>,
    pub typed: TypedProgram,
    /// Fully-concrete call instances per free-function symbol (PLAN.md R5).
    pub fn_instances: HashMap<String, Vec<Vec<Type>>>,
}

pub fn analyze(program: &Program) -> Inference {
    let mut checker = Checker::new(program);
    checker.validate_param_declarations();
    checker.precompute_global_bindings();
    checker.precompute_function_returns();
    checker.precompute_method_returns();
    for f in program.functions.values() {
        let mut scopes = checker.signature_scopes(&f.signature.params);
        let ret = f.signature.ret_ty.clone();
        checker.current_module = f.module.clone();
        checker.check_block_root(&f.decl.body, &mut scopes, ret.as_ref());
    }
    for t in program.types.values() {
        checker.current_module = t.module.clone();
        match &t.kind {
            TypeKind::Record { methods, .. } => {
                for m in methods.values() {
                    if let Some(body) = &m.decl.body {
                        let mut scopes = checker.signature_scopes(&m.signature.params);
                        let ret = m.signature.ret_ty.clone();
                        checker.check_block_with_self(body, &mut scopes, ret.as_ref(), &t.name);
                    }
                }
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    for m in v.methods.values() {
                        if let Some(body) = &m.decl.body {
                            let mut scopes = checker.signature_scopes(&m.signature.params);
                            let ret = m.signature.ret_ty.clone();
                            checker.check_block_with_self_variant(
                                body,
                                &mut scopes,
                                ret.as_ref(),
                                &t.name,
                                &v.name,
                            );
                        }
                    }
                }
            }
        }
    }
    let mut scopes = vec![HashMap::new()];
    checker.const_scopes = vec![HashSet::new()];
    for init in &program.inits {
        checker.current_module = init.path.clone();
        for s in &init.stmts {
            checker.check_stmt(s, &mut scopes);
        }
    }
    checker.const_scopes.clear();
    Inference {
        errors: checker.errors,
        typed: checker.typed,
        fn_instances: checker.fn_instances,
    }
}

struct Checker<'a> {
    program: &'a Program,
    errors: Vec<TypeError>,
    typed: TypedProgram,
    const_scopes: Vec<HashSet<String>>,
    next_unknown: u32,
    self_type: Option<String>,
    self_variant: Option<(String, String)>,
    return_contexts: Vec<ReturnContext>,
    global_scope: HashMap<String, Type>,
    function_returns: HashMap<String, Type>,
    /// (method qualifier, method name) -> return type.
    /// Record qualifiers are the type name; variant qualifiers are `Type.Variant`.
    method_returns: HashMap<(String, String), Type>,
    instantiating: HashSet<String>,
    /// Deferred structural constraints on inference variables, keyed by the
    /// variable's `Unknown` id. Recorded while checking a body that uses an
    /// unknown-typed value (a closure parameter) and verified when the variable
    /// is solved at a call site (see `crate::constraint`).
    shape_constraints: HashMap<u32, Vec<ShapeConstraint>>,
    /// The inference solver: a persistent substitution for variables pinned
    /// across expressions (such as an empty array's element type once a `push`
    /// fixes it) plus variable classification. `resolve` follows the
    /// substitution so all later uses of the same binding see the solved type,
    /// and `kind_of` distinguishes a bare empty-array element (which cannot
    /// satisfy a required position while unconstrained) from other unknowns
    /// (DESIGN.md 5.7 Phase 4 / 5; PLAN.md R1).
    solver: Solver,
    /// The module whose body is currently being checked, used to enforce
    /// per-module name visibility (DESIGN.md 2; PLAN.md R5). Set per function,
    /// method, and module-init, and swapped while a called body is re-checked.
    current_module: Vec<String>,
    /// Fully-concrete call instances per free-function symbol: every distinct
    /// tuple of resolved argument types a function is called with. This is the
    /// input to static monomorphization (DESIGN.md 7.2; PLAN.md R5 stage 5): the
    /// typed backend can compile one specialized instance per tuple. Stored as a
    /// deduplicated `Vec` because `Type` is not `Hash`/`Eq`.
    fn_instances: HashMap<String, Vec<Vec<Type>>>,
}

impl<'a> Checker<'a> {
    fn new(program: &'a Program) -> Self {
        Self {
            program,
            errors: Vec::new(),
            typed: TypedProgram::default(),
            const_scopes: Vec::new(),
            next_unknown: next_unknown_after_program(program),
            self_type: None,
            self_variant: None,
            return_contexts: Vec::new(),
            global_scope: HashMap::new(),
            function_returns: HashMap::new(),
            method_returns: HashMap::new(),
            instantiating: HashSet::new(),
            shape_constraints: HashMap::new(),
            solver: Solver::new(),
            current_module: Vec::new(),
            fn_instances: HashMap::new(),
        }
    }

    fn validate_param_declarations(&mut self) {
        let functions = self.program.functions.values().map(|f| {
            (
                format!("function `{}`", f.signature.name),
                f.signature.params.clone(),
            )
        });
        let methods = self
            .program
            .types
            .values()
            .flat_map(|info| match &info.kind {
                TypeKind::Record { methods, .. } => methods
                    .values()
                    .map(|m| {
                        (
                            format!("method `{}.{}`", info.name, m.signature.name),
                            m.signature.params.clone(),
                        )
                    })
                    .collect::<Vec<_>>(),
                TypeKind::Sum { variants } => variants
                    .iter()
                    .flat_map(|variant| {
                        variant.methods.values().map(|m| {
                            (
                                format!(
                                    "method `{}.{}.{}`",
                                    info.name, variant.name, m.signature.name
                                ),
                                m.signature.params.clone(),
                            )
                        })
                    })
                    .collect(),
            });
        let params_to_check: Vec<_> = functions.chain(methods).collect();
        for (owner, params) in params_to_check {
            self.report_duplicate_signature_params(&owner, &params);
        }
    }

    fn report_duplicate_signature_params(&mut self, owner: &str, params: &[ParamInfo]) {
        self.report_duplicate_param_names(
            owner,
            params.iter().map(|param| (param.name.as_str(), param.span)),
        );
    }

    fn report_duplicate_params(&mut self, owner: &str, params: &[Param]) {
        self.report_duplicate_param_names(
            owner,
            params.iter().map(|param| (param.name.as_str(), param.span)),
        );
    }

    fn report_duplicate_param_names<'p>(
        &mut self,
        owner: &str,
        params: impl IntoIterator<Item = (&'p str, prepoly_lexer::Span)>,
    ) {
        let mut seen = HashSet::new();
        for (name, span) in params {
            if !seen.insert(name) {
                self.errors.push(TypeError {
                    message: format!("duplicate parameter `{name}` in {owner}"),
                    span,
                });
            }
        }
    }

    fn precompute_function_returns(&mut self) {
        let mut names: Vec<String> = self.program.functions.keys().cloned().collect();
        names.sort();
        for name in names {
            if self.function_returns.contains_key(&name) {
                continue;
            }
            let Some(info) = self.program.functions.get(&name) else {
                continue;
            };
            let ty = info.signature.ret_ty.clone().unwrap_or_else(|| {
                self.infer_function_return(&info.signature.params, &info.decl.body)
            });
            self.function_returns.insert(name, ty);
        }
    }

    fn precompute_method_returns(&mut self) {
        let mut entries: Vec<(String, String, String)> = self
            .program
            .types
            .values()
            .flat_map(|info| match &info.kind {
                TypeKind::Record { methods, .. } => methods
                    .keys()
                    .map(|m| (info.name.clone(), info.name.clone(), m.clone()))
                    .collect::<Vec<_>>(),
                TypeKind::Sum { variants } => variants
                    .iter()
                    .flat_map(|variant| {
                        variant.methods.keys().map(|m| {
                            (
                                format!("{}.{}", info.name, variant.name),
                                info.name.clone(),
                                m.clone(),
                            )
                        })
                    })
                    .collect(),
            })
            .collect();
        entries.sort();
        for (qualifier, self_type, method) in entries {
            let ty = self.infer_method_return(&qualifier, &self_type, &method);
            self.method_returns.insert((qualifier, method), ty);
        }
    }

    fn infer_method_return(&mut self, qualifier: &str, self_type: &str, method: &str) -> Type {
        let Some(resolved) = self.method_for_qualifier(qualifier, method) else {
            return self.fresh_unknown();
        };
        if let Some(ty) = resolved.signature.ret_ty.clone() {
            return ty;
        }
        let signature_params = resolved.signature.params.clone();
        let decl = resolved.method;
        let Some(body) = &decl.body else {
            return Type::Void;
        };
        let saved = self.self_type.replace(self_type.to_string());
        let saved_variant = self.self_variant.clone();
        self.self_variant = qualifier
            .split_once('.')
            .map(|(_, variant)| (self_type.to_string(), variant.to_string()));
        let mut env = self.signature_param_env(&signature_params);
        // An instance method's `self` is the enclosing nominal type. Variant
        // methods use the sum type because HIR has no separate variant type.
        if signature_params.first().is_some_and(|p| p.name == "self") {
            env.insert("self".to_string(), self.type_by_name(self_type));
        }
        let mut normal = Vec::new();
        let mut errors = Vec::new();
        self.infer_returns_block(body, &mut env, &mut normal, &mut errors);
        self.self_type = saved;
        self.self_variant = saved_variant;
        let normal_ty = self.reconcile_return_types(&normal, true);
        let err_ty = self.reconcile_error_payloads(&errors, true);
        self.result_from_payloads(normal_ty, err_ty)
    }

    fn infer_function_return(&mut self, params: &[ParamInfo], body: &Block) -> Type {
        let mut env = self.signature_param_env(params);
        let mut normal = Vec::new();
        let mut errors = Vec::new();
        self.infer_returns_block(body, &mut env, &mut normal, &mut errors);
        let normal_ty = self.reconcile_return_types(&normal, true);
        let err_ty = self.reconcile_error_payloads(&errors, true);
        self.result_from_payloads(normal_ty, err_ty)
    }

    /// Combine the inferred normal (Ok) and error (Err) return payloads into a
    /// single return type. A function that only ever returns via `error(..)` /
    /// propagation still has an inferred `Ok` payload as a fresh unknown.
    fn result_from_payloads(&mut self, normal_ty: Option<Type>, err_ty: Option<Type>) -> Type {
        match (normal_ty, err_ty) {
            (Some(ok), Some(err)) => Type::result(ok, err),
            (Some(ty), None) => ty,
            (None, Some(err)) => Type::result(self.fresh_error_only_ok(), err),
            (None, None) => Type::Void,
        }
    }

    /// Reduce the explicit `return` types of a body to a single type. Unlike
    /// `common_type_list`, this carries the span of each return so that two
    /// incompatible concrete returns (e.g. `return 1` and `return "x"`) produce
    /// a diagnostic instead of silently collapsing to a fresh `Unknown`, which
    /// would let the function's return type satisfy any annotation. `report`
    /// is false at call-site re-inference to avoid duplicating the definition
    /// site's diagnostic.
    fn reconcile_return_types(&mut self, normal: &[(Type, Span)], report: bool) -> Option<Type> {
        let (first, rest) = normal.split_first()?;
        let mut common = first.0.clone();
        for (ty, span) in rest {
            if let Some(nullable) = common_nullable_type(&common, ty) {
                common = nullable;
                continue;
            }
            if !self.can_unify(&common, ty) {
                if report {
                    self.errors.push(TypeError {
                        message: format!(
                            "incompatible return types: `{}` and `{}`",
                            self.resolve(&common).display(),
                            self.resolve(ty).display()
                        ),
                        span: *span,
                    });
                }
                // Keep the first concrete type so callers check against a
                // definite type rather than cascading a second error.
                return Some(common);
            }
        }
        Some(common)
    }

    /// Reduce the inferred `Err` payloads of a fallible body to a single type.
    /// A function whose error payload comes from both a propagated `expr!` and
    /// a local `error(x)` must agree on one payload type (DESIGN.md 5.6); two
    /// incompatible concrete payloads are a diagnostic rather than a silent
    /// collapse to a fresh `Unknown` that would accept any later use. `report`
    /// is false at call-site re-inference so the definition site is not
    /// duplicated.
    fn reconcile_error_payloads(&mut self, errors: &[(Type, Span)], report: bool) -> Option<Type> {
        let (first, rest) = errors.split_first()?;
        let mut common = first.0.clone();
        for (ty, span) in rest {
            if let Some(nullable) = common_nullable_type(&common, ty) {
                common = nullable;
                continue;
            }
            if !self.can_unify(&common, ty) {
                if report {
                    self.errors.push(TypeError {
                        message: format!(
                            "incompatible error payloads: `{}` and `{}`",
                            self.resolve(&common).display(),
                            self.resolve(ty).display()
                        ),
                        span: *span,
                    });
                }
                return Some(common);
            }
        }
        Some(common)
    }

    fn infer_returns_block(
        &mut self,
        block: &Block,
        env: &mut HashMap<String, Type>,
        normal: &mut Vec<(Type, Span)>,
        errors: &mut Vec<(Type, Span)>,
    ) {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { pat, value, .. } => {
                    let ty = self.infer_expr_light(value, env, errors);
                    self.bind_pattern_light(pat, &ty, env);
                }
                Stmt::Assign { value, .. } => {
                    self.infer_expr_light(value, env, errors);
                }
                Stmt::Expr(value) => {
                    self.infer_returns_expr(value, env, normal, errors);
                }
                Stmt::While { cond, body, .. } => {
                    self.infer_expr_light(cond, env, errors);
                    self.infer_returns_block(body, &mut env.clone(), normal, errors);
                }
                Stmt::For {
                    var, iter, body, ..
                } => {
                    let iter_ty = self.infer_expr_light(iter, env, errors);
                    let item_ty = match iter_ty {
                        Type::Array(inner, _) | Type::Slice(inner) => *inner,
                        _ => self.fresh_unknown(),
                    };
                    let mut inner = env.clone();
                    inner.insert(var.clone(), item_ty);
                    self.infer_returns_block(body, &mut inner, normal, errors);
                }
                Stmt::Return(Some(expr), _) => {
                    let ty = self.infer_expr_light(expr, env, errors);
                    let resolved = self.resolve(&ty);
                    match resolved.result_payloads() {
                        Some((ok, err)) if ok.is_unknown() => {
                            errors.push((err.clone(), expr.span()))
                        }
                        _ => normal.push((ty, expr.span())),
                    }
                }
                Stmt::Return(None, span) => normal.push((Type::Void, *span)),
                Stmt::Break(_) | Stmt::Continue(_) => {}
            }
        }
    }

    fn infer_returns_expr(
        &mut self,
        expr: &Expr,
        env: &mut HashMap<String, Type>,
        normal: &mut Vec<(Type, Span)>,
        errors: &mut Vec<(Type, Span)>,
    ) {
        match expr {
            Expr::If(cond, then, els, _) => {
                self.infer_expr_light(cond, env, errors);
                self.infer_returns_block(then, &mut env.clone(), normal, errors);
                if let Some(els) = els {
                    self.infer_returns_expr(els, &mut env.clone(), normal, errors);
                }
            }
            Expr::IfLet(_, scrut, then, els, _) => {
                self.infer_expr_light(scrut, env, errors);
                self.infer_returns_block(then, &mut env.clone(), normal, errors);
                if let Some(els) = els {
                    self.infer_returns_expr(els, &mut env.clone(), normal, errors);
                }
            }
            Expr::Match(scrut, arms, _) => {
                self.infer_expr_light(scrut, env, errors);
                for arm in arms {
                    self.infer_returns_expr(&arm.body, &mut env.clone(), normal, errors);
                }
            }
            Expr::Block(block, _) => {
                self.infer_returns_block(block, &mut env.clone(), normal, errors)
            }
            other => {
                self.infer_expr_light(other, env, errors);
            }
        }
    }

    fn infer_expr_light(
        &mut self,
        expr: &Expr,
        env: &HashMap<String, Type>,
        errors: &mut Vec<(Type, Span)>,
    ) -> Type {
        match expr {
            Expr::Int(..) => Type::Int(IntKind::I32),
            Expr::Float(..) => Type::Float(FloatKind::F64),
            Expr::Bool(..) => Type::Bool,
            Expr::Null(_) => Type::null(),
            Expr::Str(..) => Type::Str,
            Expr::Ident(name, _) => env
                .get(name)
                .cloned()
                .unwrap_or_else(|| self.fresh_unknown()),
            Expr::SelfExpr(_) => env
                .get("self")
                .cloned()
                .unwrap_or_else(|| self.fresh_unknown()),
            Expr::Unary(_, inner, _) => self.infer_expr_light(inner, env, errors),
            Expr::Binary(op, left, right, _) => {
                let left = self.infer_expr_light(left, env, errors);
                let right = self.infer_expr_light(right, env, errors);
                self.infer_binary_light(*op, left, right)
            }
            Expr::Call(callee, args, _) => self.infer_call_light(callee, args, env, errors),
            Expr::Field(base, name, _) => self.infer_field_light(base, name, env, errors),
            Expr::Index(base, _, _) => match self.infer_expr_light(base, env, errors) {
                Type::Array(inner, _) | Type::Slice(inner) => *inner,
                Type::Str => Type::Str,
                _ => self.fresh_unknown(),
            },
            Expr::ErrorProp(inner, span) => {
                let ty = self.infer_expr_light(inner, env, errors);
                if let Some((ok, err)) = ty.result_payloads() {
                    errors.push((err.clone(), *span));
                    ok.clone()
                } else {
                    self.fresh_unknown()
                }
            }
            Expr::Closure(params, body, _) => {
                let mut inner = env.clone();
                for param in params {
                    let ty = param
                        .ty
                        .as_ref()
                        .and_then(|t| self.resolve_type(t).ok())
                        .unwrap_or_else(|| self.fresh_unknown());
                    inner.insert(param.name.clone(), ty);
                }
                let ret = self.infer_expr_light(body, &inner, errors);
                Type::Fun(
                    params
                        .iter()
                        .map(|p| {
                            inner
                                .get(&p.name)
                                .cloned()
                                .unwrap_or_else(|| self.fresh_unknown())
                        })
                        .collect(),
                    Box::new(ret),
                )
            }
            Expr::Array(items, _) => Type::Slice(Box::new(
                items
                    .first()
                    .map(|e| self.infer_expr_light(e, env, errors))
                    .unwrap_or_else(|| self.fresh_unknown()),
            )),
            Expr::TypeLit(name, fields, _) => self.infer_type_lit_light(name, fields, env, errors),
            Expr::VariantLit(name, variant, fields, _) => {
                self.infer_variant_lit_light(name, variant, fields, env, errors)
            }
            Expr::If(_, then, els, _) => {
                let then_ty = self.infer_block_value_light(then, &mut env.clone(), errors);
                let else_ty = els
                    .as_ref()
                    .map(|e| self.infer_expr_light(e, env, errors))
                    .unwrap_or(Type::Void);
                self.common_type_or_unknown(then_ty, else_ty)
            }
            Expr::IfLet(_, scrut, then, els, _) => {
                self.infer_expr_light(scrut, env, errors);
                let then_ty = self.infer_block_value_light(then, &mut env.clone(), errors);
                let else_ty = els
                    .as_ref()
                    .map(|e| self.infer_expr_light(e, env, errors))
                    .unwrap_or(Type::Void);
                self.common_type_or_unknown(then_ty, else_ty)
            }
            Expr::Match(scrut, arms, _) => {
                self.infer_expr_light(scrut, env, errors);
                let tys: Vec<Type> = arms
                    .iter()
                    .map(|arm| self.infer_expr_light(&arm.body, env, errors))
                    .collect();
                self.common_type_list(&tys)
                    .unwrap_or_else(|| self.fresh_unknown())
            }
            Expr::Block(block, _) => self.infer_block_value_light(block, &mut env.clone(), errors),
        }
    }

    fn infer_call_light(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        env: &HashMap<String, Type>,
        errors: &mut Vec<(Type, Span)>,
    ) -> Type {
        if let Expr::Ident(name, _) = callee {
            if name == "error" {
                let err = args
                    .first()
                    .map(|a| self.infer_expr_light(&a.expr, env, errors))
                    .unwrap_or(Type::Void);
                return Type::result(self.fresh_unknown(), err);
            }
            if let Some(ret) = self.builtin_function_type_light(name) {
                args.iter().for_each(|arg| {
                    self.infer_expr_light(&arg.expr, env, errors);
                });
                return ret;
            }
            if let Some(ret) = self.function_returns.get(name).cloned() {
                args.iter().for_each(|arg| {
                    self.infer_expr_light(&arg.expr, env, errors);
                });
                return ret;
            }
        }
        if let Expr::Field(base, method, _) = callee {
            if let Expr::Ident(tname, _) = &**base
                && env.get(tname).is_none()
            {
                let ret = self.primitive_static_type(tname, method);
                if ret.is_some() {
                    args.iter().for_each(|arg| {
                        self.infer_expr_light(&arg.expr, env, errors);
                    });
                }
                if let Some(ret) = ret {
                    return ret;
                }
            }
            let recv = self.infer_expr_light(base, env, errors);
            if let Some(ret) = builtin_method_return(&recv, method) {
                args.iter().for_each(|arg| {
                    self.infer_expr_light(&arg.expr, env, errors);
                });
                return ret;
            }
        }
        args.iter().for_each(|arg| {
            self.infer_expr_light(&arg.expr, env, errors);
        });
        self.fresh_unknown()
    }

    fn infer_field_light(
        &mut self,
        base: &Expr,
        name: &str,
        env: &HashMap<String, Type>,
        errors: &mut Vec<(Type, Span)>,
    ) -> Type {
        let shadowed = matches!(base, Expr::Ident(n, _) if env.contains_key(n));
        if let Some(ty) = self.unit_variant_type(base, name, shadowed) {
            return ty;
        }
        match self.infer_expr_light(base, env, errors) {
            Type::Record(record) => record.substitution.get(name).cloned().unwrap_or_else(|| {
                self.program
                    .types
                    .get(record.name())
                    .and_then(|info| match &info.kind {
                        TypeKind::Record { fields, .. } => fields.iter().find(|f| f.name == name),
                        TypeKind::Sum { .. } => None,
                    })
                    .and_then(|f| f.resolved_ty.clone())
                    .unwrap_or_else(|| self.fresh_unknown())
            }),
            Type::Sum(sum) => self
                .self_variant_field_type(base, &sum, name)
                .or_else(|| self.common_sum_field_type(&sum, name))
                .unwrap_or_else(|| self.fresh_unknown()),
            _ => self.fresh_unknown(),
        }
    }

    fn infer_type_lit_light(
        &mut self,
        name: &str,
        fields: &[(String, Expr)],
        env: &HashMap<String, Type>,
        errors: &mut Vec<(Type, Span)>,
    ) -> Type {
        let tn = self.resolve_self_name(name);
        let resolved = self
            .resolve_type_symbol(&tn)
            .and_then(|symbol| self.program.types.get(&symbol))
            .and_then(|info| {
                let TypeKind::Record { fields, .. } = &info.kind else {
                    return None;
                };
                Some((info.type_ref(), fields.clone()))
            });
        let Some((ret, declared)) = resolved else {
            fields.iter().for_each(|(_, expr)| {
                self.infer_expr_light(expr, env, errors);
            });
            return self.fresh_unknown();
        };
        let substitution = self.infer_lit_field_substitution(None, &declared, fields, env, errors);
        apply_nominal_substitution(ret, substitution)
    }

    fn infer_variant_lit_light(
        &mut self,
        type_name: &str,
        variant: &str,
        fields: &[(String, Expr)],
        env: &HashMap<String, Type>,
        errors: &mut Vec<(Type, Span)>,
    ) -> Type {
        let tn = self.resolve_self_name(type_name);
        let resolved = self
            .resolve_type_symbol(&tn)
            .and_then(|symbol| self.program.types.get(&symbol))
            .and_then(|info| {
                let variant = info.variant(variant)?;
                Some((info.type_ref(), variant.fields.clone()))
            });
        let Some((ret, declared)) = resolved else {
            fields.iter().for_each(|(_, expr)| {
                self.infer_expr_light(expr, env, errors);
            });
            return self.fresh_unknown();
        };
        let substitution =
            self.infer_lit_field_substitution(Some(variant), &declared, fields, env, errors);
        apply_nominal_substitution(ret, substitution)
    }

    fn infer_lit_field_substitution(
        &mut self,
        variant: Option<&str>,
        declared: &[prepoly_hir::FieldInfo],
        fields: &[(String, Expr)],
        env: &HashMap<String, Type>,
        errors: &mut Vec<(Type, Span)>,
    ) -> Substitution {
        let mut substitution = Substitution::empty();
        for field in declared {
            if let Some((_, expr)) = fields.iter().find(|(name, _)| name == &field.name) {
                let got = self.infer_expr_light(expr, env, errors);
                if field.resolved_ty.as_ref().is_some_and(Type::is_unknown) {
                    substitution.insert(field_substitution_key(variant, &field.name), got);
                }
            }
        }
        substitution
    }

    fn infer_block_value_light(
        &mut self,
        block: &Block,
        env: &mut HashMap<String, Type>,
        errors: &mut Vec<(Type, Span)>,
    ) -> Type {
        let mut last = Type::Void;
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { pat, value, .. } => {
                    let ty = self.infer_expr_light(value, env, errors);
                    self.bind_pattern_light(pat, &ty, env);
                    last = Type::Void;
                }
                Stmt::Expr(expr) => last = self.infer_expr_light(expr, env, errors),
                Stmt::Return(Some(expr), _) => return self.infer_expr_light(expr, env, errors),
                _ => last = Type::Void,
            }
        }
        last
    }

    fn infer_binary_light(&mut self, op: BinOp, left: Type, right: Type) -> Type {
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                if self.can_unify(&left, &right) {
                    left
                } else {
                    self.fresh_unknown()
                }
            }
            BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Gt
            | BinOp::Le
            | BinOp::Ge
            | BinOp::And
            | BinOp::Or => Type::Bool,
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                if self.can_unify(&left, &right) {
                    left
                } else {
                    self.fresh_unknown()
                }
            }
        }
    }

    fn primitive_static_type(&self, tname: &str, method: &str) -> Option<Type> {
        if matches!((tname, method), ("File", "stdin" | "stdout" | "stderr")) {
            return Some(self.type_by_name("File"));
        }
        primitive_static_return(tname, method)
    }

    fn common_type_list(&mut self, types: &[Type]) -> Option<Type> {
        let (first, rest) = types.split_first()?;
        let mut common = first.clone();
        for ty in rest {
            if let Some(nullable) = common_nullable_type(&common, ty) {
                common = nullable;
                continue;
            }
            if !self.can_unify(&common, ty) {
                return Some(self.fresh_unknown());
            }
        }
        Some(common)
    }

    fn bind_pattern_light(&mut self, pat: &Pattern, ty: &Type, env: &mut HashMap<String, Type>) {
        match pat {
            Pattern::Binding(name, _) if !self.is_unit_variant_name(name) => {
                env.insert(name.clone(), ty.clone());
            }
            Pattern::Record(variant, fields, _) => {
                let field_types = self.pattern_field_types(ty, variant);
                for field in fields {
                    let fty = field_types
                        .get(&field.name)
                        .cloned()
                        .unwrap_or_else(|| self.fresh_unknown());
                    if let Some(subpat) = &field.pat {
                        self.bind_pattern_light(subpat, &fty, env);
                    } else {
                        env.insert(field.name.clone(), fty);
                    }
                }
            }
            Pattern::Array(pats, _) => {
                let elem = match ty {
                    Type::Array(inner, _) | Type::Slice(inner) => &**inner,
                    _ => ty,
                };
                pats.iter()
                    .for_each(|pat| self.bind_pattern_light(pat, elem, env));
            }
            _ => {}
        }
    }

    fn fresh_unknown(&mut self) -> Type {
        let id = self.next_unknown;
        self.next_unknown += 1;
        Type::Unknown(id)
    }

    /// A fresh inference variable for the element type of a bare `[]` literal,
    /// remembered so that an unconstrained empty array escaping into a required
    /// position is reported instead of silently unifying with the required type.
    fn fresh_empty_array_elem(&mut self) -> Type {
        let id = self.next_unknown;
        self.next_unknown += 1;
        self.solver.record_var(id, InferenceVarKind::EmptyArrayElem);
        Type::Unknown(id)
    }

    /// A fresh inference variable for the `Ok` payload of a function that only
    /// returns `error(...)`. The payload type is unknowable, so it is reported
    /// if it escapes into a required position rather than silently unifying.
    fn fresh_error_only_ok(&mut self) -> Type {
        let id = self.next_unknown;
        self.next_unknown += 1;
        self.solver.record_var(id, InferenceVarKind::ErrorOnlyOk);
        Type::Unknown(id)
    }

    fn param_scope(&mut self, params: &[Param]) -> HashMap<String, Type> {
        params
            .iter()
            .map(|p| {
                let ty =
                    p.ty.as_ref()
                        .and_then(|t| self.resolve_type(t).ok())
                        .unwrap_or_else(|| self.fresh_unknown());
                (p.name.clone(), ty)
            })
            .collect()
    }

    fn signature_param_scope(&mut self, params: &[ParamInfo]) -> HashMap<String, Type> {
        params
            .iter()
            .map(|param| {
                let ty = param
                    .resolved_ty
                    .clone()
                    .unwrap_or_else(|| self.fresh_unknown());
                (param.name.clone(), ty)
            })
            .collect()
    }

    /// Infer the types of top-level `let`/`const` bindings in module/source
    /// order and record them in `global_scope` (DESIGN.md Phase 2). Bindings
    /// accumulate as iteration proceeds, so a later global is never visible to
    /// an earlier initializer. Annotation resolution errors are surfaced by
    /// `resolve_annotations`, so they are intentionally swallowed here.
    fn precompute_global_bindings(&mut self) {
        let program = self.program;
        let mut env: HashMap<String, Type> = HashMap::new();
        let mut errors = Vec::new();
        for init in &program.inits {
            for stmt in &init.stmts {
                let Stmt::Let { pat, ty, value, .. } = stmt else {
                    continue;
                };
                let value_ty = self.infer_expr_light(value, &env, &mut errors);
                let binding_ty = match ty {
                    Some(te) => match self.resolve_type(te) {
                        Ok(annotated) => self.instantiate_annotated_type(&annotated, &value_ty),
                        Err(_) => value_ty,
                    },
                    None => value_ty,
                };
                self.bind_pattern_light(pat, &binding_ty, &mut env);
            }
        }
        self.global_scope = env;
    }

    /// The scope stack used to check a function or method body: top-level
    /// globals at the bottom, signature parameters on top so parameters shadow
    /// same-named globals.
    fn signature_scopes(&mut self, params: &[ParamInfo]) -> ScopeStack {
        vec![
            self.global_scope.clone(),
            self.signature_param_scope(params),
        ]
    }

    /// A single-scope environment for return inference that layers signature
    /// parameters over the globals, mirroring `signature_scopes` shadowing.
    fn signature_param_env(&mut self, params: &[ParamInfo]) -> HashMap<String, Type> {
        let mut env = self.global_scope.clone();
        env.extend(self.signature_param_scope(params));
        env
    }

    fn resolve_type(&self, te: &TypeExpr) -> Result<Type, String> {
        match te {
            TypeExpr::Named(name, _) => self.resolve_named(name),
            TypeExpr::Array(inner, Some(n), _) => {
                Ok(Type::Array(Box::new(self.resolve_type(inner)?), *n))
            }
            TypeExpr::Array(inner, None, _) => Ok(Type::Slice(Box::new(self.resolve_type(inner)?))),
            TypeExpr::Fun(params, ret, _) => Ok(Type::Fun(
                params
                    .iter()
                    .map(|p| self.resolve_type(p))
                    .collect::<Result<_, _>>()?,
                Box::new(self.resolve_type(ret)?),
            )),
            TypeExpr::Nullable(inner, _) => Ok(Type::Nullable(Box::new(self.resolve_type(inner)?))),
        }
    }

    fn resolve_named(&self, name: &str) -> Result<Type, String> {
        if let Some(k) = IntKind::from_name(name) {
            return Ok(Type::Int(k));
        }
        match name {
            "bool" => Ok(Type::Bool),
            "float32" => Ok(Type::Float(FloatKind::F32)),
            "float64" => Ok(Type::Float(FloatKind::F64)),
            "string" => Ok(Type::Str),
            "void" => Ok(Type::Void),
            "Self" => self
                .self_type
                .as_ref()
                .map(|s| self.type_by_name(s))
                .unwrap_or(Type::SelfType)
                .pipe(Ok),
            _ => self
                .resolve_type_ref(name)
                .ok_or_else(|| format!("unknown type `{name}`")),
        }
    }

    fn type_by_name(&self, name: &str) -> Type {
        self.resolve_type_ref(name)
            .unwrap_or_else(|| Type::Record(NominalType::new(-1, name)))
    }

    fn check_block_with_self(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
        self_type: &str,
    ) {
        self.check_block_with_self_context(b, scopes, ret, self_type, None);
    }

    fn check_block_with_self_variant(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
        self_type: &str,
        variant: &str,
    ) {
        self.check_block_with_self_context(b, scopes, ret, self_type, Some(variant));
    }

    fn check_block_with_self_context(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
        self_type: &str,
        variant: Option<&str>,
    ) {
        let saved = self.self_type.replace(self_type.to_string());
        let saved_variant = self.self_variant.clone();
        self.self_variant = variant.map(|v| (self_type.to_string(), v.to_string()));
        if let Some(scope) = scopes.last_mut() {
            scope.insert("self".to_string(), self.type_by_name(self_type));
        }
        self.check_block_root(b, scopes, ret);
        self.self_type = saved;
        self.self_variant = saved_variant;
    }

    fn check_block_root(&mut self, b: &Block, scopes: &mut ScopeStack, ret: Option<&Type>) {
        let saved = std::mem::replace(&mut self.const_scopes, vec![HashSet::new()]);
        self.return_contexts.push(match ret {
            Some(ty) => ReturnContext::Explicit(ty.clone()),
            None => ReturnContext::Inferred,
        });
        self.check_block(b, scopes);
        self.return_contexts.pop();
        self.const_scopes = saved;
    }

    fn check_block(&mut self, b: &Block, scopes: &mut ScopeStack) {
        scopes.push(HashMap::new());
        self.const_scopes.push(HashSet::new());
        for s in &b.stmts {
            self.check_stmt(s, scopes);
        }
        self.const_scopes.pop();
        scopes.pop();
    }

    /// Check a `return` against the active return context. The context is the
    /// top of `return_contexts`, pushed by `check_block_root` for a function or
    /// method body and by the closure checker for a closure body. Consulting
    /// the stack rather than a positionally-threaded parameter means a `return`
    /// nested inside an `if`/bare block/`match`-arm that is evaluated as an
    /// expression is still checked against the enclosing callable's declared
    /// type, and a `return` inside a closure is checked against the closure's
    /// own (inferred) context rather than the outer function (PLAN.md R5b).
    fn check_return(
        &mut self,
        value: Option<&Expr>,
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) {
        match self.return_contexts.last().cloned() {
            Some(ReturnContext::Explicit(want)) => match value {
                Some(e) => {
                    self.check_expr_against(e, &want, scopes);
                }
                None => self.expect_assignable(&Type::Void, &want, span),
            },
            // Inferred context (closure or unannotated function) or no context
            // (module top level): type the value but do not constrain it; the
            // return type is reconciled separately.
            _ => {
                if let Some(e) = value {
                    self.check_expr(e, scopes);
                }
            }
        }
    }

    fn check_stmt(&mut self, s: &Stmt, scopes: &mut ScopeStack) {
        match s {
            Stmt::Let {
                pat,
                ty,
                value,
                is_const,
                ..
            } => {
                let binding_ty = if let Some(te) = ty {
                    match self.resolve_type(te) {
                        Ok(annotated) => {
                            let got = self.check_expr_against(value, &annotated, scopes);
                            self.instantiate_annotated_type(&annotated, &got)
                        }
                        Err(message) => {
                            self.errors.push(TypeError {
                                message,
                                span: te.span(),
                            });
                            self.check_expr(value, scopes)
                        }
                    }
                } else {
                    self.check_expr(value, scopes)
                };
                self.check_pattern_against(&binding_ty, pat);
                self.bind_pattern(pat, &binding_ty, scopes);
                if *is_const {
                    self.record_expr_type_with(value, &binding_ty, Constness::Const);
                    self.bind_const_pattern(pat);
                }
            }
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => {
                let target_ty = self.check_place(target, scopes);
                if matches!(op, AssignOp::Eq) {
                    self.check_expr_against(value, &target_ty, scopes);
                } else {
                    let value_ty = self.check_expr(value, scopes);
                    let _ = self.check_binary(assign_binop(*op), &target_ty, &value_ty, *span);
                }
            }
            Stmt::Expr(e) => {
                self.check_expr(e, scopes);
            }
            Stmt::While { cond, body, .. } => {
                self.check_condition(cond, scopes);
                self.check_block(body, scopes);
            }
            Stmt::For {
                var, iter, body, ..
            } => {
                let iter_ty = self.check_expr(iter, scopes);
                let item_ty = match self.resolve(&iter_ty) {
                    Type::Array(inner, _) | Type::Slice(inner) => *inner,
                    other => {
                        if !is_maybe_iterable(&other) {
                            self.errors.push(TypeError {
                                message: format!("cannot iterate over `{}`", other.display()),
                                span: iter.span(),
                            });
                        }
                        self.fresh_unknown()
                    }
                };
                scopes.push(HashMap::from([(var.clone(), item_ty)]));
                self.const_scopes.push(HashSet::new());
                self.check_block(body, scopes);
                self.const_scopes.pop();
                scopes.pop();
            }
            Stmt::Return(value, span) => self.check_return(value.as_ref(), *span, scopes),
            Stmt::Break(_) | Stmt::Continue(_) => {}
        }
        self.apply_guard_narrowing(s, scopes);
    }

    fn check_expr_against(&mut self, expr: &Expr, want: &Type, scopes: &mut ScopeStack) -> Type {
        // An integer literal in an integer-typed required position takes that
        // type (DESIGN.md 5.3 contextual resolution): record it at the target
        // kind so its runtime tag matches the annotation rather than defaulting
        // to int32 (PLAN.md R4 typed literals).
        if let Expr::Int(v, _) = expr {
            let target = match self.resolve(want) {
                Type::Int(k) => Some(k),
                Type::Nullable(inner) => match *inner {
                    Type::Int(k) => Some(k),
                    _ => None,
                },
                _ => None,
            };
            if let Some(k) = target
                && int_fits_kind(*v, k)
            {
                let ty = Type::Int(k);
                self.record_expr_type(expr, &ty);
                return ty;
            }
        }
        if let (Expr::Array(items, span), Type::Array(elem, len)) = (expr, self.resolve(want)) {
            if items.len() != len {
                self.errors.push(TypeError {
                    message: format!(
                        "array literal has length {}, but `{}` requires length {}",
                        items.len(),
                        want.display(),
                        len
                    ),
                    span: *span,
                });
            }
            for item in items {
                let got = self.check_expr(item, scopes);
                self.expect_expr_assignable(&got, &elem, item);
            }
            let ty = Type::Array(elem, len);
            self.record_expr_type(expr, &ty);
            return ty;
        }
        let got = self.check_expr(expr, scopes);
        self.expect_expr_assignable(&got, want, expr);
        got
    }

    fn check_expr(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        let ty = self.check_expr_inner(e, scopes);
        self.record_expr_type(e, &ty);
        ty
    }

    fn record_expr_type(&mut self, expr: &Expr, ty: &Type) {
        let constness = self.expr_constness(expr);
        self.record_expr_type_with(expr, ty, constness);
    }

    fn record_expr_type_with(&mut self, expr: &Expr, ty: &Type, constness: Constness) {
        let ty = self.resolve(ty);
        let ty = if constness == Constness::Const {
            Type::ConstOf(Box::new(ty))
        } else {
            ty
        };
        self.typed.push_expr(expr, ty, constness);
    }

    fn expr_constness(&self, expr: &Expr) -> Constness {
        match expr {
            Expr::Ident(name, _) if self.is_const_binding(name) => Constness::Const,
            Expr::Field(base, _, _) | Expr::Index(base, _, _)
                if self.expr_constness(base) == Constness::Const =>
            {
                Constness::Const
            }
            _ => Constness::Unknown,
        }
    }

    fn check_error_propagation_return_context(&mut self, span: prepoly_lexer::Span) {
        match self.return_contexts.last() {
            Some(ReturnContext::Inferred) => {}
            Some(ReturnContext::Explicit(ret)) if is_result_return_type(&self.resolve(ret)) => {}
            Some(ReturnContext::Explicit(ret)) => {
                self.errors.push(TypeError {
                    message: format!(
                        "error propagation requires `Result` return type, found `{}`",
                        self.resolve(ret).display()
                    ),
                    span,
                });
            }
            None => {
                self.errors.push(TypeError {
                    message: "error propagation cannot be used outside a function or closure"
                        .to_string(),
                    span,
                });
            }
        }
    }

    fn wrap_inferred_fallible_return(&mut self, ok: Type, errors: &[(Type, Span)]) -> Type {
        if errors.is_empty() {
            return ok;
        }
        let err = self
            .reconcile_error_payloads(errors, true)
            .unwrap_or_else(|| self.fresh_unknown());
        Type::result(ok, err)
    }

    fn is_const_binding(&self, name: &str) -> bool {
        self.const_scopes
            .iter()
            .rev()
            .any(|scope| scope.contains(name))
    }

    fn bind_const_pattern(&mut self, pat: &Pattern) {
        let mut names = Vec::new();
        self.collect_const_bindings(pat, &mut names);
        if let Some(scope) = self.const_scopes.last_mut() {
            scope.extend(names);
        }
    }

    fn collect_const_bindings(&self, pat: &Pattern, out: &mut Vec<String>) {
        match pat {
            Pattern::Binding(name, _) => {
                if !self.is_unit_variant_name(name) {
                    out.push(name.clone());
                }
            }
            Pattern::Record(_, fields, _) => {
                for field in fields {
                    if let Some(pat) = &field.pat {
                        self.collect_const_bindings(pat, out);
                    } else {
                        out.push(field.name.clone());
                    }
                }
            }
            Pattern::Array(items, _) => {
                for item in items {
                    self.collect_const_bindings(item, out);
                }
            }
            Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
        }
    }

    fn check_expr_inner(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        match e {
            Expr::Int(_, _) => Type::Int(IntKind::I32),
            Expr::Float(_, _) => Type::Float(FloatKind::F64),
            Expr::Bool(_, _) => Type::Bool,
            Expr::Null(_) => Type::null(),
            Expr::Str(segs, _) => {
                for seg in segs {
                    if let StrSeg::Expr(e) = seg {
                        self.check_expr(e, scopes);
                    }
                }
                Type::Str
            }
            Expr::Ident(name, span) => {
                if let Some(t) = self.lookup(scopes, name) {
                    t
                } else if self.is_resolvable_free_name(name) {
                    // A free function or runtime builtin used as a first-class
                    // value. Its precise function type is recovered at the call
                    // site; here we only need to accept the name as resolved.
                    self.fresh_unknown()
                } else {
                    // An undeclared value name. Name resolution is a hard
                    // pre-execution check (DESIGN.md section 6), so this is an
                    // error rather than a fresh unknown that would launder into
                    // any required type and run as `void`.
                    self.errors.push(TypeError {
                        message: format!("unknown name `{name}`"),
                        span: *span,
                    });
                    self.fresh_unknown()
                }
            }
            Expr::SelfExpr(span) => scopes
                .iter()
                .rev()
                .find_map(|s| s.get("self").cloned())
                .or_else(|| self.self_type.as_ref().map(|s| self.type_by_name(s)))
                .unwrap_or_else(|| {
                    // `self` is only meaningful inside an instance method.
                    self.errors.push(TypeError {
                        message: "`self` is only valid inside a method".to_string(),
                        span: *span,
                    });
                    self.fresh_unknown()
                }),
            Expr::Unary(op, inner, span) => {
                let ty = self.check_expr(inner, scopes);
                self.check_unary(*op, &ty, *span)
            }
            Expr::Binary(op, a, b, span) => {
                let left = self.check_expr(a, scopes);
                let right = self.check_expr(b, scopes);
                self.check_binary_expr(*op, a, &left, b, &right, *span)
            }
            Expr::Call(callee, args, span) => self.check_call(callee, args, *span, scopes),
            Expr::Field(base, name, span) => self.check_field(base, name, *span, scopes),
            Expr::Index(base, idx, span) => {
                let base_ty = self.check_expr(base, scopes);
                let idx_ty = self.check_expr(idx, scopes);
                self.expect_int_index(&idx_ty, idx.span());
                match self.resolve(&base_ty) {
                    Type::Array(inner, _) | Type::Slice(inner) => *inner,
                    Type::Str => Type::Str,
                    Type::Nullable(_) => {
                        self.report_nullable_use(*span);
                        self.fresh_unknown()
                    }
                    other => {
                        if let Type::Unknown(_) = other {
                            // Defer, but record that the receiver must be
                            // indexable so a closure like `(x) -> x[0]` rejects
                            // a non-indexable argument at its call site
                            // (PLAN.md R2).
                            self.record_shape(&base_ty, ShapeConstraint::Indexable);
                        } else if !is_maybe_indexable(&other) {
                            self.errors.push(TypeError {
                                message: format!("cannot index `{}`", other.display()),
                                span: *span,
                            });
                        }
                        self.fresh_unknown()
                    }
                }
            }
            Expr::ErrorProp(inner, span) => {
                let ty = self.check_expr(inner, scopes);
                let resolved = self.resolve(&ty);
                match resolved.result_payloads() {
                    Some((ok, _)) => {
                        self.check_error_propagation_return_context(*span);
                        ok.clone()
                    }
                    None if resolved.is_result_type() => {
                        self.check_error_propagation_return_context(*span);
                        self.fresh_unknown()
                    }
                    None if resolved.is_unknown() => self.fresh_unknown(),
                    None => {
                        self.errors.push(TypeError {
                            message: format!(
                                "error propagation requires `Result`, found `{}`",
                                resolved.display()
                            ),
                            span: inner.span(),
                        });
                        self.fresh_unknown()
                    }
                }
            }
            Expr::Closure(params, body, _) => {
                self.report_duplicate_params("closure", params);
                let mut inferred_env = env_from_scopes(scopes);
                let closure_scope = self.param_scope(params);
                inferred_env.extend(closure_scope.clone());
                let mut propagated_errors = Vec::new();
                self.infer_expr_light(body, &inferred_env, &mut propagated_errors);
                let mut closure_scopes = scopes.clone();
                closure_scopes.push(closure_scope);
                self.const_scopes.push(HashSet::new());
                self.return_contexts.push(ReturnContext::Inferred);
                let ret = self.check_expr(body, &mut closure_scopes);
                self.return_contexts.pop();
                self.const_scopes.pop();
                let ret = self.wrap_inferred_fallible_return(ret, &propagated_errors);
                // Reuse the parameter types from the scope the body was checked
                // against, so an unannotated parameter's inference variable is
                // shared between the `Fun` parameter and the return type. This
                // keeps the relationship between input and output (e.g. the
                // identity closure `(x) -> x` has type `(U) -> U` for the same
                // `U`), which `apply_callable` then instantiates per call site.
                // Without this the parameter would get a brand-new unknown,
                // letting `let s: string = ((x) -> x)(1)` type-check unsoundly.
                let frame = closure_scopes.last().expect("closure scope frame");
                let param_types = params
                    .iter()
                    .map(|p| {
                        frame
                            .get(&p.name)
                            .cloned()
                            .unwrap_or_else(|| self.fresh_unknown())
                    })
                    .collect();
                Type::Fun(param_types, Box::new(ret))
            }
            Expr::Array(es, _) => {
                let elem_ty = es
                    .first()
                    .map(|e| self.check_expr(e, scopes))
                    .unwrap_or_else(|| self.fresh_empty_array_elem());
                for e in es.iter().skip(1) {
                    let got = self.check_expr(e, scopes);
                    self.expect_expr_assignable(&got, &elem_ty, e);
                }
                Type::Slice(Box::new(elem_ty))
            }
            Expr::TypeLit(name, fields, span) => self.check_record_lit(name, fields, *span, scopes),
            Expr::VariantLit(t, variant, fields, span) => {
                self.check_variant_lit(t, variant, fields, *span, scopes)
            }
            Expr::If(cond, then, els, span) => {
                let cond_ty = self.check_condition(cond, scopes);
                let truth = cond_ty.static_truthiness();
                let mut then_scopes = scopes.clone();
                self.apply_truthy_narrowing(cond, &mut then_scopes);
                // A statically-known condition makes one arm unreachable. Its
                // body is still walked (so nested call instances are recorded for
                // monomorphization) but its type errors are discarded: a dead
                // path may not type-check -- e.g. a bare `null` (`never?`) whose
                // truthy arm narrows it to `never` -- yet must not reject the
                // program. The reachable arm alone determines the `if` type.
                let then_ty =
                    self.check_branch(then, &mut then_scopes, truth == Some(false));
                let else_ty = match els {
                    Some(e) => self.check_branch_expr(e, scopes, truth == Some(true)),
                    None => Type::Void,
                };
                match truth {
                    Some(true) => then_ty,
                    Some(false) => else_ty,
                    None => self.common_type_or_error("if", then_ty, else_ty, *span),
                }
            }
            Expr::IfLet(pat, scrut, then, els, span) => {
                let scrut_ty = self.check_expr(scrut, scopes);
                self.check_pattern_against(&scrut_ty, pat);
                let mut then_scopes = scopes.clone();
                then_scopes.push(HashMap::new());
                self.const_scopes.push(HashSet::new());
                self.bind_pattern(pat, &scrut_ty, &mut then_scopes);
                let then_ty = self.check_block_expr(then, &mut then_scopes);
                self.const_scopes.pop();
                let else_ty = els
                    .as_ref()
                    .map(|e| self.check_expr(e, scopes))
                    .unwrap_or(Type::Void);
                self.common_type_or_error("if-let", then_ty, else_ty, *span)
            }
            Expr::Match(scrut, arms, span) => {
                let scrut_ty = self.check_expr(scrut, scopes);
                let mut result_ty: Option<Type> = None;
                for arm in arms {
                    self.check_pattern_against(&scrut_ty, &arm.pattern);
                    let mut arm_scopes = scopes.clone();
                    arm_scopes.push(HashMap::new());
                    self.const_scopes.push(HashSet::new());
                    self.bind_pattern(&arm.pattern, &scrut_ty, &mut arm_scopes);
                    let arm_ty = self.check_expr(&arm.body, &mut arm_scopes);
                    self.const_scopes.pop();
                    if let Some(prev) = &result_ty {
                        result_ty =
                            Some(self.common_type_or_error("match", prev.clone(), arm_ty, *span));
                    } else {
                        result_ty = Some(arm_ty);
                    }
                }
                result_ty.unwrap_or(Type::Void)
            }
            Expr::Block(b, _) => self.check_block_expr(b, scopes),
        }
    }

    fn common_type_or_unknown(&mut self, left: Type, right: Type) -> Type {
        if let Some(nullable) = common_nullable_type(&left, &right) {
            return nullable;
        }
        if self.can_unify(&left, &right)
            || crate::structural::types_compatible(self.program, &left, &right)
        {
            left
        } else {
            self.fresh_unknown()
        }
    }

    fn common_type_or_error(
        &mut self,
        context: &str,
        left: Type,
        right: Type,
        span: prepoly_lexer::Span,
    ) -> Type {
        if let Some(nullable) = common_nullable_type(&left, &right) {
            return nullable;
        }
        if self.can_unify(&left, &right)
            || crate::structural::types_compatible(self.program, &left, &right)
        {
            return left;
        }
        if !matches!(left, Type::Unknown(_)) && !matches!(right, Type::Unknown(_)) {
            self.errors.push(TypeError {
                message: format!(
                    "`{context}` branches have incompatible types `{}` and `{}`",
                    left.display(),
                    right.display()
                ),
                span,
            });
        }
        self.fresh_unknown()
    }

    /// Type an `if` block arm, discarding its errors when `dead` (statically
    /// unreachable). The arm is still walked so its nested call instances reach
    /// monomorphization; only the type errors -- which a dead path is allowed to
    /// have -- are rolled back.
    fn check_branch(&mut self, b: &Block, scopes: &mut ScopeStack, dead: bool) -> Type {
        let mark = self.errors.len();
        let ty = self.check_block_expr(b, scopes);
        if dead {
            self.errors.truncate(mark);
        }
        ty
    }

    /// As `check_branch`, for an `else` arm (a nested expression rather than a
    /// block; an `else if` chain or a braced block lowered to an expression).
    fn check_branch_expr(&mut self, e: &Expr, scopes: &mut ScopeStack, dead: bool) -> Type {
        let mark = self.errors.len();
        let ty = self.check_expr(e, scopes);
        if dead {
            self.errors.truncate(mark);
        }
        ty
    }

    fn check_block_expr(&mut self, b: &Block, scopes: &mut ScopeStack) -> Type {
        scopes.push(HashMap::new());
        self.const_scopes.push(HashSet::new());
        let mut last = Type::Void;
        for s in &b.stmts {
            match s {
                Stmt::Expr(e) => last = self.check_expr(e, scopes),
                _ => {
                    self.check_stmt(s, scopes);
                    last = Type::Void;
                }
            }
        }
        self.const_scopes.pop();
        scopes.pop();
        last
    }

    fn check_place(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        let ty = match e {
            Expr::Field(base, name, span) => self.check_field(base, name, *span, scopes),
            Expr::Index(base, idx, span) => {
                let base_ty = self.check_expr(base, scopes);
                let idx_ty = self.check_expr(idx, scopes);
                self.expect_int_index(&idx_ty, idx.span());
                match self.resolve(&base_ty) {
                    Type::Array(inner, _) | Type::Slice(inner) => *inner,
                    Type::Nullable(_) => {
                        self.report_nullable_use(*span);
                        self.fresh_unknown()
                    }
                    other => {
                        if !is_maybe_indexable(&other) {
                            self.errors.push(TypeError {
                                message: format!("cannot index `{}`", other.display()),
                                span: *span,
                            });
                        }
                        self.fresh_unknown()
                    }
                }
            }
            // A place must be assignable: a variable, `self`, or a projection of
            // one. Anything else (a literal, call result, etc.) is not a valid
            // assignment target.
            Expr::Ident(..) | Expr::SelfExpr(_) => return self.check_expr(e, scopes),
            other => {
                self.errors.push(TypeError {
                    message: "invalid assignment target".to_string(),
                    span: other.span(),
                });
                return self.check_expr(e, scopes);
            }
        };
        self.record_expr_type(e, &ty);
        ty
    }

    /// Type a condition and return its resolved type. A condition may be of any
    /// type; its runtime truthiness is derived from the type rather than
    /// restricting what is accepted: a `bool` is used directly, a nullable tests
    /// non-null (and narrows on the truthy arm), and any other (non-nullable)
    /// type is unconditionally true. The resolved type lets callers fold a
    /// statically-known condition (see `static_truthiness`).
    fn check_condition(&mut self, cond: &Expr, scopes: &mut ScopeStack) -> Type {
        let ty = self.check_expr(cond, scopes);
        self.resolve(&ty)
    }

    fn check_record_lit(
        &mut self,
        name: &str,
        fields: &[(String, Expr)],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        let tn = self.resolve_self_name(name);
        let Some(symbol) = self.resolve_type_symbol(&tn) else {
            return self.fresh_unknown();
        };
        let Some(info) = self.program.types.get(&symbol) else {
            return self.fresh_unknown();
        };
        let TypeKind::Record {
            fields: declared, ..
        } = &info.kind
        else {
            return self.fresh_unknown();
        };
        let ret = info.type_ref();
        let substitution = self.check_lit_fields(&symbol, None, declared, fields, span, scopes);
        apply_nominal_substitution(ret, substitution)
    }

    fn check_variant_lit(
        &mut self,
        t: &str,
        variant: &str,
        fields: &[(String, Expr)],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        let tn = self.resolve_self_name(t);
        let Some(symbol) = self.resolve_type_symbol(&tn) else {
            return self.fresh_unknown();
        };
        let Some(info) = self.program.types.get(&symbol) else {
            return self.fresh_unknown();
        };
        let Some(var) = info.variant(variant) else {
            return self.fresh_unknown();
        };
        let ret = info.type_ref();
        let substitution = self.check_lit_fields(
            &format!("{symbol}.{variant}"),
            Some(variant),
            &var.fields,
            fields,
            span,
            scopes,
        );
        apply_nominal_substitution(ret, substitution)
    }

    fn check_lit_fields(
        &mut self,
        who: &str,
        variant: Option<&str>,
        declared: &[prepoly_hir::FieldInfo],
        fields: &[(String, Expr)],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Substitution {
        let mut substitution = Substitution::empty();
        let mut seen = HashSet::new();
        for (name, expr) in fields {
            if !seen.insert(name) {
                self.errors.push(TypeError {
                    message: format!("`{who}` literal repeats field `{name}`"),
                    span: expr.span(),
                });
            }
        }
        for field in declared {
            match fields.iter().find(|(name, _)| name == &field.name) {
                Some((_, expr)) => {
                    let got = if let Some(want) = &field.resolved_ty {
                        self.check_expr_against(expr, want, scopes)
                    } else {
                        self.check_expr(expr, scopes)
                    };
                    if field.resolved_ty.as_ref().is_some_and(Type::is_unknown) {
                        substitution.insert(field_substitution_key(variant, &field.name), got);
                    }
                }
                None => self.errors.push(TypeError {
                    message: format!("`{who}` literal is missing field `{}`", field.name),
                    span,
                }),
            }
        }
        for (name, expr) in fields {
            if !declared.iter().any(|f| f.name == *name) {
                self.errors.push(TypeError {
                    message: format!("`{who}` has no field `{name}`"),
                    span: expr.span(),
                });
                self.check_expr(expr, scopes);
            }
        }
        substitution
    }

    /// A fieldless variant written without braces (`Sum.Variant`) is a value of
    /// the enclosing sum type (DESIGN.md 4.2.2). `base` must name a sum type
    /// rather than a value in scope. Returns `None` when this is an ordinary
    /// field access. Variants with fields are excluded: they require `{ ... }`
    /// construction, handled elsewhere.
    fn unit_variant_type(&self, base: &Expr, name: &str, in_scope: bool) -> Option<Type> {
        let Expr::Ident(type_name, _) = base else {
            return None;
        };
        if in_scope {
            return None;
        }
        let resolved = self.resolve_self_name(type_name);
        let info = self.program.types.get(&resolved)?;
        let variant = info.variant(name)?;
        if variant.fields.is_empty() {
            Some(info.type_ref())
        } else {
            None
        }
    }

    fn check_field(
        &mut self,
        base: &Expr,
        name: &str,
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        if let Some(ty) = self.unit_variant_type(base, name, self.is_in_scope(base, scopes)) {
            return ty;
        }
        // `Sum.X` in value position is only valid for a fieldless variant
        // (handled above). Anything else is either a missing variant or a
        // variant that requires `{ ... }` construction.
        if let Expr::Ident(tname, _) = base
            && !self.is_in_scope(base, scopes)
        {
            let resolved = self.resolve_self_name(tname);
            if let Some(info) = self.program.types.get(&resolved)
                && info.is_sum()
            {
                let message = match info.variant(name) {
                    Some(_) => format!(
                        "variant `{resolved}.{name}` has fields; construct it with `{resolved}.{name} {{ ... }}`"
                    ),
                    None => format!("`{resolved}` has no variant `{name}`"),
                };
                self.errors.push(TypeError { message, span });
                return self.fresh_unknown();
            }
        }
        let base_ty = self.check_expr(base, scopes);
        match self.resolve(&base_ty) {
            Type::Record(record) => {
                if let Some(ty) = record.substitution.get(name) {
                    return ty.clone();
                }
                let Some(info) = self.program.type_by_id(record.id) else {
                    return self.fresh_unknown();
                };
                let TypeKind::Record { fields, methods } = &info.kind else {
                    return self.fresh_unknown();
                };
                if let Some(field) = fields.iter().find(|f| f.name == name) {
                    return field
                        .resolved_ty
                        .clone()
                        .unwrap_or_else(|| self.fresh_unknown());
                }
                // A bare `recv.method` (method as a value) is left to the
                // runtime; only genuinely-absent members are a static error.
                if methods.contains_key(name) {
                    return self.fresh_unknown();
                }
                self.errors.push(TypeError {
                    message: format!("`{record}` has no field `{name}`"),
                    span,
                });
                self.fresh_unknown()
            }
            Type::Sum(sum) => {
                if let Some(variant_ty) = self.self_variant_field_type(base, &sum, name) {
                    return variant_ty;
                }
                if let Some(common_ty) = self.common_sum_field_type(&sum, name) {
                    common_ty
                } else {
                    self.errors.push(TypeError {
                        message: format!("`{sum}` has no common field `{name}`"),
                        span,
                    });
                    self.fresh_unknown()
                }
            }
            Type::Nullable(_) => {
                self.report_nullable_use(span);
                self.fresh_unknown()
            }
            // A primitive has no fields; accessing one is a static error rather
            // than a deferred runtime shape (DESIGN.md 5.8). Method calls are
            // handled separately in `check_call`.
            other if is_concrete_primitive(&other) => {
                self.errors.push(TypeError {
                    message: format!("`{}` has no field `{name}`", other.display()),
                    span,
                });
                self.fresh_unknown()
            }
            // An unknown receiver defers: record that it must expose this field
            // so a closure like `(x) -> x.name` rejects a record without `name`
            // at its call site (PLAN.md R2).
            Type::Unknown(_) => {
                self.record_shape(&base_ty, ShapeConstraint::HasField(name.to_string()));
                self.fresh_unknown()
            }
            _ => self.fresh_unknown(),
        }
    }

    fn self_variant_field_type(
        &mut self,
        base: &Expr,
        sum: &NominalType,
        name: &str,
    ) -> Option<Type> {
        if !is_self_expr(base) {
            return None;
        }
        let (self_sum, variant) = self.self_variant.clone()?;
        if self_sum != sum.name() {
            return None;
        }
        self.variant_field_type(sum, &variant, name)
    }

    fn variant_field_type(&mut self, sum: &NominalType, variant: &str, name: &str) -> Option<Type> {
        let fallback = self
            .program
            .types
            .get(sum.name())?
            .variant(variant)?
            .fields
            .iter()
            .find(|field| field.name == name)
            .map(|field| field.resolved_ty.clone());
        let key = field_substitution_key(Some(variant), name);
        Some(
            sum.substitution
                .get(&key)
                .cloned()
                .or_else(|| fallback.flatten())
                .unwrap_or_else(|| self.fresh_unknown()),
        )
    }

    fn common_sum_field_type(&mut self, sum: &NominalType, name: &str) -> Option<Type> {
        let field_types = match &self.program.type_by_id(sum.id)?.kind {
            TypeKind::Sum { variants } => variants
                .iter()
                .map(|variant| {
                    let field = variant.fields.iter().find(|field| field.name == name)?;
                    Some((
                        field_substitution_key(Some(&variant.name), name),
                        field.resolved_ty.clone(),
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
            TypeKind::Record { .. } => return None,
        };
        let mut types = Vec::with_capacity(field_types.len());
        for (key, ty) in field_types {
            types.push(
                sum.substitution
                    .get(&key)
                    .cloned()
                    .or(ty)
                    .unwrap_or_else(|| self.fresh_unknown()),
            );
        }
        // On a bare sum value (no per-value refinement -- e.g. a parameter, or a
        // value widened from a refined one) every variant is possible, so an
        // unannotated (dynamic) field in any variant means the value of that variant
        // carries an arbitrary-typed field: reject common access (read it by matching
        // the variant). A refined value's substitution pins the constructed variant,
        // so its dynamic sibling variants do not make the access unsound -- this is
        // what keeps widening a refined sum to its bare nominal sound.
        if sum.substitution.is_empty() && types.iter().any(|ty| self.resolve(ty).is_unknown()) {
            return None;
        }
        let candidate = types
            .iter()
            .find(|ty| !self.resolve(ty).is_unknown())
            .or_else(|| types.first())?;
        types
            .iter()
            .all(|ty| self.can_unify(candidate, ty))
            .then(|| candidate.clone())
    }

    fn check_call(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        if let Expr::Ident(name, _) = callee {
            if name == "error" {
                let err_ty = args
                    .first()
                    .map(|a| self.check_expr(&a.expr, scopes))
                    .unwrap_or(Type::Void);
                return Type::result(self.fresh_unknown(), err_ty);
            }
            if let Some(ret) = self.builtin_function_type(name, args, span, scopes) {
                return ret;
            }
            // A local binding (e.g. a closure parameter) shadows a same-named
            // global function, matching codegen's resolution order.
            if let Some(local) = self.lookup(scopes, name) {
                return self.check_callable_value(local, args, span, scopes);
            }
            // Only a function visible from the current module resolves here; a
            // function defined in another, non-imported module is invisible and
            // falls through to the unknown-name path below (PLAN.md R5). The
            // lookup is module-aware so a name defined in several modules
            // resolves to this module's own or imported definition (R2).
            if let Some(info) = self.lookup_function(name) {
                let decl = info.decl.clone();
                let signature_params = info.signature.params.clone();
                let declared_ret = info.signature.ret_ty.clone();
                let symbol = info.symbol.clone();
                let module = info.module.clone();
                self.check_arg_count_range(name, &signature_params, args.len(), span);
                let arg_types = self.check_signature_args_collect(&signature_params, args, scopes);
                let fallback_ret = declared_ret
                    .clone()
                    .or_else(|| self.function_returns.get(&symbol).cloned())
                    .unwrap_or_else(|| self.fresh_unknown());
                // Record a fully-concrete call instance for static
                // monomorphization (PLAN.md R5 stage 5).
                let resolved_args: Vec<Type> = arg_types.iter().map(|t| self.resolve(t)).collect();
                if resolved_args.iter().all(is_concrete_type) {
                    let entry = self.fn_instances.entry(symbol.clone()).or_default();
                    if !entry.iter().any(|t| t == &resolved_args) {
                        entry.push(resolved_args);
                    }
                }
                return self.instantiate_function_call(
                    &symbol,
                    &module,
                    &signature_params,
                    &decl.body,
                    declared_ret,
                    fallback_ret,
                    &arg_types,
                );
            }
            // The callee is a bare identifier that is not `error`, a builtin, a
            // local value, or a known free function. A runtime builtin (e.g.
            // `println` when the stdlib is not loaded) still defers below; any
            // other name is undeclared and reported here rather than collapsing
            // to a fresh unknown (PLAN.md R5a).
            if !self.is_resolvable_free_name(name) && !self.is_type_word(name) {
                self.errors.push(TypeError {
                    message: format!("unknown function `{name}`"),
                    span,
                });
                for a in args {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
        }
        if let Expr::Field(base, method, _) = callee {
            if let Some(qualifier) = self.static_qualifier(base, scopes) {
                return self.check_static_call(&qualifier, method, args, span, scopes);
            }
            let recv_ty = self.check_expr(base, scopes);
            if let Type::Nullable(_) = self.resolve(&recv_ty) {
                self.report_nullable_use(base.span());
            }
            if let Some(ret) = self.builtin_method_type(&recv_ty, method, args, scopes, span) {
                return ret;
            }
            if let Some(methods) = self.methods_for_type(&recv_ty, method) {
                self.check_common_method_signatures(&methods, method, span);
                let first_signature = &methods[0].signature;
                let skip_self = first_signature
                    .params
                    .first()
                    .is_some_and(|p| p.name == "self");
                // A method without a `self` parameter is static and must be
                // called as `Type.method(..)`, not through an instance.
                if !skip_self {
                    self.errors.push(TypeError {
                        message: format!(
                            "`{method}` is a static method; call it as `Type.{method}(...)`"
                        ),
                        span,
                    });
                }
                let signature_params: Vec<ParamInfo> = if skip_self {
                    first_signature.params[1..].to_vec()
                } else {
                    first_signature.params.clone()
                };
                self.check_arg_count(method, signature_params.len(), args.len(), span);
                let arg_types = self.check_signature_args_collect(&signature_params, args, scopes);
                let mut returns = Vec::with_capacity(methods.len());
                for resolved in methods {
                    let declared_ret = resolved.signature.ret_ty.clone();
                    let fallback_ret = declared_ret
                        .clone()
                        .or_else(|| {
                            self.method_returns
                                .get(&(resolved.qualifier.clone(), method.to_string()))
                                .cloned()
                        })
                        .unwrap_or(Type::Void);
                    returns.push(self.instantiate_method_call(MethodCall {
                        owner: &resolved.qualifier,
                        self_type: &resolved.self_type,
                        name: method,
                        method: &resolved.method,
                        signature_params: &resolved.signature.params,
                        receiver_ty: if skip_self {
                            Some(recv_ty.clone())
                        } else {
                            None
                        },
                        declared_ret,
                        fallback_ret,
                        arg_types: &arg_types,
                    }));
                }
                return self
                    .common_type_list(&returns)
                    .unwrap_or_else(|| self.fresh_unknown());
            }
            // UFCS (DESIGN.md 9.4): `recv.f(args)` falls back to the free
            // function `f(recv, args)` when the receiver has no such method.
            if self.lookup(scopes, method).is_none()
                && let Some(ret) = self.check_ufcs_call(&recv_ty, method, args, span, scopes)
            {
                return ret;
            }
            if let Type::Record(record) = self.resolve(&recv_ty) {
                self.errors.push(TypeError {
                    message: format!("`{record}` has no method `{method}`"),
                    span,
                });
                for a in args {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
            if let Type::Sum(sum) = self.resolve(&recv_ty) {
                self.errors.push(TypeError {
                    message: format!("`{sum}` has no common method `{method}`"),
                    span,
                });
                for a in args {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
            // A primitive receiver has a fully known type with no user methods,
            // so an unresolved call is a static error rather than deferred
            // structural dispatch (DESIGN.md 5.8 use-site shape constraints).
            let resolved = self.resolve(&recv_ty);
            if is_concrete_primitive(&resolved) {
                self.errors.push(TypeError {
                    message: format!("`{}` has no method `{method}`", resolved.display()),
                    span,
                });
                for a in args {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
            // Otherwise the member resolves at runtime (builtin methods, or
            // deferred structural dispatch). If the receiver is an unknown
            // inference variable, record that it must expose this method so a
            // closure like `(x) -> x.speak()` rejects an `int32` argument at
            // its call site (PLAN.md R2). Evaluate the args and defer.
            if let Type::Unknown(_) = resolved {
                self.record_shape(&recv_ty, ShapeConstraint::HasMethod(method.to_string()));
            }
            for a in args {
                self.check_expr(&a.expr, scopes);
            }
            return self.fresh_unknown();
        }
        let callee_ty = self.check_expr(callee, scopes);
        self.apply_callable(callee_ty, args, span, scopes)
    }

    /// Type-check a UFCS method call `recv.f(args)` as `f(recv, args)` when `f`
    /// is a known free function. Returns `None` if no such function exists, so
    /// the caller can defer to runtime dispatch.
    fn check_ufcs_call(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        let info = self.lookup_function(method)?;
        let decl = info.decl.clone();
        let signature_params = info.signature.params.clone();
        let declared_ret = info.signature.ret_ty.clone();
        let symbol = info.symbol.clone();
        let module = info.module.clone();
        let fallback_ret = declared_ret
            .clone()
            .or_else(|| self.function_returns.get(&symbol).cloned())
            .unwrap_or_else(|| self.fresh_unknown());
        self.check_arg_count(method, signature_params.len(), args.len() + 1, span);
        // The receiver fills the first parameter.
        if let Some(first) = signature_params.first()
            && let Some(want) = param_expected_type(first)
        {
            self.expect_assignable(recv_ty, want, span);
        }
        let mut arg_types = vec![recv_ty.clone()];
        if signature_params.len() > 1 {
            arg_types.extend(self.check_signature_args_collect(
                &signature_params[1..],
                args,
                scopes,
            ));
        } else {
            for a in args {
                arg_types.push(self.check_expr(&a.expr, scopes));
            }
        }
        Some(self.instantiate_function_call(
            &symbol,
            &module,
            &signature_params,
            &decl.body,
            declared_ret,
            fallback_ret,
            &arg_types,
        ))
    }

    /// Type-check a call whose callee is a value (closure/function value).
    fn check_callable_value(
        &mut self,
        callee_ty: Type,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        self.apply_callable(callee_ty, args, span, scopes)
    }

    /// Given a resolved callee type, check argument compatibility for `Fun`
    /// types and yield the call's result type. Each argument is checked exactly
    /// once here.
    fn apply_callable(
        &mut self,
        callee_ty: Type,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        match self.resolve(&callee_ty) {
            Type::Fun(params, ret) => {
                self.check_arg_count("<closure>", params.len(), args.len(), span);
                // Instantiate the (possibly polymorphic) callable for this call
                // site: unify each concrete argument into the parameter type,
                // then resolve the declared return type through that local
                // substitution. This recovers the result of an unannotated
                // closure such as `(x) -> x` applied to `int32` as `int32`
                // instead of an unconstrained unknown, so a later
                // `let s: string = f(1)` is correctly rejected.
                let mut subst = Subst::new();
                for (idx, arg) in args.iter().enumerate() {
                    if let Some(param) = params.get(idx) {
                        let got = self.check_expr_against(&arg.expr, param, scopes);
                        let _ = subst.unify(param, &got);
                        // Verify any structural constraints the closure body
                        // recorded on this parameter (e.g. `(x) -> x + 1`
                        // requires a numeric argument) now that the concrete
                        // argument type is known (PLAN.md R2).
                        self.verify_shape_constraints(param, &got, arg.expr.span());
                    } else {
                        self.check_expr(&arg.expr, scopes);
                    }
                }
                subst.resolve_deep(&ret)
            }
            _ => {
                for arg in args {
                    self.check_expr(&arg.expr, scopes);
                }
                self.fresh_unknown()
            }
        }
    }

    fn builtin_function_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        // `len` is a runtime primitive (DESIGN.md 9.1) usable as a free
        // function. Its result is always `int64`, and its single argument must
        // be a collection or string; a concrete non-collection argument is a
        // static error rather than a deferred runtime panic.
        if name == "len" {
            self.check_arg_count("len", 1, args.len(), span);
            let arg_ty = args
                .first()
                .map(|a| self.check_expr(&a.expr, scopes))
                .unwrap_or(Type::Void);
            for a in args.iter().skip(1) {
                self.check_expr(&a.expr, scopes);
            }
            if let Some(arg) = args.first() {
                let resolved = self.resolve(&arg_ty);
                if !is_maybe_indexable(&resolved) {
                    self.errors.push(TypeError {
                        message: format!(
                            "`len` expects an array or string, found `{}`",
                            resolved.display()
                        ),
                        span: arg.expr.span(),
                    });
                }
            }
            return Some(Type::Int(IntKind::I64));
        }
        if matches!(name, "print" | "println") {
            args.iter().for_each(|a| {
                self.check_expr(&a.expr, scopes);
            });
            return Some(Type::Void);
        }
        if name == "input" {
            self.check_arg_count("input", 0, args.len(), span);
            args.iter().for_each(|a| {
                self.check_expr(&a.expr, scopes);
            });
            return Some(Type::Str);
        }
        if let Some(ret) = self.array_builtin_type(name, args, span, scopes) {
            return Some(ret);
        }
        if let Some(ret) = self.string_builtin_type(name, args, span, scopes) {
            return Some(ret);
        }
        if let Some(ret) = self.numeric_helper_type(name, args, span, scopes) {
            return Some(ret);
        }
        if let Some(ret) = self.concurrency_builtin_type(name, args, span, scopes) {
            return Some(ret);
        }
        if name == "open" {
            // `open(path: string, mode: string) -> File!` (DESIGN.md 9.1).
            self.check_builtin_args_against("open", args, &[Type::Str, Type::Str], span, scopes);
            return Some(Type::result(self.type_by_name("File"), Type::Str));
        }
        None
    }

    /// Static contracts for the numeric runtime helpers (DESIGN.md 9.1). These
    /// map onto LLVM/runtime primitives, so the value class of each argument
    /// must be correct before the runtime reads its payload bits: passing a
    /// float to `_int_to_string`, for example, would reinterpret a bit pattern
    /// as an integer. Concrete wrong classes are static errors; unknown
    /// arguments stay deferred to the runtime tag checks.
    fn numeric_helper_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        let i64_ty = Type::Int(IntKind::I64);
        let f64_ty = Type::Float(FloatKind::F64);
        let (params, ret): (Vec<NumericClass>, Type) = match name {
            "_int_to_string" => (vec![NumericClass::Int], Type::Str),
            "_float_to_string" => (vec![NumericClass::Float], Type::Str),
            "_int_parse" => (vec![NumericClass::Str], Type::result(i64_ty, Type::Str)),
            "_float_parse" => (vec![NumericClass::Str], Type::result(f64_ty, Type::Str)),
            "_int_to_float" => (vec![NumericClass::Int, NumericClass::Int], f64_ty),
            "_float_to_int" => (
                vec![NumericClass::Float, NumericClass::Int, NumericClass::Bool],
                Type::result(i64_ty, Type::Str),
            ),
            "_float_sqrt" | "_float_floor" | "_float_ceil" => (vec![NumericClass::Float], f64_ty),
            "_float_pow" => (vec![NumericClass::Float, NumericClass::Float], f64_ty),
            // Integer width conversions (DESIGN.md 9.1): widening always succeeds;
            // narrowing range-checks and yields a Result. Bits/signedness are passed
            // so the runtime matches the target type.
            "_int_widen" => (
                vec![
                    NumericClass::Int,
                    NumericClass::Int,
                    NumericClass::Int,
                    NumericClass::Bool,
                ],
                i64_ty,
            ),
            "_int_narrow" => (
                vec![
                    NumericClass::Int,
                    NumericClass::Int,
                    NumericClass::Int,
                    NumericClass::Bool,
                ],
                Type::result(i64_ty, Type::Str),
            ),
            _ => return None,
        };
        self.check_arg_count(name, params.len(), args.len(), span);
        for (idx, class) in params.iter().enumerate() {
            let Some(arg) = args.get(idx) else { continue };
            let got = self.check_expr(&arg.expr, scopes);
            let resolved = self.resolve(&got);
            if resolved.is_unknown() {
                continue;
            }
            if !class.accepts(&resolved) {
                self.errors.push(TypeError {
                    message: format!(
                        "`{name}` expects {} for argument {}, found `{}`",
                        class.describe(),
                        idx + 1,
                        resolved.display()
                    ),
                    span: arg.expr.span(),
                });
            }
        }
        for arg in args.iter().skip(params.len()) {
            self.check_expr(&arg.expr, scopes);
        }
        Some(ret)
    }

    /// Minimal static contracts for the concurrency primitives (DESIGN.md 9.1,
    /// 12.7). `spawn(f: () -> void) -> void` and `with(c, f) -> U` are the only
    /// programmer-facing concurrency API. Until cown typing is real the first
    /// `with` argument stays untyped (the closure parameter is deferred), but
    /// the callable shape and `spawn`'s zero-arity are enforced now.
    fn concurrency_builtin_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        match name {
            "spawn" => {
                self.check_arg_count("spawn", 1, args.len(), span);
                if let Some(arg) = args.first() {
                    let got = self.check_expr(&arg.expr, scopes);
                    match self.resolve(&got) {
                        Type::Fun(params, _) if !params.is_empty() => {
                            self.errors.push(TypeError {
                                message: "`spawn` expects a zero-argument closure `() -> void`"
                                    .to_string(),
                                span: arg.expr.span(),
                            });
                        }
                        Type::Fun(_, _) | Type::Unknown(_) => {}
                        other => {
                            self.errors.push(TypeError {
                                message: format!(
                                    "`spawn` expects a closure `() -> void`, found `{}`",
                                    other.display()
                                ),
                                span: arg.expr.span(),
                            });
                        }
                    }
                }
                for arg in args.iter().skip(1) {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(Type::Void)
            }
            "with" => {
                self.check_arg_count("with", 2, args.len(), span);
                if let Some(arg) = args.first() {
                    self.check_expr(&arg.expr, scopes);
                }
                let ret = match args.get(1) {
                    Some(arg) => {
                        let got = self.check_expr(&arg.expr, scopes);
                        match self.resolve(&got) {
                            Type::Fun(params, ret) => {
                                if params.len() != 1 {
                                    self.errors.push(TypeError {
                                        message:
                                            "`with` expects a one-argument closure as its second \
                                             argument"
                                                .to_string(),
                                        span: arg.expr.span(),
                                    });
                                }
                                *ret
                            }
                            Type::Unknown(_) => self.fresh_unknown(),
                            other => {
                                self.errors.push(TypeError {
                                    message: format!(
                                        "`with` expects a closure as its second argument, found \
                                         `{}`",
                                        other.display()
                                    ),
                                    span: arg.expr.span(),
                                });
                                self.fresh_unknown()
                            }
                        }
                    }
                    None => self.fresh_unknown(),
                };
                for arg in args.iter().skip(2) {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(ret)
            }
            // `sync()` joins every thread spawned so far, so values mutated by a
            // `spawn` become observable before the program continues (R6
            // value-observability / structured-concurrency barrier).
            "sync" => {
                self.check_arg_count("sync", 0, args.len(), span);
                for arg in args {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(Type::Void)
            }
            // `_cown(c)` / `_freeze(c)` are inserted by the spawn auto-acquire pass
            // to promote a capture to an atomic-count owner before the spawn; each
            // takes the capture and yields nothing.
            "_cown" | "_freeze" => {
                self.check_arg_count(name, 1, args.len(), span);
                for arg in args {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(Type::Void)
            }
            _ => None,
        }
    }

    fn builtin_function_type_light(&self, name: &str) -> Option<Type> {
        match name {
            "open" => Some(Type::result(self.type_by_name("File"), Type::Str)),
            "len" => Some(Type::Int(IntKind::I64)),
            "print" | "println" | "assert" => Some(Type::Void),
            "input" => Some(Type::Str),
            "_string_concat" | "_string_slice" | "_string_char_at" => Some(Type::Str),
            "_string_bytes" => Some(Type::Slice(Box::new(Type::Int(IntKind::U8)))),
            "_string_from_bytes" => Some(Type::result(Type::Str, Type::Str)),
            "_string_find" => Some(Type::Nullable(Box::new(Type::Int(IntKind::I64)))),
            "_string_cmp" => Some(Type::Int(IntKind::I32)),
            "_int_to_string" | "_float_to_string" => Some(Type::Str),
            "_int_parse" => Some(Type::result(Type::Int(IntKind::I64), Type::Str)),
            "_float_parse" => Some(Type::result(Type::Float(FloatKind::F64), Type::Str)),
            "_int_to_float" | "_float_sqrt" | "_float_floor" | "_float_ceil" | "_float_pow" => {
                Some(Type::Float(FloatKind::F64))
            }
            "_float_to_int" | "_int_narrow" => {
                Some(Type::result(Type::Int(IntKind::I64), Type::Str))
            }
            "_int_widen" => Some(Type::Int(IntKind::I64)),
            "spawn" | "sync" | "_cown" | "_freeze" => Some(Type::Void),
            _ => None,
        }
    }

    fn array_builtin_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        match name {
            "_array_push" => {
                self.check_arg_count(name, 2, args.len(), span);
                let arr_ty = args
                    .first()
                    .map(|arg| self.check_expr(&arg.expr, scopes))
                    .unwrap_or(Type::Void);
                let elem_ty = match self.resolve(&arr_ty) {
                    Type::Slice(inner) => *inner,
                    Type::Array(_, _) => {
                        if let Some(arg) = args.first() {
                            self.errors.push(TypeError {
                                message: "`_array_push` expects a slice, found fixed array"
                                    .to_string(),
                                span: arg.expr.span(),
                            });
                        }
                        self.fresh_unknown()
                    }
                    Type::Unknown(_) => self.fresh_unknown(),
                    other => {
                        if let Some(arg) = args.first() {
                            self.errors.push(TypeError {
                                message: format!(
                                    "`_array_push` expects a slice, found `{}`",
                                    other.display()
                                ),
                                span: arg.expr.span(),
                            });
                        }
                        self.fresh_unknown()
                    }
                };
                if let Some(value) = args.get(1) {
                    let got = self.check_expr(&value.expr, scopes);
                    self.expect_expr_assignable(&got, &elem_ty, &value.expr);
                    if matches!(self.resolve(&elem_ty), Type::Unknown(_)) {
                        let _ = self.solver.unify(&elem_ty, &got);
                    }
                }
                for arg in args.iter().skip(2) {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(Type::Void)
            }
            "_array_pop" => {
                self.check_arg_count(name, 1, args.len(), span);
                let arr_ty = args
                    .first()
                    .map(|arg| self.check_expr(&arg.expr, scopes))
                    .unwrap_or(Type::Void);
                for arg in args.iter().skip(1) {
                    self.check_expr(&arg.expr, scopes);
                }
                let elem_ty = match self.resolve(&arr_ty) {
                    Type::Slice(inner) => *inner,
                    Type::Array(_, _) => {
                        if let Some(arg) = args.first() {
                            self.errors.push(TypeError {
                                message: "`_array_pop` expects a slice, found fixed array"
                                    .to_string(),
                                span: arg.expr.span(),
                            });
                        }
                        self.fresh_unknown()
                    }
                    Type::Unknown(_) => self.fresh_unknown(),
                    other => {
                        if let Some(arg) = args.first() {
                            self.errors.push(TypeError {
                                message: format!(
                                    "`_array_pop` expects a slice, found `{}`",
                                    other.display()
                                ),
                                span: arg.expr.span(),
                            });
                        }
                        self.fresh_unknown()
                    }
                };
                Some(Type::Nullable(Box::new(elem_ty)))
            }
            // `_array_insert(arr, idx, elem)` / `_array_remove(arr, idx)` primitives
            // (DESIGN.md 9.1): the slice's element type drives the index/element
            // checks. Insert yields void; remove yields the removed element.
            "_array_insert" | "_array_remove" => {
                let want_args = if name == "_array_insert" { 3 } else { 2 };
                self.check_arg_count(name, want_args, args.len(), span);
                let arr_ty = args
                    .first()
                    .map(|arg| self.check_expr(&arg.expr, scopes))
                    .unwrap_or(Type::Void);
                let elem_ty = match self.resolve(&arr_ty) {
                    Type::Slice(inner) => *inner,
                    Type::Unknown(_) => self.fresh_unknown(),
                    other => {
                        if let Some(arg) = args.first() {
                            self.errors.push(TypeError {
                                message: format!(
                                    "`{name}` expects a slice, found `{}`",
                                    other.display()
                                ),
                                span: arg.expr.span(),
                            });
                        }
                        self.fresh_unknown()
                    }
                };
                // The index argument is an int64 offset.
                if let Some(idx) = args.get(1) {
                    let got = self.check_expr(&idx.expr, scopes);
                    self.expect_expr_assignable(&got, &Type::Int(IntKind::I64), &idx.expr);
                }
                if name == "_array_insert" {
                    if let Some(value) = args.get(2) {
                        let got = self.check_expr(&value.expr, scopes);
                        self.expect_expr_assignable(&got, &elem_ty, &value.expr);
                        if matches!(self.resolve(&elem_ty), Type::Unknown(_)) {
                            let _ = self.solver.unify(&elem_ty, &got);
                        }
                    }
                    for arg in args.iter().skip(3) {
                        self.check_expr(&arg.expr, scopes);
                    }
                    Some(Type::Void)
                } else {
                    for arg in args.iter().skip(2) {
                        self.check_expr(&arg.expr, scopes);
                    }
                    Some(elem_ty)
                }
            }
            _ => None,
        }
    }

    fn string_builtin_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        if name == "_string_find" {
            self.check_arg_count(name, 2, args.len(), span);
            args.iter().for_each(|arg| {
                self.check_expr(&arg.expr, scopes);
            });
            return Some(Type::Nullable(Box::new(Type::Int(IntKind::I64))));
        }
        let i64_ty = Type::Int(IntKind::I64);
        let bytes_ty = Type::Slice(Box::new(Type::Int(IntKind::U8)));
        let (params, ret) = match name {
            "_string_concat" => (vec![Type::Str, Type::Str], Type::Str),
            "_string_slice" => (vec![Type::Str, i64_ty.clone(), i64_ty.clone()], Type::Str),
            "_string_bytes" => (vec![Type::Str], bytes_ty),
            "_string_from_bytes" => (vec![bytes_ty], Type::result(Type::Str, Type::Str)),
            "_string_char_at" => (vec![Type::Str, i64_ty], Type::Str),
            "_string_cmp" => (vec![Type::Str, Type::Str], Type::Int(IntKind::I32)),
            _ => return None,
        };
        self.check_builtin_args_against(name, args, &params, span, scopes);
        Some(ret)
    }

    fn check_builtin_args_against(
        &mut self,
        name: &str,
        args: &[Arg],
        params: &[Type],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) {
        self.check_arg_count(name, params.len(), args.len(), span);
        for (arg, want) in args.iter().zip(params) {
            self.check_expr_against(&arg.expr, want, scopes);
        }
        for arg in args.iter().skip(params.len()) {
            self.check_expr(&arg.expr, scopes);
        }
    }

    fn builtin_method_type(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        scopes: &mut ScopeStack,
        span: prepoly_lexer::Span,
    ) -> Option<Type> {
        if let Some(ret) = self.array_method_type(recv_ty, method, args, scopes, span) {
            return Some(ret);
        }
        let ret = builtin_method_return(recv_ty, method)?;
        args.iter().for_each(|arg| {
            self.check_expr(&arg.expr, scopes);
        });
        Some(ret)
    }

    /// Type the builtin collection methods so their element types are enforced
    /// (DESIGN.md 9.1): `push(self: T[], value: T) -> void`,
    /// `pop(self: T[]) -> T?`, and `len(self) -> int64`. Element checking turns
    /// `[1].push("x")` into a static error.
    ///
    /// `push`/`pop` are slice-only: a fixed array `T[n]` has a statically fixed
    /// length (DESIGN.md 5.1/8.1 model it as an inline `[n x T]`), so a
    /// length-changing call on one is rejected. `len` and indexing remain valid
    /// for both `T[n]` and `T[]` (indexing is handled in the `Index`/place
    /// paths).
    fn array_method_type(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        scopes: &mut ScopeStack,
        span: prepoly_lexer::Span,
    ) -> Option<Type> {
        let resolved = self.resolve(recv_ty);
        let (elem, is_fixed) = match &resolved {
            Type::Slice(inner) => (Some((**inner).clone()), false),
            Type::Array(inner, _) => (Some((**inner).clone()), true),
            _ => (None, false),
        };
        match (method, &elem) {
            ("push" | "pop" | "insert" | "remove", Some(elem)) if is_fixed => {
                args.iter().for_each(|arg| {
                    self.check_expr(&arg.expr, scopes);
                });
                self.errors.push(TypeError {
                    message: format!(
                        "fixed array type `{}` has no method `{method}`",
                        resolved.display()
                    ),
                    span,
                });
                // Return the shape the slice method would have had so the call
                // site does not also report a cascading "no method" error.
                Some(match method {
                    "push" | "insert" => Type::Void,
                    "remove" => elem.clone(),
                    _ => Type::Nullable(Box::new(elem.clone())),
                })
            }
            ("push", Some(elem)) => {
                if let Some(arg) = args.first() {
                    let got = self.check_expr(&arg.expr, scopes);
                    self.expect_expr_assignable(&got, elem, &arg.expr);
                    // Pin the element type of an as-yet-unconstrained array
                    // (e.g. one bound from `[]`) to the first pushed value, so a
                    // later push of a different type is rejected. The element
                    // variable lives in the array's `Slice` type, so the pin is
                    // visible to every later use of the same binding (R3).
                    if matches!(self.resolve(elem), Type::Unknown(_)) {
                        let _ = self.solver.unify(elem, &got);
                    }
                }
                for arg in args.iter().skip(1) {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(Type::Void)
            }
            ("pop", Some(elem)) => {
                args.iter().for_each(|arg| {
                    self.check_expr(&arg.expr, scopes);
                });
                Some(Type::Nullable(Box::new(elem.clone())))
            }
            // `arr.insert(idx, v)`: idx is int64, v is the element (DESIGN.md 9.1).
            ("insert", Some(elem)) => {
                if let Some(idx) = args.first() {
                    let got = self.check_expr(&idx.expr, scopes);
                    self.expect_expr_assignable(&got, &Type::Int(IntKind::I64), &idx.expr);
                }
                if let Some(value) = args.get(1) {
                    let got = self.check_expr(&value.expr, scopes);
                    self.expect_expr_assignable(&got, elem, &value.expr);
                    if matches!(self.resolve(elem), Type::Unknown(_)) {
                        let _ = self.solver.unify(elem, &got);
                    }
                }
                for arg in args.iter().skip(2) {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(Type::Void)
            }
            // `arr.remove(idx) -> T`: removes and returns the element (DESIGN.md 9.1).
            ("remove", Some(elem)) => {
                if let Some(idx) = args.first() {
                    let got = self.check_expr(&idx.expr, scopes);
                    self.expect_expr_assignable(&got, &Type::Int(IntKind::I64), &idx.expr);
                }
                for arg in args.iter().skip(1) {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(elem.clone())
            }
            ("len", Some(_)) => {
                args.iter().for_each(|arg| {
                    self.check_expr(&arg.expr, scopes);
                });
                Some(Type::Int(IntKind::I64))
            }
            _ if method == "len" && matches!(resolved, Type::Str) => {
                args.iter().for_each(|arg| {
                    self.check_expr(&arg.expr, scopes);
                });
                Some(Type::Int(IntKind::I64))
            }
            _ => None,
        }
    }

    fn check_static_call(
        &mut self,
        qualifier: &str,
        method: &str,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        if let Some(ret) = self.primitive_static_call(qualifier, method, args, scopes) {
            return ret;
        }
        if let Some(resolved) = self.method_for_qualifier(qualifier, method) {
            let signature_params = resolved.signature.params.clone();
            self.check_arg_count(method, signature_params.len(), args.len(), span);
            let arg_types = self.check_signature_args_collect(&signature_params, args, scopes);
            let declared_ret = resolved.signature.ret_ty.clone();
            let fallback_ret = declared_ret
                .clone()
                .or_else(|| {
                    self.method_returns
                        .get(&(resolved.qualifier.clone(), method.to_string()))
                        .cloned()
                })
                .unwrap_or_else(|| self.fresh_unknown());
            return self.instantiate_method_call(MethodCall {
                owner: &resolved.qualifier,
                self_type: &resolved.self_type,
                name: method,
                method: &resolved.method,
                signature_params: &resolved.signature.params,
                receiver_ty: None,
                declared_ret,
                fallback_ret,
                arg_types: &arg_types,
            });
        }
        args.iter().for_each(|a| {
            self.check_expr(&a.expr, scopes);
        });
        self.fresh_unknown()
    }

    fn primitive_static_call(
        &mut self,
        tname: &str,
        method: &str,
        args: &[Arg],
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        let ret = self.primitive_static_type(tname, method)?;
        let arg_types: Vec<Type> = args
            .iter()
            .map(|a| self.check_expr(&a.expr, scopes))
            .collect();
        self.check_numeric_conversion_args(tname, method, &arg_types, args);
        Some(ret)
    }

    /// Constrain the source type of the numeric conversions (DESIGN.md 5.2):
    /// `intN.from`/`floatN.from` take a numeric value and `intN.parse`/
    /// `floatN.parse` take a string. Without this, `float64.from("abc")` would
    /// type-check and silently produce `0.0` at runtime. `string.from` accepts
    /// any value, so it is intentionally not constrained. Unknown arguments are
    /// deferred to the runtime.
    fn check_numeric_conversion_args(
        &mut self,
        tname: &str,
        method: &str,
        arg_types: &[Type],
        args: &[Arg],
    ) {
        let numeric_target =
            IntKind::from_name(tname).is_some() || matches!(tname, "float32" | "float64");
        if !numeric_target {
            return;
        }
        let (Some(arg_ty), Some(arg)) = (arg_types.first(), args.first()) else {
            return;
        };
        let resolved = self.resolve(arg_ty);
        if resolved.is_unknown() {
            return;
        }
        match method {
            "parse" if !matches!(resolved, Type::Str) => {
                self.errors.push(TypeError {
                    message: format!(
                        "`{tname}.parse` expects a string, found `{}`",
                        resolved.display()
                    ),
                    span: arg.expr.span(),
                });
            }
            "from" if !matches!(resolved, Type::Int(_) | Type::Float(_)) => {
                self.errors.push(TypeError {
                    message: format!(
                        "`{tname}.from` expects a numeric value, found `{}`",
                        resolved.display()
                    ),
                    span: arg.expr.span(),
                });
            }
            _ => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn instantiate_function_call(
        &mut self,
        symbol: &str,
        module: &[String],
        params: &[ParamInfo],
        body: &Block,
        declared_ret: Option<Type>,
        fallback_ret: Type,
        arg_types: &[Type],
    ) -> Type {
        if params.len() != arg_types.len() {
            return fallback_ret;
        }
        let key = format!("fn:{symbol}");
        if !self.instantiating.insert(key.clone()) {
            return fallback_ret;
        }
        // Re-check the callee body in its own module so its internal names
        // resolve under that module's visibility, not the caller's (PLAN.md R5).
        let saved_module = std::mem::replace(&mut self.current_module, module.to_vec());
        let frame = self.signature_call_frame(params, arg_types, None);
        let mut scopes = vec![frame.clone()];
        self.check_block_root(body, &mut scopes, declared_ret.as_ref());
        let ret = declared_ret.unwrap_or_else(|| self.infer_return_from_frame(body, frame));
        self.current_module = saved_module;
        self.instantiating.remove(&key);
        ret
    }

    fn instantiate_method_call(&mut self, call: MethodCall<'_>) -> Type {
        let MethodCall {
            owner,
            self_type,
            name: method_name,
            method,
            signature_params,
            receiver_ty,
            declared_ret,
            fallback_ret,
            arg_types,
        } = call;
        let has_self = signature_params.first().is_some_and(|p| p.name == "self");
        if signature_params.len().saturating_sub(usize::from(has_self)) != arg_types.len() {
            return fallback_ret;
        }
        let key = format!("method:{owner}.{method_name}");
        if !self.instantiating.insert(key.clone()) {
            return fallback_ret;
        }
        let saved = self.self_type.replace(self_type.to_string());
        let saved_variant = self.self_variant.clone();
        self.self_variant = owner
            .split_once('.')
            .map(|(_, variant)| (self_type.to_string(), variant.to_string()));
        // Re-check the method body in its defining type's module (PLAN.md R5).
        let owner_type = self_type.to_string();
        let saved_module =
            self.swap_module_for(|p| p.types.get(&owner_type).map(|t| t.module.clone()));
        let frame = self.signature_call_frame(signature_params, arg_types, receiver_ty);
        if let Some(body) = &method.body {
            let mut scopes = vec![frame.clone()];
            self.check_block_root(body, &mut scopes, declared_ret.as_ref());
        }
        let ret = match (&method.body, declared_ret) {
            (_, Some(ret)) => ret,
            (Some(body), None) => self.infer_return_from_frame(body, frame),
            (None, None) => Type::Void,
        };
        self.self_type = saved;
        self.self_variant = saved_variant;
        self.current_module = saved_module;
        self.instantiating.remove(&key);
        ret
    }

    fn signature_call_frame(
        &mut self,
        params: &[ParamInfo],
        arg_types: &[Type],
        receiver_ty: Option<Type>,
    ) -> HashMap<String, Type> {
        // Re-checking a callee body sees top-level globals; signature
        // parameters layer on top so they shadow same-named globals.
        let mut frame = self.global_scope.clone();
        let mut arg_idx = 0;
        for param in params {
            let ty = if param.name == "self" {
                receiver_ty
                    .clone()
                    .or_else(|| param.resolved_ty.clone())
                    .unwrap_or_else(|| self.fresh_unknown())
            } else if let Some(annotated) = param_expected_type(param).cloned() {
                let ty = arg_types
                    .get(arg_idx)
                    .map(|arg| self.instantiate_annotated_type(&annotated, arg))
                    .unwrap_or(annotated);
                arg_idx += 1;
                ty
            } else {
                let ty = arg_types
                    .get(arg_idx)
                    .cloned()
                    .or_else(|| param.resolved_ty.clone())
                    .unwrap_or_else(|| self.fresh_unknown());
                arg_idx += 1;
                ty
            };
            frame.insert(param.name.clone(), ty);
        }
        frame
    }

    fn instantiate_annotated_type(&self, annotated: &Type, actual: &Type) -> Type {
        match (self.resolve(annotated), self.resolve(actual)) {
            (Type::Record(want), Type::Record(have)) => {
                let mut substitution = want.substitution.clone();
                if let Some(TypeKind::Record { fields, .. }) =
                    self.program.type_by_id(want.id).map(|info| &info.kind)
                {
                    for field in fields {
                        if field.resolved_ty.as_ref().is_some_and(Type::is_unknown)
                            && let Some(actual_ty) = self.record_field_type(&have, &field.name)
                        {
                            substitution.insert(field.name.clone(), actual_ty);
                        }
                    }
                }
                if let Some(TypeKind::Record { methods, .. }) =
                    self.program.type_by_id(want.id).map(|info| &info.kind)
                {
                    for (method_name, want_method) in methods {
                        let Some(have_method) =
                            self.program
                                .type_by_id(have.id)
                                .and_then(|info| match &info.kind {
                                    TypeKind::Record { methods, .. } => methods.get(method_name),
                                    TypeKind::Sum { .. } => None,
                                })
                        else {
                            continue;
                        };
                        for (want_param, have_param) in want_method
                            .signature
                            .params
                            .iter()
                            .zip(&have_method.signature.params)
                        {
                            if want_param.name == "self" {
                                continue;
                            }
                            if want_param
                                .resolved_ty
                                .as_ref()
                                .is_some_and(Type::is_unknown)
                            {
                                let key =
                                    method_param_substitution_key(method_name, &want_param.name);
                                if let Some(actual_ty) = have
                                    .substitution
                                    .get(&key)
                                    .cloned()
                                    .or_else(|| have_param.resolved_ty.clone())
                                {
                                    substitution.insert(key, actual_ty);
                                }
                            }
                        }
                        if want_method
                            .signature
                            .ret_ty
                            .as_ref()
                            .is_some_and(Type::is_unknown)
                        {
                            let key = method_return_substitution_key(method_name);
                            let actual_ret = have
                                .substitution
                                .get(&key)
                                .cloned()
                                .or_else(|| have_method.signature.ret_ty.clone())
                                .or_else(|| {
                                    self.method_returns
                                        .get(&(have.name().to_string(), method_name.clone()))
                                        .cloned()
                                });
                            if let Some(actual_ret) = actual_ret {
                                substitution.insert(key, actual_ret);
                            }
                        }
                    }
                }
                apply_nominal_substitution(Type::Record(want), substitution)
            }
            _ => annotated.clone(),
        }
    }

    fn record_field_type(&self, record: &NominalType, field: &str) -> Option<Type> {
        record.substitution.get(field).cloned().or_else(|| {
            self.program
                .types
                .get(record.name())
                .and_then(|info| match &info.kind {
                    TypeKind::Record { fields, .. } => fields
                        .iter()
                        .find(|candidate| candidate.name == field)
                        .and_then(|candidate| candidate.resolved_ty.clone()),
                    TypeKind::Sum { .. } => None,
                })
        })
    }

    fn infer_return_from_frame(&mut self, body: &Block, mut env: HashMap<String, Type>) -> Type {
        let mut normal = Vec::new();
        let mut errors = Vec::new();
        self.infer_returns_block(body, &mut env, &mut normal, &mut errors);
        // Call-site re-inference does not report conflicts; the definition site
        // already did.
        let normal_ty = self.reconcile_return_types(&normal, false);
        let err_ty = self.reconcile_error_payloads(&errors, false);
        self.result_from_payloads(normal_ty, err_ty)
    }

    fn check_signature_args_collect(
        &mut self,
        params: &[ParamInfo],
        args: &[Arg],
        scopes: &mut ScopeStack,
    ) -> Vec<Type> {
        let mut arg_types = Vec::with_capacity(args.len());
        for (idx, arg) in args.iter().enumerate() {
            let want = params.get(idx).and_then(param_expected_type);
            let got = if let Some(want) = want {
                self.check_expr_against(&arg.expr, want, scopes)
            } else {
                self.check_expr(&arg.expr, scopes)
            };
            arg_types.push(got);
        }
        arg_types
    }

    fn check_arg_count(&mut self, name: &str, want: usize, got: usize, span: prepoly_lexer::Span) {
        if want != got {
            self.errors.push(TypeError {
                message: format!("`{name}` expects {want} argument(s), got {got}"),
                span,
            });
        }
    }

    /// Check arity allowing a trailing run of nullable parameters to be omitted
    /// (each defaults to `null`): the supplied count must be between the required
    /// minimum and the full parameter count.
    fn check_arg_count_range(
        &mut self,
        name: &str,
        params: &[ParamInfo],
        got: usize,
        span: prepoly_lexer::Span,
    ) {
        let min = required_arg_count(params);
        let max = params.len();
        if got < min || got > max {
            let want = if min == max {
                format!("{max}")
            } else {
                format!("{min} to {max}")
            };
            self.errors.push(TypeError {
                message: format!("`{name}` expects {want} argument(s), got {got}"),
                span,
            });
        }
    }

    fn check_unary(&mut self, op: UnaryOp, ty: &Type, span: prepoly_lexer::Span) -> Type {
        match self.resolve(ty) {
            Type::Nullable(_) => {
                if matches!(op, UnaryOp::Not) {
                    Type::Bool
                } else {
                    self.report_nullable_use(span);
                    self.fresh_unknown()
                }
            }
            Type::Int(k) if matches!(op, UnaryOp::Neg | UnaryOp::BitNot) => Type::Int(k),
            Type::Float(k) if matches!(op, UnaryOp::Neg) => Type::Float(k),
            Type::Bool if matches!(op, UnaryOp::Not) => Type::Bool,
            Type::Unknown(_) => self.fresh_unknown(),
            other => {
                self.errors.push(TypeError {
                    message: format!(
                        "operator `{}` is not defined for `{}`",
                        unary_op_str(op),
                        other.display()
                    ),
                    span,
                });
                self.fresh_unknown()
            }
        }
    }

    fn check_binary(
        &mut self,
        op: BinOp,
        left: &Type,
        right: &Type,
        span: prepoly_lexer::Span,
    ) -> Type {
        self.check_binary_core(op, None, left, None, right, span)
    }

    fn check_binary_expr(
        &mut self,
        op: BinOp,
        left_expr: &Expr,
        left: &Type,
        right_expr: &Expr,
        right: &Type,
        span: prepoly_lexer::Span,
    ) -> Type {
        self.check_binary_core(op, Some(left_expr), left, Some(right_expr), right, span)
    }

    fn check_binary_core(
        &mut self,
        op: BinOp,
        left_expr: Option<&Expr>,
        left: &Type,
        right_expr: Option<&Expr>,
        right: &Type,
        span: prepoly_lexer::Span,
    ) -> Type {
        let left = self.resolve(left);
        let right = self.resolve(right);
        if matches!(left, Type::Nullable(_)) || matches!(right, Type::Nullable(_)) {
            if is_null_comparison(op, &left, &right) {
                return Type::Bool;
            }
            self.report_nullable_use(span);
            return self.fresh_unknown();
        }
        self.record_binary_shape(op, &left, &right);
        if let Some(ty) = integer_literal_binary_type(op, left_expr, &left, right_expr, &right) {
            return ty;
        }
        match op {
            BinOp::Add => match (&left, &right) {
                (Type::Int(a), Type::Int(b)) if a == b => left,
                (Type::Float(a), Type::Float(b)) if a == b => left,
                (Type::Str, Type::Str) => Type::Str,
                (Type::Unknown(_), _) | (_, Type::Unknown(_)) => self.fresh_unknown(),
                _ => self.binary_error(op, &left, &right, span),
            },
            BinOp::Sub | BinOp::Mul | BinOp::Div => match (&left, &right) {
                (Type::Int(a), Type::Int(b)) if a == b => left,
                (Type::Float(a), Type::Float(b)) if a == b => left,
                (Type::Unknown(_), _) | (_, Type::Unknown(_)) => self.fresh_unknown(),
                _ => self.binary_error(op, &left, &right, span),
            },
            BinOp::Rem => match (&left, &right) {
                (Type::Int(a), Type::Int(b)) if a == b => left,
                (Type::Unknown(_), _) | (_, Type::Unknown(_)) => self.fresh_unknown(),
                _ => self.binary_error(op, &left, &right, span),
            },
            BinOp::Eq | BinOp::Ne => {
                if self.can_unify(&left, &right)
                    || matches!(left, Type::Never)
                    || matches!(right, Type::Never)
                {
                    Type::Bool
                } else {
                    self.binary_error(op, &left, &right, span)
                }
            }
            // Ordering comparisons are numeric only (DESIGN.md 5.9). Strings have
            // no ordering: `==`/`!=` compare them, but `<`/`>`/`<=`/`>=` do not.
            BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => match (&left, &right) {
                (Type::Int(a), Type::Int(b)) if a == b => Type::Bool,
                (Type::Float(a), Type::Float(b)) if a == b => Type::Bool,
                (Type::Unknown(_), _) | (_, Type::Unknown(_)) => Type::Bool,
                _ => self.binary_error(op, &left, &right, span),
            },
            BinOp::And | BinOp::Or => match (&left, &right) {
                (Type::Bool, Type::Bool) => Type::Bool,
                (Type::Unknown(_), _) | (_, Type::Unknown(_)) => Type::Bool,
                _ => self.binary_error(op, &left, &right, span),
            },
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                match (&left, &right) {
                    (Type::Int(a), Type::Int(b)) if a == b => left,
                    (Type::Unknown(_), _) | (_, Type::Unknown(_)) => self.fresh_unknown(),
                    _ => self.binary_error(op, &left, &right, span),
                }
            }
        }
    }

    fn binary_error(
        &mut self,
        op: BinOp,
        left: &Type,
        right: &Type,
        span: prepoly_lexer::Span,
    ) -> Type {
        self.errors.push(TypeError {
            message: format!(
                "operator `{}` is not defined for `{}` and `{}` (no implicit conversion)",
                op_str(op),
                left.display(),
                right.display()
            ),
            span,
        });
        self.fresh_unknown()
    }

    fn expect_int_index(&mut self, ty: &Type, span: prepoly_lexer::Span) {
        match self.resolve(ty) {
            Type::Int(_) | Type::Unknown(_) => {}
            other => self.errors.push(TypeError {
                message: format!("index must be an integer, found `{}`", other.display()),
                span,
            }),
        }
    }

    fn expect_expr_assignable(&mut self, got: &Type, want: &Type, expr: &Expr) {
        if integer_literal_fits(expr, want) {
            return;
        }
        self.expect_assignable(got, want, expr.span());
    }

    fn expect_assignable(&mut self, got: &Type, want: &Type, span: prepoly_lexer::Span) {
        let got = self.resolve(got);
        let want = self.resolve(want);
        // An unconstrained inference variable whose type cannot be inferred
        // reaching a concrete required position is an error rather than a silent
        // unification (PLAN.md R1 stage 10): a bare empty array carries no
        // element, and a function that only returns `error(...)` has no `Ok`
        // payload type. A `want` that is itself unknown leaves the contract
        // deferred rather than wrong.
        if let Type::Unknown(id) = &got
            && !want.is_unknown()
        {
            match self.solver.kind_of(*id) {
                Some(InferenceVarKind::EmptyArrayElem) => {
                    self.errors.push(TypeError {
                        message: "cannot infer element type of empty array; add a type annotation"
                            .to_string(),
                        span,
                    });
                    return;
                }
                Some(InferenceVarKind::ErrorOnlyOk) => {
                    self.errors.push(TypeError {
                        message: "cannot infer the Ok payload type of a function that only \
                                      returns errors; add a non-error return or an annotation"
                            .to_string(),
                        span,
                    });
                    return;
                }
                _ => {}
            }
        }
        if got.is_null() && !matches!(want, Type::Nullable(_)) {
            self.errors.push(TypeError {
                message: format!(
                    "cannot use `{}` where `{}` is required",
                    got.display(),
                    want.display()
                ),
                span,
            });
            return;
        }
        if matches!(got, Type::Nullable(_)) && !matches!(want, Type::Nullable(_)) {
            self.report_nullable_use(span);
            return;
        }
        if let Type::Nullable(inner) = &want
            && (self.can_unify(&got, inner) || matches!(got, Type::Never))
        {
            return;
        }
        if self.can_unify(&got, &want)
            || crate::structural::types_compatible(self.program, &got, &want)
        {
            return;
        }
        self.errors.push(TypeError {
            message: format!(
                "cannot use `{}` where `{}` is required",
                got.display(),
                want.display()
            ),
            span,
        });
    }

    fn can_unify(&self, a: &Type, b: &Type) -> bool {
        Subst::new().unify(a, b).is_ok()
            || crate::structural::types_compatible(self.program, a, b)
            || crate::structural::types_compatible(self.program, b, a)
    }

    /// Resolve a type through the persistent substitution, following solved
    /// inference variables (including nested ones). The substitution is only
    /// populated where the checker pins a variable across uses (e.g. an empty
    /// array's element type after the first `push`), so an unconstrained type is
    /// returned structurally unchanged.
    fn resolve(&self, ty: &Type) -> Type {
        self.solver.resolve(ty)
    }

    fn report_nullable_use(&mut self, span: prepoly_lexer::Span) {
        self.errors.push(TypeError {
            message: "nullable value must be checked for null before use".to_string(),
            span,
        });
    }

    fn apply_truthy_narrowing(&mut self, cond: &Expr, scopes: &mut ScopeStack) {
        if let Some(name) = narrow::truthy_narrows(cond) {
            self.narrow_non_null(name, scopes);
        }
    }

    fn apply_guard_narrowing(&mut self, stmt: &Stmt, scopes: &mut ScopeStack) {
        let Stmt::Expr(Expr::If(cond, then, None, _)) = stmt else {
            return;
        };
        if !block_always_returns(then) {
            return;
        }
        if let Some(name) = narrow::falsy_narrows(cond) {
            self.narrow_non_null(name, scopes);
        }
    }

    fn narrow_non_null(&mut self, name: &str, scopes: &mut ScopeStack) {
        for scope in scopes.iter_mut().rev() {
            if let Some(Type::Nullable(inner)) = scope.get(name).cloned().map(|t| self.resolve(&t))
            {
                scope.insert(name.to_string(), *inner);
                break;
            }
        }
    }

    fn bind_pattern(&mut self, pat: &Pattern, ty: &Type, scopes: &mut ScopeStack) {
        match pat {
            Pattern::Binding(name, _) => {
                if !self.is_unit_variant_name(name) {
                    scopes.last_mut().unwrap().insert(name.clone(), ty.clone());
                }
            }
            Pattern::Record(variant, fields, _) => {
                let field_types = self.pattern_field_types(ty, variant);
                for fp in fields {
                    let fty = field_types
                        .get(&fp.name)
                        .cloned()
                        .unwrap_or_else(|| self.fresh_unknown());
                    if let Some(subpat) = &fp.pat {
                        self.bind_pattern(subpat, &fty, scopes);
                    } else {
                        scopes.last_mut().unwrap().insert(fp.name.clone(), fty);
                    }
                }
            }
            Pattern::Array(pats, _) => {
                let elem = match self.resolve(ty) {
                    Type::Array(inner, _) | Type::Slice(inner) => *inner,
                    _ => self.fresh_unknown(),
                };
                pats.iter()
                    .for_each(|p| self.bind_pattern(p, &elem, scopes));
            }
            Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
        }
    }

    fn check_pattern_against(&mut self, scrutinee: &Type, pat: &Pattern) {
        match pat {
            Pattern::Binding(name, span) => {
                if let Some(owner) = self.variant_owner(name) {
                    match self.resolve(scrutinee) {
                        Type::Sum(sum) if sum.is_name(&owner) => {}
                        ty if owner == "Result" && ty.is_result_type() => {}
                        Type::Unknown(_) => {}
                        other => self.errors.push(TypeError {
                            message: format!(
                                "pattern variant `{name}` belongs to `{owner}`, not `{}`",
                                other.display()
                            ),
                            span: *span,
                        }),
                    }
                }
            }
            Pattern::Record(name, fields, span) => {
                let owner = self.variant_owner(name);
                if let Some(owner) = &owner {
                    match self.resolve(scrutinee) {
                        Type::Sum(sum) if sum.is_name(owner) => {}
                        ty if owner == "Result" && ty.is_result_type() => {}
                        Type::Unknown(_) => {}
                        other => self.errors.push(TypeError {
                            message: format!(
                                "pattern variant `{name}` belongs to `{owner}`, not `{}`",
                                other.display()
                            ),
                            span: *span,
                        }),
                    }
                }
                let field_types = self.pattern_field_types(scrutinee, name);
                for fp in fields {
                    let Some(field_ty) = field_types.get(&fp.name) else {
                        if owner.is_some() {
                            self.errors.push(TypeError {
                                message: format!("pattern `{name}` has no field `{}`", fp.name),
                                span: fp.span,
                            });
                        }
                        continue;
                    };
                    if let Some(subpat) = &fp.pat {
                        self.check_pattern_against(field_ty, subpat);
                    }
                }
            }
            Pattern::Array(pats, _) => {
                let elem = match self.resolve(scrutinee) {
                    Type::Array(inner, len) => {
                        if pats.len() != len {
                            self.errors.push(TypeError {
                                message: format!(
                                    "array pattern has length {}, but scrutinee has length {}",
                                    pats.len(),
                                    len
                                ),
                                span: pat.span(),
                            });
                        }
                        *inner
                    }
                    Type::Slice(inner) => *inner,
                    _ => self.fresh_unknown(),
                };
                pats.iter()
                    .for_each(|pat| self.check_pattern_against(&elem, pat));
            }
            Pattern::Literal(expr, span) => {
                let Some(lit_ty) = literal_pattern_type(expr) else {
                    return;
                };
                let scrutinee = self.resolve(scrutinee);
                if literal_pattern_matches(expr, &lit_ty, &scrutinee) {
                    return;
                }
                self.errors.push(TypeError {
                    message: format!(
                        "literal pattern of type `{}` cannot match `{}`",
                        lit_ty.display(),
                        scrutinee.display()
                    ),
                    span: *span,
                });
            }
            Pattern::Wildcard(_) => {}
        }
    }

    fn pattern_field_types(&mut self, ty: &Type, variant: &str) -> HashMap<String, Type> {
        let resolved = self.resolve(ty);
        if let Some((ok, err)) = resolved.result_payloads() {
            return match variant {
                "Ok" => HashMap::from([("value".to_string(), ok.clone())]),
                "Err" => HashMap::from([("error".to_string(), err.clone())]),
                _ => HashMap::new(),
            };
        }
        if let Type::Sum(name) = &resolved {
            return self
                .program
                .types
                .get(name.name())
                .and_then(|info| info.variant(variant))
                .map(|variant_info| {
                    variant_info
                        .fields
                        .iter()
                        .map(|field| {
                            let key = field_substitution_key(Some(variant), &field.name);
                            let ty = name
                                .substitution
                                .get(&key)
                                .cloned()
                                .or_else(|| field.resolved_ty.clone())
                                .unwrap_or_else(|| self.fresh_unknown());
                            (field.name.clone(), ty)
                        })
                        .collect()
                })
                .unwrap_or_default();
        }
        let sum_name = self.sum_containing_variant(variant);
        let fields = sum_name
            .and_then(|name| self.program.types.get(&name))
            .and_then(|info| info.variant(variant))
            .map(|v| {
                v.fields
                    .iter()
                    .map(|f| (f.name.clone(), f.resolved_ty.clone()))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        fields
            .into_iter()
            .map(|(name, ty)| {
                let ty = ty.unwrap_or_else(|| self.fresh_unknown());
                (name, ty)
            })
            .collect()
    }

    fn methods_for_type(&self, ty: &Type, method: &str) -> Option<Vec<ResolvedMethod>> {
        match self.resolve(ty) {
            Type::Record(name) => {
                // Resolve by the receiver's unique id, and key the resolved
                // method on the type's symbol so dispatch is correct when two
                // modules share a type name (PLAN.md R2).
                let info = self.program.type_by_id(name.id)?;
                let TypeKind::Record { methods, .. } = &info.kind else {
                    return None;
                };
                let m = methods.get(method)?;
                let resolved = ResolvedMethod {
                    qualifier: info.symbol.clone(),
                    self_type: info.symbol.clone(),
                    signature: m.signature.clone(),
                    method: m.decl.as_ref().clone(),
                };
                Some(vec![apply_method_substitution(
                    resolved,
                    &name.substitution,
                    method,
                )])
            }
            Type::Sum(name) => {
                let info = self.program.type_by_id(name.id)?;
                let TypeKind::Sum { variants } = &info.kind else {
                    return None;
                };
                if variants.is_empty() {
                    return None;
                }
                let methods = variants
                    .iter()
                    .map(|variant| {
                        let method = variant.methods.get(method)?;
                        Some(ResolvedMethod {
                            qualifier: format!("{}.{}", info.symbol, variant.name),
                            self_type: info.symbol.clone(),
                            signature: method.signature.clone(),
                            method: method.decl.as_ref().clone(),
                        })
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(methods)
            }
            _ => None,
        }
    }

    fn method_for_qualifier(&self, qualifier: &str, method: &str) -> Option<ResolvedMethod> {
        if let Some((sum, variant)) = qualifier.split_once('.') {
            let symbol = self.resolve_type_symbol(sum)?;
            let info = self.program.types.get(&symbol)?;
            let method = info.variant(variant)?.methods.get(method)?;
            return Some(ResolvedMethod {
                qualifier: format!("{symbol}.{variant}"),
                self_type: symbol.clone(),
                signature: method.signature.clone(),
                method: method.decl.as_ref().clone(),
            });
        }
        let type_name = self.resolve_self_name(qualifier);
        let symbol = self.resolve_type_symbol(&type_name)?;
        let TypeKind::Record { methods, .. } = &self.program.types.get(&symbol)?.kind else {
            return None;
        };
        let type_name = symbol;
        let method = methods.get(method)?;
        Some(ResolvedMethod {
            qualifier: type_name.clone(),
            self_type: type_name,
            signature: method.signature.clone(),
            method: method.decl.as_ref().clone(),
        })
    }

    fn check_common_method_signatures(
        &mut self,
        methods: &[ResolvedMethod],
        method: &str,
        span: prepoly_lexer::Span,
    ) {
        let Some((first, rest)) = methods.split_first() else {
            return;
        };
        for other in rest {
            if !crate::structural::signature_satisfies(
                self.program,
                &other.signature,
                &first.signature,
            ) || !crate::structural::signature_satisfies(
                self.program,
                &first.signature,
                &other.signature,
            ) {
                self.errors.push(TypeError {
                    message: format!(
                        "variant method `{method}` has incompatible signatures in `{}` and `{}`",
                        first.qualifier, other.qualifier
                    ),
                    span,
                });
            }
        }
    }

    fn static_qualifier(&self, expr: &Expr, scopes: &ScopeStack) -> Option<String> {
        match expr {
            Expr::Ident(name, _)
                if self.lookup(scopes, name).is_none() && self.is_type_word(name) =>
            {
                Some(self.resolve_self_name(name))
            }
            Expr::Field(base, variant, _) => {
                let Expr::Ident(type_name, _) = &**base else {
                    return None;
                };
                if self.lookup(scopes, type_name).is_some() {
                    return None;
                }
                let resolved = self.resolve_self_name(type_name);
                self.program
                    .types
                    .get(&resolved)
                    .and_then(|info| info.variant(variant))
                    .map(|_| format!("{resolved}.{variant}"))
            }
            _ => None,
        }
    }

    fn lookup(&self, scopes: &ScopeStack, name: &str) -> Option<Type> {
        scopes.iter().rev().find_map(|s| s.get(name).cloned())
    }

    /// Whether `name` denotes a legitimate value that needs no local binding: a
    /// free function visible from the current module or a runtime builtin. Used
    /// by name resolution to distinguish an undeclared identifier from a
    /// function or builtin referenced before/without a local binding. Type words
    /// and unit variants are intentionally excluded here; their value forms are
    /// `Type.method`/`Type.Variant` field accesses, not bare identifiers.
    fn is_resolvable_free_name(&self, name: &str) -> bool {
        self.is_function_visible(name) || is_runtime_builtin_value(name)
    }

    /// Whether a program free function `name` is visible from the module being
    /// checked (DESIGN.md 2): defined in that module, implicitly imported as
    /// part of the standard-library prelude, or brought in by an `import`.
    fn is_function_visible(&self, name: &str) -> bool {
        self.lookup_function(name).is_some()
    }

    /// Resolve a bare free-function name to its definition from the current
    /// module (DESIGN.md 2; PLAN.md R2). A name defined in a single module keeps
    /// its bare symbol, so the common case is a direct map hit gated by
    /// visibility. A name defined in several modules has only module-qualified
    /// symbols, so resolution prefers this module's own definition, then the one
    /// brought in by an `import`.
    fn lookup_function(&self, name: &str) -> Option<&prepoly_hir::FunInfo> {
        if let Some(info) = self.program.functions.get(name) {
            return self
                .is_module_name_visible(&info.module, name)
                .then_some(info);
        }
        if let Some(info) = self
            .program
            .functions
            .get(&prepoly_hir::qualify(name, &self.current_module))
        {
            return Some(info);
        }
        let origin = self.import_origin(name)?;
        self.program
            .functions
            .get(&prepoly_hir::qualify(name, origin))
    }

    /// The origin module path of an imported local name in the current module.
    fn import_origin(&self, name: &str) -> Option<&[String]> {
        self.program
            .import_origins
            .get(&self.current_module)?
            .get(name)
            .map(Vec::as_slice)
    }

    /// The per-module visibility rule shared by functions and types: a name
    /// declared in `defining` is visible from `current_module` when it is the
    /// same module, a compiler builtin (empty module path, e.g. `Result`), a
    /// public standard-library name (implicit prelude, DESIGN.md 9.4), or
    /// explicitly imported into the current module.
    fn is_module_name_visible(&self, defining: &[String], name: &str) -> bool {
        if defining == self.current_module.as_slice() || defining.is_empty() {
            return true;
        }
        if defining.first().map(String::as_str) == Some("std") && !name.starts_with('_') {
            return true;
        }
        self.program
            .module_imports
            .get(&self.current_module)
            .is_some_and(|names| names.iter().any(|n| n == name))
    }

    /// Switch `current_module` to the module chosen by `pick` for the duration
    /// of a re-checked callee body, returning the previous module to restore.
    /// A `None` pick leaves the module unchanged.
    fn swap_module_for(
        &mut self,
        pick: impl FnOnce(&Program) -> Option<Vec<String>>,
    ) -> Vec<String> {
        match pick(self.program) {
            Some(module) => std::mem::replace(&mut self.current_module, module),
            None => self.current_module.clone(),
        }
    }

    /// Record a deferred structural constraint on `ty` if it resolves to an
    /// inference variable. Used while checking a closure body that operates on
    /// an unknown-typed parameter; the constraint is verified when the variable
    /// is solved at a call site (see `crate::constraint`).
    fn record_shape(&mut self, ty: &Type, constraint: ShapeConstraint) {
        if let Type::Unknown(id) = self.resolve(ty) {
            self.shape_constraints
                .entry(id)
                .or_default()
                .push(constraint);
        }
    }

    /// Record an equality constraint for an unknown operand of a same-typed
    /// binary operator. Prepoly's arithmetic, ordering, and bitwise operators
    /// require both operands to share one numeric/string type (no implicit
    /// conversion, DESIGN.md 5.9), so an unknown operand paired with a concrete
    /// one must equal it. This lets `(x) -> x + 1` pin `x` to `int32`.
    fn record_binary_shape(&mut self, op: BinOp, left: &Type, right: &Type) {
        let same_typed = matches!(
            op,
            BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Rem
                | BinOp::Lt
                | BinOp::Gt
                | BinOp::Le
                | BinOp::Ge
                | BinOp::BitAnd
                | BinOp::BitOr
                | BinOp::BitXor
                | BinOp::Shl
                | BinOp::Shr
        );
        if !same_typed {
            return;
        }
        let is_operand = |t: &Type| matches!(t, Type::Int(_) | Type::Float(_) | Type::Str);
        match (left, right) {
            (Type::Unknown(_), other) if is_operand(other) => {
                self.record_shape(left, ShapeConstraint::Equals(other.clone()));
            }
            (other, Type::Unknown(_)) if is_operand(other) => {
                self.record_shape(right, ShapeConstraint::Equals(other.clone()));
            }
            _ => {}
        }
    }

    /// Verify the constraints recorded for the inference variable `var` against
    /// the concrete type `got` it has been solved to at a call site. A `got`
    /// that is still unknown is skipped (the requirement stays deferred).
    fn verify_shape_constraints(&mut self, var: &Type, got: &Type, span: prepoly_lexer::Span) {
        let Type::Unknown(id) = self.resolve(var) else {
            return;
        };
        let got = self.resolve(got);
        if matches!(got, Type::Unknown(_)) {
            return;
        }
        let Some(constraints) = self.shape_constraints.get(&id).cloned() else {
            return;
        };
        for constraint in constraints {
            match constraint {
                ShapeConstraint::Equals(expected) => {
                    if !self.can_unify(&got, &expected) {
                        self.errors.push(TypeError {
                            message: format!(
                                "cannot use `{}` where `{}` is required",
                                got.display(),
                                expected.display()
                            ),
                            span,
                        });
                    }
                }
                ShapeConstraint::HasMethod(name) => {
                    if !self.concrete_type_has_method(&got, &name) {
                        self.errors.push(TypeError {
                            message: format!("`{}` has no method `{name}`", got.display()),
                            span,
                        });
                    }
                }
                ShapeConstraint::HasField(name) => {
                    if !self.concrete_type_has_field(&got, &name) {
                        self.errors.push(TypeError {
                            message: format!("`{}` has no field `{name}`", got.display()),
                            span,
                        });
                    }
                }
                ShapeConstraint::Indexable => {
                    if !matches!(got, Type::Array(_, _) | Type::Slice(_) | Type::Str) {
                        self.errors.push(TypeError {
                            message: format!("cannot index `{}`", got.display()),
                            span,
                        });
                    }
                }
            }
        }
    }

    /// Whether a resolved concrete type definitely exposes a callable method,
    /// considering user methods, builtin collection/file/string methods, and
    /// UFCS free functions. Conservative: a non-concrete type (an unsolved
    /// variable, nullable, function, ...) returns `true` so only a method that
    /// is genuinely absent on a concrete receiver is rejected.
    fn concrete_type_has_method(&self, ty: &Type, method: &str) -> bool {
        let resolved = self.resolve(ty);
        if self.methods_for_type(&resolved, method).is_some() {
            return true;
        }
        // UFCS: `recv.m(..)` falls back to a visible free function `m(recv, ..)`.
        if self.program.functions.contains_key(method) {
            return true;
        }
        match resolved {
            Type::Str => method == "len",
            Type::Slice(_) => matches!(method, "push" | "pop" | "insert" | "remove" | "len"),
            Type::Array(_, _) => method == "len",
            Type::Record(rec) if rec.is_name("File") => {
                matches!(method, "read" | "write" | "close" | "size" | "seek")
            }
            // A user record/sum, or a primitive, with no matching member above
            // genuinely lacks the method.
            Type::Record(_)
            | Type::Sum(_)
            | Type::Int(_)
            | Type::Float(_)
            | Type::Bool
            | Type::Void => false,
            _ => true,
        }
    }

    /// Whether a resolved concrete record type exposes a field. Conservative for
    /// non-record types in the same way as `concrete_type_has_method`.
    fn concrete_type_has_field(&self, ty: &Type, field: &str) -> bool {
        match self.resolve(ty) {
            Type::Record(rec) => {
                if rec.substitution.get(field).is_some() {
                    return true;
                }
                match self.program.type_by_id(rec.id) {
                    Some(info) => match &info.kind {
                        TypeKind::Record { fields, .. } => fields.iter().any(|f| f.name == field),
                        TypeKind::Sum { .. } => false,
                    },
                    None => true,
                }
            }
            Type::Int(_) | Type::Float(_) | Type::Bool | Type::Void | Type::Str => false,
            _ => true,
        }
    }

    fn is_in_scope(&self, base: &Expr, scopes: &ScopeStack) -> bool {
        matches!(base, Expr::Ident(name, _) if self.lookup(scopes, name).is_some())
    }

    fn resolve_self_name(&self, name: &str) -> String {
        if name == "Self" {
            self.self_type.clone().unwrap_or_default()
        } else {
            name.to_string()
        }
    }

    /// The unique storage symbol of a user type named `name`, resolved from the
    /// current module (PLAN.md R2): own/unique, this module's qualified
    /// definition, or the imported one. Returns an owned String so the borrow
    /// does not outlive into later `&mut self` use.
    fn resolve_type_symbol(&self, name: &str) -> Option<String> {
        self.program
            .resolve_type(&self.current_module, name)
            .map(|t| t.symbol.clone())
    }

    /// The `Type` of a user type named `name`, resolved from the current module.
    fn resolve_type_ref(&self, name: &str) -> Option<Type> {
        self.program
            .resolve_type(&self.current_module, name)
            .map(|t| t.type_ref())
    }

    fn is_type_word(&self, name: &str) -> bool {
        self.program.has_type_named(name)
            || name == "Self"
            || name == "File"
            || IntKind::from_name(name).is_some()
            || matches!(name, "float32" | "float64" | "string" | "bool")
    }

    fn is_unit_variant_name(&self, name: &str) -> bool {
        self.program.types.values().any(|info| match &info.kind {
            TypeKind::Sum { variants } => variants
                .iter()
                .any(|v| v.name == name && v.fields.is_empty()),
            TypeKind::Record { .. } => false,
        })
    }

    fn sum_containing_variant(&self, variant: &str) -> Option<String> {
        self.program
            .types
            .values()
            .find_map(|info| match &info.kind {
                TypeKind::Sum { variants } if variants.iter().any(|v| v.name == variant) => {
                    Some(info.name.clone())
                }
                _ => None,
            })
    }

    fn variant_owner(&self, variant: &str) -> Option<String> {
        self.sum_containing_variant(variant)
    }
}

/// Free-function names the runtime resolves without a user or stdlib
/// definition (mirrors `prepoly_runtime::builtins::builtin_function`). They are
/// always legitimate value/callee names even when the standard library is not
/// loaded (for example in typeck unit tests), so name resolution must not
/// reject them. Keep this list in sync with the runtime dispatcher.
fn is_runtime_builtin_value(name: &str) -> bool {
    matches!(
        name,
        "print"
            | "println"
            | "len"
            | "assert"
            | "_panic"
            | "spawn"
            | "with"
            | "sync"
            | "_cown"
            | "_freeze"
            | "input"
            | "read_file"
            | "write_file"
            | "open"
            | "error"
            | "_string_concat"
            | "_string_slice"
            | "_string_bytes"
            | "_string_from_bytes"
            | "_string_char_at"
            | "_string_find"
            | "_string_cmp"
            | "_int_to_string"
            | "_float_to_string"
            | "_int_parse"
            | "_float_parse"
            | "_int_to_float"
            | "_float_to_int"
            | "_int_widen"
            | "_int_narrow"
            | "_float_sqrt"
            | "_float_floor"
            | "_float_ceil"
            | "_float_pow"
            | "_array_push"
            | "_array_pop"
            | "_array_insert"
            | "_array_remove"
    )
}

/// Value class expected by a numeric runtime helper argument. Used to reject a
/// concrete wrong class (e.g. a float where an integer is required) before the
/// runtime reinterprets payload bits.
enum NumericClass {
    Int,
    Float,
    Str,
    Bool,
}

impl NumericClass {
    fn accepts(&self, ty: &Type) -> bool {
        match self {
            NumericClass::Int => matches!(ty, Type::Int(_)),
            NumericClass::Float => matches!(ty, Type::Float(_)),
            NumericClass::Str => matches!(ty, Type::Str),
            NumericClass::Bool => matches!(ty, Type::Bool),
        }
    }

    fn describe(&self) -> &'static str {
        match self {
            NumericClass::Int => "an integer",
            NumericClass::Float => "a float",
            NumericClass::Str => "a string",
            NumericClass::Bool => "a bool",
        }
    }
}

/// Whether `ty` is a fully known primitive with no user fields or methods.
/// Field/method access on such a receiver cannot be deferred to runtime shape
/// dispatch and is therefore a static error.
fn is_concrete_primitive(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Int(_) | Type::Float(_) | Type::Bool | Type::Str | Type::Void
    )
}

/// Whether a (resolved) type is fully concrete: it contains no inference
/// variable, `Never`, or `Self` placeholder, so it can name a monomorphized
/// instance (PLAN.md R5 stage 5).
fn is_concrete_type(ty: &Type) -> bool {
    match ty {
        Type::Unknown(_) | Type::Never | Type::SelfType => false,
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Nullable(inner)
        | Type::ConstOf(inner) => is_concrete_type(inner),
        Type::Fun(params, ret) => params.iter().all(is_concrete_type) && is_concrete_type(ret),
        _ => true,
    }
}

fn builtin_method_return(recv_ty: &Type, method: &str) -> Option<Type> {
    let Type::Record(name) = recv_ty else {
        return None;
    };
    if !name.is_name("File") {
        return None;
    }
    match method {
        "write" | "size" => Some(Type::result(Type::Int(IntKind::I64), Type::Str)),
        "read" => Some(Type::result(
            Type::Slice(Box::new(Type::Int(IntKind::U8))),
            Type::Str,
        )),
        "close" | "seek" => Some(Type::result(Type::Void, Type::Str)),
        _ => None,
    }
}

fn primitive_static_return(tname: &str, method: &str) -> Option<Type> {
    if let Some(k) = IntKind::from_name(tname) {
        return match method {
            "from" | "parse" => Some(Type::result(Type::Int(k), Type::Str)),
            _ => None,
        };
    }
    match (tname, method) {
        ("float32", "from") => Some(Type::Float(FloatKind::F32)),
        ("float32", "parse") => Some(Type::result(Type::Float(FloatKind::F32), Type::Str)),
        ("float64", "from") => Some(Type::Float(FloatKind::F64)),
        ("float64", "parse") => Some(Type::result(Type::Float(FloatKind::F64), Type::Str)),
        ("string", "from") => Some(Type::Str),
        _ => None,
    }
}

fn integer_literal_fits(expr: &Expr, want: &Type) -> bool {
    let target = match want {
        Type::Int(kind) => Some(*kind),
        Type::Nullable(inner) => match &**inner {
            Type::Int(kind) => Some(*kind),
            _ => None,
        },
        _ => None,
    };
    match (expr, target) {
        (Expr::Int(value, _), Some(kind)) => int_fits_kind(*value, kind),
        _ => false,
    }
}

fn literal_pattern_type(expr: &Expr) -> Option<Type> {
    match expr {
        Expr::Int(..) => Some(Type::Int(IntKind::I32)),
        Expr::Float(..) => Some(Type::Float(FloatKind::F64)),
        Expr::Bool(..) => Some(Type::Bool),
        Expr::Str(..) => Some(Type::Str),
        Expr::Null(_) => Some(Type::null()),
        _ => None,
    }
}

fn literal_pattern_matches(expr: &Expr, lit_ty: &Type, scrutinee: &Type) -> bool {
    match (expr, scrutinee) {
        (_, Type::Unknown(_)) => true,
        (Expr::Int(..), Type::Int(_)) => integer_literal_fits(expr, scrutinee),
        (Expr::Null(_), Type::Nullable(_) | Type::Never) => true,
        _ => Subst::new().unify(lit_ty, scrutinee).is_ok(),
    }
}

fn integer_literal_binary_type(
    op: BinOp,
    left_expr: Option<&Expr>,
    left: &Type,
    right_expr: Option<&Expr>,
    right: &Type,
) -> Option<Type> {
    if left_expr.is_some_and(|expr| integer_literal_fits(expr, right)) {
        return integer_literal_binary_result(op, right);
    }
    if right_expr.is_some_and(|expr| integer_literal_fits(expr, left)) {
        return integer_literal_binary_result(op, left);
    }
    None
}

fn integer_literal_binary_result(op: BinOp, contextual_type: &Type) -> Option<Type> {
    if !matches!(contextual_type, Type::Int(_)) {
        return None;
    }
    match op {
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::Div
        | BinOp::Rem
        | BinOp::BitAnd
        | BinOp::BitOr
        | BinOp::BitXor
        | BinOp::Shl
        | BinOp::Shr => Some(contextual_type.clone()),
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => Some(Type::Bool),
        BinOp::And | BinOp::Or => None,
    }
}

fn is_result_return_type(ty: &Type) -> bool {
    ty.is_unknown() || ty.is_result_type()
}

fn next_unknown_after_program(program: &Program) -> u32 {
    let mut max_id = None;
    let mut record = |id| {
        max_id = Some(max_id.map_or(id, |max: u32| max.max(id)));
    };
    for info in program.types.values() {
        match &info.kind {
            TypeKind::Record { fields, methods } => {
                for field in fields {
                    if let Some(ty) = &field.resolved_ty {
                        visit_unknowns(ty, &mut record);
                    }
                }
                for method in methods.values() {
                    visit_signature_unknowns(&method.signature, &mut record);
                }
            }
            TypeKind::Sum { variants } => {
                for variant in variants {
                    for field in &variant.fields {
                        if let Some(ty) = &field.resolved_ty {
                            visit_unknowns(ty, &mut record);
                        }
                    }
                    for method in variant.methods.values() {
                        visit_signature_unknowns(&method.signature, &mut record);
                    }
                }
            }
        }
    }
    for function in program.functions.values() {
        visit_signature_unknowns(&function.signature, &mut record);
    }
    max_id.map_or(0, |id| id.saturating_add(1))
}

fn visit_signature_unknowns(signature: &CallableSignature, record: &mut impl FnMut(u32)) {
    for param in &signature.params {
        if let Some(ty) = &param.resolved_ty {
            visit_unknowns(ty, record);
        }
    }
    if let Some(ty) = &signature.ret_ty {
        visit_unknowns(ty, record);
    }
}

fn visit_unknowns(ty: &Type, record: &mut impl FnMut(u32)) {
    match ty {
        Type::Unknown(id) => record(*id),
        Type::Record(name) | Type::Sum(name) => {
            name.substitution
                .iter()
                .for_each(|(_, ty)| visit_unknowns(ty, record));
        }
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Nullable(inner)
        | Type::ConstOf(inner) => visit_unknowns(inner, record),
        Type::Fun(params, ret) => {
            params
                .iter()
                .for_each(|param| visit_unknowns(param, record));
            visit_unknowns(ret, record);
        }
        Type::Bool
        | Type::Int(_)
        | Type::Float(_)
        | Type::Str
        | Type::Void
        | Type::Never
        | Type::SelfType => {}
    }
}

fn common_nullable_type(left: &Type, right: &Type) -> Option<Type> {
    match (left.is_null(), right.is_null()) {
        (true, true) => Some(Type::null()),
        (true, false) => Some(nullable_common_side(right)),
        (false, true) => Some(nullable_common_side(left)),
        (false, false) => None,
    }
}

fn nullable_common_side(ty: &Type) -> Type {
    match ty {
        Type::Unknown(_) | Type::Nullable(_) => ty.clone(),
        other => Type::Nullable(Box::new(other.clone())),
    }
}

fn apply_nominal_substitution(ty: Type, substitution: Substitution) -> Type {
    if substitution.is_empty() {
        return ty;
    }
    match ty {
        Type::Record(name) => Type::Record(NominalType::with_substitution(
            name.id,
            name.name,
            substitution,
        )),
        Type::Sum(name) => Type::Sum(NominalType::with_substitution(
            name.id,
            name.name,
            substitution,
        )),
        other => other,
    }
}

fn field_substitution_key(variant: Option<&str>, field: &str) -> String {
    variant
        .map(|variant| format!("{variant}.{field}"))
        .unwrap_or_else(|| field.to_string())
}

fn method_param_substitution_key(method: &str, param: &str) -> String {
    format!("{method}.{param}")
}

fn method_return_substitution_key(method: &str) -> String {
    format!("{method}.return")
}

fn apply_method_substitution(
    mut resolved: ResolvedMethod,
    substitution: &Substitution,
    method: &str,
) -> ResolvedMethod {
    if substitution.is_empty() {
        return resolved;
    }
    for param in &mut resolved.signature.params {
        if param.name == "self" {
            continue;
        }
        let key = method_param_substitution_key(method, &param.name);
        if let Some(ty) = substitution.get(&key) {
            param.resolved_ty = Some(ty.clone());
        }
    }
    let key = method_return_substitution_key(method);
    if let Some(ty) = substitution.get(&key) {
        resolved.signature.ret_ty = Some(ty.clone());
    }
    resolved
}

fn param_expected_type(param: &ParamInfo) -> Option<&Type> {
    param.resolved_ty.as_ref().filter(|ty| !ty.is_unknown())
}

/// Whether a parameter is nullable. A trailing run of nullable parameters is
/// optional at call sites: each omitted argument defaults to `null` (DESIGN.md
/// 5.6). This is how `assert(cond, msg: string?)` accepts both `assert(cond)` and
/// `assert(cond, "..")` without function overloading.
fn param_is_nullable(param: &ParamInfo) -> bool {
    matches!(param.resolved_ty, Some(Type::Nullable(_)))
        || matches!(param.ty, Some(TypeExpr::Nullable(..)))
}

/// The fewest arguments a call must supply: the parameter count minus the trailing
/// run of optional (nullable) parameters.
fn required_arg_count(params: &[ParamInfo]) -> usize {
    let optional = params
        .iter()
        .rev()
        .take_while(|p| param_is_nullable(p))
        .count();
    params.len() - optional
}

fn env_from_scopes(scopes: &ScopeStack) -> HashMap<String, Type> {
    let mut env = HashMap::new();
    for scope in scopes {
        for (name, ty) in scope {
            env.insert(name.clone(), ty.clone());
        }
    }
    env
}

fn is_maybe_iterable(ty: &Type) -> bool {
    matches!(ty, Type::Array(..) | Type::Slice(..) | Type::Unknown(_))
}

fn is_maybe_indexable(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Array(..) | Type::Slice(..) | Type::Str | Type::Unknown(_)
    )
}

fn int_fits_kind(value: i64, kind: IntKind) -> bool {
    let value = value as i128;
    let (min, max) = match kind {
        IntKind::I8 => (i8::MIN as i128, i8::MAX as i128),
        IntKind::I16 => (i16::MIN as i128, i16::MAX as i128),
        IntKind::I32 => (i32::MIN as i128, i32::MAX as i128),
        IntKind::I64 => (i64::MIN as i128, i64::MAX as i128),
        IntKind::U8 => (0, u8::MAX as i128),
        IntKind::U16 => (0, u16::MAX as i128),
        IntKind::U32 => (0, u32::MAX as i128),
        IntKind::U64 => (0, u64::MAX as i128),
    };
    (min..=max).contains(&value)
}

fn assign_binop(op: AssignOp) -> BinOp {
    match op {
        AssignOp::Eq => unreachable!("plain assignment is not a binary operator"),
        AssignOp::Add => BinOp::Add,
        AssignOp::Sub => BinOp::Sub,
        AssignOp::Mul => BinOp::Mul,
        AssignOp::Div => BinOp::Div,
        AssignOp::Rem => BinOp::Rem,
    }
}

fn is_null_comparison(op: BinOp, left: &Type, right: &Type) -> bool {
    matches!(op, BinOp::Eq | BinOp::Ne) && (left.is_null() || right.is_null())
}

fn is_self_expr(expr: &Expr) -> bool {
    match expr {
        Expr::SelfExpr(_) => true,
        Expr::Ident(name, _) => name == "self",
        _ => false,
    }
}

fn block_always_returns(block: &Block) -> bool {
    block.stmts.iter().any(|s| matches!(s, Stmt::Return(..)))
}

fn op_str(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::Le => "<=",
        BinOp::Ge => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
    }
}

fn unary_op_str(op: UnaryOp) -> &'static str {
    match op {
        UnaryOp::Neg => "-",
        UnaryOp::Not => "!",
        UnaryOp::BitNot => "~",
    }
}

trait Pipe: Sized {
    fn pipe<T>(self, f: impl FnOnce(Self) -> T) -> T {
        f(self)
    }
}
impl<T> Pipe for T {}
