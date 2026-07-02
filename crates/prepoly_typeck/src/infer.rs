//! Local static type checks.
//!
//! This pass intentionally remains conservative around genuinely polymorphic or
//! structurally inferred code, but every type that is explicit in source is
//! enforced before execution. It checks annotations, constructor fields,
//! annotated function/method calls, nullable use-before-check, and operators.
//! Unknown values are represented with unification variables so uncertain code
//! can still be deferred to the runtime without accepting contradictions against
//! explicit types.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use prepoly_hir::{
    CallableSignature, Constness, FloatKind, FunInfo, IntKind, NominalType, ParamInfo, Program,
    SchemeMethod, Substitution, Type, TypeInfo, TypeKind, TypeScheme, TypedProgram,
    common_numeric_type, int_literal_kind, numeric_flows_into,
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

/// The pieces of a callable whose first parameter is filled by a receiver,
/// cloned out of a `FunInfo` so the call can be checked while the checker is
/// mutably borrowed. Shared by UFCS and primitive-method dispatch.
struct ReceiverCall {
    symbol: String,
    module: Vec<String>,
    signature_params: Vec<ParamInfo>,
    declared_ret: Option<Type>,
    decl: Rc<FunDecl>,
}

impl ReceiverCall {
    fn from_fun(info: &FunInfo) -> Self {
        Self {
            symbol: info.symbol.clone(),
            module: info.module.clone(),
            signature_params: info.signature.params.clone(),
            declared_ret: info.signature.ret_ty.clone(),
            decl: info.decl.clone(),
        }
    }
}

pub fn check(program: &Program) -> Vec<TypeError> {
    analyze(program).errors
}

pub struct Inference {
    pub errors: Vec<TypeError>,
    pub typed: TypedProgram,
    /// Fully-concrete call instances per free-function symbol.
    pub fn_instances: HashMap<String, Vec<Vec<Type>>>,
    /// Per record-type generalized scheme (its inferred type parameters and the
    /// field/method signatures over them), keyed by the type's source name. Read
    /// by the language server to render a method generically; see `build_schemes`.
    pub schemes: HashMap<String, TypeScheme>,
}

pub fn analyze(program: &Program) -> Inference {
    let mut checker = Checker::new(program);
    checker.validate_param_declarations();
    checker.precompute_global_bindings();
    checker.precompute_function_returns();
    checker.precompute_method_returns();
    // Check each type's method bodies first, then generalize each record type into
    // a scheme. The method loop binds `self` to the bare type, so a type's methods
    // share one field variable and their parameter/return variables are linked
    // through the bodies. Generalizing before the function bodies are checked makes
    // the schemes available at call sites (a function instantiates a method's
    // scheme to type the call's result) and keeps the generic field variable read
    // here free of any concrete use.
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
    checker.schemes = checker.build_schemes();

    for f in program.functions.values() {
        tracing::debug!(function = %f.signature.name, "inferring function body");
        let mut scopes = checker.signature_scopes(&f.signature.params);
        let ret = f.signature.ret_ty.clone();
        checker.current_module = f.module.clone();
        checker.check_block_root(&f.decl.body, &mut scopes, ret.as_ref());
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
    // Each expression's type was resolved against the substitution as it was
    // recorded, but a variable can be pinned *after* an expression that mentions
    // it was checked (e.g. an array element fixed by a later `push`). Re-resolve
    // every recorded type against the final substitution so the typed program
    // reflects the fully solved types -- which hover and the other LSP features
    // read directly.
    checker.finalize_typed();
    Inference {
        errors: checker.errors,
        typed: checker.typed,
        fn_instances: checker.fn_instances,
        schemes: checker.schemes,
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
    /// The resolved type of each `return` value, collected per enclosing callable
    /// (one frame per `return_contexts` frame). The full check observes the stores
    /// and pushes a body performs, so its inferred return is more precise than the
    /// light pass -- a witness-free constructor's nullable slot element resolves
    /// here. Consumed by `check_block_root` for an inferred-return body.
    return_values: Vec<Vec<(Type, prepoly_lexer::Span)>>,
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
    /// used by the local inference and monomorphization passes.
    solver: Solver,
    /// The module whose body is currently being checked, used to enforce
    /// per-module name visibility. Set per function,
    /// method, and module-init, and swapped while a called body is re-checked.
    current_module: Vec<String>,
    /// Fully-concrete call instances per free-function symbol: every distinct
    /// tuple of resolved argument types a function is called with. This is the
    /// input to static monomorphization: the
    /// typed backend can compile one specialized instance per tuple. Stored as a
    /// deduplicated `Vec` because `Type` is not `Hash`/`Eq`.
    fn_instances: HashMap<String, Vec<Vec<Type>>>,
    /// Per record-type generalized scheme, keyed by type name. Built after the
    /// method bodies are co-checked and consulted at call sites to type a method
    /// call's result by instantiating the method's scheme against the receiver.
    schemes: HashMap<String, TypeScheme>,
    /// One-shot marker set while checking the direct array-literal initializer
    /// of an unannotated `const` binding: the binding is immutable, so the
    /// literal types as a fixed-length array (`int32[3]`) rather than a growable
    /// slice. Consumed (reset) by the literal itself, so nested literals and any
    /// other position stay slices.
    fixed_array_binding: bool,
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
            return_values: Vec::new(),
            global_scope: HashMap::new(),
            function_returns: HashMap::new(),
            method_returns: HashMap::new(),
            instantiating: HashSet::new(),
            shape_constraints: HashMap::new(),
            solver: Solver::new(),
            current_module: Vec::new(),
            fn_instances: HashMap::new(),
            schemes: HashMap::new(),
            fixed_array_binding: false,
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

    /// Generalize every record type into a [`TypeScheme`]. Run after the per-type
    /// method bodies have been checked in one shared environment: that pass binds
    /// `self` to the bare type, so a type's methods share one field variable, and
    /// the bodies' stores/reads link a field's element to the methods' parameter
    /// and return variables (`HashMap`'s entry key/value is the `key`/`value` of
    /// `set`/`_insert` through `self.entries[i] = _Entry { .. }`). This reads the
    /// solver's solution for each field and method signature and quantifies the
    /// inference variables still free across them -- the inferred type parameters.
    fn build_schemes(&self) -> HashMap<String, TypeScheme> {
        let mut out = HashMap::new();
        for info in self.program.types.values() {
            if let TypeKind::Record { .. } = &info.kind {
                out.insert(info.name.clone(), self.build_record_scheme(info));
            }
        }
        out
    }

    fn build_record_scheme(&self, info: &TypeInfo) -> TypeScheme {
        let TypeKind::Record { fields, methods } = &info.kind else {
            return TypeScheme::default();
        };
        let mut params: HashSet<u32> = HashSet::new();
        let resolved = |this: &Self, t: Option<&Type>| t.map(|t| this.resolve(t));
        let mut field_types = Vec::with_capacity(fields.len());
        for field in fields {
            let ty = resolved(self, field.resolved_ty.as_ref()).unwrap_or(Type::Void);
            params.extend(self.solver.free_vars(&ty));
            field_types.push((field.name.clone(), ty));
        }
        let self_ty = info.type_ref();
        let mut scheme_methods = std::collections::BTreeMap::new();
        for (name, method) in methods {
            let mut ps = Vec::with_capacity(method.signature.params.len());
            for p in &method.signature.params {
                let ty = if p.name == "self" {
                    self_ty.clone()
                } else {
                    resolved(self, p.resolved_ty.as_ref()).unwrap_or(Type::Void)
                };
                params.extend(self.solver.free_vars(&ty));
                ps.push((p.name.clone(), ty));
            }
            let ret = self
                .method_returns
                .get(&(info.name.clone(), name.clone()))
                .map(|t| self.resolve(t))
                .or_else(|| resolved(self, method.signature.ret_ty.as_ref()))
                .unwrap_or(Type::Void);
            params.extend(self.solver.free_vars(&ret));
            scheme_methods.insert(name.clone(), SchemeMethod { params: ps, ret });
        }
        let mut params: Vec<u32> = params.into_iter().collect();
        params.sort_unstable();
        TypeScheme {
            params,
            fields: field_types,
            methods: scheme_methods,
        }
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
    /// a local `error(x)` must agree on one payload type; two
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
                    // Grow a locally-built collection's element type: a
                    // `result = []` then `result.push(x)` pins `result`'s element
                    // to `x`, so an unannotated function that returns the built
                    // collection (e.g. `slice`/`map`) infers its element type from
                    // the values pushed -- which the rest of this light pass would
                    // otherwise miss, leaving the return an unconstrained `?[]`.
                    self.track_collection_growth(value, env, errors);
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
                    let item_ty = prepoly_hir::index_element(&iter_ty)
                        .unwrap_or_else(|| self.fresh_unknown());
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

    /// If `expr` is `recv.push(value)` or `recv.insert(idx, value)` where `recv`
    /// is a slice/array, unify its element type with the pushed value's type.
    /// This pins the (fresh, local) element variable of a collection being built
    /// up, so the light return-inference pass sees the grown element type. It
    /// only ever binds the local's own element variable, not the function's
    /// parameter variables.
    fn track_collection_growth(
        &mut self,
        expr: &Expr,
        env: &HashMap<String, Type>,
        errors: &mut Vec<(Type, Span)>,
    ) {
        if let Expr::Call(callee, args, _) = expr
            && let Expr::Field(recv, method, _) = callee.as_ref()
            && matches!(method.as_str(), "push" | "insert")
            && let Some(value_arg) = args.last()
        {
            let recv_ty = self.infer_expr_light(recv, env, errors);
            if let Some(elem) = prepoly_hir::index_element(&self.resolve(&recv_ty)) {
                let value_ty = self.infer_expr_light(&value_arg.expr, env, errors);
                let _ = self.solver.unify(&elem, &value_ty);
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
            Expr::Int(v, _) => Type::Int(int_literal_kind(*v)),
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
                ref bt if prepoly_hir::index_element(bt).is_some() => {
                    prepoly_hir::index_element(bt).unwrap()
                }
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
            Expr::Range(lo, _, _) => Type::Slice(Box::new(self.infer_expr_light(lo, env, errors))),
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
        // Resolve the base before matching: an indexed element or other
        // intermediate may still be an open inference variable that the solver has
        // since pinned to a record (e.g. `self.entries[idx]` is the map's entry
        // type once a `push` fixed it). Without resolving, the match falls through
        // and the field type is lost as a fresh unknown.
        let base_ty = self.infer_expr_light(base, env, errors);
        match self.resolve(&base_ty) {
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
        if name.is_empty() {
            let field_tys: Vec<(String, Type)> = fields
                .iter()
                .map(|(fname, e)| (fname.clone(), self.infer_expr_light(e, env, errors)))
                .collect();
            return prepoly_hir::structural_record(field_tys);
        }
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
                if let Type::Tuple(elems) = ty {
                    for (pat, ety) in pats.iter().zip(elems) {
                        self.bind_pattern_light(pat, ety, env);
                    }
                } else {
                    let elem = match ty {
                        Type::Array(inner, _) | Type::Slice(inner) => &**inner,
                        _ => ty,
                    };
                    pats.iter()
                        .for_each(|pat| self.bind_pattern_light(pat, elem, env));
                }
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
    /// order and record them in `global_scope`. Bindings
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

    fn resolve_type(&mut self, te: &TypeExpr) -> Result<Type, String> {
        match te {
            TypeExpr::Named(name, _) => self.resolve_named(name),
            TypeExpr::Array(inner, Some(n), _) => {
                Ok(Type::Array(Box::new(self.resolve_type(inner)?), *n))
            }
            TypeExpr::Array(inner, None, _) => Ok(Type::Slice(Box::new(self.resolve_type(inner)?))),
            TypeExpr::Fun(params, ret, _) => {
                let mut ps = Vec::with_capacity(params.len());
                for p in params {
                    ps.push(self.resolve_type(p)?);
                }
                Ok(Type::Fun(ps, Box::new(self.resolve_type(ret)?)))
            }
            TypeExpr::Nullable(inner, _) => Ok(Type::Nullable(Box::new(self.resolve_type(inner)?))),
            // `T!` is the fallible Result; the error payload is a fresh unknown so
            // it is inferred from the body's error sites (like `infer`).
            TypeExpr::Fallible(inner, _) => {
                let ok = self.resolve_type(inner)?;
                Ok(Type::result(ok, self.fresh_unknown()))
            }
            TypeExpr::Tuple(elems, _) => {
                let mut ts = Vec::with_capacity(elems.len());
                for e in elems {
                    ts.push(self.resolve_type(e)?);
                }
                Ok(Type::Tuple(ts))
            }
            TypeExpr::Anonymous(fields, _) => {
                let mut resolved = Vec::with_capacity(fields.len());
                for (name, fty) in fields {
                    resolved.push((name.clone(), self.resolve_type(fty)?));
                }
                Ok(prepoly_hir::structural_record(resolved))
            }
            TypeExpr::Mut(inner, _) => Ok(Type::Mut(Box::new(self.resolve_type(inner)?))),
            TypeExpr::Ref(inner, _) => Ok(Type::Ref(Box::new(self.resolve_type(inner)?))),
        }
    }

    fn resolve_named(&mut self, name: &str) -> Result<Type, String> {
        if let Some(k) = IntKind::from_name(name) {
            return Ok(Type::Int(k));
        }
        match name {
            "bool" => Ok(Type::Bool),
            "float32" => Ok(Type::Float(FloatKind::F32)),
            "float64" => Ok(Type::Float(FloatKind::F64)),
            "string" => Ok(Type::Str),
            "void" => Ok(Type::Void),
            // `infer` is an unknown filled in by inference (for `infer[]` etc.).
            "infer" => Ok(self.fresh_unknown()),
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

    /// Check a function/method body. For an inferred-return body (`ret` is `None`)
    /// returns the reconciled type of its `return` values as observed by the full
    /// check (so a constructor whose slot array is filled with `null` returns the
    /// nullable element type), or `None` for an explicit-return body.
    fn check_block_root(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
    ) -> Option<Type> {
        let saved = std::mem::replace(&mut self.const_scopes, vec![HashSet::new()]);
        self.return_contexts.push(match ret {
            Some(ty) => ReturnContext::Explicit(ty.clone()),
            None => ReturnContext::Inferred,
        });
        self.return_values.push(Vec::new());
        self.check_block(b, scopes);
        let collected = self.return_values.pop().unwrap_or_default();
        self.return_contexts.pop();
        self.const_scopes = saved;
        if ret.is_none() {
            self.reconcile_return_types(&collected, false)
        } else {
            None
        }
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
    /// own (inferred) context rather than the outer function.
    fn check_return(
        &mut self,
        value: Option<&Expr>,
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) {
        let returned = match self.return_contexts.last().cloned() {
            Some(ReturnContext::Explicit(want)) => match value {
                Some(e) => {
                    // A fallible return type (`-> T!`, or any `Result`) auto-wraps a
                    // bare value as `Ok { value }`: check it against the Ok payload.
                    // A `Result`-typed value flows whole. This mirrors the inferred
                    // fallible path and the HM checker (`hm::Stmt::Return`).
                    let resolved = self.resolve(&want);
                    if let Some((ok, _err)) = resolved.result_payloads() {
                        let ok = ok.clone();
                        let got = self.check_expr(e, scopes);
                        if self.resolve(&got).is_result_type() {
                            self.expect_assignable(&got, &want, span);
                        } else {
                            self.expect_assignable(&got, &ok, span);
                        }
                        got
                    } else {
                        self.check_expr_against(e, &want, scopes)
                    }
                }
                None => {
                    self.expect_assignable(&Type::Void, &want, span);
                    Type::Void
                }
            },
            // Inferred context (closure or unannotated function) or no context
            // (module top level): type the value but do not constrain it; the
            // return type is reconciled separately.
            _ => match value {
                Some(e) => self.check_expr(e, scopes),
                None => Type::Void,
            },
        };
        // Collect the resolved return type for the enclosing callable's inferred
        // return (see `return_values`); harmless for an explicit-return body, whose
        // collected values `check_block_root` discards.
        let resolved = self.resolve(&returned);
        if let Some(frame) = self.return_values.last_mut() {
            frame.push((resolved, span));
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
                    // An unannotated `const` bound directly to a non-empty array
                    // literal is immutable, so the literal types as a
                    // fixed-length array; a `let` binding stays a growable
                    // slice. An annotation (above) always wins.
                    self.fixed_array_binding =
                        *is_const && matches!(value, Expr::Array(es, _) if !es.is_empty());
                    let t = self.check_expr(value, scopes);
                    self.fixed_array_binding = false;
                    t
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
                    // A store into an array element whose type still carries an
                    // open inference variable commits the value into it (the way
                    // `push` does), so `arr[i] = v` pins an as-yet-unknown element
                    // -- including a record element with open fields (`_Entry<?,
                    // ?>`), whose key/value the stored value refines through the
                    // solver. A fully-concrete element keeps the ordinary
                    // bidirectional check (typed integer literals, structural
                    // compatibility).
                    let target_open = matches!(target, Expr::Index(..))
                        && !self.solver.free_vars(&self.resolve(&target_ty)).is_empty();
                    if target_open {
                        let value_ty = self.check_expr(value, scopes);
                        self.expect_element_assignable(&value_ty, &target_ty, value);
                    } else {
                        self.check_expr_against(value, &target_ty, scopes);
                    }
                } else {
                    let value_ty = self.check_expr(value, scopes);
                    let result = self.check_binary(assign_binop(*op), &target_ty, &value_ty, *span);
                    // The combined result is stored back into the target, so it
                    // must flow into the target's type: `int64 += int32` widens
                    // the operand, but `int32 += float64` would need a silent
                    // float -> int truncation on the write-back and is rejected.
                    self.expect_assignable(&result, &target_ty, *span);
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
                // Iterating sees through reference/mutability wrappers and binds the
                // loop variable to the element of the same kind: over `ref(mut(T[]))`
                // each element is a `ref(mut(T))`, so mutating it writes through.
                let item_ty = self.for_element(&iter_ty).unwrap_or_else(|| {
                    self.errors.push(TypeError {
                        message: format!(
                            "cannot iterate over `{}`",
                            self.resolve(&iter_ty).display()
                        ),
                        span: iter.span(),
                    });
                    self.fresh_unknown()
                });
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
        // type (resolution): record it at the target
        // kind so its runtime tag matches the annotation rather than defaulting
        // to int32 (typed literals).
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
        // An array literal in a required slice position (`int32?[]`): each element
        // flows into the expected element type, so an integer literal takes the
        // annotated width, a `null` element is a valid nullable, and a plain value
        // widens to a nullable element. Propagating the element type is what lets
        // `[4, 1, 5, null, 65]` and `[4, 1, 5, 65]` both be `int32?[]` instead of
        // being inferred independently (a heterogeneous literal would otherwise
        // become a tuple).
        if let (Expr::Array(items, _), Type::Slice(elem)) = (expr, self.resolve(want)) {
            for item in items {
                self.check_expr_against(item, &elem, scopes);
            }
            let ty = Type::Slice(elem);
            self.record_expr_type(expr, &ty);
            return ty;
        }
        // A bracket literal in a required tuple position: each element flows into
        // its own expected type, so e.g. an int literal takes the annotated width.
        if let (Expr::Array(items, span), Type::Tuple(elems)) = (expr, self.resolve(want)) {
            if items.len() != elems.len() {
                self.errors.push(TypeError {
                    message: format!(
                        "tuple literal has {} elements, but `{}` requires {}",
                        items.len(),
                        want.display(),
                        elems.len()
                    ),
                    span: *span,
                });
            }
            for (item, ety) in items.iter().zip(&elems) {
                self.check_expr_against(item, ety, scopes);
            }
            let ty = Type::Tuple(elems);
            self.record_expr_type(expr, &ty);
            return ty;
        }
        // A closure in a position that wants a function type is checked against
        // that type: each parameter takes the expected parameter type (so an
        // unannotated `self`/value parameter is typed without a separate
        // annotation) and the body is checked against the expected return, so a
        // block-bodied closure's `return` reconciles with it rather than leaving
        // the closure's result `void`.
        if let Expr::Closure(params, body, _) = expr
            && let Type::Fun(want_params, want_ret) = self.resolve(want)
        {
            return self.check_closure_against(expr, params, body, &want_params, &want_ret, scopes);
        }
        let got = self.check_expr(expr, scopes);
        self.expect_expr_assignable(&got, want, expr);
        got
    }

    /// Check a closure literal against an expected function type, binding each
    /// parameter to the expected parameter type and the body to the expected
    /// return. Returns `Type::Fun(param_types, want_ret)`.
    fn check_closure_against(
        &mut self,
        expr: &Expr,
        params: &[Param],
        body: &Expr,
        want_params: &[Type],
        want_ret: &Type,
        scopes: &mut ScopeStack,
    ) -> Type {
        self.report_duplicate_params("closure", params);
        let mut closure_scope: HashMap<String, Type> = HashMap::new();
        let mut param_types = Vec::with_capacity(params.len());
        for (i, p) in params.iter().enumerate() {
            let expected = want_params
                .get(i)
                .cloned()
                .unwrap_or_else(|| self.fresh_unknown());
            // An explicit parameter annotation still applies and is checked
            // against the expected type; an unannotated parameter takes it.
            let ty = match &p.ty {
                Some(te) => {
                    let annotated = self
                        .resolve_type(te)
                        .unwrap_or_else(|_| self.fresh_unknown());
                    self.expect_assignable(&annotated, &expected, p.span);
                    annotated
                }
                None => expected,
            };
            closure_scope.insert(p.name.clone(), ty.clone());
            param_types.push(ty);
        }
        let mut inferred_env = env_from_scopes(scopes);
        inferred_env.extend(closure_scope.clone());
        let mut propagated_errors = Vec::new();
        self.infer_expr_light(body, &inferred_env, &mut propagated_errors);
        let mut closure_scopes = scopes.clone();
        closure_scopes.push(closure_scope);
        self.const_scopes.push(HashSet::new());
        self.return_contexts
            .push(ReturnContext::Explicit(want_ret.clone()));
        self.return_values.push(Vec::new());
        let body_val = self.check_expr(body, &mut closure_scopes);
        self.return_values.pop();
        self.return_contexts.pop();
        self.const_scopes.pop();
        // An expression-bodied closure (not a `{ ... }` block) returns its body
        // value directly, so that value must match the expected return; a block
        // body returns through the `return` context handled above.
        if !matches!(body, Expr::Block(..)) {
            self.expect_expr_assignable(&body_val, want_ret, body);
        }
        let ty = Type::Fun(param_types, Box::new(want_ret.clone()));
        self.record_expr_type(expr, &ty);
        ty
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

    /// Record a pattern binding's type at the binding identifier's own span, as
    /// a typed `Ident` entry. The binding name is not an expression, so without
    /// this the declaration site has no typed node and hover falls back to
    /// borrowing a *use*'s type -- wrong when the annotated binding type differs
    /// from the initializer's (`let b: int64 = an_int32`), and absent entirely
    /// for an unused binding. The type may still be open here; `finalize_typed`
    /// re-resolves it against the final substitution like every other entry.
    fn record_binding(&mut self, name: &str, span: Span, ty: &Type) {
        let ty = self.resolve(ty);
        self.typed.push_kind(
            prepoly_hir::TypedExprKind::Ident(name.to_string()),
            span,
            ty,
            Constness::Unknown,
        );
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

    /// Re-resolve every recorded expression type against the final substitution.
    /// Run once after all checking, so a type recorded before one of its
    /// variables was pinned still reflects the solved type. `resolve` is deep --
    /// it follows variables nested inside arrays, function types, and a nominal's
    /// substitution (so a `HashMap`'s `entries` element pinned by a later `push`
    /// shows its concrete type) -- and preserves the `ConstOf` wrapper, so
    /// constness is unchanged.
    fn finalize_typed(&mut self) {
        let resolved: Vec<Type> = self
            .typed
            .expressions
            .iter()
            .map(|e| self.solver.resolve(&e.ty))
            .collect();
        for (e, ty) in self.typed.expressions.iter_mut().zip(resolved) {
            e.ty = ty;
        }
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
            Expr::Int(v, _) => Type::Int(int_literal_kind(*v)),
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
                    // pre-execution check, so this is an
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
                let resolved = self.resolve(&base_ty);
                // A tuple is indexed by a constant literal, yielding the element
                // type at that position.
                if let Type::Tuple(elems) = &resolved {
                    let _ = self.check_expr(idx, scopes);
                    return match const_index(idx) {
                        Some(k) if (k as usize) < elems.len() => elems[k as usize].clone(),
                        Some(k) => {
                            self.errors.push(TypeError {
                                message: format!(
                                    "tuple index {k} out of bounds for `{}`",
                                    resolved.display()
                                ),
                                span: *span,
                            });
                            self.fresh_unknown()
                        }
                        None => {
                            self.errors.push(TypeError {
                                message: "a tuple can only be indexed by a constant integer"
                                    .to_string(),
                                span: *span,
                            });
                            self.fresh_unknown()
                        }
                    };
                }
                let idx_ty = self.check_expr(idx, scopes);
                self.expect_int_index(&idx_ty, idx.span());
                if let Some(elem) = prepoly_hir::index_element(&resolved) {
                    return elem;
                }
                match resolved {
                    Type::Str => Type::Str,
                    Type::Nullable(_) => {
                        self.report_nullable_use(*span);
                        self.fresh_unknown()
                    }
                    other => {
                        if let Type::Unknown(_) = other {
                            // Defer, but record that the receiver must be
                            // indexable so a closure like `(x) -> x[0]` rejects
                            // a non-indexable argument at its call site.
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
                self.return_values.push(Vec::new());
                let ret = self.check_expr(body, &mut closure_scopes);
                self.return_values.pop();
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
                // Consumed before the elements are checked, so only the direct
                // initializer of an unannotated `const` binding is fixed-length;
                // nested literals and every other position stay slices.
                let fixed = std::mem::take(&mut self.fixed_array_binding);
                let elem_tys: Vec<Type> = es.iter().map(|e| self.check_expr(e, scopes)).collect();
                // Heterogeneous concrete elements form a tuple; otherwise an
                // array. A `null` element never forces a tuple: null unifies
                // with any element type, making the element nullable
                // (`[4, null, 65]` is an `int32?` sequence).
                if let Some(tuple) = self.tuple_of_elements(es, &elem_tys) {
                    Type::Tuple(tuple)
                } else {
                    let base = elem_tys
                        .iter()
                        .zip(es)
                        .find(|(_, e)| !matches!(e, Expr::Null(_)))
                        .map(|(t, _)| t.clone())
                        .unwrap_or_else(|| self.fresh_empty_array_elem());
                    let saw_null = es.iter().any(|e| matches!(e, Expr::Null(_)));
                    let elem_ty = if saw_null && !matches!(self.resolve(&base), Type::Nullable(_)) {
                        Type::Nullable(Box::new(base))
                    } else {
                        base
                    };
                    for (got, e) in elem_tys.iter().zip(es) {
                        if matches!(e, Expr::Null(_)) {
                            continue;
                        }
                        self.expect_expr_assignable(got, &elem_ty, e);
                    }
                    if fixed {
                        Type::Array(Box::new(elem_ty), es.len())
                    } else {
                        Type::Slice(Box::new(elem_ty))
                    }
                }
            }
            Expr::Range(lo, hi, _) => {
                // `[lo..hi]` -- both bounds are integers of a shared type, the
                // element type of the resulting array.
                let lo_ty = self.check_expr(lo, scopes);
                let hi_ty = self.check_expr(hi, scopes);
                self.expect_int_index(&lo_ty, lo.span());
                self.expect_int_index(&hi_ty, hi.span());
                self.expect_expr_assignable(&hi_ty, &lo_ty, hi);
                Type::Slice(Box::new(lo_ty))
            }
            Expr::TypeLit(name, fields, span) => self.check_record_lit(name, fields, *span, scopes),
            Expr::VariantLit(t, variant, fields, span) => {
                self.check_variant_lit(t, variant, fields, *span, scopes)
            }
            Expr::If(cond, then, els, span) => {
                let cond_ty = self.check_condition(cond, scopes);
                let mut truth = cond_ty.static_truthiness();
                // Structural graceful degradation (the goal's structure-type rules):
                // when the condition is a field access on a structural value that
                // does not satisfy the then-branch for this concrete value (a
                // missing field reads as `never?`, or a present field whose type the
                // then-branch cannot use), the `if` is statically false rather than a
                // type error. Probe the then-branch; if it does not type-check, fold
                // the condition to false so its dead arm is discarded.
                if truth != Some(false) && matches!(&**cond, Expr::Field(..)) {
                    let mark = self.errors.len();
                    let mut probe = scopes.clone();
                    self.apply_truthy_narrowing(cond, &mut probe);
                    self.check_branch(then, &mut probe, false);
                    if self.errors.len() > mark {
                        self.errors.truncate(mark);
                        truth = Some(false);
                    }
                }
                let mut then_scopes = scopes.clone();
                self.apply_truthy_narrowing(cond, &mut then_scopes);
                // A statically-known condition makes one arm unreachable. Its
                // body is still walked (so nested call instances are recorded for
                // monomorphization) but its type errors are discarded: a dead
                // path may not type-check -- e.g. a bare `null` (`never?`) whose
                // truthy arm narrows it to `never` -- yet must not reject the
                // program. The reachable arm alone determines the `if` type.
                let then_ty = self.check_branch(then, &mut then_scopes, truth == Some(false));
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
                // A plain binding on a nullable scrutinee is a presence test, so on
                // the then-arm the value is proven non-null: bind it at the unwrapped
                // type (e.g. `if let p = T.from(v)` gives `p: T`), so `p.field` is
                // valid rather than a nullable-use error.
                let bind_ty = match (pat, &self.resolve(&scrut_ty)) {
                    (Pattern::Binding(_, _), Type::Nullable(inner)) => (**inner).clone(),
                    _ => scrut_ty.clone(),
                };
                self.bind_pattern(pat, &bind_ty, &mut then_scopes);
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
                let resolved = self.resolve(&base_ty);
                if let Some(elem) = prepoly_hir::index_element(&resolved) {
                    return elem;
                }
                match resolved {
                    // A store into an open array variable pins its element type,
                    // the way `push` pins it on the read side: `self.entries[i] =
                    // v` ties the field's still-open element to `v`'s type while
                    // checking. Only fires when the base is genuinely open -- a
                    // concrete `Slice`/`Array` is handled by `index_element` above,
                    // so a real element-type clash at a store still surfaces.
                    open @ Type::Unknown(_) => {
                        let elem = self.fresh_unknown();
                        let _ = self
                            .solver
                            .unify(&open, &Type::Slice(Box::new(elem.clone())));
                        elem
                    }
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
        // Anonymous structure literal `{ f: v, ... }`: a structural record whose
        // field types are the field value types.
        if name.is_empty() {
            let field_tys: Vec<(String, Type)> = fields
                .iter()
                .map(|(fname, e)| (fname.clone(), self.check_expr(e, scopes)))
                .collect();
            return prepoly_hir::structural_record(field_tys);
        }
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
        // The concrete type `Self` denotes in a field type, so a closure-typed
        // field declared `(self, T) -> U` is checked with `self` bound to the
        // type being constructed rather than the abstract `Self`.
        let self_ty = self
            .program
            .types
            .get(who.split('.').next().unwrap_or(who))
            .map(|info| info.type_ref());
        for field in declared {
            match fields.iter().find(|(name, _)| name == &field.name) {
                Some((_, expr)) => {
                    let got = if let Some(want) = &field.resolved_ty {
                        let want = match &self_ty {
                            Some(s) => substitute_self(want, s),
                            None => want.clone(),
                        };
                        self.check_expr_against(expr, &want, scopes)
                    } else {
                        self.check_expr(expr, scopes)
                    };
                    // Record the field's value type in the instance substitution
                    // when the field's declared type still carries an inference
                    // variable: a bare unannotated field (`Unknown`), or a
                    // partially-inferred annotation like `infer?[]` (a slot array
                    // whose element is inferred from use). This carries the
                    // instance's resolved field type into the typed program and the
                    // back-end seed; a fully concrete annotation is static.
                    let inferred_field = field
                        .resolved_ty
                        .as_ref()
                        .is_some_and(|t| !self.solver.free_vars(t).is_empty());
                    if inferred_field {
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
    /// the enclosing sum type. `base` must name a sum type
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
                if let Some(info) = self.program.type_by_id(record.id)
                    && let TypeKind::Record { fields, methods } = &info.kind
                {
                    if let Some(field) = fields.iter().find(|f| f.name == name) {
                        return field
                            .resolved_ty
                            .clone()
                            .unwrap_or_else(|| self.fresh_unknown());
                    }
                    // A bare `recv.method` (method as a value) is left to the runtime.
                    if methods.contains_key(name) {
                        return self.fresh_unknown();
                    }
                }
                // Accessing a field a structure does not have is an inference
                // failure typed as the always-null `never?`: an `if` on it is
                // statically false (then-branch pruned), and using it as a non-null
                // value is still rejected, which keeps structural checks sound.
                Type::null()
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
            // than a deferred runtime shape. Method calls are
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
            // at its call site.
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
                // Record the callee's type so hover can recover it. Applying it
                // below constrains an unknown callee to a function type, and the
                // final zonking pass then resolves this recorded type through it,
                // so `fun apply(f, x) { f(x) }` shows `f` as `(U) -> V`.
                self.record_expr_type(callee, &local);
                return self.check_callable_value(local, args, span, scopes);
            }
            // Only a function visible from the current module resolves here; a
            // function defined in another, non-imported module is invisible and
            // falls through to the unknown-name path below. The
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
                // monomorphization.
                let resolved_args: Vec<Type> = arg_types.iter().map(|t| self.resolve(t)).collect();
                if resolved_args.iter().all(is_concrete_type) {
                    let entry = self.fn_instances.entry(symbol.clone()).or_default();
                    if !entry.iter().any(|t| t == &resolved_args) {
                        tracing::debug!(
                            symbol = %symbol,
                            args = ?resolved_args.iter().map(|t| t.display()).collect::<Vec<_>>(),
                            "recording new monomorphization instance"
                        );
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
            // to a fresh unknown.
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
                // A method defined in another module (e.g. the stdlib) is checked by
                // re-elaborating its body with this call's concrete types. When the
                // call's argument types are inconsistent with the receiver's
                // instance -- `map.get(1)` on a `string`-keyed map -- the clash
                // surfaces inside that body, at a span the caller cannot see (and the
                // LSP cannot show). Re-attribute such body errors to this call site,
                // so the inconsistency is reported where it originates.
                let foreign_method = self
                    .program
                    .types
                    .get(&methods[0].self_type)
                    .is_some_and(|t| t.module != self.current_module);
                let before = self.errors.len();
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
                if foreign_method && self.errors.len() > before {
                    self.reattribute_errors_to_call(before, method, span);
                }
                // Type the call's result by instantiating the method's scheme
                // against the receiver instance (schemes are built before the
                // function bodies that call them). The re-elaboration above still
                // ran for its conflict checks -- a key compared with `==` does not
                // unify onto a scheme parameter, so a `map.get(1)` clash is caught
                // there, not by the scheme. The re-elaborated return is the
                // fallback when the scheme cannot resolve the result.
                if let Some(ret) = self.scheme_method_return(&recv_ty, method) {
                    return ret;
                }
                return self
                    .common_type_list(&returns)
                    .unwrap_or_else(|| self.fresh_unknown());
            }
            // A stdlib method on a primitive/array receiver (`fun string.split`,
            // `fun infer[].map`): dispatched by the receiver's class. There is no
            // UFCS fallback -- a free function is not callable through `recv.f()`.
            if let Some(ret) =
                self.check_primitive_method_call(&recv_ty, method, args, span, scopes)
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
            // structural dispatch (shape constraints).
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
            // its call site. Evaluate the args and defer.
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

    /// Type-check a call `recv.m(args)` to a stdlib method implemented on a
    /// primitive/array receiver with `fun T.m(self, ...)`. The receiver's class
    /// (`Type::primitive_class`) keys the method in `primitive_methods`; the body
    /// is an ordinary function whose first parameter is the receiver. Returns
    /// `None` if the receiver type carries no such method.
    fn check_primitive_method_call(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        let class = self.resolve(recv_ty).primitive_class()?;
        let symbol = self
            .program
            .primitive_methods
            .get(&(class.to_string(), method.to_string()))?;
        let info = self.program.functions.get(symbol)?;
        let func = ReceiverCall::from_fun(info);
        Some(self.check_receiver_call(recv_ty, &func, method, args, span, scopes))
    }

    /// Shared core of a call whose first parameter is filled by the receiver:
    /// check argument count and types (the receiver against the first parameter,
    /// the call's arguments against the rest) and instantiate the body for the
    /// resolved argument tuple, returning the inferred result type.
    fn check_receiver_call(
        &mut self,
        recv_ty: &Type,
        func: &ReceiverCall,
        method: &str,
        args: &[Arg],
        span: prepoly_lexer::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        let signature_params = &func.signature_params;
        let fallback_ret = func
            .declared_ret
            .clone()
            .or_else(|| self.function_returns.get(&func.symbol).cloned())
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
        self.instantiate_function_call(
            &func.symbol,
            &func.module,
            signature_params,
            &func.decl.body,
            func.declared_ret.clone(),
            fallback_ret,
            &arg_types,
        )
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
                        // argument type is known.
                        self.verify_shape_constraints(param, &got, arg.expr.span());
                    } else {
                        self.check_expr(&arg.expr, scopes);
                    }
                }
                subst.resolve_deep(&ret)
            }
            // Calling a value of still-unknown type constrains it to a function:
            // unify it with `(arg types...) -> fresh_ret`. This is the application
            // rule for an inference variable, so `fun apply(f, x) { return f(x) }`
            // infers `f: (unknown) -> unknown` (and `apply` as
            // `((U) -> V, U) -> V`), letting a function argument type-check and
            // monomorphize instead of leaving `f` an uncallable unknown.
            callee @ Type::Unknown(_) => {
                let arg_types: Vec<Type> = args
                    .iter()
                    .map(|arg| self.check_expr(&arg.expr, scopes))
                    .collect();
                let ret = self.fresh_unknown();
                let fun_ty = Type::Fun(arg_types, Box::new(ret.clone()));
                let _ = self.solver.unify(&callee, &fun_ty);
                ret
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
        // `len` is a runtime primitive usable as a free
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
            // `open(path: string, mode: string) -> File!`.
            self.check_builtin_args_against("open", args, &[Type::Str, Type::Str], span, scopes);
            return Some(Type::result(self.type_by_name("File"), Type::Str));
        }
        None
    }

    /// Static contracts for the numeric runtime helpers. These
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
            // Integer width conversions: widening always succeeds;
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

    /// Minimal static contracts for the concurrency primitives.
    /// `spawn(f: () -> void) -> void` and `with(c, f) -> U` are the only
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
            // `_array_insert(arr, idx, elem)` / `_array_remove(arr, idx)` primitives: the slice's element type drives the index/element
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

    /// Type the builtin collection methods so their element types are enforced:
    /// `push(self: T[], value: T) -> void`,
    /// `pop(self: T[]) -> T?`, and `len(self) -> int64`. Element checking turns
    /// `[1].push("x")` into a static error.
    ///
    /// `push`/`pop` are slice-only: a fixed array `T[n]` has a statically fixed
    /// length (modeled as an inline `[n x T]`), so a
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
        // `ref(..)`/`mut(..)` are transparent wrappers, so a method on
        // `ref(mut(T[]))` reaches the same collection as one on `T[]`. Peeling
        // them lets `push`/`len`/... be recognised -- and lets `push` pin the
        // element variable to the pushed value -- through a reference.
        let base = peel_ref_mut(&resolved);
        let (elem, is_fixed) = match base {
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
                    self.expect_element_assignable(&got, elem, &arg.expr);
                }
                self.reject_extra_args(method, args, 1, scopes, span);
                Some(Type::Void)
            }
            ("pop", Some(elem)) => {
                args.iter().for_each(|arg| {
                    self.check_expr(&arg.expr, scopes);
                });
                Some(Type::Nullable(Box::new(elem.clone())))
            }
            // `arr.insert(idx, v)`: idx is int64, v is the element.
            ("insert", Some(elem)) => {
                if let Some(idx) = args.first() {
                    let got = self.check_expr(&idx.expr, scopes);
                    self.expect_expr_assignable(&got, &Type::Int(IntKind::I64), &idx.expr);
                }
                if let Some(value) = args.get(1) {
                    let got = self.check_expr(&value.expr, scopes);
                    self.expect_element_assignable(&got, elem, &value.expr);
                }
                self.reject_extra_args(method, args, 2, scopes, span);
                Some(Type::Void)
            }
            // `arr.remove(idx) -> T`: removes and returns the element.
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
            _ if method == "len" && matches!(base, Type::Str) => {
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
        // `T.from(v)`: a *fallible* structural conversion to record type `T`. The
        // result is `T?`: whether `v` actually has every field `T` declares is
        // decided per monomorphized argument type (the conversion yields the record
        // when the concrete argument has the fields, else null), so a missing field
        // is not a static error -- the caller narrows the nullable (an `if`/`if let`)
        // and handles the failure path.
        if method == "from" {
            let target = self
                .program
                .types
                .get(qualifier)
                .and_then(|info| match &info.kind {
                    TypeKind::Record { .. } => Some(info.type_ref()),
                    _ => None,
                });
            if let Some(ty) = target {
                if let Some(arg) = args.first() {
                    self.check_expr(&arg.expr, scopes);
                }
                return Type::Nullable(Box::new(ty));
            }
        }
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

    /// Constrain the source type of the numeric conversions:
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
            // Recursive call: re-checking the body again would not terminate, so
            // fall back to the declared/precomputed return type.
            tracing::debug!(symbol = %symbol, "recursive call, using fallback return type");
            return fallback_ret;
        }
        tracing::debug!(
            symbol = %symbol,
            args = ?arg_types.iter().map(|t| self.resolve(t).display()).collect::<Vec<_>>(),
            "re-elaborating function body at call site"
        );
        // Re-check the callee body in its own module so its internal names
        // resolve under that module's visibility, not the caller's.
        let saved_module = std::mem::replace(&mut self.current_module, module.to_vec());
        let frame = self.signature_call_frame(params, arg_types, None);
        let mut scopes = vec![frame.clone()];
        let full_ret = self.check_block_root(body, &mut scopes, declared_ret.as_ref());
        let ret = match declared_ret {
            Some(ret) => ret,
            None => self.prefer_full_return(full_ret, body, frame),
        };
        self.current_module = saved_module;
        self.instantiating.remove(&key);
        ret
    }

    /// Choose an inferred-return body's return type: the full check's
    /// reconciliation when it produced one and is not a `Result` (the full check
    /// observes the stores/pushes the light pass misses), otherwise the light
    /// `infer_return_from_frame`, which assembles a fallible body's `Result` from
    /// its error sites -- something the normal-return reconciliation does not do.
    fn prefer_full_return(
        &mut self,
        full_ret: Option<Type>,
        body: &Block,
        frame: HashMap<String, Type>,
    ) -> Type {
        let light = self.infer_return_from_frame(body, frame);
        match full_ret {
            Some(t) if !self.resolve(&light).is_result_type() => t,
            _ => light,
        }
    }

    /// Type a method call's result by instantiating the method's scheme against
    /// the receiver instance: the scheme expresses the return over the type's
    /// inferred parameters, and matching the scheme's field types to the
    /// receiver's resolved field substitution fixes them (`get`'s `-> V?` becomes
    /// `-> string?` for a `string`-valued map). Returns `None` when the receiver
    /// is not a scheme'd record, the method is not in the scheme, or the return
    /// still has an open parameter the instance did not pin (a parameter that only
    /// flows through `==`, never a store or field read) -- the caller then keeps
    /// the re-elaborated return.
    fn scheme_method_return(&self, recv_ty: &Type, method: &str) -> Option<Type> {
        let mut t = self.resolve(recv_ty);
        while let Type::Ref(i) | Type::Mut(i) | Type::ConstOf(i) | Type::Nullable(i) = t {
            t = *i;
        }
        let Type::Record(nominal) = t else {
            return None;
        };
        let info = self.program.type_by_id(nominal.id)?;
        let scheme = self.schemes.get(&info.name)?;
        let scheme_method = scheme.methods.get(method)?;
        let map = scheme_instance_map(scheme, &nominal);
        let ret = apply_scheme_param_map(&scheme_method.ret, &map);
        // Only adopt the instantiated return when it is fully resolved; an open
        // variable means the instance did not constrain it, so the re-elaborated
        // return (which can still defer) is the safer choice.
        self.solver.free_vars(&ret).is_empty().then_some(ret)
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
        // Re-check the method body in its defining type's module.
        let owner_type = self_type.to_string();
        let saved_module =
            self.swap_module_for(|p| p.types.get(&owner_type).map(|t| t.module.clone()));
        let frame = self.signature_call_frame(signature_params, arg_types, receiver_ty);
        let full_ret = if let Some(body) = &method.body {
            let mut scopes = vec![frame.clone()];
            self.check_block_root(body, &mut scopes, declared_ret.as_ref())
        } else {
            None
        };
        let ret = match (&method.body, declared_ret) {
            (_, Some(ret)) => ret,
            (Some(body), None) => self.prefer_full_return(full_ret, body, frame),
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
            // A method called with the receiver passed separately (`receiver_ty`)
            // binds `self` to it and does not consume an argument slot. A
            // primitive/array method (`fun infer[].slice`) is instead instantiated
            // like a function: its receiver is `arg_types[0]`, aligned with the
            // `self` parameter, so `self` is handled by the ordinary positional
            // branch below (instantiating its `infer[]` annotation against the
            // receiver and advancing `arg_idx`).
            let ty = if param.name == "self" && receiver_ty.is_some() {
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
        // Match against the actual value type, looking through `const`/`mut`/`ref`
        // wrappers (an argument's mutability/reference does not change which
        // element type a generic parameter is instantiated with).
        let actual = peel_value_wrappers(&self.resolve(actual)).clone();
        match (self.resolve(annotated), actual) {
            // A bare `infer` parameter takes the argument's type.
            (Type::Unknown(_), have) => have,
            // A generic container parameter (`infer[]`, `infer[]?`, ...) is
            // instantiated element-wise, so e.g. `slice(arr: infer[])` applied to
            // an `int32[]` returns an `int32[]` rather than an unconstrained `?[]`.
            (Type::Slice(want), Type::Slice(have) | Type::Array(have, _)) => {
                Type::Slice(Box::new(self.instantiate_annotated_type(&want, &have)))
            }
            (Type::Array(want, n), Type::Array(have, _) | Type::Slice(have)) => {
                Type::Array(Box::new(self.instantiate_annotated_type(&want, &have)), n)
            }
            (Type::Nullable(want), Type::Nullable(have)) => {
                Type::Nullable(Box::new(self.instantiate_annotated_type(&want, &have)))
            }
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

    /// Move the body errors a foreign method produced (when re-elaborated for a
    /// call) onto the call site `span`, framed as a receiver/argument mismatch, so
    /// they are reported where the user wrote the call rather than at an
    /// unreachable span inside the stdlib. Identical re-pointed errors are
    /// deduplicated, since one inconsistency can surface at several body sites.
    fn reattribute_errors_to_call(
        &mut self,
        before: usize,
        method: &str,
        span: prepoly_lexer::Span,
    ) {
        let mut seen: HashSet<String> = HashSet::new();
        let kept: Vec<TypeError> = self
            .errors
            .split_off(before)
            .into_iter()
            .filter_map(|e| {
                let message = format!(
                    "call to `{method}` here does not match the receiver's type: {}",
                    e.message
                );
                seen.insert(message.clone())
                    .then_some(TypeError { message, span })
            })
            .collect();
        self.errors.extend(kept);
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
        // See through reference/mutability wrappers: an operand read through a
        // reference (e.g. a `ref(mut(int32))` array element bound by a `for` loop)
        // operates on its underlying value, and the operator yields that value type.
        let left = peel_ref_mut(&self.resolve(left)).clone();
        let right = peel_ref_mut(&self.resolve(right)).clone();
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
        // Numeric arithmetic/comparison between mixed types implicitly converts
        // both operands to their common type.
        let is_unknown = matches!(left, Type::Unknown(_)) || matches!(right, Type::Unknown(_));
        let numeric_common = common_numeric_type(&left, &right);
        match op {
            BinOp::Add if matches!((&left, &right), (Type::Str, Type::Str)) => Type::Str,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                if is_unknown {
                    // One operand is still an open inference variable. The result
                    // takes the *other* operand's numeric type when it is a known
                    // number, so a value flowing only through `x + 1` is concretely
                    // typed (a count read back as `int32`) and a store of it pins
                    // the destination. The open variable itself is not committed
                    // here -- a concrete re-elaboration may make it `float64` -- so
                    // numeric polymorphism is preserved.
                    match (&left, &right) {
                        (Type::Unknown(_), Type::Int(_) | Type::Float(_)) => right.clone(),
                        (Type::Int(_) | Type::Float(_), Type::Unknown(_)) => left.clone(),
                        _ => self.fresh_unknown(),
                    }
                } else if let Some(t) = numeric_common {
                    t
                } else {
                    self.binary_error(op, &left, &right, span)
                }
            }
            // Remainder is integer-only (the widths may still differ).
            BinOp::Rem => {
                if is_unknown {
                    self.fresh_unknown()
                } else if let Some(t @ Type::Int(_)) = numeric_common {
                    t
                } else {
                    self.binary_error(op, &left, &right, span)
                }
            }
            BinOp::Eq | BinOp::Ne => {
                if numeric_common.is_some()
                    || self.can_unify(&left, &right)
                    || matches!(left, Type::Never)
                    || matches!(right, Type::Never)
                {
                    Type::Bool
                } else {
                    self.binary_error(op, &left, &right, span)
                }
            }
            // Ordering comparisons are numeric only. Strings have
            // no ordering: `==`/`!=` compare them, but `<`/`>`/`<=`/`>=` do not.
            BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                if numeric_common.is_some() || is_unknown {
                    Type::Bool
                } else {
                    self.binary_error(op, &left, &right, span)
                }
            }
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
                "operator `{}` is not defined for `{}` and `{}` (no applicable conversion)",
                op_str(op),
                left.display(),
                right.display()
            ),
            span,
        });
        self.fresh_unknown()
    }

    /// The element type bound by a `for` loop over `iter_ty`, seeing through
    /// reference/mutability wrappers and re-applying them to the element (over a
    /// `ref(mut(T[]))` each element is a `ref(mut(T))`). An as-yet-unconstrained
    /// iterand (possibly under wrappers) is constrained to a slice. `None` when the
    /// iterand is not a sequence.
    fn for_element(&mut self, iter_ty: &Type) -> Option<Type> {
        match self.resolve(iter_ty) {
            Type::Slice(e) | Type::Array(e, _) => Some(*e),
            Type::Ref(inner) => self.for_element(&inner).map(|e| Type::Ref(Box::new(e))),
            Type::Mut(inner) => self.for_element(&inner).map(|e| Type::Mut(Box::new(e))),
            Type::ConstOf(inner) => self.for_element(&inner).map(|e| Type::ConstOf(Box::new(e))),
            resolved @ Type::Unknown(_) => {
                let elem = self.fresh_unknown();
                let _ = self
                    .solver
                    .unify(&resolved, &Type::Slice(Box::new(elem.clone())));
                Some(elem)
            }
            _ => None,
        }
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
        // unification: a bare empty array carries no
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
            && (self.can_unify(&got, inner)
                || numeric_flows_into(&got, &self.resolve(inner))
                || matches!(got, Type::Never))
        {
            return;
        }
        if self.can_unify(&got, &want)
            || crate::structural::types_compatible(self.program, &got, &want)
        {
            return;
        }
        // Automatic numeric conversion: a numeric value flows into a numeric
        // position of another type (int widths/signedness, int -> float); the
        // back ends convert at the flow point. float -> int stays explicit.
        if numeric_flows_into(&got, &want) {
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

    /// Check a value pushed/inserted into a slice against its element type. Unlike
    /// the bidirectional `expect_assignable` (whose reverse structural check the
    /// per-call hm pass re-gates for ordinary flow positions, but not for slice
    /// methods), this is one-directional: the value must be usable *as* the
    /// element, so a structural supertype is rejected and cannot corrupt the
    /// unboxed element layout. When the element type is still an open inference
    /// variable it is pinned to the value through `solver.unify`, so the occurs
    /// check fires -- pushing an array into itself (`a.push(a)`) is reported here
    /// instead of leaving the element unbound to be mistyped at the call site.
    fn expect_element_assignable(&mut self, got: &Type, elem: &Type, expr: &Expr) {
        let got = self.resolve(got);
        let want = self.resolve(elem);
        if integer_literal_fits(expr, &want) {
            return;
        }
        // The element type carries an open inference variable -- either it is one
        // (a fresh `?[]`) or it is a record/array with open components (an
        // `_Entry<?, ?>` element whose key/value are not yet fixed). Pin it to the
        // value by committing the unification, so the stored value's concrete type
        // refines the element through the solver's record/array unification.
        if !self.solver.free_vars(&want).is_empty() {
            // Pushing/storing `null` into a still-open element makes the element a
            // *nullable with an open inner* (`Nullable(?)`), rather than collapsing
            // it to `Nullable(Never)`. This is what lets a slot array seeded with
            // `null` (`entries.push(null)`) still take its element type from the
            // non-null values stored later: the open inner is refined below.
            if got.is_null() && matches!(want, Type::Unknown(_)) {
                let inner = self.fresh_unknown();
                let _ = self.solver.unify(elem, &Type::Nullable(Box::new(inner)));
                return;
            }
            // A non-null value stored into a nullable element refines the element's
            // *inner* type (a concrete `_Entry<K, V>` into a `_Entry?[]` slot pins
            // `K` and `V`), so a nullable container fixes its element from the
            // values inserted while still accepting `null`. Otherwise the value
            // refines the element directly.
            let outcome = match &want {
                Type::Nullable(inner) if !got.is_null() && !matches!(got, Type::Nullable(_)) => {
                    self.solver.unify(inner, &got)
                }
                _ => self.solver.unify(elem, &got),
            };
            if outcome.is_err() && want.is_unknown() {
                // The only hard failure on a *bare* element variable is the occurs
                // check: pushing the array into itself, an infinite element type.
                self.errors.push(TypeError {
                    message: "cannot push a value whose type contains this array; \
                              the element type would be infinite"
                        .to_string(),
                    span: expr.span(),
                });
            }
            // A failure against a *partially* fixed element (a record/array with
            // open components) is left to defer rather than reported: the store may
            // go through a witness alias the body itself re-reads (the table's
            // `_grow` re-inserts `old_entries[0]`), which is loose by construction.
            // A genuine clash on a fully concrete element is caught by the concrete
            // path below, which still runs because such an element has no free var.
            return;
        }
        if got.is_null() && !matches!(want, Type::Nullable(_)) {
            self.report_element_mismatch(&got, &want, expr.span());
            return;
        }
        if matches!(got, Type::Nullable(_)) && !matches!(want, Type::Nullable(_)) {
            self.report_nullable_use(expr.span());
            return;
        }
        if let Type::Nullable(inner) = &want
            && (self.assignable_into(&got, inner) || matches!(got, Type::Never))
        {
            return;
        }
        if self.assignable_into(&got, &want) {
            return;
        }
        self.report_element_mismatch(&got, &want, expr.span());
    }

    /// One-directional assignability: whether `got` is usable where `want` is
    /// required, by inference-variable unification or structural subtyping, and
    /// without the reverse structural check `can_unify` adds.
    fn assignable_into(&self, got: &Type, want: &Type) -> bool {
        Subst::new().unify(got, want).is_ok()
            || crate::structural::types_compatible(self.program, got, want)
    }

    fn report_element_mismatch(&mut self, got: &Type, want: &Type, span: prepoly_lexer::Span) {
        self.errors.push(TypeError {
            message: format!(
                "cannot use `{}` where `{}` is required",
                got.display(),
                want.display()
            ),
            span,
        });
    }

    /// Report (and still type-check, to surface their own errors) arguments beyond
    /// the fixed arity of a builtin slice mutator, so `a.push(x, y)` is rejected
    /// rather than silently dropping `y` -- which previously let `a.push(a, 2)`
    /// parse as a self-push.
    fn reject_extra_args(
        &mut self,
        method: &str,
        args: &[Arg],
        arity: usize,
        scopes: &mut ScopeStack,
        span: prepoly_lexer::Span,
    ) {
        for arg in args.iter().skip(arity) {
            self.check_expr(&arg.expr, scopes);
        }
        if args.len() > arity {
            self.errors.push(TypeError {
                message: format!(
                    "method `{method}` takes {arity} argument(s), found {}",
                    args.len()
                ),
                span,
            });
        }
    }

    /// Resolve a type through the persistent substitution, following solved
    /// inference variables (including nested ones). The substitution is only
    /// populated where the checker pins a variable across uses (e.g. an empty
    /// array's element type after the first `push`), so an unconstrained type is
    /// returned structurally unchanged.
    fn resolve(&self, ty: &Type) -> Type {
        self.solver.resolve(ty)
    }

    /// If a bracket literal's elements describe a tuple, return their types; else
    /// `None` (an array). Mirrors `hm::tuple_of_elements`: a rolled-back probe over
    /// each element's representative type (a numeric literal stands in as its
    /// default kind, not its open variable) decides array-vs-tuple, and a tuple
    /// returns the elements' actual types so an annotation can still fix widths.
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
            .map(|(e, t)| numeric_literal_repr(e).unwrap_or_else(|| self.resolve(t)))
            .collect();
        let (first, rest) = reps.split_first()?;
        let snap = self.solver.snapshot();
        let unifiable = rest.iter().all(|t| self.solver.unify(first, t).is_ok());
        self.solver.rollback(snap);
        if unifiable {
            None
        } else {
            Some(elem_tys.iter().map(|t| self.resolve(t)).collect())
        }
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
                tracing::debug!(name, to = %inner.display(), "narrowing nullable to non-null");
                scope.insert(name.to_string(), *inner);
                break;
            }
        }
    }

    fn bind_pattern(&mut self, pat: &Pattern, ty: &Type, scopes: &mut ScopeStack) {
        match pat {
            Pattern::Binding(name, span) => {
                if !self.is_unit_variant_name(name) {
                    scopes.last_mut().unwrap().insert(name.clone(), ty.clone());
                    self.record_binding(name, *span, ty);
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
                        self.record_binding(&fp.name, fp.span, &fty);
                        scopes.last_mut().unwrap().insert(fp.name.clone(), fty);
                    }
                }
            }
            Pattern::Array(pats, _) => {
                if let Type::Tuple(elems) = self.resolve(ty) {
                    // Tuple destructuring binds each position to its element type.
                    for (p, ety) in pats.iter().zip(elems) {
                        self.bind_pattern(p, &ety, scopes);
                    }
                } else {
                    let elem = match self.resolve(ty) {
                        Type::Array(inner, _) | Type::Slice(inner) => *inner,
                        _ => self.fresh_unknown(),
                    };
                    pats.iter()
                        .for_each(|p| self.bind_pattern(p, &elem, scopes));
                }
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
                // A tuple pattern checks each position against its element type and
                // must have exactly the tuple's arity.
                if let Type::Tuple(elems) = self.resolve(scrutinee) {
                    if pats.len() != elems.len() {
                        self.errors.push(TypeError {
                            message: format!(
                                "tuple pattern has length {}, but the tuple has {} elements",
                                pats.len(),
                                elems.len()
                            ),
                            span: pat.span(),
                        });
                    }
                    for (pat, ety) in pats.iter().zip(&elems) {
                        self.check_pattern_against(ety, pat);
                    }
                    return;
                }
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
                // modules share a type name.
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
    /// checked: defined in that module, implicitly imported as
    /// part of the standard-library prelude, or brought in by an `import`.
    fn is_function_visible(&self, name: &str) -> bool {
        self.lookup_function(name).is_some()
    }

    /// Resolve a bare free-function name to its definition from the current
    /// module. A name defined in a single module keeps
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
    /// public standard-library name (implicit prelude), or
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

    /// Record an equality constraint for an unknown operand when the operator
    /// needs an exact non-convertible type. Numeric operands are resolved at the
    /// call site through the common numeric type, so this mainly preserves
    /// constraints such as string concatenation.
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
    /// current module: own/unique, this module's qualified
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
/// instance.
/// The value of a constant non-negative integer index (a tuple position), or
/// `None` if the index is not a literal.
fn const_index(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Int(n, _) if *n >= 0 => Some(*n),
        _ => None,
    }
}

/// The default concrete type of a numeric literal element, for classifying a
/// bracket literal as array vs tuple (an int literal is `int32`, a float `float64`).
fn numeric_literal_repr(e: &Expr) -> Option<Type> {
    match e {
        Expr::Int(v, _) => Some(Type::Int(int_literal_kind(*v))),
        Expr::Float(_, _) => Some(Type::Float(FloatKind::F64)),
        _ => None,
    }
}

fn is_concrete_type(ty: &Type) -> bool {
    match ty {
        Type::Unknown(_) | Type::Never | Type::SelfType => false,
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Nullable(inner)
        | Type::ConstOf(inner)
        | Type::Mut(inner)
        | Type::Ref(inner) => is_concrete_type(inner),
        Type::Fun(params, ret) => params.iter().all(is_concrete_type) && is_concrete_type(ret),
        Type::Tuple(elems) => elems.iter().all(is_concrete_type),
        _ => true,
    }
}

/// Peel the transparent reference wrappers `ref(..)`/`mut(..)` to reach the
/// underlying value type, for receiver-kind dispatch.
fn peel_ref_mut(ty: &Type) -> &Type {
    match ty {
        Type::Ref(inner) | Type::Mut(inner) => peel_ref_mut(inner),
        other => other,
    }
}

/// Peel `const`/`mut`/`ref` value wrappers to reach the underlying value type.
fn peel_value_wrappers(ty: &Type) -> &Type {
    match ty {
        Type::ConstOf(inner) | Type::Mut(inner) | Type::Ref(inner) => peel_value_wrappers(inner),
        other => other,
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
    // See through a nullable cell and the reference/mutability wrappers: assigning
    // an integer literal to a `ref(mut(int32))` element (an array index through a
    // mutable reference) targets the underlying `int32`.
    fn int_kind(t: &Type) -> Option<IntKind> {
        match t {
            Type::Int(kind) => Some(*kind),
            Type::Nullable(inner) | Type::Ref(inner) | Type::Mut(inner) | Type::ConstOf(inner) => {
                int_kind(inner)
            }
            _ => None,
        }
    }
    match (expr, int_kind(want)) {
        (Expr::Int(value, _), Some(kind)) => int_fits_kind(*value, kind),
        _ => false,
    }
}

fn literal_pattern_type(expr: &Expr) -> Option<Type> {
    match expr {
        Expr::Int(v, _) => Some(Type::Int(int_literal_kind(*v))),
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
        | Type::ConstOf(inner)
        | Type::Mut(inner)
        | Type::Ref(inner) => visit_unknowns(inner, record),
        Type::Fun(params, ret) => {
            params
                .iter()
                .for_each(|param| visit_unknowns(param, record));
            visit_unknowns(ret, record);
        }
        Type::Tuple(elems) => elems.iter().for_each(|t| visit_unknowns(t, record)),
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

/// Map each scheme parameter to the receiver instance's concrete type by matching
/// the scheme's field types against the receiver's resolved field substitution
/// (`entries : _Entry<K, V>[]` vs `entries : _Entry<string, string>[]` gives `K
/// -> string`, `V -> string`). Used to instantiate a method's scheme at a call.
fn scheme_instance_map(scheme: &TypeScheme, recv: &NominalType) -> HashMap<u32, Type> {
    let mut map = HashMap::new();
    for (fname, fty) in &scheme.fields {
        if let Some(actual) = recv.substitution.get(fname) {
            match_scheme_param(fty, actual, &scheme.params, &mut map);
        }
    }
    map
}

/// Record `param -> actual` where a scheme parameter variable aligns with a
/// concrete position in the receiver's field type, recursing structurally.
fn match_scheme_param(
    scheme_ty: &Type,
    actual: &Type,
    params: &[u32],
    map: &mut HashMap<u32, Type>,
) {
    match (scheme_ty, actual) {
        (Type::Unknown(id), a) if params.contains(id) => {
            map.entry(*id).or_insert_with(|| a.clone());
        }
        (Type::Slice(s), Type::Slice(a))
        | (Type::Slice(s), Type::Array(a, _))
        | (Type::Array(s, _), Type::Slice(a))
        | (Type::Array(s, _), Type::Array(a, _))
        | (Type::Nullable(s), Type::Nullable(a))
        | (Type::Ref(s), Type::Ref(a))
        | (Type::Mut(s), Type::Mut(a))
        | (Type::ConstOf(s), Type::ConstOf(a)) => match_scheme_param(s, a, params, map),
        (Type::Record(sn), Type::Record(an)) | (Type::Sum(sn), Type::Sum(an)) => {
            for (k, sv) in sn.substitution.iter() {
                if let Some(av) = an.substitution.get(k) {
                    match_scheme_param(sv, av, params, map);
                }
            }
        }
        _ => {}
    }
}

/// Substitute scheme parameters with their concrete types throughout a type.
fn apply_scheme_param_map(ty: &Type, map: &HashMap<u32, Type>) -> Type {
    match ty {
        Type::Unknown(id) => map.get(id).cloned().unwrap_or_else(|| ty.clone()),
        Type::Slice(e) => Type::Slice(Box::new(apply_scheme_param_map(e, map))),
        Type::Array(e, n) => Type::Array(Box::new(apply_scheme_param_map(e, map)), *n),
        Type::Nullable(e) => Type::Nullable(Box::new(apply_scheme_param_map(e, map))),
        Type::Ref(e) => Type::Ref(Box::new(apply_scheme_param_map(e, map))),
        Type::Mut(e) => Type::Mut(Box::new(apply_scheme_param_map(e, map))),
        Type::ConstOf(e) => Type::ConstOf(Box::new(apply_scheme_param_map(e, map))),
        Type::Fun(ps, r) => Type::Fun(
            ps.iter().map(|p| apply_scheme_param_map(p, map)).collect(),
            Box::new(apply_scheme_param_map(r, map)),
        ),
        Type::Tuple(es) => Type::Tuple(es.iter().map(|e| apply_scheme_param_map(e, map)).collect()),
        Type::Record(n) => Type::Record(map_scheme_nominal(n, map)),
        Type::Sum(n) => Type::Sum(map_scheme_nominal(n, map)),
        other => other.clone(),
    }
}

fn map_scheme_nominal(n: &NominalType, map: &HashMap<u32, Type>) -> NominalType {
    let mut subst = Substitution::empty();
    for (k, v) in n.substitution.iter() {
        subst.insert(k, apply_scheme_param_map(v, map));
    }
    NominalType::with_substitution(n.id, n.name().to_string(), subst)
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

/// Replace every `Type::SelfType` in `ty` with `replacement` (the concrete type
/// `Self` denotes), recursing through composite types. Lets a field or parameter
/// type written with `Self` -- e.g. a closure-typed field `(self, T) -> U` -- be
/// checked against the actual type when a value of that type is constructed.
fn substitute_self(ty: &Type, replacement: &Type) -> Type {
    let rec = |t: &Type| substitute_self(t, replacement);
    match ty {
        Type::SelfType => replacement.clone(),
        Type::Array(e, n) => Type::Array(Box::new(rec(e)), *n),
        Type::Slice(e) => Type::Slice(Box::new(rec(e))),
        Type::Tuple(es) => Type::Tuple(es.iter().map(rec).collect()),
        Type::Fun(ps, r) => Type::Fun(ps.iter().map(rec).collect(), Box::new(rec(r))),
        Type::Nullable(e) => Type::Nullable(Box::new(rec(e))),
        Type::ConstOf(e) => Type::ConstOf(Box::new(rec(e))),
        Type::Mut(e) => Type::Mut(Box::new(rec(e))),
        Type::Ref(e) => Type::Ref(Box::new(rec(e))),
        other => other.clone(),
    }
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
/// optional at call sites: each omitted argument defaults to `null`. This is how `assert(cond, msg: string?)` accepts both `assert(cond)` and
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
