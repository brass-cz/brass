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

mod assign;
mod builtins;
mod instantiate;
mod light;

use assign::{common_nullable_type, integer_literal_fits};
use builtins::primitive_static_return;

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
        checker.narrowed_bindings.clear();
        checker.closure_write_targets = init
            .stmts
            .iter()
            .flat_map(|s| {
                let mut acc = HashSet::new();
                collect_closure_writes_stmt(s, false, &mut acc);
                acc
            })
            .collect();
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
    /// Bindings narrowed non-null in the current callable, with their original
    /// nullable types. A call can re-null a narrowed GLOBAL (any callee may
    /// write it) or a narrowed local ASSIGNED INSIDE A CLOSURE of this body (a
    /// closure value may run during the call), so those narrowings are undone
    /// after every call (`invalidate_narrowed_after_call`). Plain locals are
    /// unaffected: no callee can rebind them.
    narrowed_bindings: Vec<(String, Type)>,
    /// Names assigned anywhere inside a closure literal of the callable body
    /// currently being checked; see `narrowed_bindings`.
    closure_write_targets: HashSet<String>,
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
            narrowed_bindings: Vec::new(),
            closure_write_targets: HashSet::new(),
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

    fn primitive_static_type(&self, tname: &str, method: &str) -> Option<Type> {
        if matches!((tname, method), ("File", "stdin" | "stdout" | "stderr")) {
            return Some(self.type_by_name("File"));
        }
        primitive_static_return(tname, method)
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
        let saved_narrowed = std::mem::take(&mut self.narrowed_bindings);
        let saved_closure_writes = std::mem::replace(
            &mut self.closure_write_targets,
            closure_write_targets_block(b),
        );
        self.return_contexts.push(match ret {
            Some(ty) => ReturnContext::Explicit(ty.clone()),
            None => ReturnContext::Inferred,
        });
        self.return_values.push(Vec::new());
        self.check_block(b, scopes);
        let collected = self.return_values.pop().unwrap_or_default();
        self.return_contexts.pop();
        self.closure_write_targets = saved_closure_writes;
        self.narrowed_bindings = saved_narrowed;
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
                // Binding a NAME to a `void` value is a mistake with no
                // representable value behind it -- classically a block-bodied
                // closure that forgot `return`, whose call site would otherwise
                // fail much later with an opaque unsupported-construct error.
                // A wildcard (`let _ = f()`) still discards a void result.
                if let Pattern::Binding(name, span) = pat
                    && matches!(self.resolve(&binding_ty), Type::Void)
                {
                    self.errors.push(TypeError {
                        message: format!(
                            "cannot bind `{name}` to a `void` value (a block-bodied \
                             closure or function returns `void` without an explicit \
                             `return`)"
                        ),
                        span: *span,
                    });
                }
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
                let body_val = self.check_expr(body, &mut closure_scopes);
                let collected = self.return_values.pop().unwrap_or_default();
                self.return_contexts.pop();
                self.const_scopes.pop();
                // A BLOCK body yields only what it `return`s (void without one),
                // matching the back ends -- its trailing expression is not the
                // value. Any other body form is a single expression whose value
                // is the implicit return. (Previously inverted on both counts:
                // the trailing expression typed a block closure's result and an
                // explicit `return` typed it void.)
                let ret = if matches!(&**body, Expr::Block(..)) {
                    self.reconcile_return_types(&collected, false)
                        .unwrap_or(Type::Void)
                } else {
                    body_val
                };
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
                // when the condition is a field access whose then-branch does not
                // type for this concrete value (a present field whose type the
                // branch's `return` cannot produce; a missing field is already
                // `never?` and statically false above), the `if` folds to
                // statically false rather than a type error. The fold must mirror
                // the back end EXACTLY: the back end prunes an arm only when its
                // unconditionally-reached `return` value kind-conflicts with the
                // function's return type (`then_return_conflicts` in the engine).
                // Folding on any other branch error would discard diagnostics for
                // an arm the back end still emits and executes -- a type-check
                // bypass straight into the unboxed code.
                if truth != Some(false) && matches!(&**cond, Expr::Field(..)) {
                    let mark = self.errors.len();
                    let mut probe = scopes.clone();
                    self.apply_truthy_narrowing(cond, &mut probe);
                    // Isolate the probe's collected returns: they describe the
                    // (possibly dead) arm, not the enclosing callable, and the
                    // real walk below re-collects the live ones.
                    self.return_values.push(Vec::new());
                    self.check_branch(then, &mut probe, false);
                    let probe_returns = self.return_values.pop().unwrap_or_default();
                    let failed = self.errors.len() > mark;
                    self.errors.truncate(mark);
                    if failed && self.then_branch_return_conflicts(then, &probe_returns) {
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

    /// AST mirror of the back end's `then_return_conflicts` (engine `mono`): the
    /// then-branch reaches a `return <value>` through straight-line statements
    /// only (any branching construct becomes a MIR `CondBranch`, which the back
    /// end does not fold through), and the returned value's primitive kind
    /// clearly conflicts with the enclosing declared return type (its Ok payload
    /// for a fallible signature). Only such arms are pruned by the back end, so
    /// only such arms may the checker fold; anything looser would tolerate an
    /// arm that still executes.
    fn then_branch_return_conflicts(
        &mut self,
        then: &Block,
        probe_returns: &[(Type, prepoly_lexer::Span)],
    ) -> bool {
        let Some(ReturnContext::Explicit(want)) = self.return_contexts.last().cloned() else {
            return false;
        };
        let resolved_want = self.resolve(&want);
        let target = match resolved_want.result_payloads() {
            Some((ok, _)) => ok.clone(),
            None => resolved_want,
        };
        let mut ret_span = None;
        for stmt in &then.stmts {
            match stmt {
                Stmt::Return(Some(value), span) => {
                    if expr_may_branch(value) {
                        return false;
                    }
                    ret_span = Some(*span);
                    break;
                }
                Stmt::Return(None, _) => return false,
                s if stmt_may_branch(s) => return false,
                _ => {}
            }
        }
        let Some(span) = ret_span else {
            return false;
        };
        let Some((ty, _)) = probe_returns.iter().find(|(_, s)| *s == span) else {
            return false;
        };
        let ty = self.resolve(ty);
        // A returned `Result` flows whole rather than as the Ok payload; the
        // back end never folds on it.
        if ty.is_result_type() {
            return false;
        }
        prepoly_hir::primitive_kind_conflict(&ty, &target)
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
                match prepoly_hir::peel_modes(&resolved).clone() {
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
                    // A string is immutable and not element-addressable storage;
                    // it is indexable in read position, but never a valid store
                    // target (the unboxed back end has no cell to write).
                    Type::Str => {
                        self.errors.push(TypeError {
                            message: "cannot assign through a string index; strings are immutable"
                                .to_string(),
                            span: *span,
                        });
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
                        // A bare unannotated field's declared variable is SHARED
                        // by every use of the declaration -- method co-checking
                        // deliberately binds through it (the scheme links the
                        // type and its methods). A literal must not check its
                        // value against whatever that co-checking bound (the
                        // binding mixes another body's local variables in), so
                        // each literal checks against a fresh variable and
                        // records the value's own type in the substitution
                        // below. Partially-inferred annotations (an `infer?[]`
                        // slot) keep the shared variable: the store-pin
                        // machinery relies on it.
                        let want = if want.is_unknown() {
                            self.fresh_unknown()
                        } else {
                            want
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
        // A `ref`/`mut`/`const` view exposes the underlying value's members, so
        // the lookup peels the mode wrappers; otherwise a `ref(mut(T))` base
        // would fall to the permissive arm and skip field type checking.
        let resolved = self.resolve(&base_ty);
        match prepoly_hir::peel_modes(&resolved).clone() {
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
                let ret = self.check_callable_value(local, args, span, scopes);
                self.invalidate_narrowed_after_call(scopes);
                return ret;
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
                let ret = self.instantiate_function_call(
                    &symbol,
                    &module,
                    &signature_params,
                    &decl.body,
                    declared_ret,
                    fallback_ret,
                    &arg_types,
                );
                // User code ran conceptually: a narrowed global (or a local a
                // closure of this body assigns) may have been re-nulled.
                self.invalidate_narrowed_after_call(scopes);
                return ret;
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
                let ret = self.check_static_call(&qualifier, method, args, span, scopes);
                self.invalidate_narrowed_after_call(scopes);
                return ret;
            }
            let recv_ty = self.check_expr(base, scopes);
            if let Type::Nullable(_) = self.resolve(&recv_ty) {
                self.report_nullable_use(base.span());
            }
            if let Some(ret) = self.builtin_method_type(&recv_ty, method, args, scopes, span) {
                return ret;
            }
            if let Some(methods) = self.methods_for_type(&recv_ty, method) {
                return self
                    .check_methods_call(methods, &recv_ty, method, args, span, None, scopes);
            }
            // A stdlib method on a primitive/array receiver (`fun string.split`,
            // `fun infer[].map`): dispatched by the receiver's class. There is no
            // UFCS fallback -- a free function is not callable through `recv.f()`.
            if let Some(ret) =
                self.check_primitive_method_call(&recv_ty, method, args, span, scopes)
            {
                // Stdlib primitive methods are user-defined prepoly code.
                self.invalidate_narrowed_after_call(scopes);
                return ret;
            }
            // The missing-method diagnostics below look through mode wrappers so
            // a `ref(mut(T))` receiver reports against `T` instead of deferring.
            let peeled_recv = prepoly_hir::peel_modes(&self.resolve(&recv_ty)).clone();
            if let Type::Record(record) = &peeled_recv {
                // A function-typed FIELD is callable through the same syntax (a
                // method of the same name takes precedence, resolved above):
                // `a.func(4)` calls the closure the field holds.
                if let Some(fty) = self.field_value_type(record, method) {
                    let resolved = self.resolve(&fty);
                    if matches!(resolved, Type::Fun(..) | Type::Unknown(_)) {
                        self.record_expr_type(callee, &fty);
                        let ret = self.apply_callable(fty, args, span, scopes);
                        self.invalidate_narrowed_after_call(scopes);
                        return ret;
                    }
                    self.errors.push(TypeError {
                        message: format!(
                            "field `{method}` of `{record}` has type `{}` and is not callable",
                            resolved.display()
                        ),
                        span,
                    });
                    for a in args {
                        self.check_expr(&a.expr, scopes);
                    }
                    return self.fresh_unknown();
                }
                // A STRUCTURAL (anonymous) receiver resolves a method by
                // satisfaction: the unique in-scope record type declaring the
                // method whose fields the value provides dispatches without an
                // annotation. Several satisfied candidates are ambiguous, and a
                // near-miss (the method exists but the value lacks a field) is
                // reported AT THE VALUE with the missing constraint -- the
                // callee's requirements are known here.
                if record.id == prepoly_hir::STRUCTURAL_RECORD_ID {
                    let candidates = self.structural_method_candidates(record, method);
                    match candidates.as_slice() {
                        [(_, symbol)] => {
                            let nominal = self
                                .program
                                .types
                                .get(symbol)
                                .map(|info| info.type_ref())
                                .unwrap_or_else(|| Type::Record(record.clone()));
                            if let Some(methods) = self.methods_for_type(&nominal, method) {
                                let methods = methods
                                    .into_iter()
                                    .map(|m| {
                                        apply_method_substitution(m, &record.substitution, method)
                                    })
                                    .collect();
                                return self.check_methods_call(
                                    methods,
                                    &recv_ty,
                                    method,
                                    args,
                                    span,
                                    Some(base.span()),
                                    scopes,
                                );
                            }
                        }
                        [] => {
                            // Name a near-miss when one exists: which in-scope
                            // type declares the method, and which fields the
                            // value is missing for it.
                            if let Some(msg) = self.structural_near_miss(record, method) {
                                self.errors.push(TypeError {
                                    message: msg,
                                    span: base.span(),
                                });
                                for a in args {
                                    self.check_expr(&a.expr, scopes);
                                }
                                return self.fresh_unknown();
                            }
                        }
                        many => {
                            let names: Vec<&str> = many.iter().map(|(n, _)| n.as_str()).collect();
                            self.errors.push(TypeError {
                                message: format!(
                                    "ambiguous method call: the anonymous structure \
                                     satisfies `{}`, which all declare `{method}`; \
                                     annotate the value with one of them",
                                    names.join("`, `")
                                ),
                                span: base.span(),
                            });
                            for a in args {
                                self.check_expr(&a.expr, scopes);
                            }
                            return self.fresh_unknown();
                        }
                    }
                }
                self.errors.push(TypeError {
                    message: format!("`{record}` has no method `{method}`"),
                    span,
                });
                for a in args {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
            if let Type::Sum(sum) = &peeled_recv {
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
            let resolved = peeled_recv;
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
        let ret = self.apply_callable(callee_ty, args, span, scopes);
        self.invalidate_narrowed_after_call(scopes);
        ret
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
        // Mode wrappers are peeled so a `ref(string)` / `mut(T[])` receiver still
        // dispatches to the stdlib primitive method of the underlying class.
        let class = prepoly_hir::peel_modes(&self.resolve(recv_ty)).primitive_class()?;
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
    /// Type a resolved method call (the shared tail of nominal and structural
    /// method resolution): check the signature/arity/arguments, re-elaborate
    /// each candidate body, and produce the call's result type. Body errors are
    /// re-attributed to `reattribute_to` when given (a structural receiver's
    /// value span), else to the call site for a foreign-module method.
    #[allow(clippy::too_many_arguments)]
    fn check_methods_call(
        &mut self,
        methods: Vec<ResolvedMethod>,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        span: prepoly_lexer::Span,
        reattribute_to: Option<prepoly_lexer::Span>,
        scopes: &mut ScopeStack,
    ) -> Type {
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
                message: format!("`{method}` is a static method; call it as `Type.{method}(...)`"),
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
        if self.errors.len() > before {
            if let Some(value_span) = reattribute_to {
                self.reattribute_errors_to_call(before, method, value_span);
            } else if foreign_method {
                self.reattribute_errors_to_call(before, method, span);
            }
        }
        // The method body ran conceptually: undo narrowings it may have
        // invalidated (see `invalidate_narrowed_after_call`).
        self.invalidate_narrowed_after_call(scopes);
        // Type the call's result by instantiating the method's scheme
        // against the receiver instance (schemes are built before the
        // function bodies that call them). The re-elaboration above still
        // ran for its conflict checks -- a key compared with `==` does not
        // unify onto a scheme parameter, so a `map.get(1)` clash is caught
        // there, not by the scheme. The re-elaborated return is the
        // fallback when the scheme cannot resolve the result.
        if let Some(ret) = self.scheme_method_return(recv_ty, method) {
            return ret;
        }
        self.common_type_list(&returns)
            .unwrap_or_else(|| self.fresh_unknown())
    }

    /// The in-scope record types that declare method `method` AND whose declared
    /// fields the structural (anonymous) instance `record` satisfies, sorted by
    /// name for deterministic diagnostics. "In scope" means the type's bare name
    /// resolves from the current module to that type.
    fn structural_method_candidates(
        &mut self,
        record: &NominalType,
        method: &str,
    ) -> Vec<(String, String)> {
        let mut out: Vec<(String, String)> = Vec::new();
        let infos: Vec<(String, String)> = self
            .program
            .types
            .values()
            .filter_map(|info| {
                let TypeKind::Record { methods, .. } = &info.kind else {
                    return None;
                };
                if !methods.contains_key(method) {
                    return None;
                }
                Some((info.name.clone(), info.symbol.clone()))
            })
            .collect();
        for (name, symbol) in infos {
            if self.resolve_type_symbol(&name).as_deref() != Some(symbol.as_str()) {
                continue;
            }
            let Some(info) = self.program.types.get(&symbol) else {
                continue;
            };
            let sup = info.type_ref();
            let Type::Record(sup_n) = &sup else { continue };
            if crate::structural::record_satisfies_fields(self.program, record, sup_n).is_empty() {
                out.push((name, symbol));
            }
        }
        out.sort();
        out
    }

    /// A near-miss explanation for a failed structural method resolution: the
    /// in-scope record types that declare `method` but whose fields the value
    /// does NOT satisfy, with the unsatisfied members. `None` when no in-scope
    /// type declares the method at all (the plain has-no-method error reads
    /// better then).
    fn structural_near_miss(&mut self, record: &NominalType, method: &str) -> Option<String> {
        let infos: Vec<(String, String)> = self
            .program
            .types
            .values()
            .filter_map(|info| {
                let TypeKind::Record { methods, .. } = &info.kind else {
                    return None;
                };
                if !methods.contains_key(method) {
                    return None;
                }
                Some((info.name.clone(), info.symbol.clone()))
            })
            .collect();
        let mut misses: Vec<String> = Vec::new();
        for (name, symbol) in infos {
            if self.resolve_type_symbol(&name).as_deref() != Some(symbol.as_str()) {
                continue;
            }
            let info = self.program.types.get(&symbol)?;
            let sup = info.type_ref();
            let Type::Record(sup_n) = &sup else { continue };
            let issues = crate::structural::record_satisfies_fields(self.program, record, sup_n);
            if !issues.is_empty() {
                misses.push(format!("`{name}` (unsatisfied: {})", issues.join(", ")));
            }
        }
        misses.sort();
        if misses.is_empty() {
            return None;
        }
        Some(format!(
            "the anonymous structure does not satisfy any in-scope type declaring \
             `{method}`: {}",
            misses.join("; ")
        ))
    }

    /// The stored type of record field `name` on instance `record`, if the field
    /// exists: the instance substitution (an inferred field pinned at
    /// construction) wins over the declaration's annotation. `None` when the
    /// record has no such field.
    fn field_value_type(&mut self, record: &NominalType, name: &str) -> Option<Type> {
        if let Some(t) = record.substitution.get(name) {
            return Some(t.clone());
        }
        let info = self.program.type_by_id(record.id)?;
        let TypeKind::Record { fields, .. } = &info.kind else {
            return None;
        };
        let f = fields.iter().find(|f| f.name == name)?;
        Some(
            f.resolved_ty
                .clone()
                .unwrap_or_else(|| self.fresh_unknown()),
        )
    }

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
                        // Calling through a CONCRETE parameter type pins an open
                        // argument variable persistently: `(x) -> g(x)` with
                        // `g: (int32) -> int32` fixes `x = int32`, so the
                        // enclosing closure's recorded type is concrete (a
                        // closure stored into an unannotated record field takes
                        // its instance type from this). A parameter still
                        // carrying its own inference variables stays local-only:
                        // pinning through it would defeat let-polymorphism.
                        if self.solver.free_vars(param).is_empty()
                            && matches!(self.resolve(&got), Type::Unknown(_))
                        {
                            let _ = self.solver.unify(&got, param);
                        }
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
                // Every argument is still type-checked (an undeclared name in a
                // trailing argument must surface), and the conversion's arity is
                // exactly one.
                for arg in args {
                    self.check_expr(&arg.expr, scopes);
                }
                if args.len() != 1 {
                    self.errors.push(TypeError {
                        message: format!(
                            "`{qualifier}.from` takes 1 argument, found {}",
                            args.len()
                        ),
                        span,
                    });
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
            if let Some(original) = scope.get(name).cloned() {
                let Type::Nullable(inner) = self.resolve(&original) else {
                    return;
                };
                tracing::debug!(name, to = %inner.display(), "narrowing nullable to non-null");
                scope.insert(name.to_string(), (*inner).clone());
                // Remember the pre-narrowing type so a later call can undo the
                // narrowing when the binding is reachable by the callee (a
                // global or a closure-assigned local).
                self.narrowed_bindings
                    .push((name.to_string(), Type::Nullable(inner)));
                break;
            }
        }
    }

    /// Undo narrowings a call may have invalidated: a narrowed GLOBAL (frame 0
    /// of the scope stack; any callee can assign it) and a narrowed local that
    /// some closure in this body assigns (the closure may run during the call).
    /// The nullable type is restored in the current (branch-local) scope clone,
    /// so uses after the call must re-check for null. Plain locals stay
    /// narrowed: no callee can rebind them.
    fn invalidate_narrowed_after_call(&mut self, scopes: &mut ScopeStack) {
        if self.narrowed_bindings.is_empty() {
            return;
        }
        let narrowed = self.narrowed_bindings.clone();
        for (name, original) in narrowed {
            let Some(frame_idx) = scopes.iter().rposition(|s| s.contains_key(&name)) else {
                continue;
            };
            let global = frame_idx == 0;
            if !global && !self.closure_write_targets.contains(&name) {
                continue;
            }
            let still_narrowed = scopes[frame_idx]
                .get(&name)
                .is_some_and(|t| !matches!(self.resolve(t), Type::Nullable(_)));
            if still_narrowed {
                tracing::debug!(name, "re-widening narrowed binding after call");
                scopes[frame_idx].insert(name.clone(), original.clone());
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

    /// Whether the resolved scrutinee type can produce a value matching a
    /// variant pattern named `variant`. Membership is decided against the
    /// scrutinee's OWN sum definition -- two sums may share a variant name, so
    /// picking an arbitrary "owning" sum from the type table and comparing its
    /// name would accept or reject depending on hash order.
    fn scrutinee_accepts_variant(&mut self, scrutinee: &Type, variant: &str) -> bool {
        let resolved = self.resolve(scrutinee);
        if resolved.is_result_type() {
            return matches!(variant, "Ok" | "Err");
        }
        match resolved {
            Type::Sum(sum) => match self.program.type_by_id(sum.id) {
                Some(info) => info.variant(variant).is_some(),
                // No table entry (e.g. a synthesized sum): fall back to
                // matching the sum's name against the variant's possible owners.
                None => self
                    .program
                    .sums_containing_variant(variant)
                    .iter()
                    .any(|info| sum.is_name(&info.name)),
            },
            Type::Unknown(_) => true,
            _ => false,
        }
    }

    fn check_pattern_against(&mut self, scrutinee: &Type, pat: &Pattern) {
        match pat {
            Pattern::Binding(name, span) => {
                if let Some(owner) = self.variant_owner(name)
                    && !self.scrutinee_accepts_variant(scrutinee, name)
                {
                    let other = self.resolve(scrutinee);
                    self.errors.push(TypeError {
                        message: format!(
                            "pattern variant `{name}` belongs to `{owner}`, not `{}`",
                            other.display()
                        ),
                        span: *span,
                    });
                }
            }
            Pattern::Record(name, fields, span) => {
                let owner = self.variant_owner(name);
                if let Some(owner) = &owner
                    && !self.scrutinee_accepts_variant(scrutinee, name)
                {
                    let other = self.resolve(scrutinee);
                    self.errors.push(TypeError {
                        message: format!(
                            "pattern variant `{name}` belongs to `{owner}`, not `{}`",
                            other.display()
                        ),
                        span: *span,
                    });
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
        let sum_name = self.variant_owner(variant);
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
        // Mode wrappers expose the underlying value's methods: a call through a
        // `ref(mut(T))` parameter must resolve (and type-check its arguments
        // against) `T`'s methods rather than deferring to runtime dispatch.
        match prepoly_hir::peel_modes(&self.resolve(ty)).clone() {
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

    /// A sum type defining a variant named `variant`, when one exists. Several
    /// sums may share a variant name; the first of the deterministic order is
    /// returned (used for messages and as a fallback when the scrutinee's own
    /// type is unknown), so results never depend on type-table hash order.
    fn variant_owner(&self, variant: &str) -> Option<String> {
        self.program
            .sums_containing_variant(variant)
            .first()
            .map(|info| info.name.clone())
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
            | "_with_all"
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

/// Names assigned (rebound) anywhere inside a closure literal of `b`. A closure
/// captures such a binding by reference, so any call made while the binding is
/// narrowed non-null can run the closure and re-null it; the narrowing pass
/// treats these names like globals and re-widens them after calls. Shadowing is
/// not tracked (a closure-local `let` of the same name over-approximates),
/// which only re-widens more than strictly needed -- never less.
fn closure_write_targets_block(b: &Block) -> HashSet<String> {
    let mut acc = HashSet::new();
    for s in &b.stmts {
        collect_closure_writes_stmt(s, false, &mut acc);
    }
    acc
}

fn collect_closure_writes_stmt(stmt: &Stmt, in_closure: bool, acc: &mut HashSet<String>) {
    match stmt {
        Stmt::Let { value, .. } => collect_closure_writes_expr(value, in_closure, acc),
        Stmt::Assign { target, value, .. } => {
            if in_closure && let Expr::Ident(name, _) = target {
                acc.insert(name.clone());
            }
            collect_closure_writes_expr(target, in_closure, acc);
            collect_closure_writes_expr(value, in_closure, acc);
        }
        Stmt::Expr(e) => collect_closure_writes_expr(e, in_closure, acc),
        Stmt::While { cond, body, .. } => {
            collect_closure_writes_expr(cond, in_closure, acc);
            for s in &body.stmts {
                collect_closure_writes_stmt(s, in_closure, acc);
            }
        }
        Stmt::For { iter, body, .. } => {
            collect_closure_writes_expr(iter, in_closure, acc);
            for s in &body.stmts {
                collect_closure_writes_stmt(s, in_closure, acc);
            }
        }
        Stmt::Return(value, _) => {
            if let Some(e) = value {
                collect_closure_writes_expr(e, in_closure, acc);
            }
        }
        Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

fn collect_closure_writes_expr(expr: &Expr, in_closure: bool, acc: &mut HashSet<String>) {
    match expr {
        Expr::Closure(_, body, _) => collect_closure_writes_expr(body, true, acc),
        Expr::Block(b, _) => {
            for s in &b.stmts {
                collect_closure_writes_stmt(s, in_closure, acc);
            }
        }
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) => {
            collect_closure_writes_expr(inner, in_closure, acc)
        }
        Expr::Binary(_, a, b, _) | Expr::Range(a, b, _) => {
            collect_closure_writes_expr(a, in_closure, acc);
            collect_closure_writes_expr(b, in_closure, acc);
        }
        Expr::Call(callee, args, _) => {
            collect_closure_writes_expr(callee, in_closure, acc);
            for a in args {
                collect_closure_writes_expr(&a.expr, in_closure, acc);
            }
        }
        Expr::Field(base, _, _) => collect_closure_writes_expr(base, in_closure, acc),
        Expr::Index(base, idx, _) => {
            collect_closure_writes_expr(base, in_closure, acc);
            collect_closure_writes_expr(idx, in_closure, acc);
        }
        Expr::Array(items, _) => {
            for e in items {
                collect_closure_writes_expr(e, in_closure, acc);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, e) in fields {
                collect_closure_writes_expr(e, in_closure, acc);
            }
        }
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(e) = seg {
                    collect_closure_writes_expr(e, in_closure, acc);
                }
            }
        }
        Expr::If(cond, then, els, _) => {
            collect_closure_writes_expr(cond, in_closure, acc);
            for s in &then.stmts {
                collect_closure_writes_stmt(s, in_closure, acc);
            }
            if let Some(e) = els {
                collect_closure_writes_expr(e, in_closure, acc);
            }
        }
        Expr::IfLet(_, scrut, then, els, _) => {
            collect_closure_writes_expr(scrut, in_closure, acc);
            for s in &then.stmts {
                collect_closure_writes_stmt(s, in_closure, acc);
            }
            if let Some(e) = els {
                collect_closure_writes_expr(e, in_closure, acc);
            }
        }
        Expr::Match(scrut, arms, _) => {
            collect_closure_writes_expr(scrut, in_closure, acc);
            for arm in arms {
                collect_closure_writes_expr(&arm.body, in_closure, acc);
            }
        }
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => {}
    }
}

/// Whether lowering this statement can produce a MIR branch (a `CondBranch`
/// terminator) before control reaches the next statement. Used by the
/// structural if-probe: the back end's fold follows only straight-line
/// `Goto`/`Return` chains, so any branching statement before the arm's
/// `return` makes the arm non-foldable. Conservative: `true` when unsure.
fn stmt_may_branch(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Let { value, .. } => expr_may_branch(value),
        Stmt::Assign { target, value, .. } => expr_may_branch(target) || expr_may_branch(value),
        Stmt::Expr(e) => expr_may_branch(e),
        Stmt::While { .. } | Stmt::For { .. } => true,
        Stmt::Return(..) | Stmt::Break(_) | Stmt::Continue(_) => true,
    }
}

/// Whether evaluating this expression can produce a MIR branch. Short-circuit
/// operators, `expr!` propagation and every conditional construct lower through
/// a `CondBranch`; a closure literal does not (its body is a separate function).
fn expr_may_branch(e: &Expr) -> bool {
    match e {
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_)
        | Expr::Closure(..) => false,
        Expr::Str(segs, _) => segs
            .iter()
            .any(|s| matches!(s, StrSeg::Expr(e) if expr_may_branch(e))),
        Expr::Unary(_, inner, _) => expr_may_branch(inner),
        Expr::Binary(BinOp::And | BinOp::Or, ..) => true,
        Expr::Binary(_, a, b, _) => expr_may_branch(a) || expr_may_branch(b),
        Expr::Call(callee, args, _) => {
            expr_may_branch(callee) || args.iter().any(|a| expr_may_branch(&a.expr))
        }
        Expr::Field(base, ..) => expr_may_branch(base),
        Expr::Index(base, idx, _) => expr_may_branch(base) || expr_may_branch(idx),
        Expr::ErrorProp(..) => true,
        Expr::Array(items, _) => items.iter().any(expr_may_branch),
        Expr::Range(lo, hi, _) => expr_may_branch(lo) || expr_may_branch(hi),
        Expr::TypeLit(_, fields, _) => fields.iter().any(|(_, e)| expr_may_branch(e)),
        Expr::VariantLit(_, _, fields, _) => fields.iter().any(|(_, e)| expr_may_branch(e)),
        Expr::If(..) | Expr::IfLet(..) | Expr::Match(..) => true,
        Expr::Block(b, _) => b.stmts.iter().any(stmt_may_branch),
    }
}

trait Pipe: Sized {
    fn pipe<T>(self, f: impl FnOnce(Self) -> T) -> T {
        f(self)
    }
}
impl<T> Pipe for T {}
