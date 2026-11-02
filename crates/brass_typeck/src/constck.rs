//! Const checking: a value bound with `const` cannot be
//! reassigned, nor can its fields/elements be mutated. Assignments whose root
//! place is a const binding are rejected, and so is passing a const into a
//! write-through (`ref(mut(T))`) parameter of a free function or closure this
//! pass can see. Mutating a read-only `infer` parameter is rejected here too.
//!
//! Which places are const is decided here, lexically. Whether a METHOD call
//! mutates a const place depends on the method the call dispatches to, which
//! only inference knows (the receiver's type may come from an inferred return,
//! an alias, a generic instantiation): this pass records every method call
//! whose receiver or arguments are const-rooted (`ConstCalls`), and the
//! inference checker rejects the ones whose resolved method writes through
//! that receiver or argument. A call through a function value whose parameter
//! modes this pass cannot see is recorded and judged the same way, on the
//! callee's type.

use fxhash::FxHashMap as HashMap;

use brass_hir::{
    MutationInfo, NominalInfo, ParamInfo, Program, Type, TypeInfo, TypeKind, mutates_root,
    param_is_immutable_ref, param_is_infer, root_ident,
};
use brass_parser::Span;
use brass_parser::ast::*;

use crate::TypeError;

/// The calls touching a const value whose verdict depends on what the call
/// resolves to, recorded by const checking for inference to judge: method
/// calls against the resolved receiver type
/// (`Checker::check_const_method_call`), calls through a function value
/// against its resolved parameter types
/// (`Checker::check_read_only_value_args`).
#[derive(Default)]
pub(crate) struct ConstCalls {
    /// Call span -> the const binding its receiver is rooted in.
    pub(crate) receivers: HashMap<Span, String>,
    /// Call span -> each const-rooted argument: its call-site index (the
    /// receiver excluded), its const root, and its span.
    pub(crate) args: HashMap<Span, Vec<(usize, String, Span)>>,
    /// The same for a call through a function value this pass cannot see
    /// into (a function-valued parameter, any value not bound to a closure
    /// literal or a named function): whether it takes an argument by
    /// `ref(mut(T))` is decided by the callee's type in each elaboration.
    pub(crate) value_args: HashMap<Span, Vec<(usize, String, Span)>>,
    /// The program's write-through facts the verdicts are read from.
    pub(crate) mutation: MutationInfo,
}

/// A binding tracked for const checking.
#[derive(Clone)]
enum Binding {
    /// A const binding, with its type when it is statically derivable (from
    /// the annotation, the constructed value, or a called function's declared
    /// return type), which decides whether binding it to another name aliases
    /// the same heap value.
    Const(Option<Type>),
    /// A `let` bound to a const-rooted place of a derivable shared-heap type:
    /// it shares the const's value, so mutating through it is rejected exactly
    /// as through the const, but -- unlike the const itself -- a bare
    /// reassignment only rebinds the local handle (a `let` is a mutable
    /// binding; rebinding a name is not a mutation of its value).
    Alias(Type),
    /// A `let` bound to a const-rooted place whose type is not derivable
    /// here: it shares the const's value whenever that value is a heap
    /// aggregate, so mutating through it (a projection store, a mutating
    /// method, a write-through argument -- all of which imply an aggregate) is
    /// rejected, while a bare reassignment only rebinds the local.
    ConstAlias,
    /// A local bound to a named free function (`let f = mutate`): calls
    /// through it resolve to the aliased function's write-through facts.
    Fn(String),
    /// A binding initialized with a closure literal: calls through it resolve
    /// the closure's own write-through (`ref(mut(T))`) parameter positions,
    /// and `constant` keeps a `const` closure binding unassignable.
    Closure {
        write_through: Vec<usize>,
        constant: bool,
    },
    /// A non-const `let`, recorded so that it shadows an outer const of the
    /// same name: assigning to the inner binding is allowed.
    Mutable,
}

/// The bindings a destructuring `let`/`const` pattern introduces: every
/// bound name is const under `const` (the binding is immutable at any depth),
/// and a mutable shadow of any outer const of the same name under `let`.
fn destructured_bindings(pat: &Pattern, is_const: bool) -> Vec<(String, Binding)> {
    pat.bound_names()
        .into_iter()
        .map(|name| {
            let binding = if is_const {
                Binding::Const(None)
            } else {
                Binding::Mutable
            };
            (name.to_string(), binding)
        })
        .collect()
}

/// The parameter positions of a closure literal that write through to the
/// caller's value: exactly the `ref(mut(T))` parameters. Every other closure
/// parameter is a borrow the body cannot mutate, or a private copy (see the
/// parameter-passing table), so a `const` argument there is safe.
fn closure_write_through(params: &[Param]) -> Vec<usize> {
    params
        .iter()
        .enumerate()
        .filter(|(_, p)| {
            matches!(&p.ty, Some(TypeExpr::Ref(inner, _)) if matches!(**inner, TypeExpr::Mut(..)))
        })
        .map(|(i, _)| i)
        .collect()
}

type ConstScopes = Vec<HashMap<String, Binding>>;

struct ConstChecker<'a> {
    program: &'a Program,
    /// The program's write-through facts (`brass_hir::MutationInfo`): which
    /// free-function and method parameters, and which methods' `self`, a
    /// callee mutates through the caller's reference. Only a `ref(mut(T))`
    /// position (or one forwarded into such a position) writes through; an
    /// unannotated parameter the body mutates is a private copy. This pass
    /// rejects a const argument to such a free-function parameter itself and
    /// hands the facts on (`ConstCalls::mutation`) for the method calls
    /// inference judges.
    mutation: MutationInfo,
    /// The module whose body is currently being checked, so a bare callee name at
    /// a call site resolves to the same symbol the fixpoint keyed on.
    current_module: Vec<String>,
    errors: Vec<TypeError>,
    /// Method calls touching a const, for inference to judge.
    calls: ConstCalls,
}

/// The diagnostics this pass decides on its own: const reassignment, stores
/// through const places, const arguments to write-through parameters of free
/// functions and closures, and mutation of read-only parameters. Method calls
/// on const values, and calls through function values this pass cannot see
/// into, are judged by the full analysis (`crate::analyze`), which resolves
/// what each call reaches.
pub fn check(program: &Program) -> Vec<TypeError> {
    check_in(program, crate::AnalysisModules::all()).0
}

/// [`check`] over the analyzed modules, also returning the calls touching a
/// const value that inference judges (`ConstCalls`).
pub(crate) fn check_in(
    program: &Program,
    modules: crate::AnalysisModules<'_>,
) -> (Vec<TypeError>, ConstCalls) {
    let mut checker = ConstChecker {
        program,
        // Entry diagnostics still need mutation facts for seeded callees.
        mutation: MutationInfo::analyze(program),
        current_module: Vec::new(),
        errors: Vec::new(),
        calls: ConstCalls::default(),
    };
    checker.check_program(modules);
    checker.calls.mutation = checker.mutation;
    (checker.errors, checker.calls)
}

/// Peel the wrappers that do not change which value a place denotes
/// (mutability, const-ness, reference-ness, and nullability -- narrowing a
/// `T?` yields the same shared `T`), so projections and method lookups
/// dispatch on the underlying type.
fn peel(ty: &Type) -> &Type {
    match ty {
        Type::Mut(inner) | Type::ConstOf(inner) | Type::Ref(inner) | Type::Nullable(inner) => {
            peel(inner)
        }
        _ => ty,
    }
}

/// The element type of an array/slice value.
fn element_type(ty: &Type) -> Option<Type> {
    match peel(ty) {
        Type::Slice(inner) | Type::Array(inner, _) => Some((**inner).clone()),
        _ => None,
    }
}

/// Whether a value of `ty` is a shared heap aggregate: binding it aliases the
/// same value, so constness must propagate to the alias. Primitives (and
/// strings, which are immutable) are copied on binding instead.
fn is_shared_heap(ty: &Type) -> bool {
    matches!(
        peel(ty),
        Type::Record(..) | Type::Sum(..) | Type::Slice(..) | Type::Array(..) | Type::Tuple(..)
    )
}

impl ConstChecker<'_> {
    fn check_program(&mut self, modules: crate::AnalysisModules<'_>) {
        // Bodies see only the globals their defining module can resolve.
        let global_defs = self.global_bindings();
        for f in self.program.functions.values() {
            if !modules.checks(&f.module) || !modules.checks_body(f.decl.span) {
                continue;
            }
            // Parameters shadow any like-named global const. Each binds
            // mutable within its body (a private copy, or a `ref(mut(T))`
            // reference), except an immutable `ref(T)` reference, which
            // binds as const (see `param_scope`).
            let params = param_scope(&f.signature.params, false);
            self.current_module = f.module.clone();
            self.check_param_mutability(&f.signature.params, &f.decl.body);
            let globals = self.globals_visible_from(&f.module, &global_defs, true);
            self.check_block(&f.decl.body, &mut vec![globals.clone(), params]);
        }
        for t in self.program.types.values() {
            if !modules.checks(&t.module) {
                continue;
            }
            let methods: Vec<&brass_hir::MethodInfo> = match &t.kind {
                TypeKind::Record { methods, .. } => methods.values().collect(),
                TypeKind::Sum { variants } => {
                    variants.iter().flat_map(|v| v.methods.values()).collect()
                }
            };
            for m in methods {
                if !modules.checks_body(m.decl.span) {
                    continue;
                }
                if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                    continue;
                }
                let Some(body) = m.decl.body.as_ref() else {
                    continue;
                };
                // A method also binds `self` (mutable within the body). A method
                // body resolves callee names against the type's home module.
                let params = param_scope(&m.signature.params, true);
                self.current_module = t.module.clone();
                self.check_param_mutability(&m.signature.params, body);
                let globals = self.globals_visible_from(&t.module, &global_defs, true);
                self.check_block(body, &mut vec![globals.clone(), params]);
            }
        }
        // Top-level init statements build their scope up in order, so a global
        // is only visible to later top-level statements, not earlier ones.
        for init in &self.program.inits {
            if !modules.checks(&init.path) {
                continue;
            }
            self.current_module = init.path.clone();
            // Imported and implicit-prelude globals are already initialized;
            // this module's own globals enter scope in statement order below.
            let mut scopes = vec![self.globals_visible_from(&init.path, &global_defs, false)];
            for stmt in &init.stmts {
                self.check_stmt(stmt, &mut scopes);
            }
        }
    }

    /// The final binding state of every module's globals. Mutable entries are
    /// retained because they shadow imported or implicit-prelude consts.
    fn global_bindings(&self) -> HashMap<Vec<String>, HashMap<String, Binding>> {
        let mut modules: HashMap<Vec<String>, HashMap<String, Binding>> = HashMap::default();
        for init in &self.program.inits {
            let bindings = modules.entry(init.path.clone()).or_default();
            for stmt in &init.stmts {
                if let Stmt::Let {
                    pat,
                    is_const,
                    value: Some(_),
                    ..
                } = stmt
                    && !matches!(pat, Pattern::Binding(..))
                {
                    bindings.extend(destructured_bindings(pat, *is_const));
                    continue;
                }
                let Stmt::Let {
                    pat: Pattern::Binding(name, None, _),
                    ty,
                    value,
                    is_const,
                    ..
                } = stmt
                else {
                    continue;
                };
                if let Some(Expr::Closure(params, _, _)) = value {
                    bindings.insert(
                        name.clone(),
                        Binding::Closure {
                            write_through: closure_write_through(params),
                            constant: *is_const,
                        },
                    );
                } else if *is_const && let Some(value) = value {
                    bindings.insert(
                        name.clone(),
                        Binding::Const(self.binding_const_type(&init.path, ty, value)),
                    );
                } else {
                    bindings.insert(name.clone(), Binding::Mutable);
                }
            }
        }
        modules
    }

    /// Globals visible from `module`, under their local names. Prelude globals
    /// are implicit, explicit imports honor renames, and the module's own
    /// declarations take precedence when `include_own` is true.
    fn globals_visible_from(
        &self,
        module: &[String],
        defs: &HashMap<Vec<String>, HashMap<String, Binding>>,
        include_own: bool,
    ) -> HashMap<String, Binding> {
        let mut out = HashMap::default();
        let mut prelude_paths: Vec<_> = self.program.prelude_modules.iter().collect();
        prelude_paths.sort();
        for path in prelude_paths {
            if let Some(bindings) = defs.get(path) {
                for (name, binding) in bindings {
                    out.entry(name.clone()).or_insert_with(|| binding.clone());
                }
            }
        }
        if let Some(imports) = self.program.module_imports.get(module) {
            let origins = self.program.import_origins.get(module);
            let renames = self.program.import_renames.get(module);
            for local in imports {
                let Some(origin) = origins.and_then(|items| items.get(local)) else {
                    continue;
                };
                let remote = renames
                    .and_then(|items| items.get(local))
                    .map(String::as_str)
                    .unwrap_or(local);
                if let Some(binding) = defs.get(origin).and_then(|items| items.get(remote)) {
                    out.insert(local.clone(), binding.clone());
                }
            }
        }
        if include_own && let Some(bindings) = defs.get(module) {
            out.extend(
                bindings
                    .iter()
                    .map(|(name, binding)| (name.clone(), binding.clone())),
            );
        }
        out
    }

    fn check_block(&mut self, block: &Block, scopes: &mut ConstScopes) {
        scopes.push(HashMap::default());
        for stmt in &block.stmts {
            self.check_stmt(stmt, scopes);
        }
        scopes.pop();
    }

    fn check_stmt(&mut self, stmt: &Stmt, scopes: &mut ConstScopes) {
        match stmt {
            Stmt::Let {
                pat,
                ty,
                value,
                is_const,
                ..
            } => {
                let Some(value) = value else {
                    // An uninitialized `let` is never a const and aliases
                    // nothing; it just shadows any outer const of that name.
                    if let Pattern::Binding(name, None, _) = pat
                        && let Some(top) = scopes.last_mut()
                    {
                        top.insert(name.clone(), Binding::Mutable);
                    }
                    return;
                };
                self.check_expr(value, scopes);
                if !matches!(pat, Pattern::Binding(..))
                    && let Some(top) = scopes.last_mut()
                {
                    top.extend(destructured_bindings(pat, *is_const));
                }
                if let Pattern::Binding(name, None, _) = pat {
                    let alias = self.const_alias(value, scopes);
                    let fn_alias = self.fn_value_symbol(value, scopes);
                    let module = self.current_module.clone();
                    if let Some(top) = scopes.last_mut() {
                        let binding = if let Expr::Closure(params, _, _) = value {
                            Binding::Closure {
                                write_through: closure_write_through(params),
                                constant: *is_const,
                            }
                        } else if *is_const {
                            Binding::Const(self.binding_const_type(&module, ty, value))
                        } else if let Some(alias) = alias {
                            // Aliasing a const heap value binds another handle to
                            // the same shared value (the runtime shares heap
                            // objects by reference), so mutating through the
                            // alias is rejected as through the const.
                            alias
                        } else if let Some(symbol) = fn_alias {
                            Binding::Fn(symbol)
                        } else {
                            // Record the shadow so it hides an outer const.
                            Binding::Mutable
                        };
                        top.insert(name.clone(), binding);
                    }
                }
            }
            Stmt::Assign {
                target,
                value,
                span,
                ..
            } => {
                self.check_expr(value, scopes);
                self.check_expr(target, scopes);
                // A store through a const place is rejected; so is rebinding a
                // const name, except a `ConstAlias`, whose bare reassignment
                // only rebinds the local handle.
                let rejected = |binding: Option<&Binding>| match binding {
                    Some(Binding::Const(_) | Binding::Closure { constant: true, .. }) => true,
                    Some(Binding::ConstAlias | Binding::Alias(_)) => {
                        !matches!(target, Expr::Ident(..))
                    }
                    _ => false,
                };
                if let Some(root) = root_ident(target)
                    && rejected(self.const_binding(scopes, root))
                {
                    self.errors.push(TypeError {
                        message: format!("cannot assign to const value `{root}`"),
                        span: *span,
                    });
                }
            }
            Stmt::While { cond, body, .. } => {
                self.check_expr(cond, scopes);
                self.check_block(body, scopes);
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                self.check_expr(iter, scopes);
                // The loop variable is a reference into each element, so its
                // mutability matches the iterand: iterating an immutable array (a
                // const, or a `ref(T)` parameter) binds it const, rejecting an
                // in-place mutation like `e *= 2`. A mutable array binds it mutable.
                let binding = if self.const_root(iter, scopes).is_some() {
                    let elem = self
                        .const_place_type(iter, scopes)
                        .and_then(|t| element_type(&t));
                    Binding::Const(elem)
                } else {
                    Binding::Mutable
                };
                // Every name a destructuring loop variable binds takes the same
                // constness: they are all parts of the one element.
                let mut frame = HashMap::default();
                for n in pat.bound_names() {
                    frame.insert(n.to_string(), binding.clone());
                }
                scopes.push(frame);
                self.check_block(body, scopes);
                scopes.pop();
            }
            Stmt::Expr(expr) => self.check_expr(expr, scopes),
            Stmt::Return(Some(expr), _) => self.check_expr(expr, scopes),
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }

    fn check_expr(&mut self, expr: &Expr, scopes: &mut ConstScopes) {
        match expr {
            Expr::Unary(_, inner, _)
            | Expr::ErrorProp(inner, _)
            | Expr::TypeTest(inner, _, _, _) => self.check_expr(inner, scopes),
            Expr::Binary(_, left, right, _) | Expr::Range(left, right, _) => {
                self.check_expr(left, scopes);
                self.check_expr(right, scopes);
            }
            Expr::Call(callee, args, span) => {
                self.record_const_method_call(callee, args, *span, scopes);
                self.check_const_args_to_mutating_fn(callee, args, *span, scopes);
                self.check_expr(callee, scopes);
                for arg in args {
                    self.check_expr(&arg.expr, scopes);
                }
            }
            Expr::Field(base, _, _) => self.check_expr(base, scopes),
            Expr::Index(base, idx, _) => {
                self.check_expr(base, scopes);
                self.check_expr(idx, scopes);
            }
            Expr::Closure(params, body, _) => {
                // Closure parameters follow the function parameter-passing
                // table: a `ref(T)` parameter is an immutable reference (bound
                // const, so mutating through it is rejected) and an `infer`
                // parameter is a read-only copy.
                self.check_closure_param_mutability(params, body);
                let frame = params
                    .iter()
                    .map(|param| (param.name.clone(), self.closure_param_binding(param)))
                    .collect();
                scopes.push(frame);
                self.check_expr(body, scopes);
                scopes.pop();
            }
            Expr::Array(items, _) => {
                for item in items {
                    self.check_expr(item, scopes);
                }
            }
            Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
                for (_, value) in fields {
                    self.check_expr(value, scopes);
                }
            }
            Expr::Str(segments, _) => {
                for segment in segments {
                    if let StrSeg::Expr(inner) = segment {
                        self.check_expr(inner, scopes);
                    }
                }
            }
            Expr::If(cond, then, els, _) => {
                self.check_expr(cond, scopes);
                self.check_block(then, scopes);
                if let Some(els) = els {
                    self.check_expr(els, scopes);
                }
            }
            Expr::IfLet(pat, scrutinee, then, els, _) => {
                self.check_expr(scrutinee, scopes);
                let frame = self.pattern_scope(pat, scrutinee, scopes);
                scopes.push(frame);
                self.check_block(then, scopes);
                scopes.pop();
                if let Some(els) = els {
                    self.check_expr(els, scopes);
                }
            }
            Expr::Match(scrutinee, arms, _) => {
                self.check_expr(scrutinee, scopes);
                for arm in arms {
                    let frame = self.pattern_scope(&arm.pattern, scrutinee, scopes);
                    scopes.push(frame);
                    self.check_expr(&arm.body, scopes);
                    scopes.pop();
                }
            }
            Expr::Block(block, _) => self.check_block(block, scopes),
            Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(_)
            | Expr::Ident(..)
            | Expr::SelfExpr(_) => {}
        }
    }

    /// Bind names introduced by a refutable pattern in the arm where it
    /// matched. Destructured pieces of a const scrutinee remain immutable,
    /// while a whole-binding pattern can retain the scrutinee's known type.
    fn pattern_scope(
        &self,
        pat: &Pattern,
        scrutinee: &Expr,
        scopes: &ConstScopes,
    ) -> HashMap<String, Binding> {
        let binding = if self.const_root(scrutinee, scopes).is_some() {
            let ty = matches!(pat, Pattern::Binding(..))
                .then(|| self.const_place_type(scrutinee, scopes))
                .flatten();
            Binding::Const(ty)
        } else {
            Binding::Mutable
        };
        pat.bound_names()
            .into_iter()
            .map(|name| (name.to_string(), binding.clone()))
            .collect()
    }

    /// Record a method call whose receiver, or some argument, is rooted in a
    /// const binding. Whether it mutates that const depends on the method the
    /// call dispatches to, which inference decides from the resolved receiver
    /// type (a parenthesized callee is a call through a function-typed value,
    /// not a method call).
    fn record_const_method_call(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        span: brass_parser::Span,
        scopes: &ConstScopes,
    ) {
        if callee.span().is_parenthesized() {
            return;
        }
        let Expr::Field(receiver, _, _) = callee else {
            return;
        };
        if let Some(root) = self.const_root(receiver, scopes) {
            self.calls.receivers.insert(span, root.to_string());
        }
        let const_args: Vec<(usize, String, Span)> = args
            .iter()
            .enumerate()
            .filter_map(|(i, arg)| {
                let root = self.const_root(&arg.expr, scopes)?;
                Some((i, root.to_string(), arg.expr.span()))
            })
            .collect();
        if !const_args.is_empty() {
            self.calls.args.insert(span, const_args);
        }
    }

    /// Record a call through a function value whose parameter modes this pass
    /// cannot see, with its const-rooted (read-only) arguments: inference
    /// rejects the ones the callee's resolved type takes by `ref(mut(T))`
    /// (see `Checker::check_read_only_value_args`).
    fn record_const_value_call(&mut self, args: &[Arg], span: Span, scopes: &ConstScopes) {
        let const_args: Vec<(usize, String, Span)> = args
            .iter()
            .enumerate()
            .filter_map(|(i, arg)| {
                let root = self.const_root(&arg.expr, scopes)?;
                Some((i, root.to_string(), arg.expr.span()))
            })
            .collect();
        if !const_args.is_empty() {
            self.calls.value_args.insert(span, const_args);
        }
    }

    /// The const binding a place is rooted in (its root identifier), or `None`
    /// when the root is not const. Unlike `const_place_type` this does not require
    /// the place's type to be known, so it also covers const arrays/tuples whose
    /// element types could not be derived.
    fn const_root<'a>(&self, place: &'a Expr, scopes: &ConstScopes) -> Option<&'a str> {
        let root = root_ident(place)?;
        match self.const_binding(scopes, root) {
            Some(Binding::Const(_) | Binding::Alias(_) | Binding::ConstAlias) => Some(root),
            _ => None,
        }
    }

    /// Reject mutating a parameter whose type forbids it. An `a: infer` parameter
    /// receives a read-only deep copy, so mutating or rebinding it is rejected
    /// here. The other read-only case -- an immutable `ref(T)` parameter
    /// (or `self: ref(Self)`) -- binds as const in [`param_scope`], so it is
    /// reported by the const path and skipped here to avoid a duplicate error.
    /// Everything else (an unannotated parameter, a `mut(T)`/`ref(mut(T))`, a bare
    /// aggregate value, or a mutable `self`) may be mutated.
    fn check_param_mutability(&mut self, params: &[ParamInfo], body: &Block) {
        for p in params {
            if param_permits_mutation(p) || param_is_immutable_ref(p) {
                continue;
            }
            // Rebinding is checked separately from member mutation:
            // `mutates_root` deliberately ignores a bare `a = v` (rebinding a
            // private copy never reaches the caller, so it forces no copy), but
            // an `infer` parameter is READ-ONLY as a binding too.
            if !mutates_root(body, &p.name) && !rebinds(body, &p.name) {
                continue;
            }
            self.errors.push(TypeError {
                message: format!(
                    "cannot mutate parameter `{}`: an `infer` parameter is a read-only deep copy \
                     (use `mut(T)` for a mutable copy, or `ref(mut(T))` for a mutable reference)",
                    p.name
                ),
                span: p.span,
            });
        }
    }

    /// Reject passing an immutable (`const`-rooted) value into a parameter the
    /// callee requires to be mutable: it mutates that parameter through the shared
    /// reference, which would modify a value declared immutable at the call site.
    /// Any const-rooted place qualifies, a primitive included: only a
    /// `ref(mut(T))` position (directly or by forwarding) writes through, and a
    /// parameter that receives a copy never does.
    ///
    /// Covers a direct call to a write-through function (by name or through a
    /// `let f = mutate` fn alias) or to a closure literal or closure binding
    /// with `ref(mut(T))` parameters, and a higher-order call that passes a
    /// write-through function or closure alongside the const it will be applied
    /// to (`apply(mutate, o)` with `fun apply(f, v) { f(v) }`). A call through
    /// any other function value is recorded for inference instead
    /// (`ConstCalls::value_args`).
    fn check_const_args_to_mutating_fn(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        span: Span,
        scopes: &ConstScopes,
    ) {
        if let Some(write_through) = self.closure_value_write_through(callee, scopes) {
            let shown = match callee {
                Expr::Ident(name, _) => format!("`{name}`"),
                _ => "this closure".to_string(),
            };
            for (i, arg) in args.iter().enumerate() {
                if write_through.contains(&i)
                    && let Some(root) = self.const_root(&arg.expr, scopes)
                {
                    self.errors.push(TypeError {
                        message: format!(
                            "cannot pass const value `{root}` to {shown}, which requires a mutable parameter"
                        ),
                        span: arg.expr.span(),
                    });
                }
            }
            return;
        }
        let Expr::Ident(fname, _) = callee else {
            if callee.span().is_parenthesized() || !matches!(callee, Expr::Field(..)) {
                self.record_const_value_call(args, span, scopes);
            }
            return;
        };
        let Some(symbol) = self.callee_fn_symbol(fname, scopes) else {
            self.record_const_value_call(args, span, scopes);
            return;
        };
        if let Some(indices) = self.mutation.write_through_params(&symbol).cloned() {
            for (i, arg) in args.iter().enumerate() {
                if indices.contains(&i)
                    && let Some(root) = self.const_root(&arg.expr, scopes)
                {
                    self.errors.push(TypeError {
                        message: format!(
                            "cannot pass const value `{root}` to `{fname}`, which requires a mutable parameter"
                        ),
                        span: arg.expr.span(),
                    });
                }
            }
        }
        // Higher-order laundering: the callee calls one of its fn-valued
        // parameters with (some of) its other parameters. Resolve the function
        // value actually passed here and check its write-through positions
        // against the arguments it will receive. A parameter the callee
        // receives as a private copy (an unannotated one it hands to a function
        // value, which may take it by `ref(mut)`) keeps the argument out of
        // reach, so only a reference parameter can launder a const.
        let Some(calls) = self.mutation.param_calls(&symbol) else {
            return;
        };
        let copied: Vec<bool> = self
            .program
            .functions
            .get(&symbol)
            .map(|f| {
                f.signature
                    .params
                    .iter()
                    .map(|p| {
                        brass_hir::param_receives_copy(
                            self.program,
                            &f.module,
                            &f.signature.params,
                            p,
                            &f.decl.body,
                            &self.mutation,
                        )
                    })
                    .collect()
            })
            .unwrap_or_default();
        let mut hof_errors = Vec::new();
        for pc in calls {
            let Some(fn_arg) = args.get(pc.fn_param) else {
                continue;
            };
            let (gname, g_indices): (String, Vec<usize>) = match (
                &fn_arg.expr,
                self.closure_value_write_through(&fn_arg.expr, scopes),
            ) {
                (Expr::Ident(gname, _), Some(indices)) => (format!("`{gname}`"), indices),
                (_, Some(indices)) => ("a closure".to_string(), indices),
                (Expr::Ident(gname, _), None) => {
                    let Some(gsym) = self.callee_fn_symbol(gname, scopes) else {
                        continue;
                    };
                    let Some(indices) = self.mutation.write_through_params(&gsym) else {
                        continue;
                    };
                    (format!("`{gname}`"), indices.iter().copied().collect())
                }
                _ => continue,
            };
            for k in &g_indices {
                let Some(j) = pc.args.get(*k).copied().flatten() else {
                    continue;
                };
                if copied.get(j).copied().unwrap_or(false) {
                    continue;
                }
                if let Some(arg) = args.get(j)
                    && let Some(root) = self.const_root(&arg.expr, scopes)
                {
                    hof_errors.push(TypeError {
                        message: format!(
                            "cannot pass const value `{root}` to `{fname}`, which passes it to {gname} requiring a mutable parameter"
                        ),
                        span: arg.expr.span(),
                    });
                }
            }
        }
        self.errors.extend(hof_errors);
    }

    /// The write-through parameter positions of a closure value: a closure
    /// literal written in place (an immediately called or directly passed
    /// closure), or a binding initialized with one. `None` for any other
    /// expression.
    fn closure_value_write_through(
        &self,
        value: &Expr,
        scopes: &ConstScopes,
    ) -> Option<Vec<usize>> {
        match value {
            Expr::Closure(params, _, _) => Some(closure_write_through(params)),
            Expr::Ident(name, _) => match self.const_binding(scopes, name) {
                Some(Binding::Closure { write_through, .. }) => Some(write_through.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// The binding a closure parameter introduces: an immutable `ref(T)`
    /// reference binds const (with its type when it resolves), every other
    /// parameter binds mutable (a private copy or a `ref(mut(T))`).
    fn closure_param_binding(&self, param: &Param) -> Binding {
        match &param.ty {
            Some(TypeExpr::Ref(inner, _)) if !matches!(**inner, TypeExpr::Mut(..)) => {
                let module = self.current_module.clone();
                Binding::Const(
                    brass_hir::resolve(inner, |n| self.nominal_info(&module, n))
                        .ok()
                        .filter(|t| !t.is_unknown()),
                )
            }
            _ => Binding::Mutable,
        }
    }

    /// The closure counterpart of [`Self::check_param_mutability`]: an
    /// `infer` closure parameter is a read-only deep copy, so mutating or
    /// rebinding it is rejected exactly like a function's.
    fn check_closure_param_mutability(&mut self, params: &[Param], body: &Expr) {
        let block = match body {
            Expr::Block(b, _) => b.clone(),
            other => Block {
                stmts: vec![Stmt::Expr(other.clone())],
                span: other.span(),
            },
        };
        for p in params {
            if !matches!(&p.ty, Some(TypeExpr::Named(n, _)) if n == "infer") {
                continue;
            }
            if !mutates_root(&block, &p.name) && !rebinds(&block, &p.name) {
                continue;
            }
            self.errors.push(TypeError {
                message: format!(
                    "cannot mutate parameter `{}`: an `infer` parameter is a read-only deep copy \
                     (use `mut(T)` for a mutable copy, or `ref(mut(T))` for a mutable reference)",
                    p.name
                ),
                span: p.span,
            });
        }
    }

    /// Resolve a bare callee name at a call site: a local `let f = mutate` fn
    /// alias takes priority (a non-fn local shadows any like-named function),
    /// then the module-visible free function.
    fn callee_fn_symbol(&self, name: &str, scopes: &ConstScopes) -> Option<String> {
        match self.const_binding(scopes, name) {
            Some(Binding::Fn(symbol)) => Some(symbol.clone()),
            Some(_) => None,
            None => self.program.resolve_fn_symbol(&self.current_module, name),
        }
    }

    /// The symbol of the free function `value` denotes, when binding it makes a
    /// local fn alias: a bare function name, or another fn alias.
    fn fn_value_symbol(&self, value: &Expr, scopes: &ConstScopes) -> Option<String> {
        let Expr::Ident(name, _) = value else {
            return None;
        };
        self.callee_fn_symbol(name, scopes)
    }

    /// The static type of a place expression that is rooted in a const binding,
    /// following field and index projections through the type definitions.
    /// Returns `None` when the place is not const-rooted or its type could not
    /// be derived.
    fn const_place_type(&self, place: &Expr, scopes: &ConstScopes) -> Option<Type> {
        match place {
            Expr::Ident(name, _) => match self.const_binding(scopes, name) {
                Some(Binding::Const(ty)) => ty.clone(),
                Some(Binding::Alias(ty)) => Some(ty.clone()),
                _ => None,
            },
            Expr::SelfExpr(_) => match self.const_binding(scopes, "self") {
                Some(Binding::Const(ty)) => ty.clone(),
                _ => None,
            },
            Expr::Field(base, field, _) => {
                let base_ty = self.const_place_type(base, scopes)?;
                self.field_type(&base_ty, field)
            }
            Expr::Index(base, _, _) => {
                let base_ty = self.const_place_type(base, scopes)?;
                element_type(&base_ty)
            }
            _ => None,
        }
    }

    /// The declared type of a record field, resolved by the record's nominal id.
    fn field_type(&self, base_ty: &Type, field: &str) -> Option<Type> {
        let Type::Record(n) = peel(base_ty) else {
            return None;
        };
        let info = self.program.type_by_id(n.id)?;
        let TypeKind::Record { fields, .. } = &info.kind else {
            return None;
        };
        fields
            .iter()
            .find(|f| f.name == field)?
            .resolved_ty
            .clone()
            .filter(|t| !t.is_unknown())
    }

    fn const_binding<'a>(&self, scopes: &'a ConstScopes, name: &str) -> Option<&'a Binding> {
        scopes.iter().rev().find_map(|scope| scope.get(name))
    }

    /// The binding a `let` of `value` takes when `value` is a place
    /// (identifier, `self`, or a field/index projection) rooted in a const
    /// binding: `Alias` at a derived shared-heap type, nothing (an ordinary
    /// mutable copy) at a derived primitive type -- primitives are copied on
    /// binding -- and `ConstAlias` when the type is not derivable here.
    fn const_alias(&self, value: &Expr, scopes: &ConstScopes) -> Option<Binding> {
        self.const_root(value, scopes)?;
        match self.const_place_type(value, scopes) {
            Some(ty) => is_shared_heap(&ty).then_some(Binding::Alias(ty)),
            None => Some(Binding::ConstAlias),
        }
    }

    /// The statically derivable type of a const binding: the annotation when it
    /// resolves, else a type derived from the initializer -- a record/variant
    /// literal, an array literal (a slice of its first derivable element type),
    /// or a free-function or static method call's declared return type.
    fn binding_const_type(
        &self,
        module: &[String],
        ty: &Option<TypeExpr>,
        value: &Expr,
    ) -> Option<Type> {
        if let Some(te) = ty
            && let Ok(t) = brass_hir::resolve(te, |n| self.nominal_info(module, n))
            && !t.is_unknown()
        {
            return Some(t);
        }
        self.value_type(module, value)
    }

    fn nominal_info(&self, module: &[String], name: &str) -> Option<NominalInfo> {
        let info = self.program.resolve_type(module, name)?;
        Some(match info.kind {
            TypeKind::Record { .. } => NominalInfo::record(info.id),
            TypeKind::Sum { .. } => NominalInfo::sum(info.id),
        })
    }

    /// A best-effort static type for an initializer expression. Only shapes
    /// whose type is directly derivable are covered; anything else is `None`
    /// (which keeps the binding conservative, not mutable).
    fn value_type(&self, module: &[String], value: &Expr) -> Option<Type> {
        match value {
            Expr::TypeLit(name, _, _) | Expr::VariantLit(name, _, _, _) => self
                .program
                .resolve_type(module, name)
                .map(TypeInfo::type_ref),
            // A literal array is a heap slice; its element type is taken from
            // the first element whose type is derivable, staying open otherwise
            // (the slice is still known to be heap data).
            Expr::Array(items, _) => {
                let elem = items
                    .iter()
                    .find_map(|e| self.value_type(module, e))
                    .unwrap_or(Type::Unknown(brass_hir::INFER_VAR));
                Some(Type::Slice(Box::new(elem)))
            }
            Expr::Call(callee, _, _) => match &**callee {
                Expr::Ident(fname, _) => self
                    .program
                    .resolve_function(module, fname)
                    .and_then(|f| f.signature.ret_ty.clone())
                    .filter(|t| !t.is_unknown()),
                // A static method call `T.new(...)`.
                Expr::Field(recv, m, _) => {
                    let Expr::Ident(tname, _) = &**recv else {
                        return None;
                    };
                    let info = self.program.resolve_type(module, tname)?;
                    type_method(info, m)?
                        .signature
                        .ret_ty
                        .clone()
                        .filter(|t| !t.is_unknown())
                }
                _ => None,
            },
            _ => None,
        }
    }
}

/// Look up a method by name on a record or any of a sum's variants.
fn type_method<'a>(info: &'a TypeInfo, method: &str) -> Option<&'a brass_hir::MethodInfo> {
    match &info.kind {
        TypeKind::Record { methods, .. } => methods.get(method),
        TypeKind::Sum { variants } => variants.iter().find_map(|v| v.methods.get(method)),
    }
}

/// A scope binding each parameter (and `self` for a method) so it shadows a
/// like-named global const. A `ref(T)` parameter is an immutable reference, so it
/// binds as const with its declared type (mutating through it, including via a
/// self-mutating method, is rejected); every other parameter binds as a mutable
/// local (it owns its copy, or is a `ref(mut(T))` mutable reference).
fn param_scope(params: &[brass_hir::ParamInfo], is_method: bool) -> HashMap<String, Binding> {
    let mut scope = HashMap::default();
    if is_method {
        scope.insert("self".to_string(), Binding::Mutable);
    }
    for p in params {
        let binding = if param_is_immutable_ref(p) {
            Binding::Const(p.resolved_ty.clone().filter(|t| !t.is_unknown()))
        } else {
            Binding::Mutable
        };
        scope.insert(p.name.clone(), binding);
    }
    scope
}

/// Whether a parameter may be mutated in the body. Two annotations forbid it:
/// `a: infer` receives a read-only deep copy, and
/// `a: ref(T)`/`self: ref(Self)` is an immutable reference. Everything else -- an
/// unannotated parameter (a private `mut` copy, or an inferred `ref(mut(Self))`
/// for `self`), a `mut(T)`/`ref(mut(T))`, `self: Self`/`mut(Self)`, or a bare
/// aggregate value -- may be mutated. Immutable references are reported by the
/// const path (they bind as const), so callers also skip them to avoid a
/// duplicate error.
fn param_permits_mutation(p: &ParamInfo) -> bool {
    !param_is_infer(p) && !param_is_immutable_ref(p)
}

/// Whether `block` (or any nested statement block) REBINDS `name` with a bare
/// `name = value` assignment. Distinct from `mutates_root`: a rebind of a
/// private copy never reaches the caller, so it forces no copy -- but a
/// read-only (`infer`) binding forbids it all the same. Lexical bindings in
/// blocks, patterns, and closure parameter lists hide the outer parameter.
fn rebinds(block: &Block, name: &str) -> bool {
    fn pat_binds(pat: &Pattern, name: &str) -> bool {
        pat.bound_names().contains(&name)
    }

    fn in_block(block: &Block, name: &str, mut shadowed: bool) -> bool {
        for stmt in &block.stmts {
            if in_stmt(stmt, name, shadowed) {
                return true;
            }
            if let Stmt::Let { pat, .. } = stmt
                && pat_binds(pat, name)
            {
                shadowed = true;
            }
        }
        false
    }

    fn in_stmt(stmt: &Stmt, name: &str, shadowed: bool) -> bool {
        match stmt {
            Stmt::Assign {
                target: Expr::Ident(n, _),
                ..
            } if !shadowed && n == name => true,
            Stmt::Assign { target, value, .. } => {
                in_expr(value, name, shadowed) || in_expr(target, name, shadowed)
            }
            Stmt::While { cond, body, .. } => {
                in_expr(cond, name, shadowed) || in_block(body, name, shadowed)
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                in_expr(iter, name, shadowed)
                    || in_block(body, name, shadowed || pat_binds(pat, name))
            }
            Stmt::Expr(e) | Stmt::Return(Some(e), _) => in_expr(e, name, shadowed),
            Stmt::Let { value, .. } => value
                .as_ref()
                .is_some_and(|value| in_expr(value, name, shadowed)),
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => false,
        }
    }

    fn in_expr(e: &Expr, name: &str, shadowed: bool) -> bool {
        match e {
            Expr::Unary(_, inner, _)
            | Expr::ErrorProp(inner, _)
            | Expr::Field(inner, _, _)
            | Expr::TypeTest(inner, _, _, _) => in_expr(inner, name, shadowed),
            Expr::Binary(_, left, right, _)
            | Expr::Index(left, right, _)
            | Expr::Range(left, right, _) => {
                in_expr(left, name, shadowed) || in_expr(right, name, shadowed)
            }
            Expr::Call(callee, args, _) => {
                in_expr(callee, name, shadowed)
                    || args.iter().any(|arg| in_expr(&arg.expr, name, shadowed))
            }
            Expr::Closure(params, body, _) => {
                let shadowed = shadowed || params.iter().any(|param| param.name == name);
                in_expr(body, name, shadowed)
            }
            Expr::Array(items, _) => items.iter().any(|item| in_expr(item, name, shadowed)),
            Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => fields
                .iter()
                .any(|(_, value)| in_expr(value, name, shadowed)),
            Expr::Str(segments, _) => segments.iter().any(|segment| match segment {
                StrSeg::Expr(inner) => in_expr(inner, name, shadowed),
                StrSeg::Lit(_) => false,
            }),
            Expr::If(cond, then, els, _) => {
                in_expr(cond, name, shadowed)
                    || in_block(then, name, shadowed)
                    || els
                        .as_deref()
                        .is_some_and(|els| in_expr(els, name, shadowed))
            }
            Expr::IfLet(pat, scrutinee, then, els, _) => {
                in_expr(scrutinee, name, shadowed)
                    || in_block(then, name, shadowed || pat_binds(pat, name))
                    || els
                        .as_deref()
                        .is_some_and(|els| in_expr(els, name, shadowed))
            }
            Expr::Match(scrutinee, arms, _) => {
                in_expr(scrutinee, name, shadowed)
                    || arms.iter().any(|arm| {
                        in_expr(&arm.body, name, shadowed || pat_binds(&arm.pattern, name))
                    })
            }
            Expr::Block(block, _) => in_block(block, name, shadowed),
            Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(_)
            | Expr::Ident(..)
            | Expr::SelfExpr(_) => false,
        }
    }

    in_block(block, name, false)
}
