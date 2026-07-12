//! Const checking: a value bound with `const` cannot be
//! reassigned, nor can its fields/elements be mutated. Assignments whose root
//! place is a const binding are rejected. Calls to methods inferred to mutate
//! `self` are also rejected when their receiver is a const binding with a known
//! record type.

use std::collections::HashMap;

use prepoly_hir::{
    MutationInfo, NominalInfo, ParamInfo, Program, Type, TypeInfo, TypeKind, mutates_root,
    param_is_immutable_ref, param_is_infer, root_ident,
};
use prepoly_parser::ast::*;

use crate::TypeError;

/// A binding tracked for const checking. `Const` carries the binding's type
/// when it is statically derivable (from the annotation, the constructed
/// value, or a called function's return type), which is used to detect
/// mutating-method calls through field/element projections. `Fn` records a
/// local bound to a named free function (`let f = mutate`), so calls through
/// the alias resolve to the aliased function's write-through facts. `Mutable`
/// records a non-const `let` so that it shadows an outer const of the same
/// name, suppressing false positives on assignment to the inner binding.
#[derive(Clone)]
enum Binding {
    Const(Option<Type>),
    Fn(String),
    Mutable,
}

type ConstScopes = Vec<HashMap<String, Binding>>;

struct ConstChecker<'a> {
    program: &'a Program,
    /// Shared parameter-mutation facts: which free-function parameters and which
    /// methods' `self` the bodies mutate. Const checking uses this to reject
    /// passing a const value into a position the callee mutates through its
    /// reference (a `ref(mut(..))` parameter, an unannotated mutated parameter,
    /// or a mutating method on a const receiver).
    mutation: MutationInfo,
    /// The module whose body is currently being checked, so a bare callee name at
    /// a call site resolves to the same symbol the fixpoint keyed on.
    current_module: Vec<String>,
    errors: Vec<TypeError>,
}

pub fn check(program: &Program) -> Vec<TypeError> {
    let mut checker = ConstChecker {
        program,
        mutation: MutationInfo::analyze(program),
        current_module: Vec::new(),
        errors: Vec::new(),
    };
    checker.check_program();
    checker.errors
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

/// The nominal (record/sum) type name a value of `ty` dispatches methods on.
fn nominal_name(ty: &Type) -> Option<&str> {
    match peel(ty) {
        Type::Record(n) | Type::Sum(n) => Some(n.name()),
        _ => None,
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
    fn check_program(&mut self) {
        // Top-level consts are in scope for every body in the file, so function
        // and method bodies start from the module's global const bindings.
        let globals = self.global_consts();
        for f in self.program.functions.values() {
            // Parameters are mutable handles within their own body (mutating one is
            // the very thing that makes the parameter mutable to callers), and they
            // shadow any like-named global const. A `ref(T)` parameter is an
            // immutable reference, so it binds as const instead.
            let params = param_scope(&f.signature.params, false);
            self.current_module = f.module.clone();
            self.check_param_mutability(&f.signature.params, &f.decl.body);
            self.check_block(&f.decl.body, &mut vec![globals.clone(), params]);
        }
        for t in self.program.types.values() {
            let methods: Vec<&prepoly_hir::MethodInfo> = match &t.kind {
                TypeKind::Record { methods, .. } => methods.values().collect(),
                TypeKind::Sum { variants } => {
                    variants.iter().flat_map(|v| v.methods.values()).collect()
                }
            };
            for m in methods {
                if prepoly_hir::keyed_return(m.decl.ret.as_ref()) {
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
                self.check_block(body, &mut vec![globals.clone(), params]);
            }
        }
        // Top-level init statements build their scope up in order, so a global
        // is only visible to later top-level statements, not earlier ones.
        for init in &self.program.inits {
            self.current_module = init.path.clone();
            let mut scopes = vec![HashMap::new()];
            for stmt in &init.stmts {
                self.check_stmt(stmt, &mut scopes);
            }
        }
    }

    /// The top-level `const` bindings visible to every body in the file.
    /// A later top-level `let` that reuses a name shadows
    /// an earlier const, matching the order-sensitive init scope.
    fn global_consts(&self) -> HashMap<String, Binding> {
        let mut consts = HashMap::new();
        for init in &self.program.inits {
            for stmt in &init.stmts {
                let Stmt::Let {
                    pat: Pattern::Binding(name, _),
                    ty,
                    value: Some(value),
                    is_const,
                    ..
                } = stmt
                else {
                    continue;
                };
                if *is_const {
                    consts.insert(
                        name.clone(),
                        Binding::Const(self.binding_const_type(&init.path, ty, value)),
                    );
                } else {
                    consts.remove(name);
                }
            }
        }
        consts
    }

    fn check_block(&mut self, block: &Block, scopes: &mut ConstScopes) {
        scopes.push(HashMap::new());
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
                    if let Pattern::Binding(name, _) = pat
                        && let Some(top) = scopes.last_mut()
                    {
                        top.insert(name.clone(), Binding::Mutable);
                    }
                    return;
                };
                self.check_expr(value, scopes);
                if let Pattern::Binding(name, _) = pat {
                    let alias = self.const_alias_type(value, scopes);
                    let fn_alias = self.fn_value_symbol(value, scopes);
                    let module = self.current_module.clone();
                    if let Some(top) = scopes.last_mut() {
                        let binding = if *is_const {
                            Binding::Const(self.binding_const_type(&module, ty, value))
                        } else if let Some(ty) = alias {
                            // Aliasing a const heap value binds another handle to
                            // the same shared value, so constness propagates. The
                            // runtime shares heap objects by reference, hence the
                            // alias is also immutable.
                            Binding::Const(ty)
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
            Stmt::Assign { target, span, .. } => {
                self.check_expr(target, scopes);
                if let Some(root) = root_ident(target)
                    && matches!(self.const_binding(scopes, root), Some(Binding::Const(_)))
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
                let mut frame = HashMap::new();
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
            Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) => self.check_expr(inner, scopes),
            Expr::Binary(_, left, right, _) | Expr::Range(left, right, _) => {
                self.check_expr(left, scopes);
                self.check_expr(right, scopes);
            }
            Expr::Call(callee, args, span) => {
                self.check_mutating_const_call(callee, *span, scopes);
                self.check_const_args_to_mutating_fn(callee, args, scopes);
                self.check_const_args_to_mutating_method(callee, args, scopes);
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
            Expr::Closure(_, body, _) => self.check_expr(body, scopes),
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
            Expr::If(cond, then, els, _) => {
                self.check_expr(cond, scopes);
                self.check_block(then, scopes);
                if let Some(els) = els {
                    self.check_expr(els, scopes);
                }
            }
            Expr::IfLet(_, scrutinee, then, els, _) => {
                self.check_expr(scrutinee, scopes);
                self.check_block(then, scopes);
                if let Some(els) = els {
                    self.check_expr(els, scopes);
                }
            }
            Expr::Match(scrutinee, arms, _) => {
                self.check_expr(scrutinee, scopes);
                for arm in arms {
                    self.check_expr(&arm.body, scopes);
                }
            }
            Expr::Block(block, _) => self.check_block(block, scopes),
            Expr::Int(..)
            | Expr::Float(..)
            | Expr::Str(..)
            | Expr::Bool(..)
            | Expr::Null(_)
            | Expr::Ident(..)
            | Expr::SelfExpr(_) => {}
        }
    }

    fn check_mutating_const_call(
        &mut self,
        callee: &Expr,
        span: prepoly_parser::Span,
        scopes: &ConstScopes,
    ) {
        let Expr::Field(receiver, method, _) = callee else {
            return;
        };
        let place_ty = self.const_place_type(receiver, scopes);
        let nominal = place_ty.as_ref().and_then(|t| nominal_name(t));
        // A built-in growable-array mutator (`push`/`insert`/`remove`/`pop`) on a
        // const array -- or an array reachable from a const struct/sum/tuple root --
        // modifies a value declared immutable, so it is rejected. The receiver is a
        // const place that is not a user nominal type (records/sums whose own
        // methods are checked via the mutation facts below have a type name).
        if matches!(method.as_str(), "push" | "insert" | "remove" | "pop")
            && nominal.is_none()
            && let Some(root) = self.const_root(receiver, scopes)
        {
            self.errors.push(TypeError {
                message: format!("cannot call mutating method `{method}` on const value `{root}`"),
                span,
            });
            return;
        }
        // The receiver may be a nested projection of a const value
        // (e.g. `o.inner.bump()` or `arr[0].bump()`); a mutating method on any
        // place reachable from a const root is rejected (propagation).
        let Some(type_name) = nominal else {
            return;
        };
        if self.mutation.method_writes_through_self(type_name, method) {
            let root = root_ident(receiver).unwrap_or("");
            self.errors.push(TypeError {
                message: format!("cannot call mutating method `{method}` on const value `{root}`"),
                span,
            });
        }
    }

    /// The const binding a place is rooted in (its root identifier), or `None`
    /// when the root is not const. Unlike `const_place_type` this does not require
    /// the place's type to be known, so it also covers const arrays/tuples whose
    /// element types could not be derived.
    fn const_root<'a>(&self, place: &'a Expr, scopes: &ConstScopes) -> Option<&'a str> {
        let root = root_ident(place)?;
        match self.const_binding(scopes, root) {
            Some(Binding::Const(_)) => Some(root),
            _ => None,
        }
    }

    /// Reject mutating a parameter whose type forbids it. An `a: infer` parameter
    /// receives a read-only deep copy, so mutating it through its reference is
    /// rejected here. The other read-only case -- an immutable `ref(T)` parameter
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
    /// Any const-rooted place qualifies (records, sums, arrays, tuples) -- a
    /// primitive parameter is never marked mutable (it cannot be mutated through a
    /// reference), so this does not reject a copied `const` primitive argument.
    ///
    /// Covers three shapes: a direct call to a write-through function (by name or
    /// through a `let f = mutate` fn alias), and a higher-order call that passes a
    /// write-through function alongside the const it will be applied to
    /// (`apply(mutate, o)` with `fun apply(f, v) { f(v) }`).
    fn check_const_args_to_mutating_fn(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        scopes: &ConstScopes,
    ) {
        let Expr::Ident(fname, _) = callee else {
            return;
        };
        let Some(symbol) = self.callee_fn_symbol(fname, scopes) else {
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
        // against the arguments it will receive.
        let Some(calls) = self.mutation.param_calls(&symbol) else {
            return;
        };
        let mut hof_errors = Vec::new();
        for pc in calls {
            let Some(fn_arg) = args.get(pc.fn_param) else {
                continue;
            };
            let Expr::Ident(gname, _) = &fn_arg.expr else {
                continue;
            };
            let Some(gsym) = self.callee_fn_symbol(gname, scopes) else {
                continue;
            };
            let Some(g_indices) = self.mutation.write_through_params(&gsym) else {
                continue;
            };
            for k in g_indices {
                let Some(j) = pc.args.get(*k).copied().flatten() else {
                    continue;
                };
                if let Some(arg) = args.get(j)
                    && let Some(root) = self.const_root(&arg.expr, scopes)
                {
                    hof_errors.push(TypeError {
                        message: format!(
                            "cannot pass const value `{root}` to `{fname}`, which passes it to `{gname}` requiring a mutable parameter"
                        ),
                        span: arg.expr.span(),
                    });
                }
            }
        }
        self.errors.extend(hof_errors);
    }

    /// Reject passing a const-rooted value into a method argument position that
    /// writes through. The receiver's type is generally unknown here (it may be
    /// any expression), so positions are matched by method name across all types
    /// -- conservative in the same way as the fixpoint's forwarding step.
    fn check_const_args_to_mutating_method(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        scopes: &ConstScopes,
    ) {
        let Expr::Field(_, method, _) = callee else {
            return;
        };
        let indices = self.mutation.method_write_through_args_by_name(method);
        if indices.is_empty() {
            return;
        }
        for (i, arg) in args.iter().enumerate() {
            if indices.contains(&i)
                && let Some(root) = self.const_root(&arg.expr, scopes)
            {
                self.errors.push(TypeError {
                    message: format!(
                        "cannot pass const value `{root}` to method `{method}`, which requires a mutable parameter"
                    ),
                    span: arg.expr.span(),
                });
            }
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

    /// The type under which `value` aliases const heap data, if it does: a
    /// place (identifier, `self`, or a field/index projection) rooted in a
    /// const binding whose derived type is a shared heap aggregate. Primitives
    /// are copied on binding, and a place whose type could not be derived stays
    /// conservative (no alias), matching the previous behavior for untyped
    /// consts.
    fn const_alias_type(&self, value: &Expr, scopes: &ConstScopes) -> Option<Option<Type>> {
        self.const_root(value, scopes)?;
        let ty = self.const_place_type(value, scopes)?;
        is_shared_heap(&ty).then_some(Some(ty))
    }

    /// The statically derivable type of a const binding: the annotation when it
    /// resolves, else a type derived from the initializer -- a record/variant
    /// literal, an array literal (a slice of its first derivable element type),
    /// a free-function call's declared/inferred return type, or a static method
    /// call's return type.
    fn binding_const_type(
        &self,
        module: &[String],
        ty: &Option<TypeExpr>,
        value: &Expr,
    ) -> Option<Type> {
        if let Some(te) = ty
            && let Ok(t) = prepoly_hir::resolve(te, |n| self.nominal_info(module, n))
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
                    .unwrap_or(Type::Unknown(prepoly_hir::INFER_VAR));
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
fn type_method<'a>(info: &'a TypeInfo, method: &str) -> Option<&'a prepoly_hir::MethodInfo> {
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
fn param_scope(params: &[prepoly_hir::ParamInfo], is_method: bool) -> HashMap<String, Binding> {
    let mut scope = HashMap::new();
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

/// Whether a parameter may be mutated through its reference in the body. Two
/// annotations forbid it: `a: infer` receives a read-only deep copy, and
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
/// read-only (`infer`) binding forbids it all the same. Shadowing `let`s are
/// not rebinding and closures rebind their own capture, so neither is counted.
fn rebinds(block: &Block, name: &str) -> bool {
    fn in_stmt(stmt: &Stmt, name: &str) -> bool {
        match stmt {
            Stmt::Assign {
                target: Expr::Ident(n, _),
                ..
            } if n == name => true,
            Stmt::While { body, .. } | Stmt::For { body, .. } => {
                body.stmts.iter().any(|s| in_stmt(s, name))
            }
            Stmt::Expr(e) | Stmt::Return(Some(e), _) | Stmt::Assign { value: e, .. } => {
                in_expr(e, name)
            }
            Stmt::Let { value, .. } => value.as_ref().is_some_and(|v| in_expr(v, name)),
            _ => false,
        }
    }
    fn in_expr(e: &Expr, name: &str) -> bool {
        match e {
            Expr::If(_, then, els, _) => {
                then.stmts.iter().any(|s| in_stmt(s, name))
                    || els.as_deref().is_some_and(|e| in_expr(e, name))
            }
            Expr::IfLet(_, _, then, els, _) => {
                then.stmts.iter().any(|s| in_stmt(s, name))
                    || els.as_deref().is_some_and(|e| in_expr(e, name))
            }
            Expr::Match(_, arms, _) => arms.iter().any(|a| in_expr(&a.body, name)),
            Expr::Block(b, _) => b.stmts.iter().any(|s| in_stmt(s, name)),
            _ => false,
        }
    }
    block.stmts.iter().any(|s| in_stmt(s, name))
}
