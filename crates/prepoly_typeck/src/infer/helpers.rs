//! Stateless helper functions shared across the checker: syntactic
//! predicates over the AST, type-shape predicates and wrapper peeling,
//! unknown-id scanning, and substitution plumbing.

use super::*;

/// Free-function names the runtime resolves without a user or stdlib
/// definition (mirrors `prepoly_runtime::builtins::builtin_function`). They are
/// always legitimate value/callee names even when the standard library is not
/// loaded (for example in typeck unit tests), so name resolution must not
/// reject them. Keep this list in sync with the runtime dispatcher.
pub(super) fn is_runtime_builtin_value(name: &str) -> bool {
    // The native-plugin dispatch family (`_plugin_call_i` etc., emitted by
    // the loader's synthesized plugin modules) is decoded by suffix.
    if prepoly_hir::plugin_builtin_return(name).is_some() {
        return true;
    }
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
            | "_print_str"
            | "_println_str"
            | "_stdin_read"
            | "_argv"
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
/// Whether a type annotation contains a `typeof(v)` node (so its resolved type
/// must be recorded for the back end rather than re-derived scope-free).
pub(super) fn contains_typeof(te: &TypeExpr) -> bool {
    match te {
        TypeExpr::TypeOf(..) => true,
        TypeExpr::Nullable(i, _)
        | TypeExpr::Array(i, _, _)
        | TypeExpr::Fallible(i, _)
        | TypeExpr::Mut(i, _)
        | TypeExpr::Ref(i, _) => contains_typeof(i),
        TypeExpr::Tuple(es, _) => es.iter().any(contains_typeof),
        TypeExpr::Fun(ps, r, _) => ps.iter().any(contains_typeof) || contains_typeof(r),
        TypeExpr::Anonymous(fs, _) => fs.iter().any(|(_, t)| contains_typeof(t)),
        TypeExpr::Refine(b, fs, _) => {
            contains_typeof(b) || fs.iter().any(|(_, t)| contains_typeof(t))
        }
        TypeExpr::Named(..) | TypeExpr::TypeSlot(..) | TypeExpr::SelfField(..) => false,
    }
}

pub(super) fn is_concrete_primitive(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Int(_) | Type::Float(_) | Type::Bool | Type::Str | Type::Void
    )
}

/// Whether two types are records (or sums) of the same declared nominal -- so
/// unifying them only reconciles their shared field types (pinning one's open
/// fields from the other) rather than relating unrelated types.
pub(super) fn same_nominal_instance(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Record(x), Type::Record(y)) | (Type::Sum(x), Type::Sum(y)) => {
            x.id == y.id && (x.id >= 0 || x.name == y.name)
        }
        _ => false,
    }
}

/// Whether a (resolved) type is fully concrete: it contains no inference
/// variable, `Never`, or `Self` placeholder, so it can name a monomorphized
/// instance.
/// The value of a constant non-negative integer index (a tuple position), or
/// `None` if the index is not a literal.
pub(super) fn const_index(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Int(n, _) if *n >= 0 => Some(*n),
        _ => None,
    }
}

/// The default concrete type of a numeric literal element, for classifying a
/// bracket literal as array vs tuple (an int literal is `int32`, a float `float64`).
pub(super) fn numeric_literal_repr(e: &Expr) -> Option<Type> {
    match e {
        Expr::Int(v, _) => Some(Type::Int(int_literal_kind(*v))),
        Expr::Float(_, _) => Some(Type::Float(FloatKind::F64)),
        _ => None,
    }
}

pub(super) fn is_concrete_type(ty: &Type) -> bool {
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
pub(super) fn peel_ref_mut(ty: &Type) -> &Type {
    match ty {
        Type::Ref(inner) | Type::Mut(inner) => peel_ref_mut(inner),
        other => other,
    }
}

/// Peel `const`/`mut`/`ref` value wrappers to reach the underlying value type.
pub(super) fn peel_value_wrappers(ty: &Type) -> &Type {
    match ty {
        Type::ConstOf(inner) | Type::Mut(inner) | Type::Ref(inner) => peel_value_wrappers(inner),
        other => other,
    }
}

pub(super) fn literal_pattern_type(expr: &Expr) -> Option<Type> {
    match expr {
        Expr::Int(v, _) => Some(Type::Int(int_literal_kind(*v))),
        Expr::Float(..) => Some(Type::Float(FloatKind::F64)),
        Expr::Bool(..) => Some(Type::Bool),
        Expr::Str(..) => Some(Type::Str),
        Expr::Null(_) => Some(Type::null()),
        _ => None,
    }
}

pub(super) fn literal_pattern_matches(expr: &Expr, lit_ty: &Type, scrutinee: &Type) -> bool {
    match (expr, scrutinee) {
        (_, Type::Unknown(_)) => true,
        (Expr::Int(..), Type::Int(_)) => integer_literal_fits(expr, scrutinee),
        (Expr::Null(_), Type::Nullable(_) | Type::Never) => true,
        _ => Subst::new().unify(lit_ty, scrutinee).is_ok(),
    }
}

pub(super) fn is_result_return_type(ty: &Type) -> bool {
    // A `Result<..>?` return (a body that also propagates a null) still
    // receives propagated errors.
    let ty = match ty {
        Type::Nullable(inner) => inner,
        other => other,
    };
    ty.is_unknown() || ty.is_result_type()
}

pub(super) fn next_unknown_after_program(program: &Program) -> u32 {
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

pub(super) fn apply_nominal_substitution(ty: Type, substitution: Substitution) -> Type {
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

pub(super) fn field_substitution_key(variant: Option<&str>, field: &str) -> String {
    variant
        .map(|variant| format!("{variant}.{field}"))
        .unwrap_or_else(|| field.to_string())
}

/// Replace every `Type::SelfType` in `ty` with `replacement` (the concrete type
/// `Self` denotes), recursing through composite types. Lets a field or parameter
/// type written with `Self` -- e.g. a closure-typed field `(self, T) -> U` -- be
/// checked against the actual type when a value of that type is constructed.
pub(super) fn substitute_self(ty: &Type, replacement: &Type) -> Type {
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

pub(super) fn method_param_substitution_key(method: &str, param: &str) -> String {
    format!("{method}.{param}")
}

pub(super) fn method_return_substitution_key(method: &str) -> String {
    format!("{method}.return")
}

pub(super) fn apply_method_substitution(
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

pub(super) fn param_expected_type(param: &ParamInfo) -> Option<&Type> {
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
pub(super) fn required_arg_count(params: &[ParamInfo]) -> usize {
    let optional = params
        .iter()
        .rev()
        .take_while(|p| param_is_nullable(p))
        .count();
    params.len() - optional
}

pub(super) fn env_from_scopes(scopes: &ScopeStack) -> HashMap<String, Type> {
    let mut env = HashMap::new();
    for scope in scopes {
        for (name, ty) in scope {
            env.insert(name.clone(), ty.clone());
        }
    }
    env
}

pub(super) fn is_maybe_indexable(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Array(..) | Type::Slice(..) | Type::Str | Type::Unknown(_)
    )
}

pub(super) fn int_fits_kind(value: i64, kind: IntKind) -> bool {
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

pub(super) fn assign_binop(op: AssignOp) -> BinOp {
    match op {
        AssignOp::Eq => unreachable!("plain assignment is not a binary operator"),
        AssignOp::Add => BinOp::Add,
        AssignOp::Sub => BinOp::Sub,
        AssignOp::Mul => BinOp::Mul,
        AssignOp::Div => BinOp::Div,
        AssignOp::Rem => BinOp::Rem,
    }
}

pub(super) fn is_null_comparison(op: BinOp, left: &Type, right: &Type) -> bool {
    matches!(op, BinOp::Eq | BinOp::Ne) && (left.is_null() || right.is_null())
}

pub(super) fn is_self_expr(expr: &Expr) -> bool {
    match expr {
        Expr::SelfExpr(_) => true,
        Expr::Ident(name, _) => name == "self",
        _ => false,
    }
}

pub(super) fn block_always_returns(block: &Block) -> bool {
    block.stmts.iter().any(|s| matches!(s, Stmt::Return(..)))
}

/// Whether an `else` arm always returns: a braced block that does, or an
/// `else if` whose own arms all do. Any other expression (a value the `if`
/// yields) does not return.
pub(super) fn expr_always_returns(e: &Expr) -> bool {
    match e {
        Expr::Block(b, _) => block_always_returns(b),
        Expr::If(_, then, els, _) => {
            block_always_returns(then) && els.as_deref().is_some_and(expr_always_returns)
        }
        _ => false,
    }
}

/// Names assigned (rebound) anywhere inside a closure literal of `b`. A closure
/// captures such a binding by reference, so any call made while the binding is
/// narrowed non-null can run the closure and re-null it; the narrowing pass
/// treats these names like globals and re-widens them after calls. Shadowing is
/// not tracked (a closure-local `let` of the same name over-approximates),
/// which only re-widens more than strictly needed -- never less.
pub(super) fn closure_write_targets_block(b: &Block) -> HashSet<String> {
    let mut acc = HashSet::new();
    for s in &b.stmts {
        collect_closure_writes_stmt(s, false, &mut acc);
    }
    acc
}

/// Whether `block` (transitively, ignoring nested closures' parameter lists)
/// re-binds `var` -- a `let`, a `for` variable, or a pattern binding of that
/// name. Used to reject shadowing of a fields-loop variable, which is
/// substituted textually into the expanded copies.
pub(super) fn block_rebinds(block: &Block, var: &str) -> bool {
    fn pat_binds(pat: &Pattern, var: &str) -> bool {
        match pat {
            Pattern::Binding(n, _) => n == var,
            Pattern::Array(ps, _) => ps.iter().any(|p| pat_binds(p, var)),
            Pattern::Record(_, fields, _) => fields.iter().any(|f| match &f.pat {
                Some(p) => pat_binds(p, var),
                None => f.name == var,
            }),
            _ => false,
        }
    }
    fn expr_rebinds(e: &Expr, var: &str) -> bool {
        match e {
            Expr::IfLet(pat, _, then, els, _) => {
                pat_binds(pat, var)
                    || block_rebinds(then, var)
                    || els.as_ref().is_some_and(|e| expr_rebinds(e, var))
            }
            Expr::If(_, then, els, _) => {
                block_rebinds(then, var) || els.as_ref().is_some_and(|e| expr_rebinds(e, var))
            }
            Expr::Match(_, arms, _) => arms
                .iter()
                .any(|a| pat_binds(&a.pattern, var) || expr_rebinds(&a.body, var)),
            Expr::Block(b, _) => block_rebinds(b, var),
            Expr::Closure(params, body, _) => {
                params.iter().any(|p| p.name == var) || expr_rebinds(body, var)
            }
            _ => false,
        }
    }
    block.stmts.iter().any(|stmt| match stmt {
        Stmt::Let { pat, value, .. } => {
            pat_binds(pat, var) || value.as_ref().is_some_and(|v| expr_rebinds(v, var))
        }
        Stmt::For { pat, body: b, .. } => pat.bound_names().contains(&var) || block_rebinds(b, var),
        Stmt::While { body: b, .. } => block_rebinds(b, var),
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => expr_rebinds(e, var),
        Stmt::Assign { value, .. } => expr_rebinds(value, var),
        _ => false,
    })
}

pub(super) fn collect_closure_writes_stmt(
    stmt: &Stmt,
    in_closure: bool,
    acc: &mut HashSet<String>,
) {
    match stmt {
        Stmt::Let {
            value: Some(value), ..
        } => collect_closure_writes_expr(value, in_closure, acc),
        Stmt::Let { value: None, .. } => {}
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
pub(super) fn stmt_may_branch(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Let { value, .. } => value.as_ref().is_some_and(expr_may_branch),
        Stmt::Assign { target, value, .. } => expr_may_branch(target) || expr_may_branch(value),
        Stmt::Expr(e) => expr_may_branch(e),
        Stmt::While { .. } | Stmt::For { .. } => true,
        Stmt::Return(..) | Stmt::Break(_) | Stmt::Continue(_) => true,
    }
}

/// Whether evaluating this expression can produce a MIR branch. Short-circuit
/// operators, `expr!` propagation and every conditional construct lower through
/// a `CondBranch`; a closure literal does not (its body is a separate function).
pub(super) fn expr_may_branch(e: &Expr) -> bool {
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

pub(super) trait Pipe: Sized {
    fn pipe<T>(self, f: impl FnOnce(Self) -> T) -> T {
        f(self)
    }
}
impl<T> Pipe for T {}
