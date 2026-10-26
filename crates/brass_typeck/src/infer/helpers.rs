//! Stateless helper functions shared across the checker: syntactic
//! predicates over the AST, the default types of numeric and pattern
//! literals, type-shape predicates and wrapper peeling, unknown-id scanning,
//! and substitution plumbing.

use super::*;

/// Free-function names the back ends implement without a user or prelude
/// definition (the engine's `Codegen::codegen_builtin` walk and the REPL's
/// `eval_builtin`). They are always legitimate value/callee names even when
/// the prelude is not loaded (for example in typeck unit tests), so
/// name resolution must not reject them. Keep this list in sync with both back
/// ends: a name listed here but implemented by neither passes the check and
/// then fails at run time.
pub(super) fn is_runtime_builtin_value(name: &str) -> bool {
    // The native-plugin dispatch family (`_plugin_call_i` etc., emitted by
    // the loader's synthesized plugin modules) is decoded by suffix.
    if brass_hir::plugin_builtin_return(name).is_some() {
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
            | "_flush"
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
    )
}

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
        TypeExpr::Anonymous(fs, _) => fs.iter().any(|(_, t, _)| contains_typeof(t)),
        TypeExpr::Refine(b, fs, _) => {
            contains_typeof(b) || fs.iter().any(|(_, t, _)| contains_typeof(t))
        }
        TypeExpr::Named(..) | TypeExpr::TypeSlot(..) | TypeExpr::SelfField(..) => false,
    }
}

/// Whether `ty` is a fully known primitive with no user fields or methods, so
/// a field or method access on it is a static error.
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

/// The value of a constant non-negative integer index (a tuple position), or
/// `None` if the index is not a literal.
pub(super) fn const_index(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Int(n, _) if *n >= 0 => i64::try_from(*n).ok(),
        _ => None,
    }
}

/// The numeric literal an expression's value is written as: the literal
/// itself (`0`, `-1`, `0.5`), or the trailing expression of a block
/// (`{ 0 }`), the way a branch of an `if`/`match` yields it. Branch joins let
/// such a value adapt like a literal operand.
pub(super) fn value_literal(expr: &Expr) -> Option<brass_typesys::NumericLiteral> {
    match expr {
        Expr::Block(block, _) => block_literal(block),
        other => brass_typesys::NumericLiteral::of_expr(other),
    }
}

/// The numeric literal a block's trailing expression is written as.
pub(super) fn block_literal(block: &Block) -> Option<brass_typesys::NumericLiteral> {
    match block.stmts.last() {
        Some(Stmt::Expr(expr)) => value_literal(expr),
        _ => None,
    }
}

/// The type an integer literal with this value takes on its own: its default
/// ([`brass_typesys::int_literal_kind`]). A value no integer type holds falls
/// back to `int64` so typing can continue; the full check reports it at the
/// literal.
pub(super) fn int_literal_type(value: i128) -> Type {
    Type::Int(brass_typesys::int_literal_kind(value).unwrap_or(IntKind::I64))
}

/// The default type of a numeric literal element, for classifying a bracket
/// literal as array vs tuple: an integer literal's default by value (see
/// [`int_literal_type`]), `float64` for a float literal.
pub(super) fn numeric_literal_repr(e: &Expr) -> Option<Type> {
    if let Some(value) = e.int_literal_value() {
        return Some(int_literal_type(value));
    }
    match e {
        Expr::Float(_, _) => Some(Type::Float(FloatKind::F64)),
        _ => None,
    }
}

/// Whether a (resolved) type is fully concrete: it contains no inference
/// variable, `Never`, or `Self` placeholder, so it can name a monomorphized
/// instance.
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
        Type::Record(n) | Type::Sum(n) => n.substitution.iter().all(|(_, ty)| is_concrete_type(ty)),
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

/// The type a literal pattern is written at on its own (an integer by its
/// value's default, a float as `float64`, `null` as `never?`); whether it can
/// match a scrutinee is [`literal_pattern_matches`]'s question. `None` for an
/// expression that is no literal.
pub(super) fn literal_pattern_type(expr: &Expr) -> Option<Type> {
    match expr {
        Expr::Int(v, _) => Some(int_literal_type(*v)),
        Expr::Float(..) => Some(Type::Float(FloatKind::F64)),
        Expr::Bool(..) => Some(Type::Bool),
        Expr::Str(..) => Some(Type::Str),
        Expr::Null(_) => Some(Type::null()),
        _ => None,
    }
}

/// Whether a literal pattern can match a value of type `scrutinee`. An
/// integer literal follows the flow rule (its value must fit the scrutinee's
/// integer type, so `-1` matches an `int64`); a float literal adapts to either
/// float width, as it does in an expression; a value literal against a
/// nullable scrutinee tests for a present value equal to it, so it is checked
/// against the element type.
pub(super) fn literal_pattern_matches(expr: &Expr, lit_ty: &Type, scrutinee: &Type) -> bool {
    match (expr, scrutinee) {
        (_, Type::Unknown(_)) => true,
        (Expr::Null(_), Type::Nullable(_) | Type::Never) => true,
        (Expr::Null(_), _) => false,
        (_, Type::Nullable(inner)) => literal_pattern_matches(expr, lit_ty, inner),
        (Expr::Int(..), Type::Int(_)) => integer_literal_fits(expr, scrutinee),
        (Expr::Float(v, _), Type::Float(FloatKind::F32)) => (*v as f32).is_finite(),
        _ => Subst::new().unify(lit_ty, scrutinee).is_ok(),
    }
}

/// Whether a callable whose return type is `ty` receives a propagated error:
/// a `Result`, a `Result?` (a body that also propagates a null), or a
/// still-open return.
pub(super) fn is_result_return_type(ty: &Type) -> bool {
    let ty = match ty {
        Type::Nullable(inner) => inner,
        other => other,
    };
    ty.is_unknown() || ty.is_result_type()
}

/// The first inference-variable id above every one the program's type and
/// function declarations already carry, so the checker's fresh variables
/// never alias a declaration's.
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

/// `ty` (a record or sum) with `substitution` as its substitution; any other
/// type, or an empty `substitution`, is returned unchanged.
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

/// `ty` (a nominal instance) with `entries` added to its substitution,
/// replacing the ones it already has: a literal's field types written over the
/// instance a refinement alias pins (whose slot entries the literal's own
/// substitution does not carry).
pub(super) fn overlay_nominal_substitution(ty: Type, entries: &Substitution) -> Type {
    match ty {
        Type::Record(mut n) => {
            for (key, t) in entries.iter() {
                n.substitution.insert(key, t.clone());
            }
            Type::Record(n)
        }
        other => other,
    }
}

/// The key of a field's entry in a nominal substitution: the field name, or
/// `Variant.field` for a sum variant's payload field.
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

/// `resolved` with each non-`self` parameter type and the return type taken
/// from the receiver instance's `substitution` where it has an entry for them
/// (`method.param` / `method.return` keys).
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

/// A parameter's resolved declared type, unless it is a bare inference
/// variable (an unannotated parameter).
pub(super) fn param_expected_type(param: &ParamInfo) -> Option<&Type> {
    param.resolved_ty.as_ref().filter(|ty| !ty.is_unknown())
}

/// Whether a parameter is nullable. A trailing run of nullable parameters is
/// optional at call sites: each omitted argument defaults to `null`. This is
/// how `assert(cond, msg: string?)` accepts both `assert(cond)` and
/// `assert(cond, "..")` without function overloading.
fn param_is_nullable(param: &ParamInfo) -> bool {
    matches!(param.resolved_ty, Some(Type::Nullable(_)))
        || matches!(param.ty, Some(TypeExpr::Nullable(..)))
}

/// Whether a parameter is the implicit caller-location: a trailing parameter
/// annotated with the prelude's `Location` record may be omitted at call
/// sites, and MIR fills it with the call site's position (`error(..)` and
/// `Result.context(..)` build error traces from it).
pub(super) fn param_is_location(program: &Program, param: &ParamInfo) -> bool {
    matches!(&param.resolved_ty, Some(Type::Record(n)) if program.is_prelude_type(n.id, "Location"))
}

/// The fewest arguments a call must supply: the parameter count minus the trailing
/// run of optional (nullable, or implicit-location) parameters.
pub(super) fn required_arg_count(program: &Program, params: &[ParamInfo]) -> usize {
    let optional = params
        .iter()
        .rev()
        .take_while(|p| param_is_nullable(p) || param_is_location(program, p))
        .count();
    params.len() - optional
}

/// Whether a value of this type may have a length and be indexed: an array,
/// a string, or a still-open type.
pub(super) fn is_maybe_indexable(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Array(..) | Type::Slice(..) | Type::Str | Type::Unknown(_)
    )
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

/// The compile-time truth of the presence test `if let <binding> = v` over a
/// value of type `ty`: false for the always-null `never?` (an absent member),
/// true for a fully known non-nullable value (the binding is irrefutable),
/// undecided for a nullable or still-open one. A reference or `mut`
/// parameter is tested through its value. The back end folds the same test
/// (its `__present` builtin) the same way.
pub(super) fn presence_binding_truth(ty: &Type) -> Option<bool> {
    match peel_ref_mut(ty) {
        Type::Nullable(inner) => matches!(**inner, Type::Never).then_some(false),
        Type::Unknown(_) | Type::Never => None,
        other => brass_hir::is_fully_known(other).then_some(true),
    }
}

/// Whether the block always returns: one of its own statements is a
/// `return` (a `return` nested in a branch does not count).
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

/// Whether lowering this statement can produce a MIR branch (a `CondBranch`
/// terminator) before control reaches the next statement. Used by the
/// structural if-probe (`Checker::then_branch_return_conflicts`), which
/// judges an arm only by a `return` reached through straight-line
/// statements: any branching statement before it leaves the arm live.
/// Conservative: `true` when unsure.
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
        // The test itself is a compile-time constant; only evaluating the
        // subject can branch.
        Expr::TypeTest(subject, _, _, _) => expr_may_branch(subject),
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

/// `x.pipe(f)` is `f(x)`: applies a function at the end of a method chain.
pub(super) trait Pipe: Sized {
    fn pipe<T>(self, f: impl FnOnce(Self) -> T) -> T {
        f(self)
    }
}
impl<T> Pipe for T {}

/// The diagnostic for a callable value applied to itself (`x(x)`), whose type
/// would have to contain itself: named after the callee when it is a plain
/// name, generic otherwise.
pub(super) fn infinite_application_message(callee: Option<&str>) -> String {
    match callee {
        Some(name) => format!("infinite type: `{name}` is applied to itself"),
        None => "infinite type: the callee is applied to itself".to_string(),
    }
}
