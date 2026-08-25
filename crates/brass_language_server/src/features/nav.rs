//! Shared helpers for the position-driven features (hover, go-to-definition):
//! finding the identifier under the cursor, finding the tightest typed
//! expression at an offset, and turning a global span into an LSP `Location`.

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use brass_hir::{FunInfo, Type, TypedExpr, TypedExprKind};
use brass_parser::ast::{
    Block, Expr, Member, Module, Param, Pattern, Stmt, StrSeg, TopLevel, TypeBody,
};
use brass_parser::{Span, TokenKind, lex};
use tower_lsp_server::ls_types::{Location, Uri};

use crate::analysis::FullAnalysis;
use crate::document::LineIndex;

/// The identifier token containing document-local offset `off`, as
/// `(name, local span)`. Used to know what symbol the cursor is on.
pub fn ident_at(text: &str, off: usize) -> Option<(String, Span)> {
    let toks = lex(text).ok()?;
    toks.into_iter().find_map(|t| match t.kind {
        TokenKind::Ident(name) if off >= t.span.lo && off <= t.span.hi => Some((name, t.span)),
        _ => None,
    })
}

/// The smallest typed expression whose global span contains `global_off`.
/// Checker-only method-receiver evidence is excluded: it shares the enclosing
/// call's span, so it would tie with (and, recorded first, win over) the call's
/// own result entry. Same-span ties keep recording order -- the FIRST entry is
/// the generic view, which is what hover shows for a generic body (unlike
/// member resolution, see [`receiver_type_at`]).
pub fn smallest_typed_at(full: &FullAnalysis, global_off: usize) -> Option<&TypedExpr> {
    full.typed
        .expressions
        .iter()
        .filter(|e| {
            global_off >= e.span.lo
                && global_off <= e.span.hi
                && !matches!(e.kind, TypedExprKind::MethodReceiver)
        })
        .min_by_key(|e| e.span.hi - e.span.lo)
}

/// The inferred type of the receiver expression ending at global offset `hi`
/// (just before a `.`): the widest such expression, so `foo.bar.` uses
/// `foo.bar` rather than `bar`. Method-receiver evidence is excluded here too:
/// the checker records it under the whole call's span, so after
/// `re.find(x).` it would answer with `re`'s type instead of the call's
/// result. Same-span ties prefer the resolved entry (a closure body checked
/// open and re-checked at its observed instantiation records both).
/// Shared by completion, hover, and go-to-definition.
pub fn receiver_type_at(full: &FullAnalysis, hi: usize) -> Option<Type> {
    full.typed
        .expressions
        .iter()
        .filter(|e| e.span.hi == hi && !matches!(e.kind, TypedExprKind::MethodReceiver))
        .min_by_key(|e| (e.span.lo, !brass_hir::is_fully_known(&e.ty)))
        .map(|e| e.ty.clone())
}

/// Turn a global span into a `Location`, resolving the file it lives in through
/// the analysis source map. Returns `None` for a span in the embedded prelude
/// (it has no file to open).
pub fn locate(full: &FullAnalysis, span: Span) -> Option<Location> {
    let loc = full.sources.locate(span.lo)?;
    let path = loc.path?;
    let hi_local = loc.local + span.hi.saturating_sub(span.lo);
    let index = LineIndex::new(loc.src);
    let range = index.range_of(loc.src, loc.local, hi_local);
    let uri = Uri::from_file_path(path)?;
    Some(Location { uri, range })
}

pub fn contains(span: Span, off: usize) -> bool {
    off >= span.lo && off <= span.hi
}

fn within(outer: Span, inner: Span) -> bool {
    inner.lo >= outer.lo && inner.hi <= outer.hi
}

/// The parameters and body of the function or method whose declaration (its
/// signature *and* body) contains `global_off`. Including the signature lets a
/// cursor on a parameter resolve to that function, so a parameter's inferred
/// type can be recovered from its uses.
pub fn enclosing(main_ast: &Module, global_off: usize) -> Option<(Vec<&Param>, &Block)> {
    for item in &main_ast.items {
        match item {
            TopLevel::Fun(f) if contains(f.span, global_off) => {
                return Some((f.params.iter().collect(), &f.body));
            }
            TopLevel::Type(t) => {
                let members = match &t.body {
                    TypeBody::Record(members) => members,
                    TypeBody::Sum(_) | TypeBody::Alias(_) => continue,
                };
                for m in members {
                    if let Member::Method(method) = m
                        && let Some(body) = &method.body
                        && contains(method.span, global_off)
                    {
                        return Some((method.params.iter().collect(), body));
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// One lexical binding visible at a cursor. `value_span` is present only for a
/// direct `let name = value`, whose initializer supplies the declaration hover
/// type even when the binding is unused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalBinding {
    pub span: Span,
    value_span: Option<Span>,
}

/// Resolve `name` along the lexical scope path containing `global_off`.
/// Bindings from closed sibling blocks, other match arms, and completed
/// closures are never added to the path.
pub fn local_binding(main_ast: &Module, global_off: usize, name: &str) -> Option<LocalBinding> {
    let (params, body) = enclosing(main_ast, global_off)?;
    let mut visible: Vec<(String, LocalBinding)> = params
        .into_iter()
        .map(|param| {
            (
                param.name.clone(),
                LocalBinding {
                    span: param.span,
                    value_span: None,
                },
            )
        })
        .collect();
    resolve_block_binding(body, global_off, name, &mut visible)
}

fn current_binding(visible: &[(String, LocalBinding)], name: &str) -> Option<LocalBinding> {
    visible
        .iter()
        .rev()
        .find_map(|(binding_name, binding)| (binding_name == name).then_some(*binding))
}

fn resolve_block_binding(
    block: &Block,
    off: usize,
    name: &str,
    visible: &mut Vec<(String, LocalBinding)>,
) -> Option<LocalBinding> {
    for stmt in &block.stmts {
        if contains(stmt.span(), off) {
            return resolve_stmt_binding(stmt, off, name, visible);
        }
        if stmt.span().hi <= off
            && let Stmt::Let { pat, value, .. } = stmt
        {
            let direct_value = match pat {
                Pattern::Binding(_, _) => value.as_ref().map(Expr::span),
                _ => None,
            };
            push_pattern_bindings(pat, direct_value, visible);
        }
    }
    current_binding(visible, name)
}

fn resolve_stmt_binding(
    stmt: &Stmt,
    off: usize,
    name: &str,
    visible: &[(String, LocalBinding)],
) -> Option<LocalBinding> {
    match stmt {
        Stmt::Let { pat, value, .. } => {
            let direct_value = match pat {
                Pattern::Binding(_, _) => value.as_ref().map(Expr::span),
                _ => None,
            };
            binding_in_pattern(pat, off, name, direct_value).or_else(|| {
                value
                    .as_ref()
                    .filter(|expr| contains(expr.span(), off))
                    .and_then(|expr| resolve_expr_binding(expr, off, name, visible))
                    .or_else(|| current_binding(visible, name))
            })
        }
        Stmt::Assign { target, value, .. } => [target, value]
            .into_iter()
            .find(|expr| contains(expr.span(), off))
            .and_then(|expr| resolve_expr_binding(expr, off, name, visible))
            .or_else(|| current_binding(visible, name)),
        Stmt::Expr(expr) | Stmt::Return(Some(expr), _) => {
            resolve_expr_binding(expr, off, name, visible)
        }
        Stmt::While { cond, body, .. } => {
            if contains(cond.span(), off) {
                resolve_expr_binding(cond, off, name, visible)
            } else if contains(body.span, off) {
                let mut nested = visible.to_vec();
                resolve_block_binding(body, off, name, &mut nested)
            } else {
                current_binding(visible, name)
            }
        }
        Stmt::For {
            pat, iter, body, ..
        } => {
            if let Some(binding) = binding_in_pattern(pat, off, name, None) {
                return Some(binding);
            }
            if contains(iter.span(), off) {
                return resolve_expr_binding(iter, off, name, visible);
            }
            if contains(body.span, off) {
                let mut nested = visible.to_vec();
                push_pattern_bindings(pat, None, &mut nested);
                return resolve_block_binding(body, off, name, &mut nested);
            }
            current_binding(visible, name)
        }
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {
            current_binding(visible, name)
        }
    }
}

fn resolve_expr_binding(
    expr: &Expr,
    off: usize,
    name: &str,
    visible: &[(String, LocalBinding)],
) -> Option<LocalBinding> {
    let child = |expr: &Expr| {
        contains(expr.span(), off).then(|| resolve_expr_binding(expr, off, name, visible))
    };
    match expr {
        Expr::Closure(params, body, _) => {
            if let Some(param) = params
                .iter()
                .find(|param| param.name == name && contains(param.span, off))
            {
                return Some(LocalBinding {
                    span: param.span,
                    value_span: None,
                });
            }
            if contains(body.span(), off) {
                let mut nested = visible.to_vec();
                nested.extend(params.iter().map(|param| {
                    (
                        param.name.clone(),
                        LocalBinding {
                            span: param.span,
                            value_span: None,
                        },
                    )
                }));
                resolve_expr_binding(body, off, name, &nested)
            } else {
                current_binding(visible, name)
            }
        }
        Expr::Block(block, _) => {
            let mut nested = visible.to_vec();
            resolve_block_binding(block, off, name, &mut nested)
        }
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) => child(inner).flatten(),
        Expr::Binary(_, left, right, _)
        | Expr::Index(left, right, _)
        | Expr::Range(left, right, _) => child(left)
            .or_else(|| child(right))
            .flatten()
            .or_else(|| current_binding(visible, name)),
        Expr::Call(callee, args, _) => child(callee)
            .or_else(|| {
                args.iter()
                    .find(|arg| contains(arg.expr.span(), off))
                    .map(|arg| resolve_expr_binding(&arg.expr, off, name, visible))
            })
            .flatten()
            .or_else(|| current_binding(visible, name)),
        Expr::Field(receiver, _, _) | Expr::TypeTest(receiver, _, _) => child(receiver)
            .flatten()
            .or_else(|| current_binding(visible, name)),
        Expr::Array(elements, _) => elements
            .iter()
            .find(|element| contains(element.span(), off))
            .and_then(|element| resolve_expr_binding(element, off, name, visible))
            .or_else(|| current_binding(visible, name)),
        Expr::Str(segments, _) => segments
            .iter()
            .filter_map(|segment| match segment {
                StrSeg::Expr(expr) if contains(expr.span(), off) => Some(expr.as_ref()),
                _ => None,
            })
            .find_map(|expr| resolve_expr_binding(expr, off, name, visible))
            .or_else(|| current_binding(visible, name)),
        Expr::If(cond, then, alternative, _) => {
            if contains(cond.span(), off) {
                return resolve_expr_binding(cond, off, name, visible);
            }
            if contains(then.span, off) {
                let mut nested = visible.to_vec();
                return resolve_block_binding(then, off, name, &mut nested);
            }
            alternative
                .as_ref()
                .filter(|expr| contains(expr.span(), off))
                .and_then(|expr| resolve_expr_binding(expr, off, name, visible))
                .or_else(|| current_binding(visible, name))
        }
        Expr::IfLet(pat, scrutinee, then, alternative, _) => {
            if let Some(binding) = binding_in_pattern(pat, off, name, None) {
                return Some(binding);
            }
            if contains(scrutinee.span(), off) {
                return resolve_expr_binding(scrutinee, off, name, visible);
            }
            if contains(then.span, off) {
                let mut nested = visible.to_vec();
                push_pattern_bindings(pat, None, &mut nested);
                return resolve_block_binding(then, off, name, &mut nested);
            }
            alternative
                .as_ref()
                .filter(|expr| contains(expr.span(), off))
                .and_then(|expr| resolve_expr_binding(expr, off, name, visible))
                .or_else(|| current_binding(visible, name))
        }
        Expr::Match(scrutinee, arms, _) => {
            if contains(scrutinee.span(), off) {
                return resolve_expr_binding(scrutinee, off, name, visible);
            }
            let Some(arm) = arms.iter().find(|arm| contains(arm.span, off)) else {
                return current_binding(visible, name);
            };
            if let Some(binding) = binding_in_pattern(&arm.pattern, off, name, None) {
                return Some(binding);
            }
            let mut nested = visible.to_vec();
            push_pattern_bindings(&arm.pattern, None, &mut nested);
            resolve_expr_binding(&arm.body, off, name, &nested)
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => fields
            .iter()
            .find(|(_, value)| contains(value.span(), off))
            .and_then(|(_, value)| resolve_expr_binding(value, off, name, visible))
            .or_else(|| current_binding(visible, name)),
        Expr::Ident(_, _)
        | Expr::Int(_, _)
        | Expr::Float(_, _)
        | Expr::Bool(_, _)
        | Expr::Null(_)
        | Expr::SelfExpr(_) => current_binding(visible, name),
    }
}

fn binding_in_pattern(
    pattern: &Pattern,
    off: usize,
    name: &str,
    value_span: Option<Span>,
) -> Option<LocalBinding> {
    match pattern {
        Pattern::Binding(binding_name, span) => (binding_name == name && contains(*span, off))
            .then_some(LocalBinding {
                span: *span,
                value_span,
            }),
        Pattern::Record(_, fields, _) => fields.iter().find_map(|field| match &field.pat {
            Some(pattern) => binding_in_pattern(pattern, off, name, None),
            None => (field.name == name && contains(field.span, off)).then_some(LocalBinding {
                span: field.span,
                value_span: None,
            }),
        }),
        Pattern::Array(patterns, _) => patterns
            .iter()
            .find_map(|pattern| binding_in_pattern(pattern, off, name, None)),
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => None,
    }
}

fn push_pattern_bindings(
    pattern: &Pattern,
    value_span: Option<Span>,
    visible: &mut Vec<(String, LocalBinding)>,
) {
    match pattern {
        Pattern::Binding(name, span) => visible.push((
            name.clone(),
            LocalBinding {
                span: *span,
                value_span,
            },
        )),
        Pattern::Record(_, fields, _) => fields.iter().for_each(|field| match &field.pat {
            Some(pattern) => push_pattern_bindings(pattern, None, visible),
            None => visible.push((
                field.name.clone(),
                LocalBinding {
                    span: field.span,
                    value_span: None,
                },
            )),
        }),
        Pattern::Array(patterns, _) => patterns
            .iter()
            .for_each(|pattern| push_pattern_bindings(pattern, None, visible)),
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
    }
}

/// The inferred type of the local variable `name` whose declaration or use is at
/// `global_off`. The type checker records expression nodes (variable *uses*) but
/// not binding sites, so a hover on a `let`, parameter, for-loop, or pattern
/// binding finds nothing under the cursor directly; this recovers the type from
/// the bound value, or from a use of the variable in the same function.
pub fn local_var_type(full: &FullAnalysis, global_off: usize, name: &str) -> Option<Type> {
    let binding = local_binding(&full.main_ast, global_off, name)?;
    if let Some(value_span) = binding.value_span
        && let Some(e) = source_expr_at(full, value_span)
    {
        return Some(e.ty.clone());
    }
    // Binding sites are absent from the typed sidecar. Borrow a use only when
    // resolving that use through the AST reaches this exact binding, excluding
    // same-named bindings in sibling scopes and later closures.
    let mut uses: Vec<&TypedExpr> = full
        .typed
        .expressions
        .iter()
        .filter(|e| {
            matches!(&e.kind, TypedExprKind::Ident(n) if n == name)
                && local_binding(&full.main_ast, e.span.lo, name)
                    .is_some_and(|candidate| candidate.span == binding.span)
        })
        .collect();
    uses.sort_by_key(|e| e.span.lo);
    let after = uses.iter().find(|e| e.span.lo >= global_off);
    after.or_else(|| uses.last()).map(|e| e.ty.clone())
}

/// The inferred return type of a free function whose return is unannotated.
///
/// The checker's own answer is preferred, when it settled on a concrete type.
/// Failing that, the type is recovered from the call sites in the file being
/// edited: each `name(...)` call's typed result *is* the return type, so this
/// takes the one they all agree on, and `None` when they disagree (a genuinely
/// polymorphic return has no single type to show). That fallback is all there
/// used to be, and it can only work while the open file happens to CALL the
/// function -- open the module that DEFINES it and there is nothing to read,
/// which is why `http`'s `fetch` rendered as `unknown` in its own file.
pub fn inferred_return(full: &FullAnalysis, symbol: &str, name: &str) -> Option<Type> {
    if let Some(ty) = full.function_returns.get(symbol)
        && brass_hir::is_fully_known(ty)
    {
        return Some(ty.clone());
    }
    let mut call_spans: Vec<Span> = Vec::new();
    let mut visit = |e: &Expr| {
        if let Expr::Call(callee, _, span) = e
            && let Expr::Ident(n, _) = callee.as_ref()
            && n == name
        {
            call_spans.push(*span);
        }
    };
    walk_exprs(&full.main_ast, &mut visit);

    let mut ret: Option<Type> = None;
    for span in call_spans {
        let Some(e) = full
            .typed
            .expressions
            .iter()
            .find(|e| e.span == span && matches!(e.kind, TypedExprKind::Call))
        else {
            continue;
        };
        match &ret {
            None => ret = Some(e.ty.clone()),
            Some(t) if t != &e.ty => return None,
            _ => {}
        }
    }
    ret
}

/// The generic type of parameter `name` (function body `body_span`), recovered
/// from the first recorded use of the parameter in the body. The body is checked
/// generically before any call-site monomorphization, so the first recording
/// carries the inference variables of the function's general type (e.g. a
/// `for`-iterated parameter shows as `T[]`), not a concrete instance.
pub fn generic_param_type(full: &FullAnalysis, body_span: Span, name: &str) -> Option<Type> {
    full.typed
        .expressions
        .iter()
        .find(|e| {
            matches!(&e.kind, TypedExprKind::Ident(n) if n == name) && within(body_span, e.span)
        })
        .map(|e| e.ty.clone())
}

/// The generic return type of `f`, from the first recorded `return` expression
/// in its body. Used to show a param-dependent return as a variable (`-> T`); a
/// fallible/wrapped return type is not visible here and comes from the call site
/// (see [`inferred_return`]).
pub fn generic_return_type(full: &FullAnalysis, f: &FunInfo) -> Option<Type> {
    let span = first_return_value_span(&f.decl.body)?;
    full.typed
        .expressions
        .iter()
        .find(|e| e.span == span && !matches!(e.kind, TypedExprKind::MethodReceiver))
        .map(|e| e.ty.clone())
}

fn first_return_value_span(block: &Block) -> Option<Span> {
    block.stmts.iter().find_map(return_value_in_stmt)
}

fn return_value_in_stmt(s: &Stmt) -> Option<Span> {
    match s {
        Stmt::Return(Some(e), _) => Some(e.span()),
        Stmt::While { body, .. } | Stmt::For { body, .. } => first_return_value_span(body),
        Stmt::Expr(e) => return_value_in_expr(e),
        _ => None,
    }
}

fn return_value_in_expr(e: &Expr) -> Option<Span> {
    match e {
        Expr::If(_, then, els, _) | Expr::IfLet(_, _, then, els, _) => {
            first_return_value_span(then)
                .or_else(|| els.as_ref().and_then(|x| return_value_in_expr(x)))
        }
        Expr::Match(_, arms, _) => arms.iter().find_map(|a| return_value_in_expr(&a.body)),
        Expr::Block(b, _) => first_return_value_span(b),
        _ => None,
    }
}

/// The concrete argument types of the call expression whose whole span is
/// `call_span`, for binding a function's generic type variables to the specific
/// call instance under the cursor (rather than an arbitrary one).
pub fn call_args_at_span(full: &FullAnalysis, call_span: Span) -> Option<Vec<Type>> {
    let mut result = None;
    let mut visit = |e: &Expr| {
        if result.is_some() {
            return;
        }
        if let Expr::Call(callee, args, span) = e
            && *span == call_span
        {
            let mut types = Vec::new();
            // A method/UFCS call `recv.f(args)` passes `recv` as the first
            // argument (`f`'s first parameter), so include the receiver's type
            // before the explicit arguments -- otherwise the arguments map to the
            // wrong parameters and the receiver-typed first parameter (e.g.
            // `slice`'s `arr: infer[]`) is never bound.
            if let Expr::Field(recv, _, _) = callee.as_ref() {
                types.push(arg_type(full, recv.span()));
            }
            types.extend(args.iter().map(|a| arg_type(full, a.expr.span())));
            result = Some(types);
        }
    };
    walk_exprs(&full.main_ast, &mut visit);
    result
}

fn arg_type(full: &FullAnalysis, span: Span) -> Type {
    source_expr_at(full, span)
        .map(|e| e.ty.clone())
        .unwrap_or(Type::Unknown(u32::MAX))
}

/// The source expression at `span`, excluding checker-only method-receiver
/// evidence that intentionally uses the enclosing call's span.
fn source_expr_at(full: &FullAnalysis, span: Span) -> Option<&TypedExpr> {
    full.typed
        .expressions
        .iter()
        .find(|e| e.span == span && !matches!(e.kind, TypedExprKind::MethodReceiver))
}

/// Bind the inference variables of a `generic` type to the corresponding parts
/// of a `concrete` type, accumulating `variable id -> concrete type`. Transparent
/// wrappers (`?`/`const`/`mut`/`ref`) on either side are peeled first.
pub fn collect_bindings(generic: &Type, concrete: &Type, out: &mut HashMap<u32, Type>) {
    let g = peel_transparent(generic);
    let c = peel_transparent(concrete);
    match (g, c) {
        (Type::Unknown(id), _) => {
            out.entry(*id).or_insert_with(|| c.clone());
        }
        (Type::Array(g, _) | Type::Slice(g), Type::Array(c, _) | Type::Slice(c)) => {
            collect_bindings(g, c, out);
        }
        (Type::Tuple(gs), Type::Tuple(cs)) => {
            gs.iter()
                .zip(cs)
                .for_each(|(g, c)| collect_bindings(g, c, out));
        }
        (Type::Fun(gps, gr), Type::Fun(cps, cr)) => {
            gps.iter()
                .zip(cps)
                .for_each(|(g, c)| collect_bindings(g, c, out));
            collect_bindings(gr, cr, out);
        }
        _ => {}
    }
}

/// The inference variable ids occurring anywhere in `ty`.
pub fn free_vars(ty: &Type) -> HashSet<u32> {
    let mut vars = HashSet::default();
    fn go(ty: &Type, vars: &mut HashSet<u32>) {
        match ty {
            Type::Unknown(id) => {
                vars.insert(*id);
            }
            Type::Array(t, _)
            | Type::Slice(t)
            | Type::Nullable(t)
            | Type::ConstOf(t)
            | Type::Mut(t)
            | Type::Ref(t) => go(t, vars),
            Type::Tuple(ts) => ts.iter().for_each(|t| go(t, vars)),
            Type::Fun(ps, r) => {
                ps.iter().for_each(|p| go(p, vars));
                go(r, vars);
            }
            Type::Record(n) | Type::Sum(n) => n.substitution.iter().for_each(|(_, t)| go(t, vars)),
            _ => {}
        }
    }
    go(ty, &mut vars);
    vars
}

fn peel_transparent(ty: &Type) -> &Type {
    match ty {
        Type::Nullable(t) | Type::ConstOf(t) | Type::Mut(t) | Type::Ref(t) => peel_transparent(t),
        other => other,
    }
}

/// Visit every expression in the module (pre-order), for span-based lookups.
pub fn walk_exprs(main_ast: &Module, visit: &mut impl FnMut(&Expr)) {
    for item in &main_ast.items {
        match item {
            TopLevel::Fun(func) => walk_block(&func.body, visit),
            TopLevel::Type(t) => {
                let members = match &t.body {
                    TypeBody::Record(members) => members.as_slice(),
                    TypeBody::Sum(variants) => {
                        for v in variants {
                            for m in &v.members {
                                if let Member::Method(method) = m
                                    && let Some(b) = &method.body
                                {
                                    walk_block(b, visit);
                                }
                            }
                        }
                        continue;
                    }
                    TypeBody::Alias(_) => continue,
                };
                for m in members {
                    if let Member::Method(method) = m
                        && let Some(b) = &method.body
                    {
                        walk_block(b, visit);
                    }
                }
            }
            TopLevel::Stmt(s) => walk_stmt(s, visit),
        }
    }
}

fn walk_block(b: &Block, visit: &mut impl FnMut(&Expr)) {
    for s in &b.stmts {
        walk_stmt(s, visit);
    }
}

fn walk_stmt(s: &Stmt, visit: &mut impl FnMut(&Expr)) {
    match s {
        Stmt::Let {
            value: Some(value), ..
        } => walk_expr(value, visit),
        Stmt::Let { value: None, .. } => {}
        Stmt::Assign { target, value, .. } => {
            walk_expr(target, visit);
            walk_expr(value, visit);
        }
        Stmt::Expr(e) => walk_expr(e, visit),
        Stmt::While { cond, body, .. } => {
            walk_expr(cond, visit);
            walk_block(body, visit);
        }
        Stmt::For { iter, body, .. } => {
            walk_expr(iter, visit);
            walk_block(body, visit);
        }
        Stmt::Return(Some(e), _) => walk_expr(e, visit),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

fn walk_expr(e: &Expr, visit: &mut impl FnMut(&Expr)) {
    visit(e);
    match e {
        Expr::Unary(_, e, _) | Expr::ErrorProp(e, _) | Expr::Field(e, _, _) => walk_expr(e, visit),
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) => {
            walk_expr(a, visit);
            walk_expr(b, visit);
        }
        Expr::Call(callee, args, _) => {
            walk_expr(callee, visit);
            for arg in args {
                walk_expr(&arg.expr, visit);
            }
        }
        Expr::Closure(_, body, _) => walk_expr(body, visit),
        Expr::Array(elems, _) => {
            for e in elems {
                walk_expr(e, visit);
            }
        }
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(e) = seg {
                    walk_expr(e, visit);
                }
            }
        }
        Expr::If(cond, then, els, _) => {
            walk_expr(cond, visit);
            walk_block(then, visit);
            if let Some(e) = els {
                walk_expr(e, visit);
            }
        }
        Expr::IfLet(_, scrut, then, els, _) => {
            walk_expr(scrut, visit);
            walk_block(then, visit);
            if let Some(e) = els {
                walk_expr(e, visit);
            }
        }
        Expr::Match(scrut, arms, _) => {
            walk_expr(scrut, visit);
            for arm in arms {
                walk_expr(&arm.body, visit);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, v) in fields {
                walk_expr(v, visit);
            }
        }
        Expr::Block(b, _) => walk_block(b, visit),
        Expr::TypeTest(subject, _, _) => walk_expr(subject, visit),
        _ => {}
    }
}
