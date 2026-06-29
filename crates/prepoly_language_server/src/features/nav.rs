//! Shared helpers for the position-driven features (hover, go-to-definition):
//! finding the identifier under the cursor, finding the tightest typed
//! expression at an offset, and turning a global span into an LSP `Location`.

use std::collections::{HashMap, HashSet};

use prepoly_hir::{FunInfo, Type, TypedExpr, TypedExprKind};
use prepoly_lexer::{Span, TokenKind, lex};
use prepoly_parser::ast::{
    Block, Expr, Member, Module, Param, Pattern, Stmt, StrSeg, TopLevel, TypeBody,
};
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
pub fn smallest_typed_at(full: &FullAnalysis, global_off: usize) -> Option<&TypedExpr> {
    full.typed
        .expressions
        .iter()
        .filter(|e| global_off >= e.span.lo && global_off <= e.span.hi)
        .min_by_key(|e| e.span.hi - e.span.lo)
}

/// Turn a global span into a `Location`, resolving the file it lives in through
/// the analysis source map. Returns `None` for a span in the embedded prelude
/// (it has no file to open).
pub fn locate(full: &FullAnalysis, span: Span) -> Option<Location> {
    let (path, src, lo_local) = full.sources.locate(span.lo)?;
    let path = path?;
    let hi_local = lo_local + span.hi.saturating_sub(span.lo);
    let index = LineIndex::new(src);
    let range = index.range_of(src, lo_local, hi_local);
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
                    TypeBody::Sum(_) => continue,
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

/// The inferred type of the local variable `name` whose declaration or use is at
/// `global_off`. The type checker records expression nodes (variable *uses*) but
/// not binding sites, so a hover on a `let`, parameter, for-loop, or pattern
/// binding finds nothing under the cursor directly; this recovers the type from
/// the bound value, or from a use of the variable in the same function.
pub fn local_var_type(full: &FullAnalysis, global_off: usize, name: &str) -> Option<Type> {
    let (_, body) = enclosing(&full.main_ast, global_off)?;
    // Precise: the cursor is on a `let name = value` binding -> the value's type.
    if let Some(value_span) = let_value_span(body, global_off, name)
        && let Some(e) = full.typed.expressions.iter().find(|e| e.span == value_span)
    {
        return Some(e.ty.clone());
    }
    // Otherwise borrow the type from a use of the name in this function -- the
    // case for parameters, for-loop variables, and pattern bindings, which have
    // no bound value expression. Prefer the nearest use at or after the cursor,
    // so hovering a pattern binding picks the use in that same match arm rather
    // than a same-named binding in another arm.
    let mut uses: Vec<&TypedExpr> = full
        .typed
        .expressions
        .iter()
        .filter(|e| {
            matches!(&e.kind, TypedExprKind::Ident(n) if n == name) && within(body.span, e.span)
        })
        .collect();
    uses.sort_by_key(|e| e.span.lo);
    let after = uses.iter().find(|e| e.span.lo >= global_off);
    after.or_else(|| uses.last()).map(|e| e.ty.clone())
}

/// Span of the value expression of a `let name = value` whose binding identifier
/// contains `off`, searching nested blocks (loop/if/match/closure bodies).
fn let_value_span(block: &Block, off: usize, name: &str) -> Option<Span> {
    block
        .stmts
        .iter()
        .find_map(|s| let_value_in_stmt(s, off, name))
}

fn let_value_in_stmt(s: &Stmt, off: usize, name: &str) -> Option<Span> {
    match s {
        Stmt::Let { pat, value, .. } => {
            if let Pattern::Binding(n, bspan) = pat
                && n == name
                && contains(*bspan, off)
            {
                return Some(value.span());
            }
            let_value_in_expr(value, off, name)
        }
        Stmt::Assign { value, .. } => let_value_in_expr(value, off, name),
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => let_value_in_expr(e, off, name),
        Stmt::While { body, .. } | Stmt::For { body, .. } => let_value_span(body, off, name),
        _ => None,
    }
}

fn let_value_in_expr(e: &Expr, off: usize, name: &str) -> Option<Span> {
    match e {
        Expr::Block(b, _) => let_value_span(b, off, name),
        Expr::If(_, then, els, _) | Expr::IfLet(_, _, then, els, _) => {
            let_value_span(then, off, name)
                .or_else(|| els.as_ref().and_then(|e| let_value_in_expr(e, off, name)))
        }
        Expr::Match(_, arms, _) => arms
            .iter()
            .find_map(|a| let_value_in_expr(&a.body, off, name)),
        Expr::Closure(_, body, _) => let_value_in_expr(body, off, name),
        _ => None,
    }
}

/// The inferred return type of free function `name`, recovered from its call
/// sites. The signature table only records the syntactic return annotation, so
/// an unannotated return reads as absent there even though inference knows it.
/// Each `name(...)` call's typed result type *is* that return type, so this
/// returns the type all call sites agree on, or `None` when there are no calls
/// or they disagree (a genuinely polymorphic return that has no single type).
pub fn inferred_return(full: &FullAnalysis, name: &str) -> Option<Type> {
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
        .find(|e| e.span == span)
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
        if let Expr::Call(_, args, span) = e
            && *span == call_span
        {
            result = Some(args.iter().map(|a| arg_type(full, a.expr.span())).collect());
        }
    };
    walk_exprs(&full.main_ast, &mut visit);
    result
}

fn arg_type(full: &FullAnalysis, span: Span) -> Type {
    full.typed
        .expressions
        .iter()
        .find(|e| e.span == span)
        .map(|e| e.ty.clone())
        .unwrap_or(Type::Unknown(u32::MAX))
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
    let mut vars = HashSet::new();
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
        Stmt::Let { value, .. } => walk_expr(value, visit),
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
        _ => {}
    }
}
