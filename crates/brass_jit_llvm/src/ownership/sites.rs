//! Spawn-site shapes: classifying a `spawn(..)` statement's argument, extracting a
//! spawned closure's body, resolving a spawned variable to the closure literals
//! bound to it, and the spans that identify statements across the rewrite.

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use brass_parser::Span;
use brass_parser::ast::*;

use super::analysis::param_names;
use super::scopes::nested_block_stmts;

/// The argument shape of a `spawn(..)` statement.
pub(super) enum SpawnArg<'a> {
    /// `spawn(() -> ...)`: the closure literal itself.
    Literal,
    /// `spawn(name)`: a variable that must resolve to a closure literal bound in
    /// the same function scope.
    Var(&'a str, Span),
    /// Anything else (a parameter, a field, a call result): not analyzable.
    Opaque(Span),
}

/// If `stmt` is a `spawn(..)` call statement (as an expression statement or a
/// `let` initializer), classify its argument shape.
pub(super) fn spawn_arg(stmt: &Stmt) -> Option<SpawnArg<'_>> {
    let expr = match stmt {
        Stmt::Expr(e) => e,
        Stmt::Let {
            value: Some(value), ..
        } => value,
        _ => return None,
    };
    let Expr::Call(callee, args, span) = expr else {
        return None;
    };
    if !matches!(&**callee, Expr::Ident(n, _) if n == "spawn") {
        return None;
    }
    Some(match args.first().map(|a| &a.expr) {
        Some(Expr::Closure(..)) => SpawnArg::Literal,
        Some(Expr::Ident(name, ispan)) => SpawnArg::Var(name, *ispan),
        Some(other) => SpawnArg::Opaque(other.span()),
        None => SpawnArg::Opaque(*span),
    })
}

/// If `stmt` is a `spawn(<closure literal>)` statement, return the closure body
/// as a block.
pub(super) fn spawn_closure_body(stmt: &Stmt) -> Option<Block> {
    let expr = match stmt {
        Stmt::Expr(e) => e,
        Stmt::Let {
            value: Some(value), ..
        } => value,
        _ => return None,
    };
    let Expr::Call(callee, args, _) = expr else {
        return None;
    };
    if !matches!(&**callee, Expr::Ident(n, _) if n == "spawn") {
        return None;
    }
    let Expr::Closure(_, body, _) = &args.first()?.expr else {
        return None;
    };
    Some(closure_block(body))
}

pub(super) fn closure_bound_in(stmt: &Stmt) -> HashSet<String> {
    let expr = match stmt {
        Stmt::Expr(e) | Stmt::Let { value: Some(e), .. } => e,
        _ => return HashSet::default(),
    };
    if let Expr::Call(_, args, _) = expr
        && let Some(Expr::Closure(params, _, _)) = args.first().map(|a| &a.expr)
    {
        return param_names(params);
    }
    HashSet::default()
}

pub(super) fn closure_block(body: &Expr) -> Block {
    match body {
        Expr::Block(b, _) => b.clone(),
        expr => Block {
            stmts: vec![Stmt::Expr(expr.clone())],
            span: expr.span(),
        },
    }
}

pub(super) fn stmts_reference(stmts: &[Stmt], var: &str) -> bool {
    let mut refs = HashSet::default();
    crate::closure::idents_stmts(stmts, &mut refs);
    refs.contains(var)
}

/// A closure literal bound to a spawned variable: its parameters, its body as a
/// block, and the span of the binding statement.
#[derive(Clone)]
pub(super) struct ClosureBinding {
    pub(super) params: Vec<Param>,
    pub(super) body: Block,
    pub(super) span: Span,
}

/// The closure literals `name` may hold at the spawn site `target` (empty when
/// it holds no closure literal there). Bindings are applied in source order and
/// nested statement scopes receive an environment copy, so declarations in a
/// sibling or later scope cannot satisfy the spawn.
pub(super) fn closure_bindings_at(stmts: &[Stmt], target: Span, name: &str) -> Vec<ClosureBinding> {
    let mut env: HashMap<String, Vec<ClosureBinding>> = HashMap::default();
    find_spawn_bindings_stmts(stmts, target, name, &mut env).unwrap_or_default()
}

/// Closure-valued declarations selected by actual `spawn(name)` sites in this
/// scope, resolved with source-order and nested-scope visibility.
pub(super) fn spawned_binding_spans(stmts: &[Stmt]) -> HashSet<Span> {
    let mut spans = HashSet::default();
    each_spawn_site(stmts, &mut |stmt| {
        if let Some(SpawnArg::Var(name, _)) = spawn_arg(stmt) {
            spans.extend(
                closure_bindings_at(stmts, spawn_stmt_span(stmt), name)
                    .into_iter()
                    .map(|binding| binding.span),
            );
        }
    });
    spans
}

fn find_spawn_bindings_stmts(
    stmts: &[Stmt],
    target: Span,
    name: &str,
    env: &mut HashMap<String, Vec<ClosureBinding>>,
) -> Option<Vec<ClosureBinding>> {
    for stmt in stmts {
        if spawn_stmt_span(stmt) == target
            && matches!(spawn_arg(stmt), Some(SpawnArg::Var(found, _)) if found == name)
        {
            return Some(env.get(name).cloned().unwrap_or_default());
        }
        if let Some(found) = find_spawn_bindings_stmt_exprs(stmt, target, name, env) {
            return Some(found);
        }
        if let Stmt::Let { pat, value, .. } = stmt {
            let closure = match (pat, value) {
                (Pattern::Binding(binding, _, _), Some(Expr::Closure(params, body, _))) => Some((
                    binding.clone(),
                    vec![ClosureBinding {
                        params: params.clone(),
                        body: closure_block(body),
                        span: stmt_span(stmt),
                    }],
                )),
                (Pattern::Binding(binding, _, _), _) => Some((binding.clone(), Vec::new())),
                _ => None,
            };
            if let Some((binding, values)) = closure {
                env.insert(binding, values);
            }
            if !matches!(pat, Pattern::Binding(..)) {
                for binding in pat.bound_names() {
                    env.insert(binding.to_string(), Vec::new());
                }
            }
        } else if let Stmt::Assign {
            target: Expr::Ident(binding, _),
            value,
            ..
        } = stmt
        {
            let values = match value {
                Expr::Closure(params, body, _) => vec![ClosureBinding {
                    params: params.clone(),
                    body: closure_block(body),
                    span: stmt_span(stmt),
                }],
                _ => Vec::new(),
            };
            env.insert(binding.clone(), values);
        }
    }
    None
}

fn find_spawn_bindings_stmt_exprs(
    stmt: &Stmt,
    target: Span,
    name: &str,
    env: &HashMap<String, Vec<ClosureBinding>>,
) -> Option<Vec<ClosureBinding>> {
    match stmt {
        Stmt::Let {
            value: Some(value), ..
        }
        | Stmt::Expr(value)
        | Stmt::Return(Some(value), _) => find_spawn_bindings_expr(value, target, name, env),
        Stmt::Assign {
            target: lhs, value, ..
        } => find_spawn_bindings_expr(lhs, target, name, env)
            .or_else(|| find_spawn_bindings_expr(value, target, name, env)),
        Stmt::While { cond, body, .. } => find_spawn_bindings_expr(cond, target, name, env)
            .or_else(|| {
                let mut inner = env.clone();
                find_spawn_bindings_stmts(&body.stmts, target, name, &mut inner)
            }),
        Stmt::For {
            pat, iter, body, ..
        } => find_spawn_bindings_expr(iter, target, name, env).or_else(|| {
            let mut inner = env.clone();
            for binding in pat.bound_names() {
                inner.insert(binding.to_string(), Vec::new());
            }
            find_spawn_bindings_stmts(&body.stmts, target, name, &mut inner)
        }),
        Stmt::Let { value: None, .. }
        | Stmt::Return(None, _)
        | Stmt::Break(_)
        | Stmt::Continue(_) => None,
    }
}

fn find_spawn_bindings_expr(
    expr: &Expr,
    target: Span,
    name: &str,
    env: &HashMap<String, Vec<ClosureBinding>>,
) -> Option<Vec<ClosureBinding>> {
    let find = |expr| find_spawn_bindings_expr(expr, target, name, env);
    match expr {
        Expr::Unary(_, inner, _) | Expr::Field(inner, _, _) | Expr::ErrorProp(inner, _) => {
            find(inner)
        }
        Expr::Binary(_, left, right, _)
        | Expr::Index(left, right, _)
        | Expr::Range(left, right, _) => find(left).or_else(|| find(right)),
        Expr::Call(callee, args, _) => find(callee).or_else(|| {
            args.iter()
                .find_map(|arg| find_spawn_bindings_expr(&arg.expr, target, name, env))
        }),
        Expr::Array(items, _) => items.iter().find_map(find),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            fields.iter().find_map(|(_, value)| find(value))
        }
        Expr::Str(segments, _) => segments.iter().find_map(|segment| match segment {
            StrSeg::Expr(value) => find(value),
            StrSeg::Lit(_) => None,
        }),
        Expr::If(cond, then, els, _) => find(cond)
            .or_else(|| {
                let mut inner = env.clone();
                find_spawn_bindings_stmts(&then.stmts, target, name, &mut inner)
            })
            .or_else(|| els.as_deref().and_then(find)),
        Expr::IfLet(pat, scrutinee, then, els, _) => find(scrutinee)
            .or_else(|| {
                let mut inner = env.clone();
                for binding in pat.bound_names() {
                    inner.insert(binding.to_string(), Vec::new());
                }
                find_spawn_bindings_stmts(&then.stmts, target, name, &mut inner)
            })
            .or_else(|| els.as_deref().and_then(find)),
        Expr::Match(scrutinee, arms, _) => find(scrutinee).or_else(|| {
            arms.iter().find_map(|arm| {
                let mut inner = env.clone();
                for binding in arm.pattern.bound_names() {
                    inner.insert(binding.to_string(), Vec::new());
                }
                match &arm.body {
                    Expr::Block(block, _) => {
                        find_spawn_bindings_stmts(&block.stmts, target, name, &mut inner)
                    }
                    body => find_spawn_bindings_expr(body, target, name, &inner),
                }
            })
        }),
        Expr::Block(block, _) => {
            let mut inner = env.clone();
            find_spawn_bindings_stmts(&block.stmts, target, name, &mut inner)
        }
        Expr::TypeTest(subject, _, _, _) => find(subject),
        Expr::Closure(..)
        | Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => None,
    }
}

pub(super) fn each_spawn_site(stmts: &[Stmt], f: &mut impl FnMut(&Stmt)) {
    for stmt in stmts {
        if spawn_arg(stmt).is_some() {
            f(stmt);
        }
        nested_block_stmts(stmt, &mut |inner| each_spawn_site(inner, f));
    }
}

/// The span of a statement: its identity across the analyses and the rewrite,
/// and the span of a synthesized wrapping `with`.
pub(super) fn stmt_span(stmt: &Stmt) -> Span {
    match stmt {
        Stmt::Let { span, .. } | Stmt::Assign { span, .. } => *span,
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => e.span(),
        Stmt::While { cond, .. } => cond.span(),
        Stmt::For { iter, .. } => iter.span(),
        Stmt::Return(None, span) | Stmt::Break(span) | Stmt::Continue(span) => *span,
    }
}

/// The span of a spawn statement's call: the key that identifies the spawn site
/// across the analyses, and the span of its synthesized promotion statements
/// (cosmetic there: these builtins do not fail).
pub(super) fn spawn_stmt_span(stmt: &Stmt) -> Span {
    match stmt {
        Stmt::Expr(e) | Stmt::Let { value: Some(e), .. } => e.span(),
        _ => Span::new(0, 0),
    }
}
