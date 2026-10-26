//! Access guarding: the map from each handle to the cown roots whose locks guard
//! it, and the rewrite that wraps every access through a guarded handle in a lock
//! acquisition (`with`, or `_with_all` for a group of roots).

use fxhash::FxHashSet as HashSet;
use std::collections::{BTreeMap, BTreeSet};

use brass_parser::Span;
use brass_parser::ast::*;

use super::analysis::{captured, param_names, root_ident};
use super::scopes::nested_block_stmts;
use super::sites::{closure_block, stmt_span};

/// Build the handle -> lock-roots map for a scope: each cown guards itself, and
/// every binding whose initializer mentions a known handle inherits (the union
/// of) the mentioned handles' roots, iterated to fixpoint so chains (`let a =
/// c; let b = [a]`) resolve. The relation is symmetric for locals: a local
/// mentioned in a handle's initializer (`let i = Inner {..}; let o = Outer {
/// inner: i }`) may be part of that handle's object graph, so it inherits the
/// handle's roots as well. The alias rule intentionally over-approximates (see
/// `analysis::mutates`); a scalar wrongly treated as an alias just acquires a
/// lock it does not need.
pub(super) fn guard_map(
    stmts: &[Stmt],
    cowns: &BTreeSet<String>,
    locals: &HashSet<String>,
) -> BTreeMap<String, BTreeSet<String>> {
    let mut guards: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for c in cowns {
        guards.entry(c.clone()).or_default().insert(c.clone());
    }
    if guards.is_empty() {
        return guards;
    }
    loop {
        let mut changed = false;
        collect_alias_roots(stmts, locals, &mut guards, &mut changed);
        if !changed {
            break;
        }
    }
    guards
}

fn collect_alias_roots(
    stmts: &[Stmt],
    locals: &HashSet<String>,
    guards: &mut BTreeMap<String, BTreeSet<String>>,
    changed: &mut bool,
) {
    for stmt in stmts {
        let binding: Option<(&String, &Expr)> = match stmt {
            Stmt::Let {
                pat: Pattern::Binding(name, _, _),
                value: Some(value),
                ..
            } => Some((name, value)),
            Stmt::Assign {
                target: Expr::Ident(name, _),
                value,
                ..
            } => Some((name, value)),
            _ => None,
        };
        if let Some((name, value)) = binding {
            let mut mentioned = HashSet::default();
            crate::closure::idents_stmts(&[Stmt::Expr(value.clone())], &mut mentioned);
            let mut roots: BTreeSet<String> = BTreeSet::new();
            for m in &mentioned {
                if let Some(r) = guards.get(m) {
                    roots.extend(r.iter().cloned());
                }
            }
            if !roots.is_empty() {
                let entry = guards.entry(name.clone()).or_default();
                for r in roots {
                    *changed |= entry.insert(r);
                }
            }
            // The reverse direction: the locals this handle's initializer
            // mentions may be reachable from it (a closure literal only
            // captures them; its accesses are guarded where it runs).
            if let Some(own) = guards
                .get(name)
                .filter(|_| !matches!(value, Expr::Closure(..)))
                .cloned()
            {
                for m in mentioned
                    .iter()
                    .filter(|m| *m != name && locals.contains(*m))
                {
                    let entry = guards.entry(m.clone()).or_default();
                    for r in &own {
                        *changed |= entry.insert(r.clone());
                    }
                }
            }
        }
        // Aliases may be bound inside nested blocks (a conditional, a loop).
        nested_block_stmts(stmt, &mut |inner| {
            collect_alias_roots(inner, locals, guards, changed)
        });
    }
}

/// Concurrency builtins whose arguments must not be treated as guarded
/// dereferences: promotions take the bare handle to retag it, `with`/`_with_all`
/// take it to lock it, and `spawn` takes a closure. Wrapping any of these in a
/// further lock is at best noise.
const NON_FORWARDING_BUILTINS: &[&str] =
    &["with", "_with_all", "spawn", "sync", "_cown", "_freeze"];

fn callee_is_non_forwarding(callee: &Expr) -> bool {
    matches!(callee, Expr::Ident(n, _) if NON_FORWARDING_BUILTINS.contains(&n.as_str()))
}

/// Wrap each access to a guarded handle inside `stmt` in a lock acquisition, so
/// the spawner's own use of a shared cown is serialized through the same lock
/// the spawned task uses. The reentrant lock makes nested guards on the same
/// cown safe. A statement that touches no guarded handle is left unchanged.
/// `report` receives each inserted access guard's lock root and source extent;
/// deferred closure wrappers are excluded.
pub(super) fn guard_stmt_accesses(
    stmt: &mut Stmt,
    guards: &BTreeMap<String, BTreeSet<String>>,
    report: &mut impl FnMut(&str, Span),
) {
    match stmt {
        Stmt::Let {
            value: Some(value), ..
        } => guard_expr_accesses(value, guards, report),
        Stmt::Let { value: None, .. } => {}
        Stmt::Assign { target, value, .. } => {
            // A whole `c.f = v` (or `c[i] = v`) store is guarded as one unit so
            // both the place and the value evaluate under the lock.
            if root_ident(target).is_some_and(|r| guards.contains_key(r)) {
                guard_assign(stmt, guards, report);
                return;
            }
            guard_expr_accesses(target, guards, report);
            guard_expr_accesses(value, guards, report);
        }
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => guard_expr_accesses(e, guards, report),
        Stmt::While { cond, body, .. } => {
            guard_expr_accesses(cond, guards, report);
            for s in &mut body.stmts {
                guard_stmt_accesses(s, guards, report);
            }
        }
        Stmt::For { iter, body, .. } => {
            guard_expr_accesses(iter, guards, report);
            for s in &mut body.stmts {
                guard_stmt_accesses(s, guards, report);
            }
        }
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

/// Rewrite a field/element-store statement `c.f = v` whose root is guarded into
/// `with(root, (root) -> { c.f = v })` (or the `_with_all` group form), so the
/// read-modify-write happens under the object's lock. The value expression's own
/// nested accesses are guarded first so a read of *another* cown inside `v`
/// is serialized too.
fn guard_assign(
    stmt: &mut Stmt,
    guards: &BTreeMap<String, BTreeSet<String>>,
    report: &mut impl FnMut(&str, Span),
) {
    let placeholder = Stmt::Break(stmt_span(stmt));
    let mut original = std::mem::replace(stmt, placeholder);
    let mut roots: BTreeSet<String> = BTreeSet::new();
    if let Stmt::Assign { target, value, .. } = &mut original {
        if let Some(r) = root_ident(target).and_then(|r| guards.get(r)) {
            roots.extend(r.iter().cloned());
        }
        guard_expr_accesses(value, guards, report);
    }
    if roots.is_empty() {
        *stmt = original;
        return;
    }
    let span = stmt_span(&original);
    let block = Block {
        stmts: vec![original],
        span,
    };
    let roots: Vec<String> = roots.into_iter().collect();
    roots.iter().for_each(|root| report(root, span));
    *stmt = Stmt::Expr(wrap_with(Expr::Block(block, span), &roots));
}

/// Wrap each guarded access within an expression in a lock acquisition. An
/// expression node that *directly* dereferences a guarded handle -- a method call
/// `c.m(..)`, a field/index read `c.f` / `c[i]`, or a call `f(.., c, ..)` that
/// forwards the handle (or a place rooted at it) by reference -- is wrapped whole
/// so its whole evaluation holds the object's lock(s). Sub-expressions are
/// guarded first, so a nested access (a cown read inside an argument, branch, or
/// interpolation) is also serialized; the reentrant lock makes the resulting
/// nested acquisitions on the same cown safe.
fn guard_expr_accesses(
    expr: &mut Expr,
    guards: &BTreeMap<String, BTreeSet<String>>,
    report: &mut impl FnMut(&str, Span),
) {
    // Guard nested accesses first so they are serialized even when this node is
    // not itself wrapped (and stay correctly nested when it is).
    guard_children(expr, guards, report);
    // Then, if this node directly dereferences guarded handles, wrap the whole
    // node under the union of their lock roots.
    let roots = direct_guard_roots(expr, guards);
    if !roots.is_empty() {
        let span = expr.span();
        let original = std::mem::replace(expr, Expr::Null(span));
        roots.iter().for_each(|root| report(root, span));
        *expr = wrap_with(original, &roots);
    }
}

/// Recurse into an expression's children, guarding any cown access inside them.
/// A `Call`'s by-reference operands (its method receiver and the arguments that
/// are plain places rooted at a guarded handle) are *not* descended into here --
/// they are handled by wrapping the whole call in [`guard_expr_accesses`] -- so a
/// bare cown argument is not mistaken for a standalone read.
fn guard_children(
    expr: &mut Expr,
    guards: &BTreeMap<String, BTreeSet<String>>,
    report: &mut impl FnMut(&str, Span),
) {
    match expr {
        Expr::Call(callee, args, _) => {
            // A method receiver is part of the call's by-reference access; only
            // descend into a non-method callee.
            if !matches!(callee.as_ref(), Expr::Field(..)) {
                guard_expr_accesses(callee, guards, report);
            }
            if callee_is_non_forwarding(callee) {
                return;
            }
            for a in args.iter_mut() {
                // A bare place passed as an argument is guarded by wrapping the
                // call; descend only into compound argument expressions.
                if direct_arg_guard_roots(&a.expr, guards).is_none() {
                    guard_expr_accesses(&mut a.expr, guards, report);
                }
            }
        }
        Expr::Field(b, _, _) | Expr::Unary(_, b, _) | Expr::ErrorProp(b, _) => {
            guard_expr_accesses(b, guards, report)
        }
        Expr::Index(b, idx, _) | Expr::Range(b, idx, _) | Expr::Binary(_, b, idx, _) => {
            guard_expr_accesses(b, guards, report);
            guard_expr_accesses(idx, guards, report);
        }
        Expr::Array(elems, _) => elems
            .iter_mut()
            .for_each(|el| guard_expr_accesses(el, guards, report)),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => fields
            .iter_mut()
            .for_each(|(_, v)| guard_expr_accesses(v, guards, report)),
        Expr::Str(segs, _) => segs.iter_mut().for_each(|seg| {
            if let StrSeg::Expr(e) = seg {
                guard_expr_accesses(e, guards, report);
            }
        }),
        Expr::Block(block, _) => {
            for s in &mut block.stmts {
                guard_stmt_accesses(s, guards, report);
            }
        }
        Expr::TypeTest(subject, _, _, _) => guard_expr_accesses(subject, guards, report),
        Expr::If(c, t, e, _) => {
            guard_expr_accesses(c, guards, report);
            for s in &mut t.stmts {
                guard_stmt_accesses(s, guards, report);
            }
            if let Some(e) = e {
                guard_expr_accesses(e, guards, report);
            }
        }
        Expr::IfLet(_, scrut, t, e, _) => {
            guard_expr_accesses(scrut, guards, report);
            for s in &mut t.stmts {
                guard_stmt_accesses(s, guards, report);
            }
            if let Some(e) = e {
                guard_expr_accesses(e, guards, report);
            }
        }
        Expr::Match(scrut, arms, _) => {
            guard_expr_accesses(scrut, guards, report);
            arms.iter_mut()
                .for_each(|arm| guard_expr_accesses(&mut arm.body, guards, report));
        }
        Expr::Closure(params, body, _) => {
            let block = closure_block(body);
            let bound = param_names(params);
            let captures = captured(&block, &bound);
            let roots: BTreeSet<String> = captures
                .iter()
                .filter_map(|name| guards.get(name))
                .flat_map(|roots| roots.iter().cloned())
                .collect();
            if !roots.is_empty() {
                let roots: Vec<String> = roots.into_iter().collect();
                let span = body.span();
                let original = std::mem::replace(body.as_mut(), Expr::Null(span));
                *body.as_mut() = wrap_with(original, &roots);
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

/// The lock roots this expression node *directly* dereferences (sorted,
/// deduplicated): the union of the guarded handles' roots. A method call
/// contributes its receiver root and every argument rooted at a guarded handle
/// (each forwarded by reference); a plain call contributes its argument roots; a
/// field/index read contributes its base root. A bare identifier contributes
/// nothing -- copying a handle does not dereference the object.
fn direct_guard_roots(expr: &Expr, guards: &BTreeMap<String, BTreeSet<String>>) -> Vec<String> {
    let mut roots: BTreeSet<String> = BTreeSet::new();
    match expr {
        Expr::Call(callee, args, _) => {
            if callee_is_non_forwarding(callee) {
                return Vec::new();
            }
            if let Expr::Field(base, _, _) = callee.as_ref()
                && !callee.span().is_parenthesized()
                && let Some(r) = place_guard_roots(base, guards)
            {
                roots.extend(r);
            }
            for a in args {
                if let Some(r) = direct_arg_guard_roots(&a.expr, guards) {
                    roots.extend(r);
                }
            }
        }
        Expr::Field(base, _, _) | Expr::Index(base, _, _) => {
            if let Some(r) = place_guard_roots(base, guards) {
                roots.extend(r);
            }
        }
        _ => {}
    }
    roots.into_iter().collect()
}

/// The lock roots of a call argument that is a plain place (`c`, `c.f`, `c[i]`)
/// forwarded by reference, if its root is guarded. A compound argument (a call,
/// arithmetic) produces a fresh value and is not a by-reference forward.
fn direct_arg_guard_roots(
    arg: &Expr,
    guards: &BTreeMap<String, BTreeSet<String>>,
) -> Option<Vec<String>> {
    match arg {
        Expr::Ident(..) | Expr::SelfExpr(_) | Expr::Field(..) | Expr::Index(..) => {
            place_guard_roots(arg, guards)
        }
        _ => None,
    }
}

/// The lock roots of a place whose root identifier is a guarded handle.
fn place_guard_roots(
    place: &Expr,
    guards: &BTreeMap<String, BTreeSet<String>>,
) -> Option<Vec<String>> {
    root_ident(place)
        .and_then(|r| guards.get(r))
        .map(|s| s.iter().cloned().collect())
}

/// Build the lock acquisition around `body` for `roots`:
///
/// - one root: `with(c, (c) -> body)` -- the `with` handle shadows the captured
///   name so the body's accesses go through it, and the single-cown `with` also
///   opens a verification region;
/// - several roots: `_with_all(() -> body, c0, c1, ...)` -- the runtime acquires
///   the group in *address* order, so two bodies over the same objects captured
///   under different names cannot acquire them in opposite orders and deadlock,
///   as nested `with` calls ordered by name could.
///
/// The call takes the guarded expression's place and span (it has the
/// expression's type), while the synthesized closure gets an extent of its
/// own -- empty, at the expression's start -- so span-keyed checker channels
/// never read the closure's function type as the call's.
pub(super) fn wrap_with(body: Expr, roots: &[String]) -> Expr {
    let span = body.span();
    let closure_span = Span::new(span.lo, span.lo);
    if roots.len() == 1 {
        let cown = &roots[0];
        let param = Param {
            name: cown.clone(),
            ty: None,
            span,
        };
        let closure = Expr::Closure(vec![param], Box::new(body), closure_span);
        return Expr::Call(
            Box::new(Expr::Ident("with".to_string(), span)),
            vec![
                Arg {
                    expr: Expr::Ident(cown.clone(), span),
                },
                Arg { expr: closure },
            ],
            span,
        );
    }
    let closure = Expr::Closure(Vec::new(), Box::new(body), closure_span);
    let mut args = vec![Arg { expr: closure }];
    args.extend(roots.iter().map(|c| Arg {
        expr: Expr::Ident(c.clone(), span),
    }));
    Expr::Call(
        Box::new(Expr::Ident("_with_all".to_string(), span)),
        args,
        span,
    )
}
