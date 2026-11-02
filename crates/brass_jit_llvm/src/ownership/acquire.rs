//! The auto-acquire rewrite: per execution scope, promote every spawn capture to an
//! atomic-count owner before the spawn, wrap each spawned body in the locks of its
//! cowned captures, and guard the scope's own accesses to those cowns.

use fxhash::FxHashSet as HashSet;
use std::collections::{BTreeMap, BTreeSet};

use brass_parser::Span;
use brass_parser::ast::*;

use super::analysis::{captured, mutates, param_names, root_ident, stmts_block};
use super::guard::{guard_map, guard_stmt_accesses, wrap_with};
use super::scopes::{
    LexicalScopes, collect_local_bindings, collect_pattern_bindings, lexical_scopes,
    nested_block_stmts, nested_block_stmts_mut,
};
use super::sites::{
    SpawnArg, closure_bindings_at, closure_block, closure_bound_in, each_spawn_site, spawn_arg,
    spawn_closure_body, spawn_stmt_span, spawned_binding_spans, stmt_span,
};
use super::summaries::each_call;
use super::{AutoAcquireReport, GuardedAccess, SpawnError, SpawnSummaries};

/// Everything a scope's transformation needs to classify and guard, shared
/// immutably across the recursive walk.
struct ScopeCtx<'a> {
    /// Names in scope (enclosing scopes' locals/params plus this scope's own
    /// bindings). Only these are subject to ownership transfer.
    locals: HashSet<String>,
    /// The enclosing *function's* parameters: a captured parameter is always
    /// cowned (its callers may access it concurrently and are invisible here).
    fn_params: &'a HashSet<String>,
    /// The pristine (pre-transform) function body, for whole-function mutation
    /// queries; the transform must classify from what the programmer wrote.
    pristine_fn: &'a Block,
    /// The pristine statement tree of *this scope*, for resolving a spawned
    /// closure variable's binding wherever it sits in the scope (the spawn may be
    /// in a nested list, the binding in an enclosing or sibling one).
    pristine_scope: Block,
    /// Lexical binding environments for spawn sites and stored closures.
    lexical: LexicalScopes,
    /// Interprocedural spawn-capture summaries.
    summaries: &'a SpawnSummaries,
    /// Closure-valued declarations selected by a lexical `spawn(name)` site.
    spawned_bindings: HashSet<Span>,
    /// Locals promoted to cowns because they are passed to a call position that
    /// a callee spawn captures (per the summaries).
    summary_cowns: BTreeSet<String>,
    /// Handle name -> the cown roots whose locks guard a dereference through it.
    /// A cown maps to itself; an alias (`let h = o.inner`, `let w = Wrap { c }`,
    /// `let d = id(c)`) maps to the cown(s) its initializer mentions, so its
    /// accesses are serialized under the *object's* lock, not the handle's.
    guards: BTreeMap<String, BTreeSet<String>>,
    /// Names never promoted at a spawn site (see [`unpromotable_handles`]).
    unpromotable: HashSet<String>,
}

/// Insert automatic lock acquisition for every `spawn` in a function body, so
/// the programmer writes no ownership annotations yet shared mutation is still
/// serialized through the cown locks:
///
/// - each spawn closure body is wrapped to acquire its cowned captures (one
///   `with`, or `_with_all` for a group -- acquired address-ordered at runtime,
///   so overlapping capture sets cannot deadlock);
/// - every capture is promoted (`_cown`/`_freeze`) before the spawn, fixing its
///   atomic-count owner before the first cross-thread reference;
/// - every statement of the function that dereferences a cown -- anywhere, before
///   or after the spawn, through any alias -- is wrapped in the same lock, since
///   the spawned task runs concurrently with all of it;
/// - a local passed to a function that spawns a task capturing that parameter
///   (per `summaries`) is promoted and guarded exactly like a local spawn.
///
/// Report rejected spawn arguments and guards inserted on the spawning scope
/// itself. Wrappers around task entry and deferred closures are not reported.
pub fn auto_acquire(
    stmts: &mut Vec<Stmt>,
    params: &HashSet<String>,
    summaries: &SpawnSummaries,
) -> AutoAcquireReport {
    let mut report = AutoAcquireReport::default();
    let pristine = stmts_block(stmts);
    process_scope(
        stmts,
        params,
        params,
        &pristine,
        summaries,
        None,
        &mut report,
    );
    report
}

/// Transform one execution scope: a function body, or a spawned closure's body
/// (which runs on its own thread and hosts its own nested spawn sites and
/// locals). `in_scope` are the names visible from enclosing scopes.
fn process_scope(
    stmts: &mut Vec<Stmt>,
    in_scope: &HashSet<String>,
    fn_params: &HashSet<String>,
    pristine_fn: &Block,
    summaries: &SpawnSummaries,
    scope: Option<Span>,
    report: &mut AutoAcquireReport,
) {
    let mut locals = in_scope.clone();
    collect_local_bindings(stmts, &mut locals);
    let lexical = lexical_scopes(stmts, in_scope);

    // ---- analysis over the pristine scope ----
    let spawned_bindings = spawned_binding_spans(stmts);

    // Union of every site's cowned captures in this scope (literal sites plus
    // resolved closure-variable sites), for the scope-wide guard set.
    let mut all_cowns: BTreeSet<String> = BTreeSet::new();
    each_scope_site_shallow(stmts, stmts, &lexical, &mut |cbody, bound, visible| {
        let (cowns, freezes) = classify_captures(cbody, bound, visible, fn_params, pristine_fn);
        report.may_rewrite |= !cowns.is_empty() || !freezes.is_empty();
        all_cowns.extend(cowns);
    });

    // Locals handed to spawn-capturing call positions become cowns too.
    let summary_cowns = collect_summary_cowns(stmts, &locals, summaries);
    report.may_rewrite |= !summary_cowns.is_empty();
    all_cowns.extend(summary_cowns.iter().cloned());

    let ctx = ScopeCtx {
        guards: guard_map(stmts, &all_cowns, &locals),
        unpromotable: unpromotable_handles(stmts),
        pristine_scope: stmts_block(stmts),
        lexical,
        locals,
        fn_params,
        pristine_fn,
        summaries,
        spawned_bindings,
        summary_cowns,
    };

    // ---- guard the scope's own accesses ----
    // Every statement runs concurrently with the spawned task(s) -- a spawn
    // inside a loop or conditional shares state with iterations before it and
    // statements after it -- so the whole scope is guarded, not just the
    // statements textually after a spawn. Guarding happens before the transform
    // inserts wrappers/promotions, so synthesized code is never double-guarded
    // (closures, including the spawn bodies wrapped later, are not descended
    // into here).
    if !ctx.guards.is_empty() {
        for stmt in stmts.iter_mut() {
            if ctx.spawned_bindings.contains(&stmt_span(stmt)) {
                continue;
            }
            guard_stmt_accesses(stmt, &ctx.guards, &mut |root, span| {
                report.guarded_accesses.push(GuardedAccess {
                    scope,
                    root_binding: root.to_string(),
                    span,
                });
            });
        }
    }

    // ---- rewrite spawn sites, closure-variable bindings, and promotions ----
    transform_stmts(stmts, &ctx, report);
}

/// Visit each spawn site body of *this scope only* (literal spawn statements in
/// the control-flow tree, plus the binding closures of spawned locals). Unlike
/// `summaries::each_scope_spawn_body` this does not recurse into the spawned bodies:
/// nested spawns belong to the inner scope, which classifies against its own
/// locals.
fn each_scope_site_shallow(
    stmts: &[Stmt],
    all: &[Stmt],
    lexical: &LexicalScopes,
    f: &mut impl FnMut(&Block, &HashSet<String>, &HashSet<String>),
) {
    each_spawn_site(stmts, &mut |stmt| match spawn_arg(stmt) {
        Some(SpawnArg::Literal) => {
            if let Some(body) = spawn_closure_body(stmt) {
                let bound = closure_bound_in(stmt);
                let visible = lexical
                    .spawn_sites
                    .get(&spawn_stmt_span(stmt))
                    .expect("spawn site has a lexical environment");
                f(&body, &bound, visible);
            }
        }
        Some(SpawnArg::Var(name, _)) => {
            for binding in closure_bindings_at(all, spawn_stmt_span(stmt), name) {
                let bound = param_names(&binding.params);
                let visible = lexical
                    .closure_bindings
                    .get(&binding.span)
                    .expect("closure binding has a lexical environment");
                f(&binding.body, &bound, visible);
            }
        }
        Some(SpawnArg::Opaque(_)) | None => {}
    });
}

/// Partition a spawn closure's captures into `(cowns, freezes)`. A capture is
/// cowned when it is a function parameter (concurrent callers are invisible) or
/// is mutated anywhere in the pristine function -- by this closure, another
/// closure, or the spawner itself, directly or through an alias; only a capture
/// nobody ever mutates is frozen. Every captured local crosses to the new
/// thread, so both groups are promoted to an atomic-count owner. Sorted for
/// deterministic output.
fn classify_captures(
    cbody: &Block,
    bound: &HashSet<String>,
    locals: &HashSet<String>,
    fn_params: &HashSet<String>,
    pristine_fn: &Block,
) -> (Vec<String>, Vec<String>) {
    let mut caps: Vec<String> = captured(cbody, bound)
        .into_iter()
        .filter(|name| locals.contains(name))
        .collect();
    caps.sort();
    caps.into_iter()
        .partition(|var| fn_params.contains(var) || mutates(pristine_fn, var))
}

/// Locals of this scope that are passed (as a place root) into a call position
/// the summaries mark as spawn-captured: the callee hands the object to a
/// thread, so the caller must treat the local as a cown.
fn collect_summary_cowns(
    stmts: &[Stmt],
    locals: &HashSet<String>,
    summaries: &SpawnSummaries,
) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    if summaries.is_empty() {
        return out;
    }
    let block = stmts_block(stmts);
    each_call(&block, &mut |callee, recv, args| {
        let Some(indices) = summaries.get(callee) else {
            return;
        };
        for &j in indices {
            let arg = match recv {
                Some(r) if j == 0 => Some(r),
                Some(_) => args.get(j - 1).map(|a| &a.expr),
                None => args.get(j).map(|a| &a.expr),
            };
            if let Some(root) = arg.and_then(root_ident)
                && locals.contains(root)
            {
                out.insert(root.to_string());
            }
        }
    });
    out
}

/// The transformation walk over a scope's statement lists: wrap spawn bodies,
/// recurse into them as their own scopes, wrap the binding closures of spawned
/// locals, and insert ownership promotions.
fn transform_stmts(stmts: &mut Vec<Stmt>, ctx: &ScopeCtx, report: &mut AutoAcquireReport) {
    let mut i = 0;
    while i < stmts.len() {
        // Recurse into nested control-flow blocks, which may contain their own
        // spawn statements and bindings.
        nested_block_stmts_mut(&mut stmts[i], &mut |inner| {
            transform_stmts(inner, ctx, report)
        });

        // A binding of a spawned closure variable: process its body as a scope
        // of its own (nested spawns) and wrap it for its cowned captures, exactly
        // as a literal spawn argument is.
        transform_spawned_binding(&mut stmts[i], ctx, report);

        let mut inserted = 0;
        match spawn_arg(&stmts[i]) {
            Some(SpawnArg::Literal) => {
                let body = spawn_closure_body(&stmts[i]).expect("literal spawn body");
                let bound = closure_bound_in(&stmts[i]);
                let visible = ctx
                    .lexical
                    .spawn_sites
                    .get(&spawn_stmt_span(&stmts[i]))
                    .unwrap_or(&ctx.locals);
                let (cowns, freezes) =
                    classify_captures(&body, &bound, visible, ctx.fn_params, ctx.pristine_fn);
                // The spawned body is its own execution scope; nested spawns in
                // it are classified against its own locals.
                if let Some(inner) = spawn_closure_body_mut(&mut stmts[i], report) {
                    let mut inner_scope = visible.clone();
                    inner_scope.extend(bound.iter().cloned());
                    process_scope(
                        inner,
                        &inner_scope,
                        ctx.fn_params,
                        ctx.pristine_fn,
                        ctx.summaries,
                        Some(body.span),
                        report,
                    );
                }
                if !cowns.is_empty() {
                    wrap_spawn_body(&mut stmts[i], &cowns);
                }
                let mut promoted = cowns.clone();
                promoted.extend(alias_handles_at(ctx, visible, &cowns));
                inserted = insert_promotions(stmts, i, &promoted, &freezes);
            }
            Some(SpawnArg::Var(name, span)) => {
                // Resolve the closure literal(s) bound to `name` anywhere in this
                // scope's pristine tree (the spawn may be in a nested list, the
                // binding in an enclosing or sibling one; a binding in a
                // *different* scope -- another closure's body -- is a different
                // thread context and does not resolve).
                let bindings = closure_bindings_at(
                    &ctx.pristine_scope.stmts,
                    spawn_stmt_span(&stmts[i]),
                    name,
                );
                if bindings.is_empty() {
                    report.errors.push(SpawnError {
                        message: format!(
                            "`spawn` requires a closure literal or a local bound to one; \
                             `{name}` is not bound to a closure literal in this function"
                        ),
                        span,
                    });
                } else {
                    // Union over all bindings of the name: promotions must cover
                    // whichever closure the spawn actually runs.
                    let mut cowns: BTreeSet<String> = BTreeSet::new();
                    let mut freezes: BTreeSet<String> = BTreeSet::new();
                    for binding in &bindings {
                        let bound = param_names(&binding.params);
                        let visible = ctx
                            .lexical
                            .closure_bindings
                            .get(&binding.span)
                            .unwrap_or(&ctx.locals);
                        let (c, f) = classify_captures(
                            &binding.body,
                            &bound,
                            visible,
                            ctx.fn_params,
                            ctx.pristine_fn,
                        );
                        cowns.extend(c);
                        freezes.extend(f);
                    }
                    let freezes: Vec<String> = freezes.difference(&cowns).cloned().collect();
                    let mut promoted: Vec<String> = cowns.iter().cloned().collect();
                    let visible = ctx
                        .lexical
                        .spawn_sites
                        .get(&spawn_stmt_span(&stmts[i]))
                        .unwrap_or(&ctx.locals);
                    let cowns: Vec<String> = cowns.into_iter().collect();
                    promoted.extend(alias_handles_at(ctx, visible, &cowns));
                    inserted = insert_promotions(stmts, i, &promoted, &freezes);
                }
            }
            Some(SpawnArg::Opaque(span)) => {
                report.errors.push(SpawnError {
                    message: "`spawn` requires a closure literal or a local bound to one; \
                              this argument cannot be analyzed for ownership"
                        .to_string(),
                    span,
                });
            }
            None => {
                // Not a spawn site: insert the summary-cown promotion right after
                // a binding of a local that a callee spawn captures, so the
                // object owns an atomic count before the call hands it over.
                inserted = insert_summary_promotion_after_binding(stmts, i, ctx);
            }
        }
        i += inserted + 1;
    }
}

/// If `stmt` binds a closure literal to a local that is spawned somewhere in
/// this scope, process the closure body as its own scope and wrap it for its
/// cowned captures (mirroring a literal spawn argument).
fn transform_spawned_binding(stmt: &mut Stmt, ctx: &ScopeCtx, report: &mut AutoAcquireReport) {
    let binding_span = stmt_span(stmt);
    let (params, body) = match stmt {
        Stmt::Let {
            pat: Pattern::Binding(_, _, _),
            value: Some(Expr::Closure(params, body, _)),
            ..
        } => (params, body),
        Stmt::Assign {
            target: Expr::Ident(_, _),
            value: Expr::Closure(params, body, _),
            ..
        } => (params, body),
        _ => return,
    };
    if !ctx.spawned_bindings.contains(&binding_span) {
        return;
    }
    let block = closure_block(body);
    let bound = param_names(params);
    let visible = ctx
        .lexical
        .closure_bindings
        .get(&binding_span)
        .unwrap_or(&ctx.locals);
    let (cowns, _) = classify_captures(&block, &bound, visible, ctx.fn_params, ctx.pristine_fn);
    // The bound closure body is its own execution scope once spawned.
    let mut inner_scope = visible.clone();
    inner_scope.extend(bound);
    process_scope(
        closure_body_stmts_mut(body, report),
        &inner_scope,
        ctx.fn_params,
        ctx.pristine_fn,
        ctx.summaries,
        Some(block.span),
        report,
    );
    if !cowns.is_empty() {
        let span = body.span();
        let original = std::mem::replace(body.as_mut(), Expr::Null(span));
        *body.as_mut() = wrap_with(original, &cowns);
    }
}

/// The handles visible at a spawn site that reach into the object graph of one
/// of its cowned captures without being captured themselves (`let h = o.inner`
/// before the spawn, or `i` after `let o = Outer { inner: i }`). The spawner
/// keeps using them outside the lock -- capturing them into guard closures,
/// copying, dropping -- while the task reaches the same objects under the lock,
/// so their reference counts must be atomic from the spawn on: they are
/// promoted with the captures. Sorted, so the emitted order is stable.
fn alias_handles_at(ctx: &ScopeCtx, visible: &HashSet<String>, cowns: &[String]) -> Vec<String> {
    let mut out: Vec<String> = ctx
        .guards
        .iter()
        .filter(|(handle, roots)| {
            visible.contains(*handle)
                && !cowns.contains(handle)
                && !ctx.unpromotable.contains(*handle)
                && roots.iter().any(|r| cowns.contains(r))
        })
        .map(|(handle, _)| handle.clone())
        .collect();
    out.sort();
    out
}

/// The handles of a scope that a spawn site never promotes: a name declared
/// without an initializer (`let x: T`), which may still be unassigned there,
/// and a name bound to a closure literal, which is not part of any object
/// graph (a closure that reaches a cown is guarded where it runs).
fn unpromotable_handles(stmts: &[Stmt]) -> HashSet<String> {
    fn walk(stmts: &[Stmt], out: &mut HashSet<String>) {
        for stmt in stmts {
            match stmt {
                Stmt::Let {
                    pat, value: None, ..
                } => collect_pattern_bindings(pat, out),
                Stmt::Let {
                    pat: Pattern::Binding(name, _, _),
                    value: Some(Expr::Closure(..)),
                    ..
                }
                | Stmt::Assign {
                    target: Expr::Ident(name, _),
                    value: Expr::Closure(..),
                    ..
                } => {
                    out.insert(name.clone());
                }
                _ => {}
            }
            nested_block_stmts(stmt, &mut |inner| walk(inner, out));
        }
    }
    let mut out = HashSet::default();
    walk(stmts, &mut out);
    out
}

/// Insert `_cown`/`_freeze` promotion statements before `stmts[i]` (a spawn
/// site), returning how many were inserted. Promotions run before the spawn so
/// the owner -- and thus the reference count's atomicity -- is fixed before the
/// closure crosses to the new thread.
fn insert_promotions(
    stmts: &mut Vec<Stmt>,
    i: usize,
    cowns: &[String],
    freezes: &[String],
) -> usize {
    let span = spawn_stmt_span(&stmts[i]);
    let promos: Vec<Stmt> = cowns
        .iter()
        .map(|c| promote_stmt("_cown", c, span))
        .chain(freezes.iter().map(|c| promote_stmt("_freeze", c, span)))
        .collect();
    let inserted = promos.len();
    for (k, p) in promos.into_iter().enumerate() {
        stmts.insert(i + k, p);
    }
    inserted
}

/// If `stmts[i]` binds a local that the summaries mark as spawn-captured by a
/// callee, insert `_cown(local)` right after the binding (any point before the
/// call works; the binding is the earliest the name exists). Returns how many
/// statements were inserted.
fn insert_summary_promotion_after_binding(
    stmts: &mut Vec<Stmt>,
    i: usize,
    ctx: &ScopeCtx,
) -> usize {
    let Stmt::Let {
        pat: Pattern::Binding(name, _, _),
        ..
    } = &stmts[i]
    else {
        return 0;
    };
    if !ctx.summary_cowns.contains(name.as_str()) {
        return 0;
    }
    let name = name.clone();
    let span = stmt_span(&stmts[i]);
    stmts.insert(i + 1, promote_stmt("_cown", &name, span));
    1
}

/// The mutable statement list of a `spawn(closure)`'s body in `stmt`, if `stmt`
/// is a spawn site whose argument is a block closure. Lets the transform recurse
/// into a nested spawn so its captures are promoted and its body guarded.
fn spawn_closure_body_mut<'a>(
    stmt: &'a mut Stmt,
    report: &mut AutoAcquireReport,
) -> Option<&'a mut Vec<Stmt>> {
    let expr = match stmt {
        Stmt::Expr(e) | Stmt::Let { value: Some(e), .. } => e,
        _ => return None,
    };
    let Expr::Call(callee, args, _) = expr else {
        return None;
    };
    if !matches!(&**callee, Expr::Ident(n, _) if n == "spawn") {
        return None;
    }
    let Expr::Closure(_, body, _) = &mut args.first_mut()?.expr else {
        return None;
    };
    Some(closure_body_stmts_mut(body, report))
}

/// Return a mutable statement view of a closure body. An expression-bodied
/// closure returns its expression, while a block's trailing expression is only
/// a statement, so normalization must make that return explicit before the
/// ownership pass inserts guards or nested-spawn rewrites.
fn closure_body_stmts_mut<'a>(
    body: &'a mut Box<Expr>,
    report: &mut AutoAcquireReport,
) -> &'a mut Vec<Stmt> {
    if !matches!(body.as_ref(), Expr::Block(..)) {
        report.may_rewrite = true;
        let span = body.span();
        let value = std::mem::replace(body.as_mut(), Expr::Null(span));
        *body.as_mut() = Expr::Block(
            Block {
                stmts: vec![Stmt::Return(Some(value), span)],
                span,
            },
            span,
        );
    }
    let Expr::Block(block, _) = body.as_mut() else {
        unreachable!("closure body normalized to a block")
    };
    &mut block.stmts
}

/// A `builtin(var)` statement -- `_cown(var)` or `_freeze(var)` -- inserted before
/// a spawn to promote `var` to an atomic-count owner.
fn promote_stmt(builtin: &str, var: &str, span: Span) -> Stmt {
    Stmt::Expr(Expr::Call(
        Box::new(Expr::Ident(builtin.to_string(), span)),
        vec![Arg {
            expr: Expr::Ident(var.to_string(), span),
        }],
        span,
    ))
}

/// Rewrite the spawn closure's body in `stmt` to acquire each cowned capture
/// around the whole body.
fn wrap_spawn_body(stmt: &mut Stmt, cowns: &[String]) {
    let expr = match stmt {
        Stmt::Expr(e) | Stmt::Let { value: Some(e), .. } => e,
        _ => return,
    };
    let Expr::Call(callee, args, _) = expr else {
        return;
    };
    if !matches!(&**callee, Expr::Ident(n, _) if n == "spawn") {
        return;
    }
    let Some(arg) = args.first_mut() else { return };
    let Expr::Closure(_, body, span) = &mut arg.expr else {
        return;
    };
    let span = *span;
    let original = std::mem::replace(body.as_mut(), Expr::Null(span));
    *body.as_mut() = wrap_with(original, cowns);
}
