//! Automatic ownership analysis for `spawn` captures (DESIGN.md 12.7-12.8).
//!
//! A `spawn` runs its closure on a real OS thread, so each captured value is
//! shared between the spawner and that thread. The decision here is therefore
//! load-bearing, not advisory: [`auto_acquire`] realizes it before the spawn so
//! the capture has an atomic reference count from its first cross-thread
//! reference. A capture the closure mutates is made a cown (and its access wrapped
//! in `with`, which lock-guards it); a read-only capture is frozen (immutable).
//! Both are `rc_atomic` owner classes, which is what makes the otherwise-racy
//! cross-thread reference counting sound. [`decide`] additionally classifies a
//! capture as move/freeze/cown from its liveness for the auto-acquire diagnostic
//! (DESIGN.md 12.9.2).

use std::collections::HashSet;

use prepoly_lexer::Span;
use prepoly_parser::ast::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ownership {
    /// Not live after the spawn: hand exclusive ownership to the thread.
    Move,
    /// Live after the spawn but only read inside: freeze (immutable share).
    Freeze,
    /// Mutated inside the closure: wrap in a cown with auto-acquire.
    Cown,
}

/// Decide ownership for `var` captured by `closure_body`, given whether the
/// variable is still used after the spawn point.
pub fn decide(var: &str, live_after: bool, closure_body: &Block) -> Ownership {
    if !live_after {
        return Ownership::Move;
    }
    if mutates(closure_body, var) {
        Ownership::Cown
    } else {
        Ownership::Freeze
    }
}

/// Whether `body` mutates `var` (assigns to it or one of its fields/elements).
pub fn mutates(body: &Block, var: &str) -> bool {
    let mut found = false;
    scan_block(body, var, &mut found);
    found
}

fn scan_block(b: &Block, var: &str, found: &mut bool) {
    for s in &b.stmts {
        match s {
            Stmt::Assign { target, value, .. } => {
                if root_ident(target) == Some(var) {
                    *found = true;
                }
                scan_expr(value, var, found);
            }
            Stmt::Expr(e) => scan_expr(e, var, found),
            Stmt::Let { value, .. } => scan_expr(value, var, found),
            Stmt::Return(Some(e), _) => scan_expr(e, var, found),
            Stmt::While { cond, body, .. } => {
                scan_expr(cond, var, found);
                scan_block(body, var, found);
            }
            Stmt::For { iter, body, .. } => {
                scan_expr(iter, var, found);
                scan_block(body, var, found);
            }
            _ => {}
        }
    }
}

/// Look for a mutation of `var` inside an expression. A method call on `var`
/// (`var.m(..)`) is conservatively treated as a mutation: without per-method
/// `mutates_self` results, assuming it may mutate keeps a shared object cowned
/// (and so lock-guarded) rather than frozen, which is the safe direction.
fn scan_expr(e: &Expr, var: &str, found: &mut bool) {
    match e {
        Expr::Call(callee, args, _) => {
            if let Expr::Field(base, _, _) = &**callee
                && root_ident(base) == Some(var)
            {
                *found = true;
            }
            scan_expr(callee, var, found);
            args.iter().for_each(|a| scan_expr(&a.expr, var, found));
        }
        Expr::Field(b, _, _)
        | Expr::Index(b, _, _)
        | Expr::Unary(_, b, _)
        | Expr::ErrorProp(b, _) => scan_expr(b, var, found),
        Expr::Binary(_, a, b, _) => {
            scan_expr(a, var, found);
            scan_expr(b, var, found);
        }
        Expr::Block(block, _) => scan_block(block, var, found),
        Expr::If(c, t, e, _) => {
            scan_expr(c, var, found);
            scan_block(t, var, found);
            if let Some(e) = e {
                scan_expr(e, var, found);
            }
        }
        _ => {}
    }
}

fn root_ident(e: &Expr) -> Option<&str> {
    match e {
        Expr::Ident(n, _) => Some(n),
        Expr::Field(b, _, _) | Expr::Index(b, _, _) => root_ident(b),
        _ => None,
    }
}

/// Names referenced (and thus captured) inside a spawn closure body.
pub fn captured(body: &Block, bound: &HashSet<String>) -> HashSet<String> {
    let mut refs = HashSet::new();
    crate::closure::idents_block(body, &mut refs);
    refs.into_iter().filter(|r| !bound.contains(r)).collect()
}

/// One captured variable's automatically chosen ownership at a `spawn` site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaptureDecision {
    pub var: String,
    pub ownership: Ownership,
}

/// Decide auto-ownership for every `spawn(closure)` capture reachable in a
/// function `body` (DESIGN.md 12.7-12.8). Liveness is approximated per
/// statement list: a capture is "live after" the spawn when it is referenced in
/// a later statement of the same block, so a value used only by the spawned
/// task is moved, one read afterwards is frozen, and one mutated inside the
/// closure and read afterwards is cowned. Over-approximating liveness is safe:
/// it can only upgrade `Move` to `Freeze`/`Cown`, never the reverse, which never
/// hands shared state to a thread that another path still uses. The decisions
/// are deterministic (sorted by variable name) so callers can report them.
pub fn analyze_spawns(body: &Block, params: &HashSet<String>) -> Vec<CaptureDecision> {
    analyze_spawns_stmts(&body.stmts, params)
}

/// As [`analyze_spawns`] but over a bare statement slice, for module-init code
/// whose top-level statements have no enclosing block. `params` are local names
/// already in scope (function parameters); local `let`/`for` bindings are added
/// automatically. Only these locals are subject to ownership transfer: a free
/// name that is a function or global is not a captured value.
pub fn analyze_spawns_stmts(stmts: &[Stmt], params: &HashSet<String>) -> Vec<CaptureDecision> {
    let mut locals = params.clone();
    collect_local_bindings(stmts, &mut locals);
    let mut out = Vec::new();
    analyze_block(stmts, &locals, &mut out);
    out
}

fn analyze_block(stmts: &[Stmt], locals: &HashSet<String>, out: &mut Vec<CaptureDecision>) {
    for (i, stmt) in stmts.iter().enumerate() {
        if let Stmt::While { body, .. } | Stmt::For { body, .. } = stmt {
            analyze_block(&body.stmts, locals, out);
        }
        let Some(closure_body) = spawn_closure_body(stmt) else {
            continue;
        };
        // A nested spawn inside the spawned closure is its own site.
        analyze_block(&closure_body.stmts, locals, out);
        let bound = closure_bound_in(stmt);
        let mut captures: Vec<String> = captured(&closure_body, &bound)
            .into_iter()
            .filter(|name| locals.contains(name))
            .collect();
        captures.sort();
        let rest = &stmts[i + 1..];
        for var in captures {
            let live_after = stmts_reference(rest, &var);
            out.push(CaptureDecision {
                ownership: decide(&var, live_after, &closure_body),
                var,
            });
        }
    }
}

/// Collect names bound by `let`/`for` anywhere in a statement slice. Scoping is
/// ignored (a superset is safe: it only widens the set of names treated as
/// captured locals rather than globals).
fn collect_local_bindings(stmts: &[Stmt], out: &mut HashSet<String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { pat, .. } => collect_pattern_bindings(pat, out),
            Stmt::For { var, body, .. } => {
                out.insert(var.clone());
                collect_local_bindings(&body.stmts, out);
            }
            Stmt::While { body, .. } => collect_local_bindings(&body.stmts, out),
            _ => {}
        }
    }
}

fn collect_pattern_bindings(pat: &Pattern, out: &mut HashSet<String>) {
    match pat {
        Pattern::Binding(name, _) => {
            out.insert(name.clone());
        }
        Pattern::Record(_, fields, _) => {
            for field in fields {
                match &field.pat {
                    Some(sub) => collect_pattern_bindings(sub, out),
                    None => {
                        out.insert(field.name.clone());
                    }
                }
            }
        }
        Pattern::Array(pats, _) => pats.iter().for_each(|p| collect_pattern_bindings(p, out)),
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
    }
}

/// If `stmt` is a top-level `spawn(closure)` call (as an expression statement or
/// a `let` initializer), return the closure body as a block.
fn spawn_closure_body(stmt: &Stmt) -> Option<Block> {
    let expr = match stmt {
        Stmt::Expr(e) => e,
        Stmt::Let { value, .. } => value,
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

fn closure_bound_in(stmt: &Stmt) -> HashSet<String> {
    let expr = match stmt {
        Stmt::Expr(e) | Stmt::Let { value: e, .. } => e,
        _ => return HashSet::new(),
    };
    if let Expr::Call(_, args, _) = expr
        && let Some(Expr::Closure(params, body, _)) = args.first().map(|a| &a.expr)
    {
        return crate::closure::bound_names(params, &closure_block(body));
    }
    HashSet::new()
}

fn closure_block(body: &Expr) -> Block {
    match body {
        Expr::Block(b, _) => b.clone(),
        expr => Block {
            stmts: vec![Stmt::Expr(expr.clone())],
            span: expr.span(),
        },
    }
}

fn stmts_reference(stmts: &[Stmt], var: &str) -> bool {
    let mut refs = HashSet::new();
    crate::closure::idents_stmts(stmts, &mut refs);
    refs.contains(var)
}

// ----- auto-acquire (DESIGN.md 12.9) -----

/// Insert automatic `with` acquisition for every `spawn` closure that mutates a
/// captured cown, so the programmer writes no ownership annotations yet shared
/// mutation is still serialized through the cown lock (DESIGN.md 12.9.1: wrap the
/// whole closure body in one `with` per cowned capture). A capture that is moved
/// (exclusive to the thread) or frozen (read-only) needs no lock and is left
/// alone. `params` are the names already in scope around `stmts`.
pub fn auto_acquire(stmts: &mut Vec<Stmt>, params: &HashSet<String>) {
    let mut locals = params.clone();
    collect_local_bindings(stmts, &mut locals);
    auto_acquire_in(stmts, &locals);
}

fn auto_acquire_in(stmts: &mut Vec<Stmt>, locals: &HashSet<String>) {
    let mut i = 0;
    while i < stmts.len() {
        // Recurse into loop bodies (which may themselves contain spawns).
        if let Stmt::While { body, .. } | Stmt::For { body, .. } = &mut stmts[i] {
            auto_acquire_in(&mut body.stmts, locals);
        }
        let (cowns, freezes) = spawn_capture_promotions(&stmts[i], locals);
        if cowns.is_empty() && freezes.is_empty() {
            i += 1;
            continue;
        }
        // Lock-guard each mutated capture's access inside the closure body.
        if !cowns.is_empty() {
            wrap_spawn_body(&mut stmts[i], &cowns);
        }
        // Promote every capture to an atomic-count owner *before* the spawn, so the
        // owner is fixed before the closure captures (retains) the value and the
        // count is atomic from the first cross-thread reference: a mutated capture
        // becomes a cown, a read-only one is frozen.
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
        i += inserted + 1;
    }
}

/// The span used for a spawn's synthesized promotion statements (cosmetic: these
/// builtins do not fail, so the span only ever surfaces in internal diagnostics).
fn spawn_stmt_span(stmt: &Stmt) -> Span {
    match stmt {
        Stmt::Expr(e) | Stmt::Let { value: e, .. } => e.span(),
        _ => Span::new(0, 0),
    }
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

/// The captures of a `spawn` closure in `stmt`, partitioned into `(cowns,
/// freezes)`: those the closure mutates (cowned, so their access is lock-guarded)
/// and those it only reads (frozen). Every captured local crosses to the new
/// thread, so both groups are promoted to an atomic-count owner -- the move/freeze
/// liveness distinction is not used for atomicity, only the mutation does. Sorted
/// for deterministic, deadlock-free lock ordering.
fn spawn_capture_promotions(stmt: &Stmt, locals: &HashSet<String>) -> (Vec<String>, Vec<String>) {
    let Some(closure_body) = spawn_closure_body(stmt) else {
        return (Vec::new(), Vec::new());
    };
    let bound = closure_bound_in(stmt);
    let mut caps: Vec<String> = captured(&closure_body, &bound)
        .into_iter()
        .filter(|name| locals.contains(name))
        .collect();
    caps.sort();
    caps.into_iter()
        .partition(|var| mutates(&closure_body, var))
}

/// Rewrite the spawn closure's body in `stmt` to `with(c, (c) -> body)` nested
/// per cown, so each cowned capture is acquired around the body.
fn wrap_spawn_body(stmt: &mut Stmt, cowns: &[String]) {
    let expr = match stmt {
        Stmt::Expr(e) | Stmt::Let { value: e, .. } => e,
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

/// Build `with(c0, (c0) -> with(c1, (c1) -> body))` for cowns `[c0, c1]`. The
/// `with` handle shadows the captured name so the body's accesses go through it.
fn wrap_with(body: Expr, cowns: &[String]) -> Expr {
    let mut inner = body;
    for cown in cowns.iter().rev() {
        let span = inner.span();
        let param = Param {
            name: cown.clone(),
            ty: None,
            span,
        };
        let closure = Expr::Closure(vec![param], Box::new(inner), span);
        inner = Expr::Call(
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
    inner
}

#[cfg(test)]
mod tests {
    use super::*;
    use prepoly_parser::ast::TopLevel;
    use prepoly_parser::parse;

    fn main_body(src: &str) -> Block {
        let module = parse(src).expect("parse");
        for item in module.items {
            if let TopLevel::Fun(f) = item
                && f.name == "main"
            {
                return f.body;
            }
        }
        panic!("no `main`");
    }

    fn decisions(src: &str) -> Vec<CaptureDecision> {
        analyze_spawns(&main_body(src), &HashSet::new())
    }

    #[test]
    fn capture_only_used_by_spawn_is_moved() {
        let d = decisions(
            "fun main() {\n    let data = [1, 2, 3]\n    spawn(() -> { println(data) })\n}\n",
        );
        assert_eq!(
            d,
            vec![CaptureDecision {
                var: "data".into(),
                ownership: Ownership::Move
            }]
        );
    }

    #[test]
    fn capture_read_after_spawn_is_frozen() {
        let d = decisions(
            "fun main() {\n    let data = [1, 2, 3]\n    spawn(() -> { println(data) })\n    println(data)\n}\n",
        );
        assert_eq!(
            d,
            vec![CaptureDecision {
                var: "data".into(),
                ownership: Ownership::Freeze
            }]
        );
    }

    #[test]
    fn capture_mutated_in_spawn_and_live_is_cowned() {
        let d = decisions(
            "fun main() {\n    let count = 0\n    spawn(() -> { count = count + 1 })\n    println(count)\n}\n",
        );
        assert_eq!(
            d,
            vec![CaptureDecision {
                var: "count".into(),
                ownership: Ownership::Cown
            }]
        );
    }

    #[test]
    fn no_spawn_yields_no_decisions() {
        assert!(decisions("fun main() {\n    let x = 1\n    println(x)\n}\n").is_empty());
    }

    #[test]
    fn method_call_on_capture_counts_as_mutation() {
        // A mutating method call (not a direct assignment) must still cown the
        // capture, so it is lock-guarded across threads.
        let d = decisions(
            "fun main() {\n    let c = make()\n    spawn(() -> { c.add(1) })\n    use(c)\n}\n",
        );
        assert_eq!(
            d,
            vec![CaptureDecision {
                var: "c".into(),
                ownership: Ownership::Cown
            }]
        );
    }

    #[test]
    fn auto_acquire_wraps_a_cowned_spawn_body_in_with() {
        // The cowned capture's spawn body is rewritten to acquire it via `with`,
        // so concurrent mutation goes through the lock without any annotation.
        let mut body = main_body(
            "fun main() {\n    let c = make()\n    spawn(() -> { c.add(1) })\n    use(c)\n}\n",
        );
        auto_acquire(&mut body.stmts, &HashSet::new());
        let wrapped = body.stmts.iter().any(spawn_body_is_with);
        assert!(wrapped, "cowned spawn body should be wrapped in `with`");
    }

    fn spawn_body_is_with(stmt: &Stmt) -> bool {
        let Stmt::Expr(Expr::Call(callee, args, _)) = stmt else {
            return false;
        };
        if !matches!(&**callee, Expr::Ident(n, _) if n == "spawn") {
            return false;
        }
        let Some(Expr::Closure(_, body, _)) = args.first().map(|a| &a.expr) else {
            return false;
        };
        matches!(&**body, Expr::Call(c, _, _) if matches!(&**c, Expr::Ident(n, _) if n == "with"))
    }
}
