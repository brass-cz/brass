//! Automatic ownership analysis for `spawn` captures.
//!
//! A `spawn` runs its closure on a real OS thread, so each captured value is
//! shared between the spawner and that thread. The decision here is therefore
//! load-bearing, not advisory: [`auto_acquire`] realizes it before the spawn so
//! the capture has an atomic reference count from its first cross-thread
//! reference. A capture that is mutated *anywhere in the function* is made a cown
//! -- its access wrapped in `with` (or the group form `_with_all` when one body
//! touches several cowns), which lock-guards it on both the task and the spawner
//! side; a capture that is genuinely read-only is frozen (deeply immutable).
//! Both are `rc_atomic` owner classes, which is what makes the otherwise-racy
//! cross-thread reference counting sound. [`decide`] classifies a capture as
//! move/freeze/cown for the auto-acquire diagnostic.
//!
//! Spawn arguments the pass can see through are a closure literal or a local
//! bound to one in the same function; any other argument (a parameter, a field,
//! a call result) is rejected with a compile error ([`SpawnError`]) -- an
//! unanalyzed spawn would share its captures with no promotion and no lock,
//! which is exactly the silent data race this pass exists to prevent.
//!
//! [`spawn_capture_summaries`] additionally computes, per function, which
//! parameters are captured by a spawn reachable inside it (iterated to fixpoint
//! over the call graph); [`auto_acquire`] uses the summaries to promote and
//! guard a caller's local that it hands to such a function, so a spawn hidden in
//! a helper still serializes the caller's own accesses.

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::collections::{BTreeMap, BTreeSet};

use brass_parser::Span;
use brass_parser::ast::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ownership {
    /// Not live after the spawn: hand exclusive ownership to the thread.
    Move,
    /// Live after the spawn and mutated by no one: freeze (immutable share).
    Freeze,
    /// Mutated anywhere in the function (by the closure, the spawner, or through
    /// an alias), or a parameter whose callers the analysis cannot see: wrap in a
    /// cown with auto-acquire.
    Cown,
}

/// A diagnostic the pass reports through the driver's error path: a `spawn`
/// whose argument it cannot resolve to a closure body. Compiling it silently
/// would hand unguarded shared state to a thread.
#[derive(Clone, Debug)]
pub struct SpawnError {
    pub message: String,
    pub span: Span,
}

/// Interprocedural summaries: for each function or method name, the parameter
/// indices (0-based, `self` included for methods) whose argument object is
/// captured by a `spawn` reachable inside the callee. Keyed by bare name -- the
/// pass runs before name resolution -- so same-named functions merge; that only
/// over-approximates (extra promotion/locking), never under.
pub type SpawnSummaries = HashMap<String, HashSet<usize>>;

/// Decide ownership for `var` captured by a spawn in a function whose whole
/// (pristine) body is `fn_scope` and whose parameters are `params`, given
/// whether the variable is still used after the spawn point.
///
/// The mutation test deliberately covers the *whole function*, not just the
/// closure: a capture the task only reads still races if the spawner keeps
/// writing it after the spawn (through any alias), so it must be a lock-guarded
/// cown -- freezing it would let a writer race lock-free readers. A parameter is
/// always cowned: its callers are invisible here and may mutate concurrently.
pub fn decide(
    var: &str,
    live_after: bool,
    fn_scope: &Block,
    params: &HashSet<String>,
) -> Ownership {
    if !live_after {
        return Ownership::Move;
    }
    if params.contains(var) || mutates(fn_scope, var) {
        Ownership::Cown
    } else {
        Ownership::Freeze
    }
}

/// Builtins known to only read their arguments, so passing a capture to one is
/// not a mutation. Everything else -- user functions and any other builtin -- is
/// treated conservatively as possibly mutating an argument it receives by place:
/// an unannotated parameter is a mutable reference by default (book: types.md), so
/// `f(var)` may write through `var`. Over-approximating mutation is the safe
/// direction -- it cowns (lock-guards) a capture rather than freezing it -- so a
/// genuinely read-only capture is at worst needlessly locked, never raced.
const READONLY_BUILTINS: &[&str] = &["println", "print"];

/// Whether `body` mutates `var`: assigns to it (or a field/element of it), calls a
/// method on it, or passes it (or a place rooted at it) to a function that is not
/// known read-only. The whole expression tree is traversed, so a mutation reached
/// through a `match`/`if let`/nested closure/array/record/interpolation is found
/// (a gap here would freeze a mutated capture and let two threads race it).
///
/// Local aliases are followed conservatively: a `let a = <expr mentioning a known
/// alias>` may bind another handle to (or a container of) the same object -- a
/// bare copy (`let a = var`), a projection (`let a = var.f`), a wrapping
/// aggregate (`let a = Wrap { c: var }` / `[var]`), or a call result (`let a =
/// id(var)`). A later mutation through `a` then counts as a mutation of `var`.
/// The rule over-approximates (a scalar derived from `var` also becomes an
/// "alias"), which can only upgrade freeze to cown -- extra locking, never a race.
pub fn mutates(body: &Block, var: &str) -> bool {
    let mut found = false;
    let mut aliases = HashSet::default();
    aliases.insert(var.to_string());
    scan_block(body, &mut aliases, &mut found);
    found
}

fn scan_block(b: &Block, aliases: &mut HashSet<String>, found: &mut bool) {
    for s in &b.stmts {
        if *found {
            return;
        }
        scan_stmt(s, aliases, found);
    }
}

fn scan_stmt(s: &Stmt, aliases: &mut HashSet<String>, found: &mut bool) {
    match s {
        Stmt::Let { pat, value, .. } => {
            if let Some(value) = value {
                scan_expr(value, aliases, found);
                // A binding whose initializer mentions a current alias may be
                // another handle to (or a container of) the same object; track it
                // for the rest of the scan (see `mutates` for why
                // over-approximating here is safe).
                if let Pattern::Binding(name, _) = pat
                    && expr_mentions_any(value, aliases)
                {
                    aliases.insert(name.clone());
                }
            }
        }
        Stmt::Assign { target, value, .. } => {
            if root_ident(target).is_some_and(|r| aliases.contains(r)) {
                *found = true;
            }
            scan_expr(target, aliases, found);
            scan_expr(value, aliases, found);
            // A rebinding `a = <expr mentioning an alias>` makes `a` a handle too.
            if let Expr::Ident(name, _) = target
                && expr_mentions_any(value, aliases)
            {
                aliases.insert(name.clone());
            }
        }
        Stmt::Expr(e) => scan_expr(e, aliases, found),
        Stmt::While { cond, body, .. } => {
            scan_expr(cond, aliases, found);
            scan_block(body, aliases, found);
        }
        Stmt::For { iter, body, .. } => {
            scan_expr(iter, aliases, found);
            scan_block(body, aliases, found);
        }
        Stmt::Return(Some(e), _) => scan_expr(e, aliases, found),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

/// Whether `e` mentions (references as an identifier, anywhere inside) any name
/// in `names`. Used for the conservative alias rule: an initializer that touches
/// a known handle may alias its object.
fn expr_mentions_any(e: &Expr, names: &HashSet<String>) -> bool {
    let mut refs = HashSet::default();
    crate::closure::idents_stmts(&[Stmt::Expr(e.clone())], &mut refs);
    refs.iter().any(|r| names.contains(r))
}

/// Whether a call through `callee` is to a builtin known to only read its
/// arguments, so a capture passed to it is not mutated.
fn call_is_readonly(callee: &Expr) -> bool {
    matches!(callee, Expr::Ident(n, _) if READONLY_BUILTINS.contains(&n.as_str()))
}

/// Look for a mutation of any current alias inside an expression. Three forms
/// count as a mutation: a method call on a place rooted at an alias (`a.m(..)`),
/// an alias (or a place rooted at it) passed as an argument to a non-read-only
/// call, and -- via `scan_stmt` -- an assignment to it. Every sub-expression is
/// visited so a mutation nested anywhere is caught.
fn scan_expr(e: &Expr, aliases: &mut HashSet<String>, found: &mut bool) {
    if *found {
        return;
    }
    match e {
        Expr::Call(callee, args, _) => {
            // A method call on a place rooted at an alias may mutate it.
            if let Expr::Field(base, _, _) = &**callee
                && root_ident(base).is_some_and(|r| aliases.contains(r))
            {
                *found = true;
            }
            // Passing an alias (or `a.f` / `a[i]`) by reference to a function that
            // is not known read-only may mutate it through a mutable-reference
            // parameter. A value *derived* from an alias (e.g. `a + 1`, whose root
            // is not an identifier) is a fresh value and cannot alias it.
            if !call_is_readonly(callee) {
                for a in args {
                    if root_ident(&a.expr).is_some_and(|r| aliases.contains(r)) {
                        *found = true;
                    }
                }
            }
            scan_expr(callee, aliases, found);
            args.iter().for_each(|a| scan_expr(&a.expr, aliases, found));
        }
        Expr::Field(b, _, _) | Expr::Unary(_, b, _) | Expr::ErrorProp(b, _) => {
            scan_expr(b, aliases, found)
        }
        Expr::Index(b, idx, _) | Expr::Range(b, idx, _) | Expr::Binary(_, b, idx, _) => {
            scan_expr(b, aliases, found);
            scan_expr(idx, aliases, found);
        }
        Expr::Closure(_, body, _) => scan_expr(body, aliases, found),
        Expr::Array(elems, _) => elems.iter().for_each(|el| scan_expr(el, aliases, found)),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => fields
            .iter()
            .for_each(|(_, v)| scan_expr(v, aliases, found)),
        Expr::Str(segs, _) => segs.iter().for_each(|seg| {
            if let StrSeg::Expr(e) = seg {
                scan_expr(e, aliases, found);
            }
        }),
        Expr::Block(block, _) => scan_block(block, aliases, found),
        Expr::If(c, t, e, _) => {
            scan_expr(c, aliases, found);
            scan_block(t, aliases, found);
            if let Some(e) = e {
                scan_expr(e, aliases, found);
            }
        }
        Expr::IfLet(_, scrut, t, e, _) => {
            scan_expr(scrut, aliases, found);
            scan_block(t, aliases, found);
            if let Some(e) = e {
                scan_expr(e, aliases, found);
            }
        }
        Expr::Match(scrut, arms, _) => {
            scan_expr(scrut, aliases, found);
            arms.iter()
                .for_each(|arm| scan_expr(&arm.body, aliases, found));
        }
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => {}
    }
}

fn root_ident(e: &Expr) -> Option<&str> {
    match e {
        Expr::Ident(n, _) => Some(n),
        Expr::SelfExpr(_) => Some("self"),
        Expr::Field(b, _, _) | Expr::Index(b, _, _) => root_ident(b),
        _ => None,
    }
}

/// Names referenced (and thus captured) inside a spawn closure body. `bound` is
/// the closure's own params and top-level locals. Names a *nested* closure binds
/// are also excluded: they belong to the inner scope, so a nested spawn's loop
/// counter is not mistaken for a capture of this one.
pub fn captured(body: &Block, bound: &HashSet<String>) -> HashSet<String> {
    let mut refs = HashSet::default();
    crate::closure::idents_block(body, &mut refs);
    let mut nested = HashSet::default();
    collect_nested_closure_bindings(body, &mut nested);
    refs.into_iter()
        .filter(|r| !bound.contains(r) && !nested.contains(r))
        .collect()
}

/// Collect the params and locals bound inside any closure nested in `body`. Used
/// by [`captured`] to drop an inner closure's own bindings from the outer
/// closure's capture set.
fn collect_nested_closure_bindings(body: &Block, out: &mut HashSet<String>) {
    crate::closure::each_nested_closure(body, |params, cbody| {
        for p in params {
            out.insert(p.name.clone());
        }
        collect_local_bindings(&cbody.stmts, out);
    });
}

/// One captured variable's automatically chosen ownership at a `spawn` site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaptureDecision {
    pub var: String,
    pub ownership: Ownership,
}

/// Decide auto-ownership for every `spawn` capture reachable in a function
/// `body`. Liveness is approximated per statement list: a capture is "live
/// after" the spawn when it is referenced in a later statement of the same
/// block. Over-approximating liveness is safe: it can only upgrade `Move` to
/// `Freeze`/`Cown`, never the reverse. The decisions are deterministic (sorted
/// by variable name) so callers can report them.
pub fn analyze_spawns(body: &Block, params: &HashSet<String>) -> Vec<CaptureDecision> {
    analyze_spawns_stmts(&body.stmts, params)
}

/// As [`analyze_spawns`] but over a bare statement slice, for module-init code
/// whose top-level statements have no enclosing block. `params` are the
/// function's parameters (already in scope); local `let`/`for` bindings are added
/// automatically. Only these locals are subject to ownership transfer: a free
/// name that is a function or global is not a captured value.
pub fn analyze_spawns_stmts(stmts: &[Stmt], params: &HashSet<String>) -> Vec<CaptureDecision> {
    let mut locals = params.clone();
    collect_local_bindings(stmts, &mut locals);
    let fn_scope = stmts_block(stmts);
    let mut out = Vec::new();
    analyze_block(stmts, &locals, params, &fn_scope, &mut out);
    out
}

/// A whole statement slice viewed as one block, for whole-function queries.
fn stmts_block(stmts: &[Stmt]) -> Block {
    Block {
        stmts: stmts.to_vec(),
        span: Span::new(0, 0),
    }
}

fn analyze_block(
    stmts: &[Stmt],
    locals: &HashSet<String>,
    params: &HashSet<String>,
    fn_scope: &Block,
    out: &mut Vec<CaptureDecision>,
) {
    for (i, stmt) in stmts.iter().enumerate() {
        // Descend into every nested block (loops, conditionals, match arms, block
        // exprs), which may contain their own spawns.
        nested_block_stmts(stmt, &mut |inner| {
            analyze_block(inner, locals, params, fn_scope, out)
        });
        let Some(closure_body) = spawn_closure_body(stmt) else {
            continue;
        };
        // A nested spawn inside the spawned closure is its own site.
        analyze_block(&closure_body.stmts, locals, params, fn_scope, out);
        let bound = closure_bound_in(stmt);
        let mut captures: Vec<String> = captured(&closure_body, &bound)
            .into_iter()
            .filter(|name| locals.contains(name))
            .collect();
        captures.sort();
        let rest = &stmts[i + 1..];
        for var in captures {
            // Liveness must see through aliases: the object stays reachable after
            // the spawn through any handle bound from the capture (`let w = Wrap {
            // c }; ...; w.c.add(1)` keeps `c`'s object live even though the name
            // `c` never recurs), so a use of any alias keeps it from being moved.
            let handles = alias_closure(fn_scope, &var);
            let live_after = handles.iter().any(|h| stmts_reference(rest, h));
            out.push(CaptureDecision {
                ownership: decide(&var, live_after, fn_scope, params),
                var,
            });
        }
    }
}

/// The conservative alias closure of `var` over a function body: `var` plus every
/// name bound (by `let` or plain assignment, anywhere in the tree) from an
/// initializer that mentions a known handle. Matches the alias rule `mutates`
/// applies (see there for why over-approximating is safe).
fn alias_closure(fn_scope: &Block, var: &str) -> HashSet<String> {
    let mut handles: HashSet<String> = HashSet::default();
    handles.insert(var.to_string());
    loop {
        let before = handles.len();
        collect_mention_aliases(&fn_scope.stmts, &mut handles);
        if handles.len() == before {
            break;
        }
    }
    handles
}

fn collect_mention_aliases(stmts: &[Stmt], handles: &mut HashSet<String>) {
    for stmt in stmts {
        let binding: Option<(&String, &Expr)> = match stmt {
            Stmt::Let {
                pat: Pattern::Binding(name, _),
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
        if let Some((name, value)) = binding
            && expr_mentions_any(value, handles)
        {
            handles.insert(name.clone());
        }
        nested_block_stmts(stmt, &mut |inner| collect_mention_aliases(inner, handles));
    }
}

/// Collect names bound by `let`/`for` anywhere in a statement slice. Scoping is
/// ignored (a superset is safe: it only widens the set of names treated as
/// captured locals rather than globals). Every nested block -- loop bodies, `if`
/// / `if let` branches, `match` arms, block expressions -- is descended into, so a
/// capture bound inside one is still recognised as a transferable local.
/// Closure bodies are *not* descended into: their bindings belong to the
/// closure's own scope (see [`process_scope`]'s recursion).
fn collect_local_bindings(stmts: &[Stmt], out: &mut HashSet<String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { pat, .. } => collect_pattern_bindings(pat, out),
            Stmt::For { pat, .. } => collect_pattern_bindings(pat, out),
            _ => {}
        }
        nested_block_stmts(stmt, &mut |inner| collect_local_bindings(inner, out));
    }
}

/// Apply `f` to every statement list directly nested in `stmt` through control
/// flow: loop bodies, `if`/`if let` branches, `match` arms (block bodies), and
/// block expressions. Closures are *not* descended into (a spawn closure is a
/// separate execution scope). The mutable twin is [`nested_block_stmts_mut`].
fn nested_block_stmts(stmt: &Stmt, f: &mut dyn FnMut(&[Stmt])) {
    match stmt {
        Stmt::While { body, .. } | Stmt::For { body, .. } => f(&body.stmts),
        Stmt::Expr(e) | Stmt::Let { value: Some(e), .. } | Stmt::Return(Some(e), _) => {
            nested_block_stmts_expr(e, f)
        }
        _ => {}
    }
}

fn nested_block_stmts_expr(e: &Expr, f: &mut dyn FnMut(&[Stmt])) {
    match e {
        Expr::If(_, t, els, _) | Expr::IfLet(_, _, t, els, _) => {
            f(&t.stmts);
            if let Some(els) = els {
                nested_block_stmts_expr(els, f);
            }
        }
        Expr::Block(b, _) => f(&b.stmts),
        Expr::Match(_, arms, _) => {
            for arm in arms {
                if let Expr::Block(b, _) = &arm.body {
                    f(&b.stmts);
                }
            }
        }
        _ => {}
    }
}

/// Mutable [`nested_block_stmts`]: apply `f` to every directly-nested statement
/// list so a pass that rewrites the AST (auto-acquire) reaches spawns nested in
/// conditionals and blocks, not only at the top level of a function or loop.
fn nested_block_stmts_mut(stmt: &mut Stmt, f: &mut dyn FnMut(&mut Vec<Stmt>)) {
    match stmt {
        Stmt::While { body, .. } | Stmt::For { body, .. } => f(&mut body.stmts),
        Stmt::Expr(e) | Stmt::Let { value: Some(e), .. } | Stmt::Return(Some(e), _) => {
            nested_block_stmts_expr_mut(e, f)
        }
        _ => {}
    }
}

fn nested_block_stmts_expr_mut(e: &mut Expr, f: &mut dyn FnMut(&mut Vec<Stmt>)) {
    match e {
        Expr::If(_, t, els, _) | Expr::IfLet(_, _, t, els, _) => {
            f(&mut t.stmts);
            if let Some(els) = els {
                nested_block_stmts_expr_mut(els, f);
            }
        }
        Expr::Block(b, _) => f(&mut b.stmts),
        Expr::Match(_, arms, _) => {
            for arm in arms {
                if let Expr::Block(b, _) = &mut arm.body {
                    f(&mut b.stmts);
                }
            }
        }
        _ => {}
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

// ----- spawn-site shapes -----

/// The argument shape of a `spawn(..)` statement.
enum SpawnArg<'a> {
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
fn spawn_arg(stmt: &Stmt) -> Option<SpawnArg<'_>> {
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
fn spawn_closure_body(stmt: &Stmt) -> Option<Block> {
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

fn closure_bound_in(stmt: &Stmt) -> HashSet<String> {
    let expr = match stmt {
        Stmt::Expr(e) | Stmt::Let { value: Some(e), .. } => e,
        _ => return HashSet::default(),
    };
    if let Expr::Call(_, args, _) = expr
        && let Some(Expr::Closure(params, body, _)) = args.first().map(|a| &a.expr)
    {
        return crate::closure::bound_names(params, &closure_block(body));
    }
    HashSet::default()
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
    let mut refs = HashSet::default();
    crate::closure::idents_stmts(stmts, &mut refs);
    refs.contains(var)
}

/// The names of the local variables that are spawned as closure variables
/// (`spawn(name)`) anywhere in this scope's control-flow tree.
fn spawned_var_names(stmts: &[Stmt], out: &mut HashSet<String>) {
    for stmt in stmts {
        if let Some(SpawnArg::Var(name, _)) = spawn_arg(stmt) {
            out.insert(name.to_string());
        }
        nested_block_stmts(stmt, &mut |inner| spawned_var_names(inner, out));
    }
}

/// The closure literals bound to `name` (via `let name = <closure>` or
/// `name = <closure>`) in this scope's control-flow tree, as `(params, body)`.
fn closure_bindings_of(stmts: &[Stmt], name: &str, out: &mut Vec<(Vec<Param>, Block)>) {
    for stmt in stmts {
        match stmt {
            Stmt::Let {
                pat: Pattern::Binding(n, _),
                value: Some(Expr::Closure(params, body, _)),
                ..
            } if n == name => out.push((params.clone(), closure_block(body))),
            Stmt::Assign {
                target: Expr::Ident(n, _),
                value: Expr::Closure(params, body, _),
                ..
            } if n == name => out.push((params.clone(), closure_block(body))),
            _ => {}
        }
        nested_block_stmts(stmt, &mut |inner| closure_bindings_of(inner, name, out));
    }
}

// ----- interprocedural summaries -----

/// Compute [`SpawnSummaries`] for a program's functions and methods, given each
/// as `(name, parameter names, body)`. Two steps:
///
/// 1. Direct: a spawn site inside `f` (literal, or a closure variable bound in
///    `f`) captures one of `f`'s parameters.
/// 2. Transitive fixpoint: `f` passes a place rooted at one of its parameters
///    into a call position already known to be spawn-captured (`fun f(p) {
///    start(p) }` where `start` spawns a task capturing its first parameter
///    makes `p` spawn-captured in `f` too), like the write-through-parameter
///    analysis in `brass_hir::mutation`.
pub fn spawn_capture_summaries(fns: &[(String, Vec<String>, &Block)]) -> SpawnSummaries {
    let mut summaries: SpawnSummaries = HashMap::default();

    // Step 1: direct captures of a parameter by a spawn site in the body.
    for (name, params, body) in fns {
        let mut captured_params: HashSet<usize> = HashSet::default();
        each_scope_spawn_body(&body.stmts, &body.stmts, &mut |cbody, bound| {
            for cap in captured(cbody, bound) {
                if let Some(i) = params.iter().position(|p| *p == cap) {
                    captured_params.insert(i);
                }
            }
        });
        if !captured_params.is_empty() {
            summaries
                .entry(name.clone())
                .or_default()
                .extend(captured_params);
        }
    }

    // Step 2: propagate through call sites until nothing changes.
    loop {
        let mut changed = false;
        for (name, params, body) in fns {
            let mut found: HashSet<usize> = HashSet::default();
            each_call(&stmts_block(&body.stmts), &mut |callee, recv, args| {
                let Some(indices) = summaries.get(callee) else {
                    return;
                };
                for &j in indices {
                    let arg = match recv {
                        // Method call: position 0 is the receiver.
                        Some(r) if j == 0 => Some(r),
                        Some(_) => args.get(j - 1).map(|a| &a.expr),
                        None => args.get(j).map(|a| &a.expr),
                    };
                    if let Some(root) = arg.and_then(root_ident)
                        && let Some(i) = params.iter().position(|p| *p == root)
                    {
                        found.insert(i);
                    }
                }
            });
            if !found.is_empty() {
                let entry = summaries.entry(name.clone()).or_default();
                for i in found {
                    changed |= entry.insert(i);
                }
            }
        }
        if !changed {
            break;
        }
    }
    summaries
}

/// Visit every spawn-closure body reachable in the scope tree rooted at `stmts`
/// (through control flow and through nested spawn closures): literal spawn
/// arguments and closures bound to a spawned local. `all` is the full scope for
/// resolving closure-variable bindings. Used for summary computation, where
/// unresolvable spawn arguments are simply skipped (the transform reports them).
fn each_scope_spawn_body(
    stmts: &[Stmt],
    all: &[Stmt],
    f: &mut impl FnMut(&Block, &HashSet<String>),
) {
    let mut vars = HashSet::default();
    spawned_var_names(stmts, &mut vars);
    for name in &vars {
        let mut bindings = Vec::new();
        closure_bindings_of(all, name, &mut bindings);
        for (params, body) in bindings {
            let bound = crate::closure::bound_names(&params, &body);
            f(&body, &bound);
            each_scope_spawn_body(&body.stmts, &body.stmts, f);
        }
    }
    each_literal_spawn(stmts, &mut |stmt| {
        if let Some(body) = spawn_closure_body(stmt) {
            let bound = closure_bound_in(stmt);
            f(&body, &bound);
            each_scope_spawn_body(&body.stmts, &body.stmts, f);
        }
    });
}

/// Visit every statement in the control-flow tree that is a literal spawn site.
fn each_literal_spawn(stmts: &[Stmt], f: &mut impl FnMut(&Stmt)) {
    for stmt in stmts {
        if matches!(spawn_arg(stmt), Some(SpawnArg::Literal)) {
            f(stmt);
        }
        nested_block_stmts(stmt, &mut |inner| each_literal_spawn(inner, f));
    }
}

/// Visit every call expression in `block` (descending everything, closures
/// included) as `(callee name, method receiver, args)`. A free call `g(a, b)`
/// yields `("g", None, args)`; a method call `r.m(a)` yields `("m", Some(r),
/// args)`.
fn each_call<'a>(block: &'a Block, f: &mut impl FnMut(&'a str, Option<&'a Expr>, &'a [Arg])) {
    fn walk_stmt<'a>(s: &'a Stmt, f: &mut impl FnMut(&'a str, Option<&'a Expr>, &'a [Arg])) {
        match s {
            Stmt::Let {
                value: Some(value), ..
            }
            | Stmt::Expr(value)
            | Stmt::Return(Some(value), _) => walk_expr(value, f),
            Stmt::Let { value: None, .. } => {}
            Stmt::Assign { target, value, .. } => {
                walk_expr(target, f);
                walk_expr(value, f);
            }
            Stmt::While { cond, body, .. } => {
                walk_expr(cond, f);
                body.stmts.iter().for_each(|s| walk_stmt(s, f));
            }
            Stmt::For { iter, body, .. } => {
                walk_expr(iter, f);
                body.stmts.iter().for_each(|s| walk_stmt(s, f));
            }
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }
    fn walk_expr<'a>(e: &'a Expr, f: &mut impl FnMut(&'a str, Option<&'a Expr>, &'a [Arg])) {
        match e {
            Expr::Call(callee, args, _) => {
                match callee.as_ref() {
                    Expr::Ident(name, _) => f(name, None, args),
                    Expr::Field(base, method, _) => f(method, Some(base), args),
                    _ => {}
                }
                walk_expr(callee, f);
                args.iter().for_each(|a| walk_expr(&a.expr, f));
            }
            Expr::Field(b, _, _) | Expr::Unary(_, b, _) | Expr::ErrorProp(b, _) => walk_expr(b, f),
            Expr::Index(b, i, _) | Expr::Range(b, i, _) | Expr::Binary(_, b, i, _) => {
                walk_expr(b, f);
                walk_expr(i, f);
            }
            Expr::Closure(_, body, _) => walk_expr(body, f),
            Expr::Array(elems, _) => elems.iter().for_each(|el| walk_expr(el, f)),
            Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
                fields.iter().for_each(|(_, v)| walk_expr(v, f))
            }
            Expr::Str(segs, _) => segs.iter().for_each(|seg| {
                if let StrSeg::Expr(e) = seg {
                    walk_expr(e, f);
                }
            }),
            Expr::Block(b, _) => b.stmts.iter().for_each(|s| walk_stmt(s, f)),
            Expr::If(c, t, e, _) => {
                walk_expr(c, f);
                t.stmts.iter().for_each(|s| walk_stmt(s, f));
                if let Some(e) = e {
                    walk_expr(e, f);
                }
            }
            Expr::IfLet(_, scrut, t, e, _) => {
                walk_expr(scrut, f);
                t.stmts.iter().for_each(|s| walk_stmt(s, f));
                if let Some(e) = e {
                    walk_expr(e, f);
                }
            }
            Expr::Match(scrut, arms, _) => {
                walk_expr(scrut, f);
                arms.iter().for_each(|arm| walk_expr(&arm.body, f));
            }
            Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(_)
            | Expr::Ident(..)
            | Expr::SelfExpr(_) => {}
        }
    }
    block.stmts.iter().for_each(|s| walk_stmt(s, f));
}

// ----- auto-acquire -----

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
    /// Interprocedural spawn-capture summaries.
    summaries: &'a SpawnSummaries,
    /// Locals of this scope that are spawned as closure variables.
    spawned_vars: HashSet<String>,
    /// Locals promoted to cowns because they are passed to a call position that
    /// a callee spawn captures (per the summaries).
    summary_cowns: BTreeSet<String>,
    /// Handle name -> the cown roots whose locks guard a dereference through it.
    /// A cown maps to itself; an alias (`let h = o.inner`, `let w = Wrap { c }`,
    /// `let d = id(c)`) maps to the cown(s) its initializer mentions, so its
    /// accesses are serialized under the *object's* lock, not the handle's.
    guards: BTreeMap<String, BTreeSet<String>>,
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
/// Returns the compile errors for spawn arguments the pass cannot analyze; the
/// caller surfaces them through the driver diagnostics (running such a spawn
/// unguarded would be a silent data race).
/// Reject spawn shapes the ownership pass cannot make race-free, checked over
/// the PRISTINE tree before `auto_acquire` rewrites it:
///
/// - a `spawn` inside a closure literal that is not itself spawned: the pass
///   analyzes function bodies and spawned closures only, so such a spawn's
///   captures would get no promotion and no guarding at all;
/// - a spawned task touching a module global that is written anywhere in the
///   program: module storage has no binding to promote to a cown, so the task
///   and any writer would race unguarded. Never-written globals stay shareable.
pub fn pre_spawn_errors(
    stmts: &[Stmt],
    params: &HashSet<String>,
    mutated_globals: &HashSet<String>,
) -> Vec<SpawnError> {
    let mut errors = Vec::new();
    let mut bound = params.clone();
    collect_local_bindings(stmts, &mut bound);
    pre_scan_scope(stmts, stmts, &bound, mutated_globals, &mut errors);
    errors
}

fn pre_scan_scope(
    stmts: &[Stmt],
    all: &[Stmt],
    bound: &HashSet<String>,
    mutated_globals: &HashSet<String>,
    errors: &mut Vec<SpawnError>,
) {
    let mut spawned = HashSet::default();
    spawned_var_names(stmts, &mut spawned);
    for stmt in stmts {
        match spawn_arg(stmt) {
            Some(SpawnArg::Literal) => {
                if let Some(body) = spawn_closure_body(stmt) {
                    pre_check_spawn_body(&body, stmt.span(), bound, mutated_globals, errors);
                }
                continue;
            }
            // The variable's binding closures are visited below; an opaque
            // argument is reported by `auto_acquire` itself.
            Some(SpawnArg::Var(..)) | Some(SpawnArg::Opaque(..)) => continue,
            None => {}
        }
        // A `let f = () -> ...` binding of a variable that IS spawned in this
        // scope is a spawn body, not a plain closure.
        if let Stmt::Let {
            pat: brass_parser::ast::Pattern::Binding(name, _),
            value: Some(Expr::Closure(..)),
            ..
        } = stmt
            && spawned.contains(name)
        {
            continue;
        }
        if let Stmt::Assign {
            target: Expr::Ident(name, _),
            value: Expr::Closure(..),
            ..
        } = stmt
            && spawned.contains(name)
        {
            continue;
        }
        nested_block_stmts(stmt, &mut |inner| {
            pre_scan_scope(inner, all, bound, mutated_globals, errors)
        });
        each_stmt_expr(stmt, &mut |e| pre_check_plain_expr(e, errors));
    }
    // Spawned-variable bindings: their closure bodies are spawn scopes.
    for name in &spawned {
        let mut bindings = Vec::new();
        closure_bindings_of(all, name, &mut bindings);
        for (cparams, body) in bindings {
            let span = body.span;
            let mut cbound = bound.clone();
            cbound.extend(cparams.iter().map(|p| p.name.clone()));
            pre_check_spawn_body(&body, span, &cbound, mutated_globals, errors);
        }
    }
}

/// Check one spawned closure body: no writable-global captures, then recurse
/// into it as its own scope (it may host nested spawns and plain closures).
fn pre_check_spawn_body(
    body: &Block,
    span: Span,
    enclosing_bound: &HashSet<String>,
    mutated_globals: &HashSet<String>,
    errors: &mut Vec<SpawnError>,
) {
    let cbound = crate::closure::bound_names(&[], body);
    let mut frees: Vec<String> = captured(body, &cbound)
        .into_iter()
        .filter(|n| !enclosing_bound.contains(n) && mutated_globals.contains(n))
        .collect();
    frees.sort();
    for name in frees {
        errors.push(SpawnError {
            message: format!(
                "spawned task accesses module global `{name}`, which is written \
                 elsewhere; share it through a local value captured by the task"
            ),
            span,
        });
    }
    let mut inner = enclosing_bound.clone();
    collect_local_bindings(&body.stmts, &mut inner);
    pre_scan_scope(&body.stmts, &body.stmts, &inner, mutated_globals, errors);
}

/// A closure literal in a plain expression position (not a spawn argument or a
/// spawned variable's binding) must not contain a `spawn`: the pass never
/// analyzes such a body, so the spawn's captures would be entirely unguarded.
fn pre_check_plain_expr(e: &Expr, errors: &mut Vec<SpawnError>) {
    if let Expr::Closure(_, body, _) = e {
        let mut spans = Vec::new();
        collect_spawn_spans_expr(body, &mut spans);
        for span in spans {
            errors.push(SpawnError {
                message: "`spawn` inside a closure that is not itself spawned is not \
                          analyzable; spawn from the enclosing body or a named function"
                    .to_string(),
                span,
            });
        }
    }
}

/// Every direct subexpression of `stmt` (not descending into nested statement
/// blocks, which `nested_block_stmts` covers).
fn each_stmt_expr(stmt: &Stmt, f: &mut dyn FnMut(&Expr)) {
    match stmt {
        Stmt::Let {
            value: Some(value), ..
        } => each_expr(value, f),
        Stmt::Let { value: None, .. } => {}
        Stmt::Assign { target, value, .. } => {
            each_expr(target, f);
            each_expr(value, f);
        }
        Stmt::Expr(e) => each_expr(e, f),
        Stmt::While { cond, .. } => each_expr(cond, f),
        Stmt::For { iter, .. } => each_expr(iter, f),
        Stmt::Return(Some(e), _) => each_expr(e, f),
        _ => {}
    }
}

/// Apply `f` to `e` and every nested expression, without crossing into
/// statement blocks of control-flow expressions (covered by the statement
/// walk) but including closure literals themselves (`f` decides whether to
/// look inside).
fn each_expr(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    match e {
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) | Expr::Field(inner, _, _) => {
            each_expr(inner, f)
        }
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
            each_expr(a, f);
            each_expr(b, f);
        }
        Expr::Call(callee, args, _) => {
            each_expr(callee, f);
            for a in args {
                each_expr(&a.expr, f);
            }
        }
        Expr::Array(items, _) => {
            for i in items {
                each_expr(i, f);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, fe) in fields {
                each_expr(fe, f);
            }
        }
        Expr::Str(segs, _) => {
            for seg in segs {
                if let brass_parser::ast::StrSeg::Expr(inner) = seg {
                    each_expr(inner, f);
                }
            }
        }
        _ => {}
    }
}

/// Spans of every `spawn(..)` call reachable in `e`, including inside nested
/// closures and control-flow blocks.
fn collect_spawn_spans_expr(e: &Expr, out: &mut Vec<Span>) {
    if let Expr::Call(callee, _, span) = e
        && matches!(&**callee, Expr::Ident(n, _) if n == "spawn")
    {
        out.push(*span);
    }
    match e {
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) | Expr::Field(inner, _, _) => {
            collect_spawn_spans_expr(inner, out)
        }
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
            collect_spawn_spans_expr(a, out);
            collect_spawn_spans_expr(b, out);
        }
        Expr::Call(callee, args, _) => {
            collect_spawn_spans_expr(callee, out);
            for a in args {
                collect_spawn_spans_expr(&a.expr, out);
            }
        }
        Expr::Array(items, _) => {
            for i in items {
                collect_spawn_spans_expr(i, out);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, fe) in fields {
                collect_spawn_spans_expr(fe, out);
            }
        }
        Expr::Str(segs, _) => {
            for seg in segs {
                if let brass_parser::ast::StrSeg::Expr(inner) = seg {
                    collect_spawn_spans_expr(inner, out);
                }
            }
        }
        Expr::Closure(_, body, _) => collect_spawn_spans_expr(body, out),
        Expr::Block(b, _) => {
            for s in &b.stmts {
                collect_spawn_spans_stmt(s, out);
            }
        }
        Expr::If(c, t, els, _) => {
            collect_spawn_spans_expr(c, out);
            for s in &t.stmts {
                collect_spawn_spans_stmt(s, out);
            }
            if let Some(e) = els {
                collect_spawn_spans_expr(e, out);
            }
        }
        Expr::IfLet(_, scrut, t, els, _) => {
            collect_spawn_spans_expr(scrut, out);
            for s in &t.stmts {
                collect_spawn_spans_stmt(s, out);
            }
            if let Some(e) = els {
                collect_spawn_spans_expr(e, out);
            }
        }
        Expr::Match(scrut, arms, _) => {
            collect_spawn_spans_expr(scrut, out);
            for arm in arms {
                collect_spawn_spans_expr(&arm.body, out);
            }
        }
        _ => {}
    }
}

/// Spans of every `spawn` in `stmts`, at any nesting depth (closures included).
/// The driver uses this to reject module-top-level spawns: init code never runs
/// through the ownership pass, so nothing would promote or guard their captures.
pub fn all_spawn_spans(stmts: &[Stmt]) -> Vec<Span> {
    let mut out = Vec::new();
    for s in stmts {
        collect_spawn_spans_stmt(s, &mut out);
    }
    out
}

fn collect_spawn_spans_stmt(stmt: &Stmt, out: &mut Vec<Span>) {
    each_stmt_expr(stmt, &mut |e| {
        if let Expr::Call(callee, _, span) = e
            && matches!(&**callee, Expr::Ident(n, _) if n == "spawn")
        {
            out.push(*span);
        }
        if let Expr::Closure(_, body, _) = e {
            collect_spawn_spans_expr(body, out);
        }
    });
    nested_block_stmts(stmt, &mut |inner| {
        for s in inner {
            collect_spawn_spans_stmt(s, out);
        }
    });
}

pub fn auto_acquire(
    stmts: &mut Vec<Stmt>,
    params: &HashSet<String>,
    summaries: &SpawnSummaries,
) -> Vec<SpawnError> {
    let mut errors = Vec::new();
    let pristine = stmts_block(stmts);
    process_scope(stmts, params, params, &pristine, summaries, &mut errors);
    errors
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
    errors: &mut Vec<SpawnError>,
) {
    let mut locals = in_scope.clone();
    collect_local_bindings(stmts, &mut locals);

    // ---- analysis over the pristine scope ----
    let mut spawned_vars = HashSet::default();
    spawned_var_names(stmts, &mut spawned_vars);

    // Union of every site's cowned captures in this scope (literal sites plus
    // resolved closure-variable sites), for the scope-wide guard set.
    let mut all_cowns: BTreeSet<String> = BTreeSet::new();
    each_scope_site_shallow(stmts, stmts, &mut |cbody, bound| {
        let (cowns, _) = classify_captures(cbody, bound, &locals, fn_params, pristine_fn);
        all_cowns.extend(cowns);
    });

    // Locals handed to spawn-capturing call positions become cowns too.
    let summary_cowns = collect_summary_cowns(stmts, &locals, summaries);
    all_cowns.extend(summary_cowns.iter().cloned());

    let ctx = ScopeCtx {
        guards: guard_map(stmts, &all_cowns),
        pristine_scope: stmts_block(stmts),
        locals,
        fn_params,
        pristine_fn,
        summaries,
        spawned_vars,
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
            guard_stmt_accesses(stmt, &ctx.guards);
        }
    }

    // ---- rewrite spawn sites, closure-variable bindings, and promotions ----
    transform_stmts(stmts, &ctx, errors);
}

/// Visit each spawn site body of *this scope only* (literal spawn statements in
/// the control-flow tree, plus the binding closures of spawned locals). Unlike
/// [`each_scope_spawn_body`] this does not recurse into the spawned bodies:
/// nested spawns belong to the inner scope, which classifies against its own
/// locals.
fn each_scope_site_shallow(
    stmts: &[Stmt],
    all: &[Stmt],
    f: &mut impl FnMut(&Block, &HashSet<String>),
) {
    let mut vars = HashSet::default();
    spawned_var_names(stmts, &mut vars);
    for name in &vars {
        let mut bindings = Vec::new();
        closure_bindings_of(all, name, &mut bindings);
        for (params, body) in bindings {
            let bound = crate::closure::bound_names(&params, &body);
            f(&body, &bound);
        }
    }
    each_literal_spawn(stmts, &mut |stmt| {
        if let Some(body) = spawn_closure_body(stmt) {
            let bound = closure_bound_in(stmt);
            f(&body, &bound);
        }
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

/// Build the handle -> lock-roots map for a scope: each cown guards itself, and
/// every binding whose initializer mentions a known handle inherits (the union
/// of) the mentioned handles' roots, iterated to fixpoint so chains (`let a =
/// c; let b = [a]`) resolve. The alias rule intentionally over-approximates
/// (see [`mutates`]); a scalar wrongly treated as an alias just acquires a lock
/// it does not need.
fn guard_map(stmts: &[Stmt], cowns: &BTreeSet<String>) -> BTreeMap<String, BTreeSet<String>> {
    let mut guards: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for c in cowns {
        guards.entry(c.clone()).or_default().insert(c.clone());
    }
    if guards.is_empty() {
        return guards;
    }
    loop {
        let mut changed = false;
        collect_alias_roots(stmts, &mut guards, &mut changed);
        if !changed {
            break;
        }
    }
    guards
}

fn collect_alias_roots(
    stmts: &[Stmt],
    guards: &mut BTreeMap<String, BTreeSet<String>>,
    changed: &mut bool,
) {
    for stmt in stmts {
        let binding: Option<(&String, &Expr)> = match stmt {
            Stmt::Let {
                pat: Pattern::Binding(name, _),
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
        }
        // Aliases may be bound inside nested blocks (a conditional, a loop).
        nested_block_stmts(stmt, &mut |inner| {
            collect_alias_roots(inner, guards, changed)
        });
    }
}

/// The transformation walk over a scope's statement lists: wrap spawn bodies,
/// recurse into them as their own scopes, wrap the binding closures of spawned
/// locals, and insert ownership promotions.
fn transform_stmts(stmts: &mut Vec<Stmt>, ctx: &ScopeCtx, errors: &mut Vec<SpawnError>) {
    let mut i = 0;
    while i < stmts.len() {
        // Recurse into nested control-flow blocks, which may contain their own
        // spawn statements and bindings.
        nested_block_stmts_mut(&mut stmts[i], &mut |inner| {
            transform_stmts(inner, ctx, errors)
        });

        // A binding of a spawned closure variable: process its body as a scope
        // of its own (nested spawns) and wrap it for its cowned captures, exactly
        // as a literal spawn argument is.
        transform_spawned_binding(&mut stmts[i], ctx, errors);

        let mut inserted = 0;
        match spawn_arg(&stmts[i]) {
            Some(SpawnArg::Literal) => {
                let body = spawn_closure_body(&stmts[i]).expect("literal spawn body");
                let bound = closure_bound_in(&stmts[i]);
                let (cowns, freezes) =
                    classify_captures(&body, &bound, &ctx.locals, ctx.fn_params, ctx.pristine_fn);
                // The spawned body is its own execution scope; nested spawns in
                // it are classified against its own locals.
                if let Some(inner) = spawn_closure_body_mut(&mut stmts[i]) {
                    process_scope(
                        inner,
                        &ctx.locals,
                        ctx.fn_params,
                        ctx.pristine_fn,
                        ctx.summaries,
                        errors,
                    );
                }
                if !cowns.is_empty() {
                    wrap_spawn_body(&mut stmts[i], &cowns);
                }
                inserted = insert_promotions(stmts, i, &cowns, &freezes);
            }
            Some(SpawnArg::Var(name, span)) => {
                // Resolve the closure literal(s) bound to `name` anywhere in this
                // scope's pristine tree (the spawn may be in a nested list, the
                // binding in an enclosing or sibling one; a binding in a
                // *different* scope -- another closure's body -- is a different
                // thread context and does not resolve).
                let mut bindings = Vec::new();
                closure_bindings_of(&ctx.pristine_scope.stmts, name, &mut bindings);
                if bindings.is_empty() {
                    errors.push(SpawnError {
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
                    for (params, body) in &bindings {
                        let bound = crate::closure::bound_names(params, body);
                        let (c, f) = classify_captures(
                            body,
                            &bound,
                            &ctx.locals,
                            ctx.fn_params,
                            ctx.pristine_fn,
                        );
                        cowns.extend(c);
                        freezes.extend(f);
                    }
                    let freezes: Vec<String> = freezes.difference(&cowns).cloned().collect();
                    let cowns: Vec<String> = cowns.into_iter().collect();
                    inserted = insert_promotions(stmts, i, &cowns, &freezes);
                }
            }
            Some(SpawnArg::Opaque(span)) => {
                errors.push(SpawnError {
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
fn transform_spawned_binding(stmt: &mut Stmt, ctx: &ScopeCtx, errors: &mut Vec<SpawnError>) {
    let (name, params, body) = match stmt {
        Stmt::Let {
            pat: Pattern::Binding(name, _),
            value: Some(Expr::Closure(params, body, _)),
            ..
        } => (name, params, body),
        Stmt::Assign {
            target: Expr::Ident(name, _),
            value: Expr::Closure(params, body, _),
            ..
        } => (name, params, body),
        _ => return,
    };
    if !ctx.spawned_vars.contains(name.as_str()) {
        return;
    }
    let block = closure_block(body);
    let bound = crate::closure::bound_names(params, &block);
    let (cowns, _) = classify_captures(&block, &bound, &ctx.locals, ctx.fn_params, ctx.pristine_fn);
    // The bound closure body is its own execution scope once spawned.
    if let Expr::Block(b, _) = body.as_mut() {
        process_scope(
            &mut b.stmts,
            &ctx.locals,
            ctx.fn_params,
            ctx.pristine_fn,
            ctx.summaries,
            errors,
        );
    }
    if !cowns.is_empty() {
        let span = body.span();
        let original = std::mem::replace(body.as_mut(), Expr::Null(span));
        *body.as_mut() = wrap_with(original, &cowns);
    }
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
        pat: Pattern::Binding(name, _),
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
fn spawn_closure_body_mut(stmt: &mut Stmt) -> Option<&mut Vec<Stmt>> {
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
    match body.as_mut() {
        Expr::Block(b, _) => Some(&mut b.stmts),
        _ => None,
    }
}

// ----- access guarding -----

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
fn guard_stmt_accesses(stmt: &mut Stmt, guards: &BTreeMap<String, BTreeSet<String>>) {
    match stmt {
        Stmt::Let {
            value: Some(value), ..
        } => guard_expr_accesses(value, guards),
        Stmt::Let { value: None, .. } => {}
        Stmt::Assign { target, value, .. } => {
            // A whole `c.f = v` (or `c[i] = v`) store is guarded as one unit so
            // both the place and the value evaluate under the lock.
            if root_ident(target).is_some_and(|r| guards.contains_key(r)) {
                guard_assign(stmt, guards);
                return;
            }
            guard_expr_accesses(target, guards);
            guard_expr_accesses(value, guards);
        }
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => guard_expr_accesses(e, guards),
        Stmt::While { cond, body, .. } => {
            guard_expr_accesses(cond, guards);
            for s in &mut body.stmts {
                guard_stmt_accesses(s, guards);
            }
        }
        Stmt::For { iter, body, .. } => {
            guard_expr_accesses(iter, guards);
            for s in &mut body.stmts {
                guard_stmt_accesses(s, guards);
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
fn guard_assign(stmt: &mut Stmt, guards: &BTreeMap<String, BTreeSet<String>>) {
    let placeholder = Stmt::Break(stmt_span(stmt));
    let mut original = std::mem::replace(stmt, placeholder);
    let mut roots: BTreeSet<String> = BTreeSet::new();
    if let Stmt::Assign { target, value, .. } = &mut original {
        if let Some(r) = root_ident(target).and_then(|r| guards.get(r)) {
            roots.extend(r.iter().cloned());
        }
        guard_expr_accesses(value, guards);
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
fn guard_expr_accesses(expr: &mut Expr, guards: &BTreeMap<String, BTreeSet<String>>) {
    // Guard nested accesses first so they are serialized even when this node is
    // not itself wrapped (and stay correctly nested when it is).
    guard_children(expr, guards);
    // Then, if this node directly dereferences guarded handles, wrap the whole
    // node under the union of their lock roots.
    let roots = direct_guard_roots(expr, guards);
    if !roots.is_empty() {
        let span = expr.span();
        let original = std::mem::replace(expr, Expr::Null(span));
        *expr = wrap_with(original, &roots);
    }
}

/// Recurse into an expression's children, guarding any cown access inside them.
/// A `Call`'s by-reference operands (its method receiver and the arguments that
/// are plain places rooted at a guarded handle) are *not* descended into here --
/// they are handled by wrapping the whole call in [`guard_expr_accesses`] -- so a
/// bare cown argument is not mistaken for a standalone read.
fn guard_children(expr: &mut Expr, guards: &BTreeMap<String, BTreeSet<String>>) {
    match expr {
        Expr::Call(callee, args, _) => {
            // A method receiver is part of the call's by-reference access; only
            // descend into a non-method callee.
            if !matches!(callee.as_ref(), Expr::Field(..)) {
                guard_expr_accesses(callee, guards);
            }
            if callee_is_non_forwarding(callee) {
                return;
            }
            for a in args.iter_mut() {
                // A bare place passed as an argument is guarded by wrapping the
                // call; descend only into compound argument expressions.
                if direct_arg_guard_roots(&a.expr, guards).is_none() {
                    guard_expr_accesses(&mut a.expr, guards);
                }
            }
        }
        Expr::Field(b, _, _) | Expr::Unary(_, b, _) | Expr::ErrorProp(b, _) => {
            guard_expr_accesses(b, guards)
        }
        Expr::Index(b, idx, _) | Expr::Range(b, idx, _) | Expr::Binary(_, b, idx, _) => {
            guard_expr_accesses(b, guards);
            guard_expr_accesses(idx, guards);
        }
        Expr::Array(elems, _) => elems
            .iter_mut()
            .for_each(|el| guard_expr_accesses(el, guards)),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => fields
            .iter_mut()
            .for_each(|(_, v)| guard_expr_accesses(v, guards)),
        Expr::Str(segs, _) => segs.iter_mut().for_each(|seg| {
            if let StrSeg::Expr(e) = seg {
                guard_expr_accesses(e, guards);
            }
        }),
        Expr::Block(block, _) => {
            for s in &mut block.stmts {
                guard_stmt_accesses(s, guards);
            }
        }
        Expr::If(c, t, e, _) => {
            guard_expr_accesses(c, guards);
            for s in &mut t.stmts {
                guard_stmt_accesses(s, guards);
            }
            if let Some(e) = e {
                guard_expr_accesses(e, guards);
            }
        }
        Expr::IfLet(_, scrut, t, e, _) => {
            guard_expr_accesses(scrut, guards);
            for s in &mut t.stmts {
                guard_stmt_accesses(s, guards);
            }
            if let Some(e) = e {
                guard_expr_accesses(e, guards);
            }
        }
        Expr::Match(scrut, arms, _) => {
            guard_expr_accesses(scrut, guards);
            arms.iter_mut()
                .for_each(|arm| guard_expr_accesses(&mut arm.body, guards));
        }
        // A closure here is a non-spawn closure value; its body is not part of the
        // spawner's straight-line flow, so leave it (a spawn closure was already
        // handled at the spawn site).
        Expr::Closure(..)
        | Expr::Int(..)
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

/// The span of a statement, for synthesizing a wrapping `with`.
fn stmt_span(stmt: &Stmt) -> Span {
    match stmt {
        Stmt::Let { span, .. } | Stmt::Assign { span, .. } => *span,
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => e.span(),
        Stmt::While { cond, .. } => cond.span(),
        Stmt::For { iter, .. } => iter.span(),
        Stmt::Return(None, span) | Stmt::Break(span) | Stmt::Continue(span) => *span,
    }
}

/// The span used for a spawn's synthesized promotion statements (cosmetic: these
/// builtins do not fail, so the span only ever surfaces in internal diagnostics).
fn spawn_stmt_span(stmt: &Stmt) -> Span {
    match stmt {
        Stmt::Expr(e) | Stmt::Let { value: Some(e), .. } => e.span(),
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

/// Build the lock acquisition around `body` for `roots`:
///
/// - one root: `with(c, (c) -> body)` -- the `with` handle shadows the captured
///   name so the body's accesses go through it, and the single-cown `with` also
///   opens a verification region;
/// - several roots: `_with_all(() -> body, c0, c1, ...)` -- the runtime acquires
///   the group in *address* order, so two bodies over the same objects captured
///   under different names cannot acquire in opposite orders and deadlock (the
///   old nested name-ordered `with` form did exactly that).
fn wrap_with(body: Expr, roots: &[String]) -> Expr {
    let span = body.span();
    if roots.len() == 1 {
        let cown = &roots[0];
        let param = Param {
            name: cown.clone(),
            ty: None,
            span,
        };
        let closure = Expr::Closure(vec![param], Box::new(body), span);
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
    let closure = Expr::Closure(Vec::new(), Box::new(body), span);
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

#[cfg(test)]
mod tests {
    use super::*;
    use brass_parser::ast::TopLevel;
    use brass_parser::parse;

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
        analyze_spawns(&main_body(src), &HashSet::default())
    }

    fn acquire(body: &mut Block) -> Vec<SpawnError> {
        auto_acquire(
            &mut body.stmts,
            &HashSet::default(),
            &SpawnSummaries::default(),
        )
    }

    /// Render a statement list compactly for structural assertions.
    fn contains_call(stmts: &[Stmt], name: &str) -> bool {
        let mut found = false;
        let block = stmts_block(stmts);
        each_call(&block, &mut |callee, _, _| {
            if callee == name {
                found = true;
            }
        });
        found
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
    fn mutation_through_a_ref_function_call_counts_as_mutation() {
        // Passing the capture to a function (whose default parameter is a mutable
        // reference) may mutate it, so it must be cowned -- not frozen, which would
        // let two threads race it.
        let d = decisions(
            "fun main() {\n    let c = make()\n    spawn(() -> { bump(c) })\n    use(c)\n}\n",
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
    fn mutation_inside_a_match_arm_counts_as_mutation() {
        // A mutation nested in a `match` arm body must be found by the full-tree
        // scan; missing it would freeze a mutated capture and race it.
        let d = decisions(
            "fun main() {\n    let c = make()\n    spawn(() -> { match 1 {\n        _ => { c.x = 1 }\n    } })\n    use(c)\n}\n",
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
    fn spawner_side_mutation_after_a_read_only_spawn_upgrades_to_cown() {
        // The closure only READS `c`, but the spawner passes it to a possibly
        // mutating call afterwards: freezing would let the spawner write while
        // the task reads lock-free. The whole-function mutation rule must cown it
        // so both sides are serialized.
        let d = decisions(
            "fun main() {\n    let c = make()\n    spawn(() -> { println(c) })\n    use(c)\n}\n",
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
    fn read_only_capture_everywhere_stays_frozen() {
        // Nobody ever mutates `c` (only read-only builtins touch it), so it is
        // genuinely immutable after the spawn and freezing is the right call.
        let d = decisions(
            "fun main() {\n    let c = make()\n    spawn(() -> { println(c) })\n    println(c)\n}\n",
        );
        assert_eq!(
            d,
            vec![CaptureDecision {
                var: "c".into(),
                ownership: Ownership::Freeze
            }]
        );
    }

    #[test]
    fn spawner_mutation_through_a_container_alias_upgrades_to_cown() {
        // The spawner wraps `c` in a record before the spawn and mutates through
        // the wrapper afterwards. The conservative alias rule must see `w` as a
        // handle to `c`'s object and classify the capture a cown.
        let d = decisions(
            "fun main() {\n    let c = make()\n    let w = Wrap { c: c }\n    spawn(() -> { println(c) })\n    w.c.add(1)\n}\n",
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
        let errors = acquire(&mut body);
        assert!(errors.is_empty(), "no spawn errors: {errors:?}");
        let wrapped = body.stmts.iter().any(spawn_body_is_with);
        assert!(wrapped, "cowned spawn body should be wrapped in `with`");
    }

    #[test]
    fn multi_cown_spawn_body_uses_the_group_wrap() {
        // A body that mutates two captures must acquire them as a group through
        // `_with_all` (address-ordered at runtime), not as nested name-ordered
        // `with` scopes -- the nesting deadlocked when another spawn captured the
        // same objects under names that sort the other way.
        let mut body = main_body(
            "fun main() {\n    let a = make()\n    let b = make()\n    spawn(() -> { a.add(1)\n        b.add(1) })\n    use(a)\n    use(b)\n}\n",
        );
        let errors = acquire(&mut body);
        assert!(errors.is_empty());
        assert!(
            contains_call(&body.stmts, "_with_all"),
            "two cowns must be acquired via the group form"
        );
    }

    #[test]
    fn mutation_through_an_alias_in_the_closure_counts_as_mutation() {
        // A capture mutated through a local alias (`let a = c; a.add(1)`) is rooted
        // at `a`, but `a` aliases `c`, so the capture must still be cowned -- not
        // frozen, which would race it.
        let d = decisions(
            "fun main() {\n    let c = make()\n    spawn(() -> { let a = c\n        a.add(1) })\n    use(c)\n}\n",
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
    fn nested_closure_local_is_not_captured_by_the_outer_spawn() {
        // A loop counter bound inside a nested spawn closure belongs to the inner
        // scope; it must not be seen as a capture (and promoted) by the outer spawn.
        let body = main_body(
            "fun main() {\n    let c = make()\n    spawn(() -> {\n        spawn(() -> { let i = 0\n            c.add(i) })\n    })\n}\n",
        );
        // The outer spawn's closure body is the second statement's argument.
        let Stmt::Expr(Expr::Call(_, args, _)) = &body.stmts[1] else {
            panic!("expected spawn statement");
        };
        let Expr::Closure(_, outer_body, _) = &args[0].expr else {
            panic!("expected closure");
        };
        let Expr::Block(b, _) = outer_body.as_ref() else {
            panic!("expected block body");
        };
        let caps = captured(b, &HashSet::default());
        assert!(
            !caps.contains("i"),
            "the inner closure's local `i` must not be a capture of the outer spawn: {caps:?}"
        );
        assert!(
            caps.contains("c"),
            "the outer spawn still captures `c`: {caps:?}"
        );
    }

    #[test]
    fn spawner_access_after_a_cowned_spawn_is_guarded() {
        // The spawner's own later access to a cowned capture must be wrapped in
        // `with` too, so it does not race the spawned task. Here the trailing
        // `c.add(2)` runs concurrently with the spawned `c.add(1)`.
        let mut body = main_body(
            "fun main() {\n    let c = make()\n    spawn(() -> { c.add(1) })\n    c.add(2)\n}\n",
        );
        let errors = acquire(&mut body);
        assert!(errors.is_empty());
        let guarded = body.stmts.iter().any(|s| {
            matches!(s, Stmt::Expr(Expr::Call(callee, _, _))
                if matches!(&**callee, Expr::Ident(n, _) if n == "with"))
        });
        assert!(
            guarded,
            "the spawner's own access to the cown should be guarded by `with`"
        );
    }

    #[test]
    fn spawn_inside_a_loop_guards_accesses_after_the_loop() {
        // A spawn nested in a `while` shares state with everything the function
        // does afterwards; the pass must guard the access *outside* the loop's
        // statement list (the old per-list live set missed it and raced).
        let mut body = main_body(
            "fun main() {\n    let c = make()\n    let k = 0\n    while k < 2 {\n        spawn(() -> { c.add(1) })\n        k = k + 1\n    }\n    c.add(2)\n}\n",
        );
        let errors = acquire(&mut body);
        assert!(errors.is_empty());
        let guarded = body.stmts.iter().any(|s| {
            matches!(s, Stmt::Expr(Expr::Call(callee, _, _))
                if matches!(&**callee, Expr::Ident(n, _) if n == "with"))
        });
        assert!(
            guarded,
            "the post-loop access must be guarded even though the spawn is nested"
        );
    }

    #[test]
    fn closure_variable_spawn_is_promoted_and_wrapped() {
        // `let task = () -> {...}; spawn(task)` must behave exactly like a
        // literal spawn: the bound closure's body is lock-wrapped and the capture
        // promoted before the spawn -- previously this shape got NO promotion, so
        // two threads raced the capture's non-atomic reference count.
        let mut body = main_body(
            "fun main() {\n    let c = make()\n    let task = () -> { c.add(1) }\n    spawn(task)\n    c.add(2)\n}\n",
        );
        let errors = acquire(&mut body);
        assert!(errors.is_empty(), "spawn(var) resolves: {errors:?}");
        assert!(
            contains_call(&body.stmts, "_cown"),
            "the capture must be promoted before the spawn"
        );
        // The bound closure's body is wrapped in a lock acquisition.
        let bound_wrapped = body.stmts.iter().any(|s| {
            let Stmt::Let {
                value: Some(Expr::Closure(_, cbody, _)),
                ..
            } = s
            else {
                return false;
            };
            matches!(cbody.as_ref(), Expr::Call(c, _, _)
                if matches!(&**c, Expr::Ident(n, _) if n == "with"))
        });
        assert!(bound_wrapped, "the bound closure body must be lock-wrapped");
    }

    #[test]
    fn unresolvable_spawn_argument_is_a_compile_error() {
        // A spawn whose argument is not a closure literal (here: a call result)
        // cannot be analyzed; compiling it silently would hand unguarded shared
        // state to a thread, so it must be rejected.
        let mut body = main_body("fun main() {\n    spawn(make())\n}\n");
        let errors = acquire(&mut body);
        assert_eq!(errors.len(), 1, "expected one spawn error: {errors:?}");
        assert!(errors[0].message.contains("closure literal"));
    }

    #[test]
    fn spawn_of_an_unbound_variable_is_a_compile_error() {
        // `spawn(f)` where `f` is a parameter (not bound to a closure literal in
        // this function) is equally opaque and must be rejected.
        let module = parse("fun run(f) {\n    spawn(f)\n}\n").expect("parse");
        let TopLevel::Fun(mut f) = module.items.into_iter().next().unwrap() else {
            panic!("expected fun");
        };
        let params: HashSet<String> = f.params.iter().map(|p| p.name.clone()).collect();
        let errors = auto_acquire(&mut f.body.stmts, &params, &SpawnSummaries::default());
        assert_eq!(errors.len(), 1, "expected one spawn error: {errors:?}");
    }

    #[test]
    fn summaries_mark_parameters_captured_by_callee_spawns() {
        // `start(c)` spawns a task capturing its parameter; `outer(x)` forwards
        // its own parameter to `start`. Both must be summarized (the second via
        // the call-graph fixpoint).
        let src =
            "fun start(c) {\n    spawn(() -> { c.add(1) })\n}\nfun outer(x) {\n    start(x)\n}\n";
        let module = parse(src).expect("parse");
        let mut fns: Vec<(String, Vec<String>, Block)> = Vec::new();
        for item in module.items {
            if let TopLevel::Fun(f) = item {
                fns.push((
                    f.name.clone(),
                    f.params.iter().map(|p| p.name.clone()).collect(),
                    f.body,
                ));
            }
        }
        let borrowed: Vec<(String, Vec<String>, &Block)> = fns
            .iter()
            .map(|(n, p, b)| (n.clone(), p.clone(), b))
            .collect();
        let summaries = spawn_capture_summaries(&borrowed);
        assert_eq!(
            summaries.get("start"),
            Some(&HashSet::from_iter([0])),
            "start spawns a task capturing its parameter 0"
        );
        assert_eq!(
            summaries.get("outer"),
            Some(&HashSet::from_iter([0])),
            "outer forwards its parameter into start's captured position"
        );
    }

    #[test]
    fn caller_local_passed_to_a_spawning_callee_is_promoted_and_guarded() {
        // With `start` summarized, a caller's local handed to it must be
        // promoted to a cown and the caller's own accesses guarded -- the spawn
        // in the helper races the caller otherwise.
        let mut summaries = SpawnSummaries::default();
        summaries.insert("start".to_string(), HashSet::from_iter([0]));
        let mut body =
            main_body("fun main() {\n    let c = make()\n    start(c)\n    c.add(1)\n}\n");
        let errors = auto_acquire(&mut body.stmts, &HashSet::default(), &summaries);
        assert!(errors.is_empty());
        assert!(
            contains_call(&body.stmts, "_cown"),
            "the local must be promoted before the call hands it to the callee"
        );
        assert!(
            contains_call(&body.stmts, "with"),
            "the caller's own accesses must be lock-guarded"
        );
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
