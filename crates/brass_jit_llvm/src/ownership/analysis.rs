//! Spawn-capture analysis: the names a closure body captures (and rebinds), whether
//! a function body mutates a variable through any alias, and the per-capture
//! ownership decision at each `spawn` site.

use fxhash::FxHashSet as HashSet;

use brass_parser::Span;
use brass_parser::ast::*;

use super::Ownership;
use super::scopes::{collect_pattern_bindings, nested_block_stmts};
use super::sites::{closure_bound_in, spawn_closure_body, stmts_reference};

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
/// a `ref(mut(T))` parameter writes through to the caller's value (book:
/// types.md), so `f(var)` may mutate `var`. Over-approximating mutation is the safe
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
                if let Pattern::Binding(name, _, _) = pat
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
                && !callee.span().is_parenthesized()
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
        Expr::TypeTest(subject, _, _, _) => scan_expr(subject, aliases, found),
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

pub(super) fn root_ident(e: &Expr) -> Option<&str> {
    match e {
        Expr::Ident(n, _) => Some(n),
        Expr::SelfExpr(_) => Some("self"),
        Expr::Field(b, _, _) | Expr::Index(b, _, _) => root_ident(b),
        _ => None,
    }
}

/// Names referenced free inside a closure body. `bound` contains bindings that
/// enter with the body, normally its parameters. Local declarations are applied
/// in source order and control-flow/pattern scopes are kept distinct, so a
/// shadowed name does not suppress a reference to a different binding.
pub fn captured(body: &Block, bound: &HashSet<String>) -> HashSet<String> {
    capture_scan(body, bound).free
}

/// The free names a closure body assigns as a whole (`n = 5`, `n += 1`), each
/// with the assignment's span, in source order: rebindings of a variable the
/// body captures rather than declares. Scoped like [`captured`]; a store into a
/// captured object's field or element (`p.x = 1`) mutates the object and is not
/// a rebinding.
pub fn rebound_captures(body: &Block, bound: &HashSet<String>) -> Vec<(String, Span)> {
    capture_scan(body, bound).rebound
}

/// What one walk of a closure body collects: its free names, and its
/// assignments to free names as a whole.
#[derive(Default)]
pub(super) struct CaptureScan {
    pub(super) free: HashSet<String>,
    pub(super) rebound: Vec<(String, Span)>,
}

pub(super) fn capture_scan(body: &Block, bound: &HashSet<String>) -> CaptureScan {
    let mut scopes = vec![bound.clone()];
    let mut scan = CaptureScan::default();
    capture_block(body, &mut scopes, &mut scan, HashSet::default());
    scan
}

fn capture_block(
    block: &Block,
    scopes: &mut Vec<HashSet<String>>,
    scan: &mut CaptureScan,
    bindings: HashSet<String>,
) {
    scopes.push(bindings);
    for stmt in &block.stmts {
        capture_stmt(stmt, scopes, scan);
    }
    scopes.pop();
}

fn capture_stmt(stmt: &Stmt, scopes: &mut Vec<HashSet<String>>, scan: &mut CaptureScan) {
    match stmt {
        Stmt::Let { pat, value, .. } => {
            if let Some(value) = value {
                capture_expr(value, scopes, scan);
            }
            collect_pattern_bindings(pat, scopes.last_mut().expect("capture scope"));
        }
        Stmt::Assign {
            target,
            value,
            span,
            ..
        } => {
            if let Expr::Ident(name, _) = target
                && !scopes.iter().rev().any(|scope| scope.contains(name))
            {
                scan.rebound.push((name.clone(), *span));
            }
            capture_expr(target, scopes, scan);
            capture_expr(value, scopes, scan);
        }
        Stmt::Expr(expr) | Stmt::Return(Some(expr), _) => capture_expr(expr, scopes, scan),
        Stmt::While { cond, body, .. } => {
            capture_expr(cond, scopes, scan);
            capture_block(body, scopes, scan, HashSet::default());
        }
        Stmt::For {
            pat, iter, body, ..
        } => {
            capture_expr(iter, scopes, scan);
            let mut bindings = HashSet::default();
            collect_pattern_bindings(pat, &mut bindings);
            capture_block(body, scopes, scan, bindings);
        }
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

fn capture_expr(expr: &Expr, scopes: &mut Vec<HashSet<String>>, scan: &mut CaptureScan) {
    match expr {
        Expr::Ident(name, _) => {
            if !scopes.iter().rev().any(|scope| scope.contains(name)) {
                scan.free.insert(name.clone());
            }
        }
        Expr::SelfExpr(_) => {
            if !scopes.iter().rev().any(|scope| scope.contains("self")) {
                scan.free.insert("self".to_string());
            }
        }
        Expr::Unary(_, inner, _) | Expr::Field(inner, _, _) | Expr::ErrorProp(inner, _) => {
            capture_expr(inner, scopes, scan)
        }
        Expr::Binary(_, left, right, _)
        | Expr::Index(left, right, _)
        | Expr::Range(left, right, _) => {
            capture_expr(left, scopes, scan);
            capture_expr(right, scopes, scan);
        }
        Expr::Call(callee, args, _) => {
            capture_expr(callee, scopes, scan);
            for arg in args {
                capture_expr(&arg.expr, scopes, scan);
            }
        }
        Expr::Closure(params, body, _) => {
            let bindings = params.iter().map(|param| param.name.clone()).collect();
            scopes.push(bindings);
            capture_expr(body, scopes, scan);
            scopes.pop();
        }
        Expr::Array(items, _) => {
            for item in items {
                capture_expr(item, scopes, scan);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, value) in fields {
                capture_expr(value, scopes, scan);
            }
        }
        Expr::Str(segments, _) => {
            for segment in segments {
                if let StrSeg::Expr(value) = segment {
                    capture_expr(value, scopes, scan);
                }
            }
        }
        Expr::If(cond, then, els, _) => {
            capture_expr(cond, scopes, scan);
            capture_block(then, scopes, scan, HashSet::default());
            if let Some(els) = els {
                capture_expr(els, scopes, scan);
            }
        }
        Expr::IfLet(pat, scrutinee, then, els, _) => {
            capture_expr(scrutinee, scopes, scan);
            let mut bindings = HashSet::default();
            collect_pattern_bindings(pat, &mut bindings);
            capture_block(then, scopes, scan, bindings);
            if let Some(els) = els {
                capture_expr(els, scopes, scan);
            }
        }
        Expr::Match(scrutinee, arms, _) => {
            capture_expr(scrutinee, scopes, scan);
            for arm in arms {
                let mut bindings = HashSet::default();
                collect_pattern_bindings(&arm.pattern, &mut bindings);
                scopes.push(bindings);
                capture_expr(&arm.body, scopes, scan);
                scopes.pop();
            }
        }
        Expr::Block(block, _) => capture_block(block, scopes, scan, HashSet::default()),
        Expr::TypeTest(subject, _, _, _) => capture_expr(subject, scopes, scan),
        Expr::Int(..) | Expr::Float(..) | Expr::Bool(..) | Expr::Null(_) => {}
    }
}

pub(super) fn param_names(params: &[Param]) -> HashSet<String> {
    params.iter().map(|param| param.name.clone()).collect()
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
    let fn_scope = stmts_block(stmts);
    let mut out = Vec::new();
    analyze_block(stmts, params, params, &fn_scope, &mut out);
    out
}

/// A whole statement slice viewed as one block, for whole-function queries.
pub(super) fn stmts_block(stmts: &[Stmt]) -> Block {
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
    let mut visible = locals.clone();
    for (i, stmt) in stmts.iter().enumerate() {
        analyze_nested_spawns_stmt(stmt, &visible, params, fn_scope, out);
        if let Some(closure_body) = spawn_closure_body(stmt) {
            let bound = closure_bound_in(stmt);
            let mut closure_visible = visible.clone();
            closure_visible.extend(bound.iter().cloned());
            // A nested spawn inside the spawned closure is its own site.
            analyze_block(&closure_body.stmts, &closure_visible, params, fn_scope, out);
            let mut captures: Vec<String> = captured(&closure_body, &bound)
                .into_iter()
                .filter(|name| visible.contains(name))
                .collect();
            captures.sort();
            let rest = &stmts[i + 1..];
            for var in captures {
                // Liveness must see through aliases: the object stays reachable after
                // the spawn through any handle bound from the capture.
                let handles = alias_closure(fn_scope, &var);
                let live_after = handles.iter().any(|h| stmts_reference(rest, h));
                out.push(CaptureDecision {
                    ownership: decide(&var, live_after, fn_scope, params),
                    var,
                });
            }
        }
        if let Stmt::Let { pat, .. } = stmt {
            collect_pattern_bindings(pat, &mut visible);
        }
    }
}

fn analyze_nested_spawns_stmt(
    stmt: &Stmt,
    visible: &HashSet<String>,
    params: &HashSet<String>,
    fn_scope: &Block,
    out: &mut Vec<CaptureDecision>,
) {
    match stmt {
        Stmt::Let {
            value: Some(value), ..
        }
        | Stmt::Expr(value)
        | Stmt::Return(Some(value), _) => {
            analyze_nested_spawns_expr(value, visible, params, fn_scope, out)
        }
        Stmt::Assign { target, value, .. } => {
            analyze_nested_spawns_expr(target, visible, params, fn_scope, out);
            analyze_nested_spawns_expr(value, visible, params, fn_scope, out);
        }
        Stmt::While { cond, body, .. } => {
            analyze_nested_spawns_expr(cond, visible, params, fn_scope, out);
            analyze_block(&body.stmts, visible, params, fn_scope, out);
        }
        Stmt::For {
            pat, iter, body, ..
        } => {
            analyze_nested_spawns_expr(iter, visible, params, fn_scope, out);
            let mut inner = visible.clone();
            collect_pattern_bindings(pat, &mut inner);
            analyze_block(&body.stmts, &inner, params, fn_scope, out);
        }
        Stmt::Let { value: None, .. }
        | Stmt::Return(None, _)
        | Stmt::Break(_)
        | Stmt::Continue(_) => {}
    }
}

fn analyze_nested_spawns_expr(
    expr: &Expr,
    visible: &HashSet<String>,
    params: &HashSet<String>,
    fn_scope: &Block,
    out: &mut Vec<CaptureDecision>,
) {
    match expr {
        Expr::Unary(_, inner, _) | Expr::Field(inner, _, _) | Expr::ErrorProp(inner, _) => {
            analyze_nested_spawns_expr(inner, visible, params, fn_scope, out)
        }
        Expr::Binary(_, left, right, _)
        | Expr::Index(left, right, _)
        | Expr::Range(left, right, _) => {
            analyze_nested_spawns_expr(left, visible, params, fn_scope, out);
            analyze_nested_spawns_expr(right, visible, params, fn_scope, out);
        }
        Expr::Call(callee, args, _) => {
            analyze_nested_spawns_expr(callee, visible, params, fn_scope, out);
            for arg in args {
                analyze_nested_spawns_expr(&arg.expr, visible, params, fn_scope, out);
            }
        }
        Expr::Array(items, _) => {
            for item in items {
                analyze_nested_spawns_expr(item, visible, params, fn_scope, out);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, value) in fields {
                analyze_nested_spawns_expr(value, visible, params, fn_scope, out);
            }
        }
        Expr::Str(segments, _) => {
            for segment in segments {
                if let StrSeg::Expr(value) = segment {
                    analyze_nested_spawns_expr(value, visible, params, fn_scope, out);
                }
            }
        }
        Expr::If(cond, then, els, _) => {
            analyze_nested_spawns_expr(cond, visible, params, fn_scope, out);
            analyze_block(&then.stmts, visible, params, fn_scope, out);
            if let Some(els) = els {
                analyze_nested_spawns_expr(els, visible, params, fn_scope, out);
            }
        }
        Expr::IfLet(pat, scrutinee, then, els, _) => {
            analyze_nested_spawns_expr(scrutinee, visible, params, fn_scope, out);
            let mut inner = visible.clone();
            collect_pattern_bindings(pat, &mut inner);
            analyze_block(&then.stmts, &inner, params, fn_scope, out);
            if let Some(els) = els {
                analyze_nested_spawns_expr(els, visible, params, fn_scope, out);
            }
        }
        Expr::Match(scrutinee, arms, _) => {
            analyze_nested_spawns_expr(scrutinee, visible, params, fn_scope, out);
            for arm in arms {
                let mut inner = visible.clone();
                collect_pattern_bindings(&arm.pattern, &mut inner);
                match &arm.body {
                    Expr::Block(block, _) => {
                        analyze_block(&block.stmts, &inner, params, fn_scope, out)
                    }
                    body => analyze_nested_spawns_expr(body, &inner, params, fn_scope, out),
                }
            }
        }
        Expr::Block(block, _) => analyze_block(&block.stmts, visible, params, fn_scope, out),
        Expr::TypeTest(subject, _, _, _) => {
            analyze_nested_spawns_expr(subject, visible, params, fn_scope, out)
        }
        // Spawned closure bodies are handled from their enclosing call statement;
        // plain closures are separate execution scopes.
        Expr::Closure(..)
        | Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => {}
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
        if let Some((name, value)) = binding
            && expr_mentions_any(value, handles)
        {
            handles.insert(name.clone());
        }
        nested_block_stmts(stmt, &mut |inner| collect_mention_aliases(inner, handles));
    }
}
