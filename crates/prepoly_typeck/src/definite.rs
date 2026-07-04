//! Definite assignment for uninitialized `let` bindings (`let x: T`).
//!
//! Such a binding has no value until it is assigned -- either the whole
//! binding at once, or (for a record whose default skeleton is constructible,
//! see `prepoly_typesys::default_constructible`) one field at a time. Reading
//! the binding before it is fully assigned, or reading a field before that
//! field is assigned, would observe the skeleton's placeholder values, so both
//! are compile errors. The analysis is a structured dataflow walk over the
//! body: branches join by intersection, terminated paths (return/break/
//! continue) drop out of the join, and loop bodies are checked but do not
//! contribute facts (they may run zero times).

use std::collections::{BTreeSet, HashMap};

use prepoly_hir::{Program, TypeInfo, TypeKind};
use prepoly_lexer::Span;
use prepoly_parser::ast::*;

use crate::TypeError;

/// Report every use of an uninitialized `let` binding that is not definitely
/// assigned at that point.
pub fn check(program: &Program) -> Vec<TypeError> {
    let mut errors = Vec::new();
    for f in program.functions.values() {
        check_body(program, None, &f.decl.body, &mut errors);
    }
    for info in program.types.values() {
        match &info.kind {
            TypeKind::Record { methods, .. } => {
                for m in methods.values() {
                    if prepoly_hir::keyed_return(m.decl.ret.as_ref()) {
                        continue;
                    }
                    if let Some(body) = m.decl.body.as_ref() {
                        check_body(program, Some(info), body, &mut errors);
                    }
                }
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    for m in v.methods.values() {
                        if prepoly_hir::keyed_return(m.decl.ret.as_ref()) {
                            continue;
                        }
                        if let Some(body) = m.decl.body.as_ref() {
                            check_body(program, Some(info), body, &mut errors);
                        }
                    }
                }
            }
        }
    }
    errors
}

fn check_body(
    program: &Program,
    self_info: Option<&TypeInfo>,
    body: &Block,
    errors: &mut Vec<TypeError>,
) {
    let mut w = Walker {
        program,
        self_info,
        tracked: Vec::new(),
        scopes: Vec::new(),
        state: FlowState {
            states: Vec::new(),
            reachable: true,
        },
        errors,
    };
    w.walk_block(body);
}

/// One uninitialized binding under analysis.
struct Tracked {
    name: String,
    /// All declared field names when the annotation is a record whose default
    /// skeleton is constructible -- the precondition for field-wise init.
    fields: Option<BTreeSet<String>>,
    /// Why field-wise initialization is unavailable (`fields` is `None`).
    fieldwise_block: String,
}

/// How much of a tracked binding is definitely assigned. `Partial(empty)` is
/// the fresh (fully uninitialized) state.
#[derive(Clone, PartialEq)]
enum InitState {
    Partial(BTreeSet<String>),
    Init,
}

#[derive(Clone)]
struct FlowState {
    /// Indexed by tracked id.
    states: Vec<InitState>,
    /// Whether this program point is reachable; unreachable states report no
    /// errors and drop out of joins.
    reachable: bool,
}

fn join(a: FlowState, b: FlowState) -> FlowState {
    if !a.reachable {
        return b;
    }
    if !b.reachable {
        return a;
    }
    let states = a
        .states
        .into_iter()
        .zip(b.states)
        .map(|(x, y)| match (x, y) {
            (InitState::Init, InitState::Init) => InitState::Init,
            (InitState::Init, o) | (o, InitState::Init) => o,
            (InitState::Partial(p), InitState::Partial(q)) => {
                InitState::Partial(p.intersection(&q).cloned().collect())
            }
        })
        .collect();
    FlowState {
        states,
        reachable: true,
    }
}

struct Walker<'p, 'e> {
    program: &'p Program,
    self_info: Option<&'p TypeInfo>,
    tracked: Vec<Tracked>,
    /// Innermost-last scopes: `Some(id)` is a tracked binding, `None` shadows
    /// an outer tracked binding with an ordinary (initialized) one.
    scopes: Vec<HashMap<String, Option<usize>>>,
    state: FlowState,
    errors: &'e mut Vec<TypeError>,
}

impl<'p, 'e> Walker<'p, 'e> {
    fn lookup(&self, name: &str) -> Option<usize> {
        for scope in self.scopes.iter().rev() {
            if let Some(entry) = scope.get(name) {
                return *entry;
            }
        }
        None
    }

    fn shadow(&mut self, name: &str) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), None);
        }
    }

    fn shadow_pattern(&mut self, pat: &Pattern) {
        for name in pattern_names(pat) {
            self.shadow(&name);
        }
    }

    fn error(&mut self, message: String, span: Span) {
        if self.state.reachable {
            self.errors.push(TypeError { message, span });
        }
    }

    /// The record type named by an uninitialized let's annotation, if any.
    fn named_type(&self, te: &TypeExpr) -> Option<&'p TypeInfo> {
        let TypeExpr::Named(name, _) = te else {
            return None;
        };
        if name == "Self" {
            return self.self_info;
        }
        self.program
            .types
            .get(name)
            .or_else(|| self.program.types.values().find(|i| &i.name == name))
    }

    fn walk_block(&mut self, b: &Block) {
        self.scopes.push(HashMap::new());
        for stmt in &b.stmts {
            self.walk_stmt(stmt);
        }
        self.scopes.pop();
    }

    fn walk_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let {
                pat,
                ty,
                value: None,
                ..
            } => {
                let Pattern::Binding(name, _) = pat else {
                    return; // rejected by the infer pass
                };
                let (fields, block_reason) = match ty.as_ref().and_then(|te| self.named_type(te)) {
                    Some(info) => match &info.kind {
                        TypeKind::Record { fields, .. } => {
                            if prepoly_typesys::default_constructible(
                                self.program,
                                &info.type_ref(),
                            ) {
                                (
                                    Some(fields.iter().map(|f| f.name.clone()).collect()),
                                    String::new(),
                                )
                            } else {
                                (
                                    None,
                                    format!(
                                        "`{}` has a field with no default value; assign the \
                                         whole value instead",
                                        info.name
                                    ),
                                )
                            }
                        }
                        TypeKind::Sum { .. } => (
                            None,
                            "its type is a sum type; assign the whole value".into(),
                        ),
                    },
                    None => (None, "its type is not a record".into()),
                };
                let id = self.tracked.len();
                self.tracked.push(Tracked {
                    name: name.clone(),
                    fields,
                    fieldwise_block: block_reason,
                });
                self.state.states.push(InitState::Partial(BTreeSet::new()));
                if let Some(scope) = self.scopes.last_mut() {
                    scope.insert(name.clone(), Some(id));
                }
            }
            Stmt::Let {
                pat,
                value: Some(value),
                ..
            } => {
                self.walk_expr(value);
                self.shadow_pattern(pat);
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                // The value evaluates before the store, so `x = x + 1` on an
                // uninitialized `x` is a read error first.
                self.walk_expr(value);
                self.walk_assign_target(target, *op);
            }
            Stmt::Expr(e) => self.walk_expr(e),
            Stmt::While { cond, body, .. } => {
                self.walk_expr(cond);
                // The body may run zero times: check it against the current
                // state, then discard what it established.
                let snapshot = self.state.clone();
                self.walk_block(body);
                self.state = snapshot;
            }
            Stmt::For {
                var, iter, body, ..
            } => {
                // A fields-loop runs exactly once per field, so an
                // unconditional `x[f] = ...` in its body assigns EVERY field:
                // the one loop form that fully initializes a tracked record.
                if let Some((fvar, arg, fbody)) = prepoly_hir::fields_loop_target(stmt) {
                    // `fields(x)` reads x's TYPE, not its value, so a tracked
                    // (still-uninitialized) argument is fine.
                    if let Expr::Ident(name, _) = arg
                        && let Some(id) = self.lookup(name)
                    {
                        self.walk_fields_loop_over_tracked(id, fvar, fbody);
                        return;
                    }
                    self.walk_expr(arg);
                    let snapshot = self.state.clone();
                    self.scopes.push(HashMap::from([(fvar.to_string(), None)]));
                    self.walk_block(fbody);
                    self.scopes.pop();
                    self.state = snapshot;
                    return;
                }
                self.walk_expr(iter);
                let snapshot = self.state.clone();
                self.scopes.push(HashMap::from([(var.clone(), None)]));
                self.walk_block(body);
                self.scopes.pop();
                self.state = snapshot;
            }
            Stmt::Return(value, _) => {
                if let Some(value) = value {
                    self.walk_expr(value);
                }
                self.state.reachable = false;
            }
            Stmt::Break(_) | Stmt::Continue(_) => {
                self.state.reachable = false;
            }
        }
    }

    /// A fields-loop body over a tracked binding `x`: statements before the
    /// unconditional top-level `x[f] = <value>` follow the normal rules (so a
    /// read of `x` or `x[f]` there is an error); the assignment itself counts
    /// as assigning every field, because the loop visits each one. Statements
    /// after it still see `x` as uninitialized within the body (a later read
    /// would observe OTHER fields not yet visited); the binding becomes fully
    /// initialized after the loop.
    fn walk_fields_loop_over_tracked(&mut self, id: usize, var: &str, body: &Block) {
        // Model the loop's ONE iteration: the field name `var` addresses "the
        // current field", so `ret[var] = v` assigns it. Rebind `ret`'s name to
        // a fresh synthetic binding `cur` (a whole-assign slot) for the body, so
        // the ordinary dataflow -- branches, early `return`, `if let` -- decides
        // whether every non-diverging path assigns the current field. If so, the
        // loop (which visits every field) leaves `ret` fully initialized.
        let cur = self.tracked.len();
        let ret_name = self.tracked[id].name.clone();
        self.tracked.push(Tracked {
            name: ret_name.clone(),
            fields: None,
            fieldwise_block: String::new(),
        });
        self.state.states.push(InitState::Partial(BTreeSet::new()));
        self.scopes.push(HashMap::from([
            (var.to_string(), None),
            (ret_name, Some(cur)),
        ]));
        for stmt in &body.stmts {
            self.walk_stmt(stmt);
        }
        self.scopes.pop();
        let assigns_current = self.state.reachable && self.state.states[cur] == InitState::Init;
        // Drop the synthetic binding; no state outside the loop references it.
        self.tracked.truncate(cur);
        self.state.states.truncate(cur);
        if assigns_current && self.state.reachable {
            self.state.states[id] = InitState::Init;
        }
    }

    /// An assignment target is a PLACE: its root is written, not read, but
    /// every projection on the way is a read of the value it projects from.
    fn walk_assign_target(&mut self, target: &Expr, op: AssignOp) {
        match target {
            Expr::Ident(name, span) => {
                let Some(id) = self.lookup(name) else { return };
                if op == AssignOp::Eq {
                    self.state.states[id] = InitState::Init;
                } else {
                    // A compound assignment reads the current value first.
                    self.require_init(id, *span);
                }
            }
            Expr::Field(base, fname, span) => {
                if let Expr::Ident(name, _) = &**base
                    && let Some(id) = self.lookup(name)
                {
                    if self.state.states[id] == InitState::Init {
                        return; // an ordinary field mutation
                    }
                    if op != AssignOp::Eq {
                        self.require_field(id, fname, *span);
                        return;
                    }
                    match &self.tracked[id].fields {
                        Some(all) => {
                            let all = all.clone();
                            let InitState::Partial(set) = &mut self.state.states[id] else {
                                return;
                            };
                            set.insert(fname.clone());
                            if all.iter().all(|f| set.contains(f)) {
                                self.state.states[id] = InitState::Init;
                            }
                        }
                        None => {
                            let msg = format!(
                                "cannot initialize `{}` field by field: {}",
                                self.tracked[id].name, self.tracked[id].fieldwise_block
                            );
                            self.error(msg, *span);
                        }
                    }
                    return;
                }
                // A deeper place (`p.a.b = ..`): the base is read.
                self.walk_expr(base);
            }
            // `x[i] = v`: a whole-element store into a tracked binding. Inside a
            // fields-loop this is `ret[field] = v`, which assigns the current
            // field (the synthetic binding is whole-assign, so `Eq` marks it
            // initialized; a compound op reads first).
            Expr::Index(base, idx, span) => {
                if let Expr::Ident(name, _) = &**base
                    && let Some(id) = self.lookup(name)
                {
                    self.walk_expr(idx);
                    if op == AssignOp::Eq {
                        self.state.states[id] = InitState::Init;
                    } else {
                        self.require_init(id, *span);
                    }
                    return;
                }
                self.walk_expr(base);
                self.walk_expr(idx);
            }
            other => self.walk_expr(other),
        }
    }

    fn require_init(&mut self, id: usize, span: Span) {
        if self.state.states[id] != InitState::Init {
            let msg = format!(
                "`{}` is used before it is fully initialized",
                self.tracked[id].name
            );
            self.error(msg, span);
        }
    }

    fn require_field(&mut self, id: usize, fname: &str, span: Span) {
        let ok = match &self.state.states[id] {
            InitState::Init => true,
            InitState::Partial(set) => set.contains(fname),
        };
        if !ok {
            let msg = format!(
                "field `{fname}` of `{}` is read before it is assigned",
                self.tracked[id].name
            );
            self.error(msg, span);
        }
    }

    fn walk_expr(&mut self, e: &Expr) {
        match e {
            Expr::Ident(name, span) => {
                if let Some(id) = self.lookup(name) {
                    self.require_init(id, *span);
                }
            }
            Expr::Field(base, fname, span) => {
                if let Expr::Ident(name, _) = &**base
                    && let Some(id) = self.lookup(name)
                {
                    self.require_field(id, fname, *span);
                    return;
                }
                self.walk_expr(base);
            }
            Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) => self.walk_expr(inner),
            Expr::Binary(_, l, r, _) | Expr::Index(l, r, _) | Expr::Range(l, r, _) => {
                self.walk_expr(l);
                self.walk_expr(r);
            }
            // `typeof(x)` reads only x's TYPE, never its value, so it is legal
            // on an uninitialized binding (like `fields(x)`).
            Expr::Call(callee, args, _)
                if matches!(&**callee, Expr::Ident(n, _) if n == "typeof" || n == "fields")
                    && args.len() == 1
                    && matches!(&args[0].expr, Expr::Ident(n, _) if self.lookup(n).is_some()) => {}
            Expr::Call(callee, args, _) => {
                self.walk_expr(callee);
                for a in args {
                    self.walk_expr(&a.expr);
                }
            }
            Expr::Array(es, _) => {
                for e in es {
                    self.walk_expr(e);
                }
            }
            Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
                for (_, e) in fields {
                    self.walk_expr(e);
                }
            }
            Expr::Str(segs, _) => {
                for seg in segs {
                    if let StrSeg::Expr(e) = seg {
                        self.walk_expr(e);
                    }
                }
            }
            Expr::If(cond, then, els, _) => {
                self.walk_expr(cond);
                let before = self.state.clone();
                self.walk_block(then);
                // Rewind to the pre-branch state for the else side (or the
                // fall-through when there is none), then join both outcomes.
                let after_then = std::mem::replace(&mut self.state, before);
                if let Some(els) = els {
                    self.walk_expr(els);
                }
                let after_else = self.state.clone();
                self.state = join(after_then, after_else);
            }
            Expr::IfLet(pat, scrut, then, els, _) => {
                self.walk_expr(scrut);
                let before = self.state.clone();
                self.scopes.push(HashMap::new());
                self.shadow_pattern(pat);
                self.walk_block(then);
                self.scopes.pop();
                let after_then = std::mem::replace(&mut self.state, before);
                if let Some(els) = els {
                    self.walk_expr(els);
                }
                let after_else = self.state.clone();
                self.state = join(after_then, after_else);
            }
            Expr::Match(scrut, arms, _) => {
                self.walk_expr(scrut);
                let before = self.state.clone();
                let mut joined: Option<FlowState> = None;
                for arm in arms {
                    self.state = before.clone();
                    self.scopes.push(HashMap::new());
                    self.shadow_pattern(&arm.pattern);
                    self.walk_expr(&arm.body);
                    self.scopes.pop();
                    let arm_state = std::mem::replace(&mut self.state, before.clone());
                    joined = Some(match joined {
                        Some(j) => join(j, arm_state),
                        None => arm_state,
                    });
                }
                self.state = joined.unwrap_or(before);
            }
            Expr::Block(b, _) => self.walk_block(b),
            Expr::Closure(_, body, span) => {
                // A closure body runs at an unknown time; capturing a binding
                // that is not yet fully initialized could observe the
                // placeholder skeleton, so it is rejected outright. Assignments
                // inside the closure do not count toward initialization.
                let mut names = BTreeSet::new();
                collect_idents(body, &mut names);
                for name in names {
                    if let Some(id) = self.lookup(&name)
                        && self.state.states[id] != InitState::Init
                    {
                        let msg = format!(
                            "`{name}` is captured by a closure before it is fully initialized"
                        );
                        self.error(msg, *span);
                    }
                }
            }
            Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(_)
            | Expr::SelfExpr(_) => {}
        }
    }
}

fn pattern_names(pat: &Pattern) -> Vec<String> {
    let mut names = Vec::new();
    collect_pattern_names(pat, &mut names);
    names
}

fn collect_pattern_names(pat: &Pattern, out: &mut Vec<String>) {
    match pat {
        Pattern::Binding(name, _) => out.push(name.clone()),
        Pattern::Array(ps, _) => {
            for p in ps {
                collect_pattern_names(p, out);
            }
        }
        Pattern::Record(_, fields, _) => {
            // Shorthand `{ name }` binds the field to its own name; an explicit
            // sub-pattern binds whatever names it introduces.
            for f in fields {
                match &f.pat {
                    Some(sub) => collect_pattern_names(sub, out),
                    None => out.push(f.name.clone()),
                }
            }
        }
        _ => {}
    }
}

/// Every identifier mentioned anywhere in `e` (over-approximate: shadowing
/// inside nested scopes is ignored). Used only for the closure-capture check.
fn collect_idents(e: &Expr, out: &mut BTreeSet<String>) {
    match e {
        Expr::Ident(name, _) => {
            out.insert(name.clone());
        }
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) | Expr::Closure(_, inner, _) => {
            collect_idents(inner, out)
        }
        Expr::Binary(_, l, r, _) | Expr::Index(l, r, _) | Expr::Range(l, r, _) => {
            collect_idents(l, out);
            collect_idents(r, out);
        }
        Expr::Call(callee, args, _) => {
            collect_idents(callee, out);
            for a in args {
                collect_idents(&a.expr, out);
            }
        }
        Expr::Field(base, _, _) => collect_idents(base, out),
        Expr::Array(es, _) => {
            for e in es {
                collect_idents(e, out);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, e) in fields {
                collect_idents(e, out);
            }
        }
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(e) = seg {
                    collect_idents(e, out);
                }
            }
        }
        Expr::If(c, t, els, _) => {
            collect_idents(c, out);
            collect_block_idents(t, out);
            if let Some(els) = els {
                collect_idents(els, out);
            }
        }
        Expr::IfLet(_, scrut, t, els, _) => {
            collect_idents(scrut, out);
            collect_block_idents(t, out);
            if let Some(els) = els {
                collect_idents(els, out);
            }
        }
        Expr::Match(scrut, arms, _) => {
            collect_idents(scrut, out);
            for arm in arms {
                collect_idents(&arm.body, out);
            }
        }
        Expr::Block(b, _) => collect_block_idents(b, out),
        Expr::Int(..) | Expr::Float(..) | Expr::Bool(..) | Expr::Null(_) | Expr::SelfExpr(_) => {}
    }
}

fn collect_block_idents(b: &Block, out: &mut BTreeSet<String>) {
    for stmt in &b.stmts {
        match stmt {
            Stmt::Let { value, .. } => {
                if let Some(value) = value {
                    collect_idents(value, out);
                }
            }
            Stmt::Assign { target, value, .. } => {
                collect_idents(target, out);
                collect_idents(value, out);
            }
            Stmt::Expr(e) => collect_idents(e, out),
            Stmt::While { cond, body, .. } => {
                collect_idents(cond, out);
                collect_block_idents(body, out);
            }
            Stmt::For { iter, body, .. } => {
                collect_idents(iter, out);
                collect_block_idents(body, out);
            }
            Stmt::Return(Some(e), _) => collect_idents(e, out),
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }
}
