//! Definite assignment for uninitialized `let` bindings (`let x: T`).
//!
//! Such a binding has no value until it is assigned -- either the whole
//! binding at once, or (for a record whose default skeleton is constructible,
//! see `brass_typesys::default_constructible`) one field at a time. Reading
//! the binding before it is fully assigned, or reading a field before that
//! field is assigned, would observe the skeleton's placeholder values, so both
//! are compile errors. The analysis is a structured dataflow walk over the
//! body: branches join by intersection, terminated paths (return/break/
//! continue) drop out of the join, and loop bodies are checked but do not
//! contribute facts (they may run zero times).

use fxhash::FxHashMap as HashMap;
use std::collections::BTreeSet;

use brass_hir::{Program, TypeInfo, TypeKind};
use brass_parser::Span;
use brass_parser::ast::*;

use crate::TypeError;

/// Report every use of an uninitialized `let` binding that is not definitely
/// assigned at that point.
pub fn check(program: &Program) -> Vec<TypeError> {
    check_in(program, crate::AnalysisModules::all())
}

pub(crate) fn check_in(program: &Program, modules: crate::AnalysisModules<'_>) -> Vec<TypeError> {
    let mut errors = Vec::new();
    for f in program.functions.values() {
        if !modules.checks(&f.module) {
            continue;
        }
        check_body(program, &f.module, None, &f.decl.body, &mut errors);
    }
    for info in program.types.values() {
        if !modules.checks(&info.module) {
            continue;
        }
        match &info.kind {
            TypeKind::Record { methods, .. } => {
                for m in methods.values() {
                    if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                        continue;
                    }
                    if let Some(body) = m.decl.body.as_ref() {
                        check_body(program, &info.module, Some(info), body, &mut errors);
                    }
                }
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    for m in v.methods.values() {
                        if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                            continue;
                        }
                        if let Some(body) = m.decl.body.as_ref() {
                            check_body(program, &info.module, Some(info), body, &mut errors);
                        }
                    }
                }
            }
        }
    }
    for init in &program.inits {
        if !modules.checks(&init.path) {
            continue;
        }
        check_statements(program, &init.path, None, &init.stmts, &mut errors);
    }
    errors
}

fn check_body(
    program: &Program,
    module: &[String],
    self_info: Option<&TypeInfo>,
    body: &Block,
    errors: &mut Vec<TypeError>,
) {
    check_statements(program, module, self_info, &body.stmts, errors);
}

fn check_statements(
    program: &Program,
    module: &[String],
    self_info: Option<&TypeInfo>,
    statements: &[Stmt],
    errors: &mut Vec<TypeError>,
) {
    let mut w = Walker {
        program,
        module,
        self_info,
        tracked: Vec::new(),
        scopes: Vec::new(),
        loop_exits: Vec::new(),
        state: FlowState {
            states: Vec::new(),
            reachable: true,
        },
        errors,
    };
    w.walk_scope(statements);
}

/// One uninitialized binding under analysis.
struct Tracked {
    name: String,
    /// All declared field names when the annotation is a record whose default
    /// skeleton is constructible -- the precondition for field-wise init.
    fields: Option<BTreeSet<String>>,
    /// Why field-wise initialization is unavailable (`fields` is `None`).
    fieldwise_block: String,
    /// The temporary slot representing one fields-loop iteration. Only this
    /// binding lets an indexed store stand for initialization of a whole slot.
    synthetic_field_slot: bool,
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

#[derive(Default)]
struct LoopExits {
    returns: Vec<FlowState>,
    breaks: Vec<FlowState>,
    continues: Vec<FlowState>,
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

/// Convert one completed fields-loop body path back from its synthetic
/// current-field slot to the enclosing binding's state.
fn finish_fields_path(
    mut state: FlowState,
    current: usize,
    target: usize,
    completes_iteration: bool,
) -> FlowState {
    let assigned_current = state.states.get(current) == Some(&InitState::Init);
    state.states.truncate(current);
    if completes_iteration && assigned_current {
        state.states[target] = InitState::Init;
    }
    state
}

struct Walker<'p, 'e> {
    program: &'p Program,
    module: &'p [String],
    self_info: Option<&'p TypeInfo>,
    tracked: Vec<Tracked>,
    /// Innermost-last scopes: `Some(id)` is a tracked binding, `None` shadows
    /// an outer tracked binding with an ordinary (initialized) one.
    scopes: Vec<HashMap<String, Option<usize>>>,
    /// Control exits are collected per enclosing loop. Returns are copied to
    /// every frame because they leave all loops; break/continue target only the
    /// innermost frame.
    loop_exits: Vec<LoopExits>,
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

    /// The nominal declaration and full instance named by an uninitialized
    /// let's annotation. A refinement alias keeps its substitution here rather
    /// than decaying to the base declaration's open fields.
    fn named_type(&self, te: &TypeExpr) -> Option<(&'p TypeInfo, brass_hir::Type)> {
        let TypeExpr::Named(name, _) = te else {
            return None;
        };
        if name == "Self" {
            let info = self.self_info?;
            return Some((info, info.type_ref()));
        }
        if let Some(alias) = self.program.resolve_type_alias(self.module, name) {
            let nominal = match &alias.ty {
                brass_hir::Type::Record(n) | brass_hir::Type::Sum(n) => n,
                _ => return None,
            };
            return Some((self.program.type_by_id(nominal.id)?, alias.ty.clone()));
        }
        let info = self.program.resolve_type(self.module, name)?;
        Some((info, info.type_ref()))
    }

    fn walk_block(&mut self, b: &Block) {
        self.walk_scope(&b.stmts);
    }

    fn walk_scope(&mut self, statements: &[Stmt]) {
        let tracked_len = self.tracked.len();
        self.scopes.push(HashMap::default());
        for stmt in statements {
            self.walk_stmt(stmt);
        }
        self.scopes.pop();
        // Lexical locals have no users beyond this point. Keeping either their
        // descriptors or state slots would desynchronize ids after a branch
        // rewinds to its pre-branch state.
        self.tracked.truncate(tracked_len);
        self.state.states.truncate(tracked_len);
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
                    Some((info, instance)) => match &info.kind {
                        TypeKind::Record { fields, .. } => {
                            if brass_typesys::default_constructible(self.program, &instance) {
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
                    synthetic_field_slot: false,
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
                self.loop_exits.push(LoopExits::default());
                self.walk_block(body);
                self.loop_exits.pop();
                self.state = snapshot;
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                // A fields-loop runs exactly once per field, so an
                // unconditional `x[f] = ...` in its body assigns EVERY field:
                // the one loop form that fully initializes a tracked record.
                if let Some((fvar, arg, fbody)) = brass_hir::fields_loop_target(stmt) {
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
                    self.scopes
                        .push(HashMap::from_iter([(fvar.to_string(), None)]));
                    self.loop_exits.push(LoopExits::default());
                    self.walk_block(fbody);
                    self.loop_exits.pop();
                    self.scopes.pop();
                    self.state = snapshot;
                    return;
                }
                self.walk_expr(iter);
                let snapshot = self.state.clone();
                let frame = pat
                    .bound_names()
                    .into_iter()
                    .map(|n| (n.to_string(), None))
                    .collect();
                self.scopes.push(frame);
                self.loop_exits.push(LoopExits::default());
                self.walk_block(body);
                self.loop_exits.pop();
                self.scopes.pop();
                self.state = snapshot;
            }
            Stmt::Return(value, _) => {
                if let Some(value) = value {
                    self.walk_expr(value);
                }
                if self.state.reachable {
                    let exit = self.state.clone();
                    for outcomes in &mut self.loop_exits {
                        outcomes.returns.push(exit.clone());
                    }
                }
                self.state.reachable = false;
            }
            Stmt::Break(_) => {
                if self.state.reachable
                    && let Some(outcomes) = self.loop_exits.last_mut()
                {
                    outcomes.breaks.push(self.state.clone());
                }
                self.state.reachable = false;
            }
            Stmt::Continue(_) => {
                if self.state.reachable
                    && let Some(outcomes) = self.loop_exits.last_mut()
                {
                    outcomes.continues.push(self.state.clone());
                }
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
        let before = self.state.clone();
        let cur = self.tracked.len();
        let ret_name = self.tracked[id].name.clone();
        self.tracked.push(Tracked {
            name: ret_name.clone(),
            fields: None,
            fieldwise_block: String::new(),
            synthetic_field_slot: true,
        });
        self.state.states.push(InitState::Partial(BTreeSet::new()));
        self.scopes.push(HashMap::from_iter([
            (var.to_string(), None),
            (ret_name, Some(cur)),
        ]));
        self.loop_exits.push(LoopExits::default());
        for stmt in &body.stmts {
            self.walk_stmt(stmt);
        }
        let outcomes = self.loop_exits.pop().expect("fields-loop control frame");
        self.scopes.pop();

        // Fallthrough and continue complete the current iteration; a break
        // reaches the statement after the loop without visiting later fields.
        // Return paths leave the function and therefore do not participate in
        // the post-loop definite state.
        let mut post_loop = None;
        if self.state.reachable {
            post_loop = Some(finish_fields_path(self.state.clone(), cur, id, true));
        }
        for state in outcomes.continues {
            let state = finish_fields_path(state, cur, id, true);
            post_loop = Some(post_loop.map_or(state.clone(), |joined| join(joined, state)));
        }
        for state in outcomes.breaks {
            let state = finish_fields_path(state, cur, id, false);
            post_loop = Some(post_loop.map_or(state.clone(), |joined| join(joined, state)));
        }
        debug_assert!(
            post_loop.is_some() || !outcomes.returns.is_empty() || !before.reachable,
            "a reachable fields-loop body must have a control outcome"
        );

        // Drop the synthetic binding; no state outside the loop references it.
        self.tracked.truncate(cur);
        self.state = post_loop.unwrap_or_else(|| {
            let mut unreachable = before;
            unreachable.reachable = false;
            unreachable
        });
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
            // Only the fields-loop's synthetic current-field slot treats an
            // indexed store as whole-slot initialization. An ordinary `x[i]`
            // projection must first read an initialized aggregate.
            Expr::Index(base, idx, span) => {
                if let Expr::Ident(name, _) = &**base
                    && let Some(id) = self.lookup(name)
                {
                    self.walk_expr(idx);
                    if self.tracked[id].synthetic_field_slot && op == AssignOp::Eq {
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
            Expr::TypeTest(subject, _, _) => self.walk_expr(subject),
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
                self.scopes.push(HashMap::default());
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
                    self.scopes.push(HashMap::default());
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
            Expr::Closure(params, body, span) => {
                // A closure body runs at an unknown time; capturing a binding
                // that is not yet fully initialized could observe the
                // placeholder skeleton, so it is rejected at construction.
                let free = closure_free_variables(params, body);
                for name in &free {
                    if let Some(id) = self.lookup(name)
                        && self.state.states[id] != InitState::Init
                    {
                        let msg = format!(
                            "`{name}` is captured by a closure before it is fully initialized"
                        );
                        self.error(msg, *span);
                    }
                }

                // Captures are checked above and treated as initialized within
                // this independent analysis. The nested walker still tracks
                // closure-local uninitialized lets, while its state changes can
                // never establish facts in the enclosing function.
                let mut frame: HashMap<String, Option<usize>> =
                    free.into_iter().map(|name| (name, None)).collect();
                frame.extend(params.iter().map(|param| (param.name.clone(), None)));
                let mut nested = Walker {
                    program: self.program,
                    module: self.module,
                    self_info: self.self_info,
                    tracked: Vec::new(),
                    scopes: vec![frame],
                    loop_exits: Vec::new(),
                    state: FlowState {
                        states: Vec::new(),
                        reachable: self.state.reachable,
                    },
                    errors: self.errors,
                };
                nested.walk_expr(body);
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

/// Names a closure resolves outside its own lexical scopes. This is the exact
/// capture set relevant to definite assignment; locals, pattern bindings, and
/// parameters in either this closure or a nested one are excluded.
fn closure_free_variables(params: &[Param], body: &Expr) -> BTreeSet<String> {
    let mut collector = FreeVariables {
        scopes: vec![params.iter().map(|param| param.name.clone()).collect()],
        free: BTreeSet::new(),
    };
    collector.expr(body);
    collector.free
}

struct FreeVariables {
    scopes: Vec<BTreeSet<String>>,
    free: BTreeSet<String>,
}

impl FreeVariables {
    fn is_bound(&self, name: &str) -> bool {
        self.scopes.iter().rev().any(|scope| scope.contains(name))
    }

    fn bind_pattern(&mut self, pattern: &Pattern) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.extend(pattern_names(pattern));
        }
    }

    fn block(&mut self, block: &Block) {
        self.scopes.push(BTreeSet::new());
        for statement in &block.stmts {
            self.statement(statement);
            if let Stmt::Let { pat, .. } = statement {
                self.bind_pattern(pat);
            }
        }
        self.scopes.pop();
    }

    fn statement(&mut self, statement: &Stmt) {
        match statement {
            Stmt::Let { value, .. } => {
                if let Some(value) = value {
                    self.expr(value);
                }
            }
            Stmt::Assign { target, value, .. } => {
                self.expr(value);
                self.expr(target);
            }
            Stmt::Expr(expr) | Stmt::Return(Some(expr), _) => self.expr(expr),
            Stmt::While { cond, body, .. } => {
                self.expr(cond);
                self.block(body);
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                self.expr(iter);
                self.scopes.push(pattern_names(pat).into_iter().collect());
                self.block(body);
                self.scopes.pop();
            }
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Ident(name, _) => {
                if !self.is_bound(name) {
                    self.free.insert(name.clone());
                }
            }
            Expr::Unary(_, inner, _)
            | Expr::ErrorProp(inner, _)
            | Expr::Field(inner, _, _)
            | Expr::TypeTest(inner, _, _) => self.expr(inner),
            Expr::Binary(_, left, right, _)
            | Expr::Index(left, right, _)
            | Expr::Range(left, right, _) => {
                self.expr(left);
                self.expr(right);
            }
            Expr::Call(callee, args, _) => {
                self.expr(callee);
                for arg in args {
                    self.expr(&arg.expr);
                }
            }
            Expr::Closure(params, body, _) => {
                self.scopes
                    .push(params.iter().map(|param| param.name.clone()).collect());
                self.expr(body);
                self.scopes.pop();
            }
            Expr::Array(items, _) => {
                for item in items {
                    self.expr(item);
                }
            }
            Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
                for (_, value) in fields {
                    self.expr(value);
                }
            }
            Expr::Str(segments, _) => {
                for segment in segments {
                    if let StrSeg::Expr(inner) = segment {
                        self.expr(inner);
                    }
                }
            }
            Expr::If(cond, then, els, _) => {
                self.expr(cond);
                self.block(then);
                if let Some(els) = els {
                    self.expr(els);
                }
            }
            Expr::IfLet(pattern, scrutinee, then, els, _) => {
                self.expr(scrutinee);
                self.scopes
                    .push(pattern_names(pattern).into_iter().collect());
                self.block(then);
                self.scopes.pop();
                if let Some(els) = els {
                    self.expr(els);
                }
            }
            Expr::Match(scrutinee, arms, _) => {
                self.expr(scrutinee);
                for arm in arms {
                    self.scopes
                        .push(pattern_names(&arm.pattern).into_iter().collect());
                    self.expr(&arm.body);
                    self.scopes.pop();
                }
            }
            Expr::Block(block, _) => self.block(block),
            Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(_)
            | Expr::SelfExpr(_) => {}
        }
    }
}
