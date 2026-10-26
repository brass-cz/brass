//! Top-level initialization ordering. Module globals are
//! initialized in appearance order, so an initializer that reads a global
//! defined later in the same module is a compile error -- whether it names the
//! global itself or reaches it through the functions and methods it calls.
//! Cycles always manifest as such a forward reference (the first member of the
//! cycle to be initialized refers to a not-yet-initialized later member), so
//! detecting forward references also rejects circular initialization without a
//! separate graph pass.
//!
//! Only references to the module's own globals are constrained: function and
//! type names are resolved regardless of order, and imported globals belong to
//! a module that is initialized earlier by the import topological order (whose
//! code cannot call back into this module without an import cycle).

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use brass_hir::{Program, TypeKind};
use brass_parser::Span;
use brass_parser::ast::*;

use crate::TypeError;

/// Report every top-level statement that reads one of its module's globals
/// at or before that global's own initializer, directly or through the
/// functions and methods it calls.
pub fn check(program: &Program) -> Vec<TypeError> {
    check_in(program, crate::AnalysisModules::all())
}

/// [`check`] over the modules `modules` checks.
pub(crate) fn check_in(program: &Program, modules: crate::AnalysisModules<'_>) -> Vec<TypeError> {
    let mut errors = Vec::new();
    for module in &program.inits {
        if !modules.checks(&module.path) {
            continue;
        }
        check_module(program, &module.path, &module.stmts, &mut errors);
    }
    errors
}

fn check_module(program: &Program, path: &[String], stmts: &[Stmt], errors: &mut Vec<TypeError>) {
    // First-definition index of each global binding name in this module.
    let mut def_index: HashMap<String, usize> = HashMap::default();
    for (i, stmt) in stmts.iter().enumerate() {
        if let Stmt::Let { pat, .. } = stmt {
            for name in pattern_names(pat) {
                def_index.entry(name).or_insert(i);
            }
        }
    }
    let globals: HashSet<String> = def_index.keys().cloned().collect();
    if globals.is_empty() {
        return;
    }
    let mut graph = CallGraph::new(program, path, &globals);
    for (i, stmt) in stmts.iter().enumerate() {
        let mut facts = Facts::default();
        let mut walker = Walker {
            program,
            module: path,
            globals: &globals,
            self_type: None,
            facts: &mut facts,
        };
        walker.stmt(stmt, &HashSet::default());
        let is_forward = |name: &String| def_index.get(name).is_some_and(|&j| j >= i);
        for (name, span) in facts.reads {
            // A reference to a global whose definition is at or after the
            // current statement is a forward (or self) reference.
            if is_forward(&name) {
                errors.push(TypeError {
                    message: format!("global `{name}` is used before it is initialized"),
                    span,
                });
            }
        }
        let mut reported: HashSet<(Span, String)> = HashSet::default();
        for (callee, span) in facts.calls {
            for target in graph.targets(&callee) {
                let reads: Vec<String> = graph.transitive_reads(target).into_iter().collect();
                for name in reads.into_iter().filter(|n| is_forward(n)) {
                    if reported.insert((span, name.clone())) {
                        errors.push(TypeError {
                            message: format!(
                                "global `{name}` is used before it is initialized (through `{}`)",
                                callee.display(program)
                            ),
                            span,
                        });
                    }
                }
            }
        }
    }
}

/// A callable named by a call (or referenced as a value): a free function by
/// its source name, or a method by name -- with the declaring type's symbol
/// when the receiver is known syntactically (`Type.m(..)`, `self.m(..)`).
#[derive(Clone, PartialEq, Eq, Hash)]
enum Callee {
    Function(String),
    Method(Option<String>, String),
}

impl Callee {
    /// The callee as the diagnostic names it: `Type.method` when the
    /// receiver's type is known, the bare name otherwise.
    fn display(&self, program: &Program) -> String {
        match self {
            Callee::Method(Some(owner), name) => match program.types.get(owner) {
                Some(info) => format!("{}.{name}", info.name),
                None => name.clone(),
            },
            Callee::Function(name) | Callee::Method(None, name) => name.clone(),
        }
    }
}

/// The module's own globals a body reads and the callables it calls, each at
/// the span of the reference.
#[derive(Default)]
struct Facts {
    reads: Vec<(String, Span)>,
    calls: Vec<(Callee, Span)>,
}

/// A body of the module: a free function by symbol, or a method by its
/// declaring type's symbol, variant (for a sum) and name.
#[derive(Clone, PartialEq, Eq, Hash)]
enum BodyKey {
    Function(String),
    Method(String, Option<String>, String),
}

/// The module's callables, the globals each reads directly, and the transitive
/// closure of those reads over the calls between them (memoized).
struct CallGraph<'p> {
    program: &'p Program,
    module: &'p [String],
    globals: &'p HashSet<String>,
    facts: HashMap<BodyKey, Facts>,
    closed: HashMap<BodyKey, HashSet<String>>,
}

impl<'p> CallGraph<'p> {
    fn new(program: &'p Program, module: &'p [String], globals: &'p HashSet<String>) -> Self {
        Self {
            program,
            module,
            globals,
            facts: HashMap::default(),
            closed: HashMap::default(),
        }
    }

    /// The module's bodies a callee may name. A method whose receiver is not
    /// known syntactically may be any same-named method of a type the module
    /// declares; only those bodies can read this module's globals.
    fn targets(&self, callee: &Callee) -> Vec<BodyKey> {
        let program = self.program;
        match callee {
            Callee::Function(name) => program
                .functions
                .values()
                .filter(|f| f.module == self.module && f.signature.name == *name)
                .map(|f| BodyKey::Function(f.symbol.clone()))
                .collect(),
            Callee::Method(owner, name) => {
                let mut out = Vec::new();
                for info in program.types.values() {
                    if info.module != self.module
                        || owner.as_ref().is_some_and(|o| *o != info.symbol)
                    {
                        continue;
                    }
                    match &info.kind {
                        TypeKind::Record { methods, .. } => {
                            if methods.contains_key(name) {
                                out.push(BodyKey::Method(info.symbol.clone(), None, name.clone()));
                            }
                        }
                        TypeKind::Sum { variants } => {
                            for v in variants.iter().filter(|v| v.methods.contains_key(name)) {
                                out.push(BodyKey::Method(
                                    info.symbol.clone(),
                                    Some(v.name.clone()),
                                    name.clone(),
                                ));
                            }
                        }
                    }
                }
                out
            }
        }
    }

    /// The direct facts of one body, computed on first use.
    fn facts(&mut self, key: &BodyKey) -> &Facts {
        if !self.facts.contains_key(key) {
            let mut facts = Facts::default();
            let program = self.program;
            let (params, body, self_type): (&[Param], Option<&Block>, Option<String>) = match key {
                BodyKey::Function(symbol) => {
                    let f = &program.functions[symbol];
                    (&f.decl.params, Some(&f.decl.body), None)
                }
                BodyKey::Method(symbol, variant, name) => {
                    let info = &program.types[symbol];
                    let method = match (&info.kind, variant) {
                        (TypeKind::Record { methods, .. }, _) => methods.get(name),
                        (TypeKind::Sum { variants }, Some(v)) => variants
                            .iter()
                            .find(|candidate| candidate.name == *v)
                            .and_then(|candidate| candidate.methods.get(name)),
                        (TypeKind::Sum { .. }, None) => None,
                    };
                    match method {
                        Some(m) => (&m.decl.params, m.decl.body.as_ref(), Some(symbol.clone())),
                        None => (&[], None, None),
                    }
                }
            };
            if let Some(body) = body {
                let mut bound: HashSet<String> = params.iter().map(|p| p.name.clone()).collect();
                bound.insert("self".to_string());
                let mut walker = Walker {
                    program,
                    module: self.module,
                    globals: self.globals,
                    self_type,
                    facts: &mut facts,
                };
                walker.block(body, &bound);
            }
            self.facts.insert(key.clone(), facts);
        }
        &self.facts[key]
    }

    /// Every module global `key` reads, directly or through the bodies it
    /// calls. A cycle of calls contributes each member's reads once.
    fn transitive_reads(&mut self, key: BodyKey) -> HashSet<String> {
        if let Some(done) = self.closed.get(&key) {
            return done.clone();
        }
        let mut reads: HashSet<String> = HashSet::default();
        let mut seen: HashSet<BodyKey> = HashSet::default();
        let mut stack = vec![key.clone()];
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            if let Some(done) = self.closed.get(&current) {
                reads.extend(done.iter().cloned());
                continue;
            }
            let calls: Vec<Callee> = {
                let facts = self.facts(&current);
                reads.extend(facts.reads.iter().map(|(name, _)| name.clone()));
                facts
                    .calls
                    .iter()
                    .map(|(callee, _)| callee.clone())
                    .collect()
            };
            for callee in calls {
                stack.extend(self.targets(&callee));
            }
        }
        self.closed.insert(key, reads.clone());
        reads
    }
}

/// Collects a body's [`Facts`], tracking the locals that shadow globals and
/// functions.
struct Walker<'w> {
    program: &'w Program,
    module: &'w [String],
    globals: &'w HashSet<String>,
    /// The declaring type of the method being walked, for `self.m(..)`.
    self_type: Option<String>,
    facts: &'w mut Facts,
}

impl Walker<'_> {
    fn stmt(&mut self, stmt: &Stmt, bound: &HashSet<String>) {
        match stmt {
            Stmt::Let {
                value: Some(value), ..
            } => self.expr(value, bound),
            Stmt::Let { value: None, .. } => {}
            Stmt::Assign { target, value, .. } => {
                self.expr(target, bound);
                self.expr(value, bound);
            }
            Stmt::Expr(e) => self.expr(e, bound),
            Stmt::While { cond, body, .. } => {
                self.expr(cond, bound);
                self.block(body, bound);
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                self.expr(iter, bound);
                let mut inner = bound.clone();
                for n in pat.bound_names() {
                    inner.insert(n.to_string());
                }
                self.block(body, &inner);
            }
            Stmt::Return(Some(e), _) => self.expr(e, bound),
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }

    /// Walk a block tracking the locals introduced by earlier `let` statements
    /// so they shadow same-named globals for the remainder of the block.
    fn block(&mut self, block: &Block, bound: &HashSet<String>) {
        let mut local = bound.clone();
        for stmt in &block.stmts {
            if let Stmt::Let { pat, value, .. } = stmt {
                if let Some(value) = value {
                    self.expr(value, &local);
                }
                for name in pattern_names(pat) {
                    local.insert(name);
                }
            } else {
                self.stmt(stmt, &local);
            }
        }
    }

    /// Record the callable a call's callee (or a value reference) names.
    fn callee(&mut self, callee: &Expr, bound: &HashSet<String>) {
        match callee {
            Expr::Ident(name, span) if !bound.contains(name) && !self.globals.contains(name) => {
                self.facts
                    .calls
                    .push((Callee::Function(name.clone()), *span));
            }
            Expr::Field(base, method, span) if !callee.span().is_parenthesized() => {
                let owner = match base.as_ref() {
                    Expr::SelfExpr(_) => self.self_type.clone(),
                    Expr::Ident(name, _)
                        if !bound.contains(name) && !self.globals.contains(name) =>
                    {
                        self.program
                            .resolve_type(self.module, name)
                            .map(|info| info.symbol.clone())
                    }
                    _ => None,
                };
                self.facts
                    .calls
                    .push((Callee::Method(owner, method.clone()), *span));
            }
            _ => {}
        }
    }

    fn expr(&mut self, expr: &Expr, bound: &HashSet<String>) {
        match expr {
            Expr::Ident(name, span) => {
                if !bound.contains(name) {
                    if self.globals.contains(name) {
                        self.facts.reads.push((name.clone(), *span));
                    } else {
                        // A function referenced as a value may be called by
                        // whatever receives it.
                        self.callee(expr, bound);
                    }
                }
            }
            Expr::TypeTest(subject, _, _, _) => self.expr(subject, bound),
            Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(_)
            | Expr::SelfExpr(_) => {}
            Expr::Str(segs, _) => {
                for seg in segs {
                    if let StrSeg::Expr(inner) = seg {
                        self.expr(inner, bound);
                    }
                }
            }
            Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) | Expr::Field(inner, _, _) => {
                self.expr(inner, bound);
            }
            Expr::Binary(_, l, r, _) | Expr::Index(l, r, _) | Expr::Range(l, r, _) => {
                self.expr(l, bound);
                self.expr(r, bound);
            }
            Expr::Call(callee, args, _) => {
                match callee.as_ref() {
                    // A method call: the receiver is evaluated, the method runs.
                    Expr::Field(base, _, _) if !callee.span().is_parenthesized() => {
                        self.callee(callee, bound);
                        self.expr(base, bound);
                    }
                    // A named callee is a global read (a closure value) or a
                    // function call; anything else is an ordinary value.
                    other => self.expr(other, bound),
                }
                for arg in args {
                    self.expr(&arg.expr, bound);
                }
            }
            Expr::Closure(params, body, _) => {
                let mut inner = bound.clone();
                for p in params {
                    inner.insert(p.name.clone());
                }
                self.expr(body, &inner);
            }
            Expr::Array(items, _) => {
                for item in items {
                    self.expr(item, bound);
                }
            }
            Expr::TypeLit(_, fields, _) => {
                for (_, value) in fields {
                    self.expr(value, bound);
                }
            }
            Expr::VariantLit(_, _, fields, _) => {
                for (_, value) in fields {
                    self.expr(value, bound);
                }
            }
            Expr::If(cond, then, els, _) => {
                self.expr(cond, bound);
                self.block(then, bound);
                if let Some(els) = els {
                    self.expr(els, bound);
                }
            }
            Expr::IfLet(pat, scrut, then, els, _) => {
                self.expr(scrut, bound);
                let mut inner = bound.clone();
                for name in pattern_names(pat) {
                    inner.insert(name);
                }
                self.block(then, &inner);
                if let Some(els) = els {
                    self.expr(els, bound);
                }
            }
            Expr::Match(scrut, arms, _) => {
                self.expr(scrut, bound);
                for arm in arms {
                    let mut inner = bound.clone();
                    for name in pattern_names(&arm.pattern) {
                        inner.insert(name);
                    }
                    self.expr(&arm.body, &inner);
                }
            }
            Expr::Block(block, _) => self.block(block, bound),
        }
    }
}

/// Names bound by a pattern. Variant/record destructuring binds its fields.
fn pattern_names(pat: &Pattern) -> Vec<String> {
    let mut names = Vec::new();
    collect_pattern_names(pat, &mut names);
    names
}

fn collect_pattern_names(pat: &Pattern, out: &mut Vec<String>) {
    match pat {
        Pattern::Binding(name, _, _) => out.push(name.clone()),
        Pattern::Record(_, _, fields, _) => {
            for field in fields {
                match &field.pat {
                    Some(sub) => collect_pattern_names(sub, out),
                    None => out.push(field.name.clone()),
                }
            }
        }
        Pattern::Array(pats, _) => {
            for p in pats {
                collect_pattern_names(p, out);
            }
        }
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
    }
}
