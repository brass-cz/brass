//! Which earlier inputs of an interactive REPL session run again before a new
//! one.
//!
//! The session is checked as one program, but each input executes once: an
//! earlier call, `input()` or print is never repeated. A later input still
//! needs the values of earlier bindings, so the statements that only rebuild
//! values -- bindings and updates whose expressions are free of side effects
//! -- run again ahead of it (see [`plan`]). A binding whose value came from
//! anything else is unavailable to later inputs, and the REPL says so (see
//! [`ReplayPlan::explain`]) instead of reporting an unknown name.

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use brass_hir::{MutationInfo, ParamInfo, Program};
use brass_parser::ast::{Block, Expr, Stmt, StrSeg, TopLevel};
use brass_parser::{Span, parse};

/// The earlier inputs to run again before a new input, and the bindings that
/// are not available to it.
pub(crate) struct ReplayPlan {
    /// The earlier inputs to run again, in session order.
    pub(crate) statements: Vec<String>,
    /// Bindings a later input cannot use, with the reason.
    unavailable: HashMap<String, Unavailable>,
}

/// Why an earlier binding is not available to later inputs.
#[derive(Clone, Copy)]
enum Unavailable {
    /// Its initializer has effects (a call, `input()`, an interpolated string
    /// that may run a `display` method, control flow), so it is not run again.
    Bound,
    /// An earlier input that is not run again may have changed it.
    Changed,
}

impl ReplayPlan {
    /// A diagnostic explaining a failed check of the replayed program when the
    /// failure is an unknown name that an earlier input bound but that is not
    /// available to this one; `None` for any other failure.
    pub(crate) fn explain(&self, error: &str) -> Option<String> {
        let name = error.split("unknown name `").nth(1)?.split('`').next()?;
        let reason = self.unavailable.get(name)?;
        Some(match reason {
            Unavailable::Bound => format!(
                "error: `{name}` is not available in this input: the REPL runs each input \
                 once, and `{name}` was bound by a statement with side effects (its \
                 initializer calls a function, interpolates a string or branches), which \
                 is not run again; use it in the input that binds it"
            ),
            Unavailable::Changed => format!(
                "error: `{name}` is not available in this input: the REPL runs each input \
                 once, and an earlier input that is not run again (a call, a loop or a \
                 branch) may have changed `{name}`"
            ),
        })
    }
}

/// Plan the replay of the earlier inputs `prior` of a session whose checked
/// program is `program`. An input runs again when it is a single statement
/// that only rebuilds values:
///
/// - a `let`/`const` binding whose initializer is free of side effects:
///   literals (strings without interpolation), names of available bindings
///   and of functions, operators, field and index reads, ranges, array,
///   record and variant constructions, and closure literals that write no
///   captured binding;
/// - an assignment to (a place rooted at) an available binding, with a
///   side-effect-free target and value;
/// - a growable-array update (`push`, `insert`, `remove`, `pop`) of an
///   available binding, with side-effect-free arguments.
///
/// Every other input is not run again, and the bindings it makes are
/// unavailable to later inputs. So is every binding an input that is not run
/// again may change -- assign, mutate in place, or hand to a callee that
/// writes through its parameter -- because its replayed value would be
/// stale: such a binding is not rebuilt at all. Values are shared by
/// reference (`let c = xs` names the same array), so a change reaches every
/// binding built from or stored into the changed one. A binding initialized
/// from an unavailable one is unavailable too; binding the name again in a
/// later input makes it available again.
pub(crate) fn plan(prior: &[String], program: &Program) -> ReplayPlan {
    let module = program
        .functions
        .get("main")
        .map(|f| f.module.clone())
        .unwrap_or_else(|| vec!["main".to_string()]);
    let info = MutationInfo::analyze(program);
    let inputs: Vec<Vec<Stmt>> = prior.iter().map(|item| input_statements(item)).collect();
    // Which bindings a later input changes is only known once the whole
    // session is walked, and an excluded binding excludes what reads it, so
    // the walk repeats until no new binding is found changed.
    let mut stale: HashSet<(String, usize)> = HashSet::default();
    loop {
        let mut planner = Planner {
            program,
            module: &module,
            info: &info,
            stale: &stale,
            available: HashSet::default(),
            unavailable: HashMap::default(),
            bound_at: HashMap::default(),
            links: HashMap::default(),
            changed: HashSet::default(),
        };
        let replayed: Vec<bool> = inputs
            .iter()
            .enumerate()
            .map(|(index, stmts)| planner.input(index, stmts))
            .collect();
        if planner.changed.is_subset(&stale) {
            let statements = prior
                .iter()
                .zip(replayed)
                .filter(|(_, replayed)| *replayed)
                .map(|(item, _)| item.clone())
                .collect();
            return ReplayPlan {
                statements,
                unavailable: planner.unavailable,
            };
        }
        stale.extend(planner.changed);
    }
}

/// The statements of one input; empty when it does not parse (it was
/// accepted, so it does) or holds no statement.
fn input_statements(item: &str) -> Vec<Stmt> {
    let Ok(module) = parse(item) else {
        return Vec::new();
    };
    module
        .items
        .into_iter()
        .filter_map(|item| match item {
            TopLevel::Stmt(stmt) => Some(stmt),
            _ => None,
        })
        .collect()
}

struct Planner<'p> {
    program: &'p Program,
    module: &'p [String],
    info: &'p MutationInfo,
    /// Bindings, as `(name, index of the input that bound it)`, that an
    /// input which is not run again changes: they are not rebuilt.
    stale: &'p HashSet<(String, usize)>,
    available: HashSet<String>,
    unavailable: HashMap<String, Unavailable>,
    /// The input that made the current binding of each name.
    bound_at: HashMap<String, usize>,
    /// For each name, the names whose values it may share: it was built from
    /// them, stored into them, or handed to the same statement.
    links: HashMap<String, HashSet<String>>,
    /// The bindings found changed by an input that is not run again.
    changed: HashSet<(String, usize)>,
}

impl Planner<'_> {
    /// Classify the earlier input number `index`, updating the binding sets;
    /// whether it runs again.
    fn input(&mut self, index: usize, stmts: &[Stmt]) -> bool {
        let replayed = matches!(stmts, [stmt] if self.replayable(index, stmt));
        for stmt in stmts {
            self.link(stmt);
            if !replayed {
                self.record_changes(stmt);
            }
            if let Stmt::Let { pat, .. } = stmt {
                for name in pat.bound_names() {
                    self.bound_at.insert(name.to_string(), index);
                    if replayed {
                        self.available.insert(name.to_string());
                        self.unavailable.remove(name);
                    } else {
                        let reason = if self.stale.contains(&(name.to_string(), index)) {
                            Unavailable::Changed
                        } else {
                            Unavailable::Bound
                        };
                        self.available.remove(name);
                        self.unavailable.insert(name.to_string(), reason);
                    }
                }
            }
        }
        replayed
    }

    /// Whether `stmt` (the input number `index`) only rebuilds values from
    /// available bindings and binds none a later input changes.
    fn replayable(&self, index: usize, stmt: &Stmt) -> bool {
        match stmt {
            Stmt::Let { pat, value, .. } => {
                value.as_ref().is_none_or(|v| self.pure(v))
                    && pat
                        .bound_names()
                        .iter()
                        .all(|name| !self.stale.contains(&(name.to_string(), index)))
            }
            Stmt::Assign { target, value, .. } => {
                self.rooted_at_available(target) && self.pure(target) && self.pure(value)
            }
            Stmt::Expr(Expr::Call(callee, args, _)) => match &**callee {
                Expr::Field(receiver, method, _) => {
                    !callee.span().is_parenthesized()
                        && matches!(method.as_str(), "push" | "insert" | "remove" | "pop")
                        && self.rooted_at_available(receiver)
                        && self.pure(receiver)
                        && args.iter().all(|arg| self.pure(&arg.expr))
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn rooted_at_available(&self, place: &Expr) -> bool {
        brass_hir::root_ident(place).is_some_and(|root| self.available.contains(root))
    }

    /// Whether evaluating `e` has no effect beyond producing its value, and
    /// every name it reads is still available.
    fn pure(&self, e: &Expr) -> bool {
        match e {
            Expr::Int(..) | Expr::Float(..) | Expr::Bool(..) | Expr::Null(..) => true,
            Expr::Ident(name, _) => !self.unavailable.contains_key(name),
            Expr::Str(segments, _) => segments
                .iter()
                .all(|segment| matches!(segment, StrSeg::Lit(_))),
            Expr::Unary(_, inner, _) | Expr::Field(inner, _, _) => self.pure(inner),
            Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
                self.pure(a) && self.pure(b)
            }
            Expr::Array(items, _) => items.iter().all(|item| self.pure(item)),
            Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
                fields.iter().all(|(_, value)| self.pure(value))
            }
            Expr::Closure(params, body, _) => {
                // Building a closure runs nothing; it must capture only
                // available bindings and write none of them (a later call
                // that is not run again would change them unseen).
                let mut names = Vec::new();
                mentioned_names(body, &mut names);
                names.iter().all(|name| {
                    params.iter().any(|p| p.name == *name)
                        || (!self.unavailable.contains_key(name) && !self.changes(body, name))
                })
            }
            Expr::SelfExpr(..)
            | Expr::Call(..)
            | Expr::ErrorProp(..)
            | Expr::If(..)
            | Expr::IfLet(..)
            | Expr::TypeTest(..)
            | Expr::Match(..)
            | Expr::Block(..) => false,
        }
    }

    /// Link the names whose values `stmt` may make shared: what a binding,
    /// an assignment or an in-place update stores with what it reads, and
    /// for any other statement everything it mentions.
    fn link(&mut self, stmt: &Stmt) {
        let mut read = Vec::new();
        let mut stored: Vec<String> = match stmt {
            Stmt::Let { pat, value, .. } => {
                if let Some(value) = value {
                    mentioned_names(value, &mut read);
                }
                let bound: Vec<String> = pat.bound_names().iter().map(|n| n.to_string()).collect();
                // A new binding shares nothing with the one it shadows.
                for name in &bound {
                    self.unlink(name);
                }
                bound
            }
            Stmt::Assign { target, value, .. } => {
                mentioned_names(value, &mut read);
                brass_hir::root_ident(target)
                    .map(str::to_string)
                    .into_iter()
                    .collect()
            }
            other => {
                statement_names(other, &mut read);
                Vec::new()
            }
        };
        // Only bindings of the session hold values; a function's name does not.
        read.retain(|name| self.bound_at.contains_key(name));
        if !matches!(stmt, Stmt::Let { .. } | Stmt::Assign { .. }) {
            stored = read.clone();
        }
        for target in &stored {
            for source in &read {
                if source != target {
                    self.links
                        .entry(target.clone())
                        .or_default()
                        .insert(source.clone());
                    self.links
                        .entry(source.clone())
                        .or_default()
                        .insert(target.clone());
                }
            }
        }
    }

    /// Forget the links of a binding a new one of the same name shadows.
    fn unlink(&mut self, name: &str) {
        if let Some(linked) = self.links.remove(name) {
            for other in linked {
                if let Some(back) = self.links.get_mut(&other) {
                    back.remove(name);
                }
            }
        }
    }

    /// Record the bindings a statement that is not run again may change --
    /// directly, or through a value they share with a changed one.
    fn record_changes(&mut self, stmt: &Stmt) {
        // Binding a closure literal runs none of its body.
        if let Stmt::Let {
            value: Some(Expr::Closure(..)),
            ..
        } = stmt
        {
            return;
        }
        let block = Expr::Block(
            Block {
                stmts: vec![stmt.clone()],
                span: Span::new(0, 0),
            },
            Span::new(0, 0),
        );
        let mut mentioned = Vec::new();
        statement_names(stmt, &mut mentioned);
        let mut changed: Vec<String> = mentioned
            .into_iter()
            .filter(|name| self.bound_at.contains_key(name) && self.changes(&block, name))
            .collect();
        let mut seen: HashSet<String> = changed.iter().cloned().collect();
        let mut next = 0;
        while let Some(name) = changed.get(next).cloned() {
            next += 1;
            for linked in self.links.get(&name).into_iter().flatten() {
                if seen.insert(linked.clone()) {
                    changed.push(linked.clone());
                }
            }
        }
        for name in changed {
            if let Some(&index) = self.bound_at.get(&name) {
                self.changed.insert((name.clone(), index));
            }
            if self.available.remove(&name) {
                self.unavailable.insert(name, Unavailable::Changed);
            }
        }
    }

    /// Whether running `e` may change the binding `name`: assign it (or a
    /// place rooted at it), or mutate its value -- in place, or through a
    /// callee or function value that writes through what it is handed.
    fn changes(&self, e: &Expr, name: &str) -> bool {
        if assigns(e, name) {
            return true;
        }
        let block = match e {
            Expr::Block(block, _) => block.clone(),
            other => Block {
                stmts: vec![Stmt::Expr(other.clone())],
                span: Span::new(0, 0),
            },
        };
        brass_hir::mutates_value::<ParamInfo>(
            self.program,
            self.module,
            &[],
            &block,
            name,
            self.info,
        )
    }
}

/// Every identifier a statement mentions.
fn statement_names(stmt: &Stmt, out: &mut Vec<String>) {
    let block = Expr::Block(
        Block {
            stmts: vec![stmt.clone()],
            span: Span::new(0, 0),
        },
        Span::new(0, 0),
    );
    mentioned_names(&block, out);
}

/// Every identifier `e` mentions, nested closures and blocks included.
fn mentioned_names(e: &Expr, out: &mut Vec<String>) {
    visit_expr(e, &mut |node| {
        if let Node::Expr(Expr::Ident(name, _)) = node {
            out.push(name.clone());
        }
    });
}

/// Whether `e` contains an assignment whose target is rooted at `name`.
fn assigns(e: &Expr, name: &str) -> bool {
    let mut found = false;
    visit_expr(e, &mut |node| {
        if let Node::AssignTarget(target) = node {
            found |= brass_hir::root_ident(target) == Some(name);
        }
    });
    found
}

/// A node [`visit_expr`] reports: every expression, and every assignment
/// target.
enum Node<'e> {
    Expr(&'e Expr),
    AssignTarget(&'e Expr),
}

fn visit_expr<'e>(e: &'e Expr, f: &mut impl FnMut(Node<'e>)) {
    f(Node::Expr(e));
    match e {
        Expr::Unary(_, a, _)
        | Expr::ErrorProp(a, _)
        | Expr::Field(a, _, _)
        | Expr::TypeTest(a, _, _, _) => visit_expr(a, f),
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
            visit_expr(a, f);
            visit_expr(b, f);
        }
        Expr::Call(callee, args, _) => {
            visit_expr(callee, f);
            for arg in args {
                visit_expr(&arg.expr, f);
            }
        }
        Expr::Closure(_, body, _) => visit_expr(body, f),
        Expr::Array(items, _) => items.iter().for_each(|item| visit_expr(item, f)),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            fields.iter().for_each(|(_, value)| visit_expr(value, f))
        }
        Expr::Str(segments, _) => {
            for segment in segments {
                if let StrSeg::Expr(inner) = segment {
                    visit_expr(inner, f);
                }
            }
        }
        Expr::If(cond, then, els, _) => {
            visit_expr(cond, f);
            visit_block(then, f);
            if let Some(els) = els {
                visit_expr(els, f);
            }
        }
        Expr::IfLet(_, scrut, then, els, _) => {
            visit_expr(scrut, f);
            visit_block(then, f);
            if let Some(els) = els {
                visit_expr(els, f);
            }
        }
        Expr::Match(scrut, arms, _) => {
            visit_expr(scrut, f);
            for arm in arms {
                visit_expr(&arm.body, f);
            }
        }
        Expr::Block(block, _) => visit_block(block, f),
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(..)
        | Expr::Ident(..)
        | Expr::SelfExpr(..) => {}
    }
}

fn visit_block<'e>(block: &'e Block, f: &mut impl FnMut(Node<'e>)) {
    for stmt in &block.stmts {
        match stmt {
            Stmt::Let { value, .. } => {
                if let Some(value) = value {
                    visit_expr(value, f);
                }
            }
            Stmt::Assign { target, value, .. } => {
                f(Node::AssignTarget(target));
                visit_expr(target, f);
                visit_expr(value, f);
            }
            Stmt::While { cond, body, .. } => {
                visit_expr(cond, f);
                visit_block(body, f);
            }
            Stmt::For { iter, body, .. } => {
                visit_expr(iter, f);
                visit_block(body, f);
            }
            Stmt::Expr(e) | Stmt::Return(Some(e), _) => visit_expr(e, f),
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The replayed inputs of `prior`, checked as the session program.
    fn replayed(prior: &[&str]) -> Vec<String> {
        let src = format!("fun main() {{\n{}\n}}\n", prior.join("\n"));
        let ast = parse(&src).expect("parse");
        let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty(), "{errors:?}");
        let prior: Vec<String> = prior.iter().map(|s| s.to_string()).collect();
        plan(&prior, &program).statements
    }

    #[test]
    fn side_effect_free_bindings_and_updates_run_again() {
        let prior = [
            "let answer = 42",
            "let b = 3 + answer * 2",
            "let xs = [1, 2, b]",
            "xs.push(4)",
            "xs[0] = -xs[1]",
            "let p = { x: b, y: xs[0] }",
            "let inc = (n) -> n + b",
        ];
        assert_eq!(replayed(&prior), prior);
    }

    #[test]
    fn effects_are_not_repeated_and_what_they_touch_is_dropped() {
        let replay = replayed(&[
            "let line = input()!",
            "let n = line.len()",
            "let xs = [1, 2]",
            "let copy = xs",
            "println(xs)",
            "for i in [0..2] { copy.push(i) }",
            "let later = copy",
            "let ys = [3]",
            "let shown = \"{ys}\"",
        ]);
        // `n` reads an effectful binding; the loop, which is not run again,
        // changes `copy` and so `xs`, whose array it names: neither is
        // rebuilt (their replayed value would be stale), nor `later`, which
        // reads one. An interpolated string may run a `display` method.
        assert_eq!(replay, ["let ys = [3]"]);
    }

    #[test]
    fn binding_a_name_again_makes_it_available() {
        let replay = replayed(&[
            "let xs = [1]",
            "for i in [0..2] { xs.push(i) }",
            "let xs = [7]",
            "let first = xs[0]",
        ]);
        assert_eq!(replay, ["let xs = [7]", "let first = xs[0]"]);
    }

    #[test]
    fn a_closure_writing_a_capture_is_not_rebuilt() {
        let replay = replayed(&["let total = 0", "let add = (n) -> { total = total + n }"]);
        assert_eq!(replay, ["let total = 0"]);
    }
}
