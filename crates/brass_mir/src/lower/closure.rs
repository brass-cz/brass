//! Closure lowering: capturing a closure's environment, lowering its body
//! into its own [`MirClosure`], and building closure values.
//!
//! A closure value is built where its literal is evaluated -- except for a
//! *generalized* closure binding (`brass_hir::generalize`), which is
//! let-polymorphic: the binding records a [`ClosureTemplate`] (the literal
//! plus the environment it captured) instead of a value, and every use of
//! the name builds a fresh closure from it. Each use is then its own
//! closure, typed and compiled at that use's instantiation; capturing by
//! reference makes the fresh values behave as one shared value, except that
//! function values compare by identity, so each use equals no other value.
//! A module-level generalized binding has no local environment at all (its
//! free names are globals and functions), so a use in any body of any module
//! rebuilds it from the declaration alone.

use std::rc::Rc;

use brass_hir::Type;
use brass_parser::Span;
use brass_parser::ast::{Arg, Block, Expr, Param, Stmt};

use crate::analysis::free_vars_of;
use crate::cfg::Terminator;
use crate::ids::{BlockId, ClosureId};
use crate::lower::{FnLower, ProgramCtx};
use crate::program::MirClosure;
use crate::value::{Operand, Rvalue};

/// How a lowered closure receives its arguments.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ParamPassing {
    /// The parameter-passing table every source closure follows, exactly
    /// like a function: an annotated aggregate, `mut(T)` or `infer`, and an
    /// unannotated parameter the body mutates, are private deep copies made
    /// on entry; `ref(..)` and read-only parameters borrow.
    Table,
    /// Every parameter borrows the caller's value: a compiler-built
    /// forwarder (whose callee applies its own passing), and a `with`
    /// callback, whose parameter is the guarded shared object itself.
    Borrow,
}

/// What one free name of a closure body resolves to in the enclosing body.
#[derive(Clone)]
pub(crate) enum EnvValue {
    /// A local value: the operand holding it, and whether it is a shared
    /// cell (the operand is then the one-element cell array).
    Value { value: Operand, cell: bool },
    /// A generalized closure binding, rebuilt inside the body at each use.
    Template(Rc<ClosureTemplate>),
}

/// The bindings a closure body's free names resolve to where it is created,
/// in a fixed order. Its value leaves, depth first, are the closure's
/// captured operands.
#[derive(Clone, Default)]
pub(crate) struct ClosureEnv(Vec<(String, EnvValue)>);

impl ClosureEnv {
    /// The captured values, depth first, each with its capture name and
    /// whether it is a cell. A value reached through a template is named by
    /// its path (`template#name`), which no source identifier can spell, so
    /// it never collides with a name the body binds itself.
    fn slots(&self) -> Vec<(String, Operand, bool)> {
        let mut out = Vec::new();
        self.collect_slots("", &mut out);
        out
    }

    fn collect_slots(&self, prefix: &str, out: &mut Vec<(String, Operand, bool)>) {
        for (name, value) in &self.0 {
            match value {
                EnvValue::Value { value, cell } => {
                    out.push((format!("{prefix}{name}"), value.clone(), *cell))
                }
                EnvValue::Template(t) => t.env.collect_slots(&format!("{prefix}{name}#"), out),
            }
        }
    }

    /// The same environment over new value operands, consumed depth first in
    /// [`Self::slots`] order: how the body of a closure created from this
    /// environment sees it (each value is one of its capture locals).
    fn rebased(&self, values: &mut impl Iterator<Item = Operand>) -> ClosureEnv {
        ClosureEnv(
            self.0
                .iter()
                .map(|(name, value)| {
                    let value = match value {
                        EnvValue::Value { cell, .. } => EnvValue::Value {
                            value: values.next().expect("one operand per captured value"),
                            cell: *cell,
                        },
                        EnvValue::Template(t) => EnvValue::Template(Rc::new(ClosureTemplate {
                            env: t.env.rebased(values),
                            ..(**t).clone()
                        })),
                    };
                    (name.clone(), value)
                })
                .collect(),
        )
    }
}

/// A generalized closure binding: the closure literal and the environment it
/// captured at the binding, from which every use builds its own closure.
#[derive(Clone)]
pub(crate) struct ClosureTemplate {
    params: Vec<Param>,
    body: Rc<Expr>,
    env: ClosureEnv,
    /// The module whose names the body resolves in.
    module: Vec<String>,
    self_type: Option<String>,
}

impl<'a, 'p> FnLower<'a, 'p> {
    /// Lower a source closure literal, whose parameters follow the
    /// parameter-passing table (see [`Self::lower_closure_passing`]).
    pub(super) fn lower_closure(&mut self, params: &[Param], body: &Expr, span: Span) -> Operand {
        self.lower_closure_passing(params, body, ParamPassing::Table, Some(span))
    }

    /// Lower a closure: capture the free variables in scope, lower its body into
    /// its own MIR, register it in the program-wide table, and yield a closure
    /// value naming the captured operands. `passing` decides how the closure
    /// receives its arguments. `typed_at` is the source span whose checked
    /// function type (the `expr_types` channel) types the value: the checker
    /// fixed the parameter types there -- from an expected function type or
    /// the closure's applications -- and the back end instantiates the body
    /// at exactly those types rather than re-deriving them from its uses.
    pub(super) fn lower_closure_passing(
        &mut self,
        params: &[Param],
        body: &Expr,
        passing: ParamPassing,
        typed_at: Option<Span>,
    ) -> Operand {
        let env = self.closure_env(params, body);
        let (module, self_type) = (self.module.clone(), self.self_type.clone());
        self.emit_closure(&env, params, body, passing, module, self_type, typed_at)
    }

    /// Bind the generalized closure binding `name = (params) -> body` as a
    /// template: no value is built here, every use builds its own.
    pub(super) fn bind_closure_template(&mut self, name: &str, params: &[Param], body: &Expr) {
        let template = ClosureTemplate {
            params: params.to_vec(),
            body: Rc::new(body.clone()),
            env: self.closure_env(params, body),
            module: self.module.clone(),
            self_type: self.self_type.clone(),
        };
        self.bind_template(name, Rc::new(template));
    }

    /// Build the closure value of one use of a generalized closure binding,
    /// typed by the checker's instantiation recorded at `typed_at` (the use).
    pub(super) fn instantiate_template(
        &mut self,
        template: &ClosureTemplate,
        typed_at: Option<Span>,
    ) -> Operand {
        self.emit_closure(
            &template.env,
            &template.params,
            &template.body,
            ParamPassing::Table,
            template.module.clone(),
            template.self_type.clone(),
            typed_at,
        )
    }

    /// Build the closure value of one use of the module-level generalized
    /// closure binding stored under global symbol `symbol`, when it is one.
    pub(super) fn instantiate_global_template(
        &mut self,
        symbol: &str,
        typed_at: Option<Span>,
    ) -> Option<Operand> {
        let (module, params, body) = self.ctx.tables.global_templates.get(symbol)?.clone();
        Some(self.emit_closure(
            &ClosureEnv::default(),
            &params,
            &body,
            ParamPassing::Table,
            module,
            None,
            typed_at,
        ))
    }

    /// The environment of a closure literal created here: each free name of
    /// its body bound in this scope (a value or a generalized binding), in
    /// sorted name order. Names not bound here are globals or functions,
    /// which the body resolves itself.
    fn closure_env(&self, params: &[Param], body: &Expr) -> ClosureEnv {
        let block = closure_block(body);
        let mut env = Vec::new();
        for n in free_vars_of(params, &block) {
            if let Some(template) = self.lookup_template(&n) {
                env.push((n, EnvValue::Template(template)));
            } else if let Some(local) = self.lookup(&n) {
                // A cell-promoted capture is the shared cell array (its local
                // holds the array pointer); the closure body accesses it
                // through element 0.
                let cell = self.is_cell(&n);
                env.push((
                    n,
                    EnvValue::Value {
                        value: Operand::Local(local),
                        cell,
                    },
                ));
            }
        }
        ClosureEnv(env)
    }

    /// Lower the body as a new closure over `env` and emit its value.
    #[allow(clippy::too_many_arguments)]
    fn emit_closure(
        &mut self,
        env: &ClosureEnv,
        params: &[Param],
        body: &Expr,
        passing: ParamPassing,
        module: Vec<String>,
        self_type: Option<String>,
        typed_at: Option<Span>,
    ) -> Operand {
        let id = self.ctx.fresh_closure_id();
        let closure = lower_closure_body(
            self.ctx, module, self_type, id, env, params, body, passing, typed_at,
        );
        self.ctx.closures.borrow_mut().push(closure);
        let value = Rvalue::Closure {
            id,
            captures: env.slots().into_iter().map(|(_, op, _)| op).collect(),
        };
        // The checked function type every instance shares rides on the
        // local; a type the instances disagree on is looked up per instance
        // by the site (see `LocalDecl::seed_site`).
        match typed_at {
            Some(span) => {
                let shared = self
                    .ctx
                    .expr_type(span)
                    .filter(|ty| matches!(ty, Type::Fun(..)))
                    .cloned();
                self.b.emit_seeded(value, span, shared)
            }
            None => self.b.emit(value),
        }
    }

    /// Eta-expand a bare reference to top-level function `name` of `arity`
    /// parameters into the forwarding closure `(a0, .., a{n-1}) -> name(a0, ..,
    /// a{n-1})`. Reuses closure lowering, so the value is an ordinary closure the
    /// monomorphizer and both back ends already handle.
    ///
    /// A value the checker typed with fewer parameters (a function whose
    /// trailing parameters are optional, used at the arity its use needs)
    /// forwards only those; the call fills the omitted ones with `null`
    /// exactly as a direct call omitting them does.
    pub(super) fn lower_fn_value(
        &mut self,
        name: &str,
        arity: usize,
        typed_at: Option<Span>,
    ) -> Operand {
        let arity = match typed_at.and_then(|span| self.ctx.expr_type(span)) {
            Some(Type::Fun(params, _)) if params.len() < arity => params.len(),
            _ => arity,
        };
        let span = Span::new(0, 0);
        let names: Vec<String> = (0..arity).map(|i| format!("__eta{i}")).collect();
        let params: Vec<Param> = names
            .iter()
            .map(|n| Param {
                name: n.clone(),
                ty: None,
                span,
            })
            .collect();
        let args: Vec<Arg> = names
            .iter()
            .map(|n| Arg {
                expr: Expr::Ident(n.clone(), span),
            })
            .collect();
        let body = Expr::Call(Box::new(Expr::Ident(name.to_string(), span)), args, span);
        // A pure forwarder: the function's own entry applies its parameter
        // passing, so the wrapper must hand the arguments on untouched (a
        // copy here would cut a `ref(mut(T))` parameter's write-through).
        self.lower_closure_passing(&params, &body, ParamPassing::Borrow, typed_at)
    }
}

/// View a closure body as a block (an expression body becomes a one-statement
/// block whose value is returned).
fn closure_block(body: &Expr) -> Block {
    match body {
        Expr::Block(b, _) => b.clone(),
        other => Block {
            stmts: vec![Stmt::Expr(other.clone())],
            span: other.span(),
        },
    }
}

/// Lower a closure body into its own [`MirClosure`]. Captures are bound first
/// (the closure environment), then parameters; the body returns its value.
#[allow(clippy::too_many_arguments)]
fn lower_closure_body(
    ctx: &ProgramCtx,
    module: Vec<String>,
    self_type: Option<String>,
    id: ClosureId,
    env: &ClosureEnv,
    params: &[Param],
    body: &Expr,
    passing: ParamPassing,
    created_at: Option<Span>,
) -> MirClosure {
    let mut fl = FnLower::new(ctx, module.clone(), self_type);
    // Cell candidates local to this closure: its own captured-and-mutated
    // bindings (for nested closures). As in `lower_callable`, each binder
    // decides for its own binding, so a parameter binds plainly (shadowing any
    // same-named captured cell) while a `let` of a candidate name is promoted.
    fl.cells = crate::analysis::cell_promotions(&closure_block(body));
    let slots = env.slots();
    let captures: Vec<_> = slots
        .iter()
        .map(|(name, _, _)| fl.b.fresh_local(Some(name.clone())))
        .collect();
    // The body sees its environment over its own capture locals: a captured
    // value is bound to its local (a shared cell stays a cell binding: its
    // local holds the cell array, read and written through element 0), and a
    // captured generalized binding is a template over the capture locals of
    // the values it captured.
    let rebased = env.rebased(&mut captures.iter().map(|l| Operand::Local(*l)));
    for (name, value) in rebased.0 {
        match value {
            EnvValue::Value {
                value: Operand::Local(local),
                cell,
            } => fl.bind_as(&name, local, cell),
            EnvValue::Value { .. } => unreachable!("a capture is bound to its local"),
            EnvValue::Template(template) => fl.bind_template(&name, template),
        }
    }
    // Closure parameters follow the same passing table as function
    // parameters (see [`ParamPassing::Table`]): a closure never writes through
    // to its caller -- nor into a `const` argument -- unless its parameter is
    // `ref(mut(T))`.
    let copies = match passing {
        ParamPassing::Table => fl.entry_param_copies(params, &closure_block(body)),
        ParamPassing::Borrow => vec![false; params.len()],
    };
    let param_locals = fl.bind_params(params, &copies);
    match body {
        // Block body: explicit returns drive control flow; a falling-off tail
        // returns void.
        Expr::Block(b, _) => {
            fl.lower_body_stmts(&b.stmts);
            if !fl.b.terminated() {
                fl.b.terminate(Terminator::Return(Operand::void()));
            }
        }
        // Expression body: its value is the closure result.
        other => {
            let v = fl.lower_expr(other);
            if !fl.b.terminated() {
                fl.b.terminate(Terminator::Return(v));
            }
        }
    }
    let mir_body = fl.b.finish(param_locals.clone(), BlockId(0));
    // A closure has no return annotation, so its fallibility is always the
    // inferred form: an `error(...)`/Result-`!` body returns a `Result` whose
    // bare returns codegen Ok-wraps. A nullable-operand `!` (a `null_props`
    // span) instead makes the return nullable, exactly as for functions.
    let fallible = crate::analysis::fallible_block_except(&closure_block(body), ctx.null_props);
    MirClosure {
        source: body.span(),
        created_at,
        capture_cells: slots.iter().map(|(_, _, cell)| *cell).collect(),
        id,
        params: param_locals,
        captures,
        capture_names: slots.into_iter().map(|(name, _, _)| name).collect(),
        module,
        fallible,
        body: mir_body,
    }
}
