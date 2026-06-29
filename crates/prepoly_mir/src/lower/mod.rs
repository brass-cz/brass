//! HIR (AST-bearing) -> MIR lowering: building the type-independent CFG.
//!
//! [`lower_program`] walks a `prepoly_hir::Program` the same way codegen does
//! (free functions, record/sum methods, module inits, nested closures) and
//! produces a [`MirProgram`]. Each callable body becomes a [`MirBody`] via a
//! [`FnLower`], which keeps a [`BodyBuilder`] cursor plus the lexical scope and
//! loop-target stacks needed to place branches.
//!
//! The lowering performs three jobs and no type work:
//!  - control flow (`if`/`while`/`for`/`match`/`if let`/`&&`/`||`/`expr!`) is
//!    decomposed into basic blocks (see [`stmt`]);
//!  - expressions are flattened to three-address form, every value named by a
//!    local (see [`expr`]);
//!  - calls, places, and globals are resolved structurally, matching how the
//!    AST-walking codegen routes them so a MIR-driven back end is a faithful
//!    refactor.

mod expr;
mod pattern;
mod stmt;

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use prepoly_hir::{Program, TypeKind};
use prepoly_parser::ast::{AssignOp, BinOp, Block, Param};

use crate::analysis::fallible_block;
use crate::builder::BodyBuilder;
use crate::cfg::MirBody;
use crate::ids::{BlockId, ClosureId, LocalId};
use crate::program::{MirClosure, MirFunction, MirInit, MirMethod, MirProgram};

/// Shared, immutable-by-reference state for one lowering run. Interior
/// mutability holds the growing closure table and the global closure-id counter,
/// so deeply nested closure lowering can borrow this context immutably and still
/// register the closures it discovers without a borrow conflict.
pub(crate) struct ProgramCtx<'p> {
    program: &'p Program,
    /// Every sum-variant name in the program, used to tell a binding pattern
    /// (`x`) from a unit-variant pattern (`Red`) during match lowering.
    variant_names: std::collections::HashSet<String>,
    closures: RefCell<Vec<MirClosure>>,
    next_closure: Cell<u32>,
}

impl<'p> ProgramCtx<'p> {
    fn new(program: &'p Program) -> Self {
        let mut variant_names = std::collections::HashSet::new();
        for info in program.types.values() {
            if let TypeKind::Sum { variants } = &info.kind {
                for v in &variants[..] {
                    variant_names.insert(v.name.clone());
                }
            }
        }
        ProgramCtx {
            program,
            variant_names,
            closures: RefCell::new(Vec::new()),
            next_closure: Cell::new(0),
        }
    }

    /// Allocate the next globally-unique closure id.
    fn fresh_closure_id(&self) -> ClosureId {
        let id = self.next_closure.get();
        self.next_closure.set(id + 1);
        ClosureId(id)
    }

    /// Whether `name` denotes a type rather than a value: a user type, `Self`,
    /// the builtin `File`, or a primitive type word. Mirrors codegen's
    /// `is_type_word` so `Type.method(...)` routes as a static call.
    fn is_type_word(&self, name: &str) -> bool {
        self.program.types.contains_key(name)
            || name == "Self"
            || name == "File"
            || prepoly_hir::IntKind::from_name(name).is_some()
            || matches!(name, "float32" | "float64" | "string" | "bool")
    }

    /// The declared field names of record type `ty` (as seen from `module`), in
    /// declaration order, or `None` if `ty` is not a record. Used to desugar
    /// `T.from(v)` into a record built from `v`'s fields.
    fn record_field_names(&self, module: &[String], ty: &str) -> Option<Vec<String>> {
        let info = self.program.resolve_type(module, ty)?;
        match &info.kind {
            TypeKind::Record { fields, .. } => {
                Some(fields.iter().map(|f| f.name.clone()).collect())
            }
            _ => None,
        }
    }

    /// The dispatch key for a static call `ty.method(...)`: a user type's unique
    /// symbol, or the primitive type word unchanged (matches codegen).
    fn static_qualifier(&self, module: &[String], ty: &str) -> String {
        self.program
            .resolve_type(module, ty)
            .map(|t| t.symbol.clone())
            .unwrap_or_else(|| ty.to_string())
    }

    /// Resolve a bare free-function name to its storage symbol as seen from
    /// `module` (own/unique, this module's qualified, or imported), using the
    /// program's central resolver.
    fn resolve_fn_symbol(&self, module: &[String], name: &str) -> Option<String> {
        self.program.resolve_fn_symbol(module, name)
    }

    /// Per-parameter nullability of free function `name` as seen from `module`,
    /// used to pad omitted trailing nullable arguments with `null` at call sites
    /// (DESIGN.md 5.6). `None` if `name` is not a known free function.
    fn fn_param_nullability(&self, module: &[String], name: &str) -> Option<Vec<bool>> {
        self.program.resolve_function(module, name).map(|info| {
            info.signature
                .params
                .iter()
                .map(|p| matches!(p.ty, Some(prepoly_parser::ast::TypeExpr::Nullable(..))))
                .collect()
        })
    }

    /// Per-parameter "deep-copy the argument" flags for free function `name`: true
    /// where the parameter is a non-reference heap aggregate (array, tuple, record,
    /// or sum), so passing it by value copies rather than shares. A `ref(...)`
    /// parameter borrows (false); a primitive/string or unannotated parameter needs
    /// no copy (false). `None` if `name` is not a known free function.
    fn fn_param_copies(&self, module: &[String], name: &str) -> Option<Vec<bool>> {
        self.program.resolve_function(module, name).map(|info| {
            info.signature
                .params
                .iter()
                .map(|p| match &p.ty {
                    Some(t) => self.type_needs_copy(module, t),
                    None => false,
                })
                .collect()
        })
    }

    fn type_needs_copy(&self, module: &[String], t: &prepoly_parser::ast::TypeExpr) -> bool {
        use prepoly_parser::ast::TypeExpr;
        match t {
            // A reference borrows; a `mut(T)` is a mutable place whose copy-ness is
            // that of `T`. A non-reference array/slice parameter is passed by deep
            // copy. (Records, sums, and tuples are not yet copied at the back end, so
            // they keep their current shared passing until that is implemented.)
            TypeExpr::Ref(..) => false,
            TypeExpr::Mut(inner, _) => self.type_needs_copy(module, inner),
            TypeExpr::Array(..) => true,
            _ => false,
        }
    }
}

/// Per-body lowering state.
pub(crate) struct FnLower<'a, 'p> {
    pub(crate) b: BodyBuilder,
    pub(crate) ctx: &'a ProgramCtx<'p>,
    pub(crate) module: Vec<String>,
    pub(crate) self_type: Option<String>,
    /// Lexical scopes mapping source names to local slots; innermost last.
    scopes: Vec<HashMap<String, LocalId>>,
    /// Active loop targets as (continue, break) block pairs; innermost last.
    pub(crate) loops: Vec<(BlockId, BlockId)>,
    /// Names heap-promoted to a shared cell (a one-element array): a captured and
    /// mutated local (DESIGN.md 8.4). Reads/writes of such a name go through the
    /// cell's element 0; the closure captures the shared cell pointer.
    pub(crate) cells: std::collections::HashSet<String>,
}

impl<'a, 'p> FnLower<'a, 'p> {
    fn new(ctx: &'a ProgramCtx<'p>, module: Vec<String>, self_type: Option<String>) -> Self {
        FnLower {
            b: BodyBuilder::new(),
            ctx,
            module,
            self_type,
            scopes: vec![HashMap::new()],
            loops: Vec::new(),
            cells: std::collections::HashSet::new(),
        }
    }

    /// Whether `name` is heap-promoted to a shared cell in this body.
    pub(crate) fn is_cell(&self, name: &str) -> bool {
        self.cells.contains(name)
    }

    // ----- scopes -----

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    pub(crate) fn bind(&mut self, name: &str, local: LocalId) {
        self.scopes
            .last_mut()
            .expect("a scope is always open")
            .insert(name.to_string(), local);
    }

    pub(crate) fn lookup(&self, name: &str) -> Option<LocalId> {
        self.scopes.iter().rev().find_map(|s| s.get(name).copied())
    }

    /// Create a freshly named local, copy `op` into it, and bind `name` to it.
    /// Used for `let`, `for`, and pattern bindings so a bound name gets its own
    /// slot (writes to the binding never alias the source value).
    ///
    /// A captured-and-mutated binding (`is_cell`) is heap-promoted to a
    /// one-element cell array shared with the closures that capture it, with the
    /// value stored at element 0 (DESIGN.md 8.4). Routing every binder through
    /// here applies the wrap uniformly: a `for` variable or a destructured field
    /// that a closure captures and mutates is promoted exactly like a `let`,
    /// instead of being stored as a scalar that read/write/capture sites then
    /// wrongly index as an array.
    pub(crate) fn bind_value(&mut self, name: &str, op: crate::value::Operand) {
        let local = if self.is_cell(name) {
            let cell = self.b.emit(crate::value::Rvalue::Array(vec![op]));
            self.b.make_local(cell)
        } else {
            let local = self.b.fresh_local(Some(name.to_string()));
            self.b.push(crate::cfg::MirStmt::Assign(
                local,
                crate::value::Rvalue::Use(op),
            ));
            local
        };
        self.bind(name, local);
    }

    /// Resolve a possibly-`Self` type word to the concrete type name in scope.
    pub(crate) fn resolve_self_name(&self, name: &str) -> String {
        if name == "Self" {
            self.self_type.clone().unwrap_or_else(|| name.to_string())
        } else {
            name.to_string()
        }
    }

    // ----- callable bodies -----

    /// Lower a function/method body: bind parameters, run the statement
    /// sequence, and close any open tail with `return void`.
    fn lower_callable(&mut self, params: &[Param], body: &Block) -> Vec<LocalId> {
        // Heap-promote captured-and-mutated locals to shared cells (DESIGN.md 8.4).
        // Parameters are excluded -- they have no `let` to wrap.
        self.cells = crate::analysis::cell_promotions(body);
        for p in params {
            self.cells.remove(&p.name);
        }
        let param_locals = self.bind_params(params);
        self.lower_body_stmts(&body.stmts);
        self.close_void();
        param_locals
    }

    /// Bind each parameter to a fresh named local, returning them in order.
    fn bind_params(&mut self, params: &[Param]) -> Vec<LocalId> {
        params
            .iter()
            .map(|p| {
                // A parameter with a resolvable annotation is bound to a typed local
                // so monomorphization uses its declared type, not each call's argument
                // type. A nullable parameter thus stays nullable when a value or an
                // omitted-null argument is passed; the instance's parameter types
                // (set in monomorphization) drive the caller's argument coercion.
                let local = match p.ty.as_ref().and_then(stmt::resolve_simple_type) {
                    Some(t) => self.b.fresh_local_typed(Some(p.name.clone()), t),
                    None => self.b.fresh_local(Some(p.name.clone())),
                };
                self.bind(&p.name, local);
                local
            })
            .collect()
    }

    /// Terminate the current block with `return void` unless it already ended.
    fn close_void(&mut self) {
        if !self.b.terminated() {
            self.b
                .terminate(crate::cfg::Terminator::Return(crate::value::Operand::void()));
        }
    }
}

/// The binary operator a compound assignment folds through.
pub(crate) fn compound_op(op: AssignOp) -> BinOp {
    match op {
        AssignOp::Add => BinOp::Add,
        AssignOp::Sub => BinOp::Sub,
        AssignOp::Mul => BinOp::Mul,
        AssignOp::Div => BinOp::Div,
        AssignOp::Rem => BinOp::Rem,
        AssignOp::Eq => unreachable!("plain assignment is not a folding operator"),
    }
}

/// Lower a single callable body standalone, returning the body and any closures
/// it spawned. Convenient for tests and for on-demand lowering of one callable;
/// [`lower_program`] keeps closure ids unique across the whole program instead.
pub fn lower_body(
    program: &Program,
    module: &[String],
    self_type: Option<&str>,
    params: &[Param],
    body: &Block,
) -> (MirBody, Vec<MirClosure>) {
    let ctx = ProgramCtx::new(program);
    let body = lower_one(
        &ctx,
        module.to_vec(),
        self_type.map(str::to_string),
        params,
        body,
    );
    let mut closures = ctx.closures.into_inner();
    closures.sort_by_key(|c| c.id.0);
    (body, closures)
}

/// Lower one callable into a [`MirBody`] using a shared context.
fn lower_one(
    ctx: &ProgramCtx,
    module: Vec<String>,
    self_type: Option<String>,
    params: &[Param],
    body: &Block,
) -> MirBody {
    let mut fl = FnLower::new(ctx, module, self_type);
    let param_locals = fl.lower_callable(params, body);
    fl.b.finish(param_locals, BlockId(0))
}

/// Lower a whole program to MIR: every function, method, init body, and the
/// closures they spawn. Item enumeration mirrors `codegen::gen_functions` /
/// `gen_inits`, including the `Name@module` storage-symbol keys.
pub fn lower_program(program: &Program) -> MirProgram {
    let ctx = ProgramCtx::new(program);
    let mut out = MirProgram::default();

    let mut fn_names: Vec<&String> = program.functions.keys().collect();
    fn_names.sort();
    for name in fn_names {
        let info = &program.functions[name];
        let body = lower_one(
            &ctx,
            info.module.clone(),
            None,
            &info.decl.params,
            &info.decl.body,
        );
        out.functions.push(MirFunction {
            name: info.decl.name.clone(),
            symbol: info.symbol.clone(),
            module: info.module.clone(),
            fallible: function_fallible(info.decl.ret.as_ref(), &info.decl.body),
            body,
        });
    }

    let mut type_names: Vec<&String> = program.types.keys().collect();
    type_names.sort();
    for tn in type_names {
        let info = &program.types[tn];
        let self_type = Some(info.name.clone());
        match &info.kind {
            TypeKind::Record { methods, .. } => {
                let mut ms: Vec<&String> = methods.keys().collect();
                ms.sort();
                for m in ms {
                    let method = &methods[m];
                    if let Some(body) = &method.decl.body {
                        out.methods.push(lower_method(
                            &ctx,
                            info,
                            None,
                            &method.decl.name,
                            &method.decl.params,
                            body,
                            self_type.clone(),
                        ));
                    }
                }
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    let mut ms: Vec<&String> = v.methods.keys().collect();
                    ms.sort();
                    for m in ms {
                        let method = &v.methods[m];
                        if let Some(body) = &method.decl.body {
                            out.methods.push(lower_method(
                                &ctx,
                                info,
                                Some(v.name.clone()),
                                &method.decl.name,
                                &method.decl.params,
                                body,
                                self_type.clone(),
                            ));
                        }
                    }
                }
            }
        }
    }

    for init in &program.inits {
        let body = lower_init(&ctx, init.path.clone(), &init.stmts);
        out.inits.push(MirInit {
            module: init.path.clone(),
            body,
        });
    }

    let mut closures = ctx.closures.into_inner();
    closures.sort_by_key(|c| c.id.0);
    out.closures = closures;
    out
}

#[allow(clippy::too_many_arguments)]
fn lower_method(
    ctx: &ProgramCtx,
    info: &prepoly_hir::TypeInfo,
    variant: Option<String>,
    method: &str,
    params: &[Param],
    body: &Block,
    self_type: Option<String>,
) -> MirMethod {
    let mir_body = lower_one(ctx, info.module.clone(), self_type.clone(), params, body);
    MirMethod {
        type_name: info.name.clone(),
        type_symbol: info.symbol.clone(),
        variant,
        method: method.to_string(),
        self_type,
        module: info.module.clone(),
        fallible: method_fallible(params, body),
        body: mir_body,
    }
}

/// A method auto-wraps plain returns in `Result.Ok` when it has no declared
/// return type and its body uses `error`/`expr!` (matches codegen).
fn method_fallible(_params: &[Param], body: &Block) -> bool {
    fallible_block(body)
}

/// A free function auto-wraps plain returns in `Result.Ok` (and propagates
/// errors) when its return type is `T!` (explicitly fallible), or when it has no
/// return annotation and its body uses `error(...)`/`expr!` (inferred fallible).
/// An explicit non-`T!` return type means the body builds its own value, so bare
/// returns are not wrapped.
fn function_fallible(ret: Option<&prepoly_parser::ast::TypeExpr>, body: &Block) -> bool {
    match ret {
        Some(prepoly_parser::ast::TypeExpr::Fallible(..)) => true,
        Some(_) => false,
        None => fallible_block(body),
    }
}

/// Lower a module init body: top-level `let`/`const` initialize module globals;
/// every other statement runs as ordinary code (matches `codegen::gen_inits`).
fn lower_init(
    ctx: &ProgramCtx,
    module: Vec<String>,
    stmts: &[prepoly_parser::ast::Stmt],
) -> MirBody {
    use prepoly_parser::ast::Stmt;

    let mut fl = FnLower::new(ctx, module, None);
    for s in stmts {
        if fl.b.terminated() {
            break;
        }
        match s {
            Stmt::Let { pat, value, .. } => {
                let v = fl.lower_expr(value);
                fl.store_global_pattern(pat, v);
            }
            _ => fl.lower_stmt(s),
        }
    }
    fl.close_void();
    fl.b.finish(Vec::new(), BlockId(0))
}

impl<'a, 'p> FnLower<'a, 'p> {
    /// Store a top-level binding into module globals. A bare name binds directly;
    /// an array/tuple pattern destructures by position, storing each element's
    /// binding into its own global (so `let [i, s] = [1, "s"]` at module level
    /// makes `i` and `s` globals, matching how it binds locals inside a function).
    fn store_global_pattern(
        &mut self,
        pat: &prepoly_parser::ast::Pattern,
        v: crate::value::Operand,
    ) {
        use crate::cfg::MirStmt;
        use crate::value::{Literal, Operand, Place, Projection, Rvalue};
        use prepoly_parser::ast::Pattern;
        match pat {
            Pattern::Binding(name, _) => {
                self.b.push(MirStmt::SetGlobal(name.clone(), v));
            }
            Pattern::Array(pats, _) => {
                let subj = self.b.make_local(v);
                for (i, p) in pats.iter().enumerate() {
                    let elem = self.b.emit(Rvalue::Load(Place::projected(
                        subj,
                        vec![Projection::Index(Operand::Const(Literal::Int(i as i64)))],
                    )));
                    self.store_global_pattern(p, elem);
                }
            }
            // A record/variant pattern or a wildcard/literal at module top level is
            // not a global binding form: the value was already evaluated for effects.
            Pattern::Record(..) | Pattern::Wildcard(_) | Pattern::Literal(..) => {}
        }
    }
}
