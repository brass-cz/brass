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

use prepoly_hir::{Program, Type, TypeKind};
use prepoly_parser::Span;
use prepoly_parser::ast::{AssignOp, BinOp, Block, Param};

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
    /// The program's mutation facts (self-mutating methods, write-through
    /// positions), computed once per lowering: the entry-copy decision for an
    /// unannotated parameter needs them to count handing the parameter to a
    /// mutating position (a `m.set(..)` receiver) as a mutation, exactly like
    /// the const checker does.
    mutation: prepoly_hir::MutationInfo,
    /// Every sum-variant name in the program, used to tell a binding pattern
    /// (`x`) from a unit-variant pattern (`Red`) during match lowering.
    variant_names: std::collections::HashSet<String>,
    /// Checker-resolved types of selected expressions, keyed by source span. A
    /// call whose result is a constructed aggregate is looked up here so its
    /// result local is seeded `Known`, carrying the instance type the back end
    /// would otherwise be unable to infer (a witness-free constructor). Empty
    /// when lowering without a checked program (tests, deferred re-lowering).
    expr_types: &'p HashMap<Span, Type>,
    /// Spans of free-call arguments the checker verified as anonymous
    /// structural values fitting a view-ELIGIBLE callee parameter's row. Only
    /// these arguments are wrapped in [`crate::Rvalue::RecordView`]; lowering
    /// itself stays type-free -- the checker decided, this set is the channel.
    /// Empty when lowering without a checked program, so no view is ever
    /// emitted then (tests, deferred re-lowering keep full values).
    view_args: &'p std::collections::HashSet<Span>,
    /// Value expressions the checker accepted as a declared sum subtype at a
    /// flow site, keyed by the expression's span, mapped to the PARENT sum
    /// instance the site required. Lowering rebuilds exactly these values as
    /// the parent (per-variant tag test + reconstruction); the child's variant
    /// payloads may be wider, so identity flow would misread the unboxed
    /// layout. Empty when lowering without a checked program.
    sum_views: &'p HashMap<Span, Type>,
    /// Source positions of every call expression (diagnostic label, 1-based
    /// line/col), keyed by the call's span. A call that omits a callee's
    /// trailing `Location` parameter is completed from this map; empty when
    /// lowering without a checked program (the fill degrades to a placeholder).
    call_locations: &'p HashMap<Span, (String, u32, u32)>,
    /// `expr!` sites whose propagated Err payload is re-raised wrapped into
    /// the prelude `Error` (gaining the site's location); the propagation arm
    /// rebuilds the value. Empty when lowering without a checked program.
    lift_errs: &'p std::collections::HashSet<Span>,
    /// Field lists of `for f in fields(x)` loops, keyed by the loop statement's
    /// span: the checker resolved the record type and checked one expanded copy
    /// per field; lowering unrolls the same copies (`prepoly_hir::expand`).
    /// Empty when lowering without a checked program -- a fields-loop reached
    /// through deferred re-lowering is therefore unsupported.
    fields_loops: &'p HashMap<Span, Vec<String>>,
    /// Resolved type names of `typeof(x)` calls, keyed by call span; each
    /// such call lowers to this string constant.
    type_names: &'p HashMap<Span, String>,
    /// Resolved binding types of `typeof`-bearing local annotations, keyed by
    /// the annotation span; a `let x: typeof(v)` slot is seeded from this.
    typeof_types: &'p HashMap<Span, Type>,
    /// Spans of `expr!` operators the checker resolved with a NULLABLE operand:
    /// those lower to a presence test (`__present`/`__nonnull`) whose null arm
    /// propagates `Result.Null`, instead of the `Result` tag-test shape. Empty
    /// when lowering without a checked program (tests, deferred re-lowering),
    /// where a nullable `!` is therefore unsupported.
    null_props: &'p std::collections::HashSet<Span>,
    /// Names each module's init binds as module-level globals (top-level
    /// `let`s), used to key global storage per defining module.
    module_globals: HashMap<Vec<String>, std::collections::HashSet<String>>,
    /// Defining module of each standard-library global (the implicit prelude:
    /// `INT64_MAX` etc. are visible everywhere without an import). First
    /// definition in sorted module order wins, deterministically.
    prelude_globals: HashMap<String, Vec<String>>,
    closures: RefCell<Vec<MirClosure>>,
    next_closure: Cell<u32>,
}

impl<'p> ProgramCtx<'p> {
    #[allow(clippy::too_many_arguments)] // mirrors the checker's channel outputs
    fn new(
        program: &'p Program,
        expr_types: &'p HashMap<Span, Type>,
        view_args: &'p std::collections::HashSet<Span>,
        sum_views: &'p HashMap<Span, Type>,
        call_locations: &'p HashMap<Span, (String, u32, u32)>,
        lift_errs: &'p std::collections::HashSet<Span>,
        fields_loops: &'p HashMap<Span, Vec<String>>,
        type_names: &'p HashMap<Span, String>,
        typeof_types: &'p HashMap<Span, Type>,
        null_props: &'p std::collections::HashSet<Span>,
    ) -> Self {
        let mut variant_names = std::collections::HashSet::new();
        for info in program.types.values() {
            if let TypeKind::Sum { variants } = &info.kind {
                for v in &variants[..] {
                    variant_names.insert(v.name.clone());
                }
            }
        }
        let mut module_globals: HashMap<Vec<String>, std::collections::HashSet<String>> =
            HashMap::new();
        for init in &program.inits {
            let names = module_globals.entry(init.path.clone()).or_default();
            for s in &init.stmts {
                if let prepoly_parser::ast::Stmt::Let { pat, .. } = s {
                    collect_global_names(pat, names);
                }
            }
        }
        let mut prelude_globals: HashMap<String, Vec<String>> = HashMap::new();
        let mut std_paths: Vec<&Vec<String>> = module_globals
            .keys()
            .filter(|p| p.first().is_some_and(|seg| seg == "std"))
            .collect();
        std_paths.sort();
        for path in std_paths {
            for name in &module_globals[path] {
                prelude_globals
                    .entry(name.clone())
                    .or_insert_with(|| path.clone());
            }
        }
        ProgramCtx {
            program,
            mutation: prepoly_hir::MutationInfo::analyze(program),
            variant_names,
            expr_types,
            view_args,
            sum_views,
            call_locations,
            lift_errs,
            fields_loops,
            type_names,
            typeof_types,
            null_props,
            module_globals,
            prelude_globals,
            closures: RefCell::new(Vec::new()),
            next_closure: Cell::new(0),
        }
    }

    /// Whether the checker recorded the argument at `span` as convertible into
    /// its callee parameter's view.
    fn is_view_arg(&self, span: Span) -> bool {
        self.view_args.contains(&span)
    }

    /// Whether the checker resolved the `expr!` at `span` with a nullable
    /// operand (null propagates as `Result.Null`).
    fn is_null_prop(&self, span: Span) -> bool {
        self.null_props.contains(&span)
    }

    /// The parent sum instance the checker recorded for the value expression
    /// at `span`, when that value flows as a declared sum subtype.
    fn sum_view_target(&self, span: Span) -> Option<&Type> {
        self.sum_views.get(&span)
    }

    /// A bare reference to nominal `name` when every declared field is
    /// concrete (fully known) and it has no type slots: safe to seed a local
    /// slot with. A generic nominal's open fields must stay inferred -- the
    /// witness machinery owns them -- so it yields `None`.
    fn concrete_nominal_ref(&self, module: &[String], name: &str) -> Option<Type> {
        let info = self.program.resolve_type(module, name)?;
        if !info.slots.is_empty() {
            return None;
        }
        let concrete_fields = |fields: &[prepoly_hir::FieldInfo]| {
            fields.iter().all(|f| {
                f.resolved_ty
                    .as_ref()
                    .is_some_and(prepoly_hir::is_fully_known)
            })
        };
        let concrete = match &info.kind {
            TypeKind::Record { fields, .. } => concrete_fields(fields),
            TypeKind::Sum { variants } => variants.iter().all(|v| concrete_fields(&v.fields)),
        };
        concrete.then(|| info.type_ref())
    }

    /// The source position of the call at `span`, or a placeholder when
    /// lowering without a checked program (tests, deferred re-lowering).
    fn call_location(&self, span: Span) -> (String, u32, u32) {
        self.call_locations
            .get(&span)
            .cloned()
            .unwrap_or_else(|| ("<unknown>".to_string(), 0, 0))
    }

    /// The full parameter count of free function `name` when its LAST
    /// parameter is the implicit caller-location (a `Location`-annotated
    /// trailing parameter a call may omit; lowering fills the call site in).
    fn free_fn_wants_location(&self, module: &[String], name: &str) -> Option<usize> {
        let info = self.program.resolve_function(module, name)?;
        params_want_location(&info.signature.params)
    }

    /// Like [`Self::free_fn_wants_location`] for a method name: the fill is
    /// routed by name (lowering is type-free), so it applies only when every
    /// method of that name agrees on the trailing-location arity.
    fn method_wants_location(&self, method: &str) -> Option<usize> {
        let mut want: Option<usize> = None;
        for info in self.program.types.values() {
            let sigs: Vec<_> = match &info.kind {
                TypeKind::Record { methods, .. } => methods
                    .get(method)
                    .map(|m| &m.signature)
                    .into_iter()
                    .collect(),
                TypeKind::Sum { variants } => variants
                    .iter()
                    .filter_map(|v| v.methods.get(method).map(|m| &m.signature))
                    .collect(),
            };
            for sig in sigs {
                match (want, params_want_location(&sig.params)) {
                    (None, Some(n)) => want = Some(n),
                    (Some(prev), Some(n)) if prev == n => {}
                    // Disagreement (or a same-named method without the
                    // parameter): no fill, the checker's arity check governs.
                    _ => return None,
                }
            }
        }
        want
    }

    /// The storage key of module-level global `name` as referenced from
    /// `module`. Globals are keyed per *defining* module (`name@a/b`, like
    /// function storage symbols), so two modules' same-named top-level `let`s
    /// never share a slot. A name the referencing module does not define itself
    /// resolves through its import origin, then through the stdlib prelude
    /// (`INT64_MAX` and friends are visible without an import); an unresolved
    /// name keys under the referencing module (the checker rejects genuinely
    /// unknown names).
    /// Whether `name` resolves to a module-level global visible from `module`
    /// (its own, an import origin's, or a stdlib prelude global) -- the same
    /// resolution [`Self::global_symbol`] keys storage by.
    fn is_global_name(&self, module: &[String], name: &str) -> bool {
        let defines = |m: &[String], n: &str| {
            self.module_globals
                .get(m)
                .is_some_and(|names| names.contains(n))
        };
        defines(module, name)
            || self
                .program
                .import_origins
                .get(module)
                .and_then(|o| o.get(name))
                .is_some_and(|origin| defines(origin, name))
            || self
                .aliased_global(module, name)
                .is_some_and(|(declared, origin)| defines(&origin, &declared))
            || self.prelude_globals.contains_key(name)
    }

    fn global_symbol(&self, module: &[String], name: &str) -> String {
        let defines = |m: &[String], n: &str| {
            self.module_globals
                .get(m)
                .is_some_and(|names| names.contains(n))
        };
        if defines(module, name) {
            return prepoly_hir::qualify(name, module);
        }
        if let Some(origin) = self
            .program
            .import_origins
            .get(module)
            .and_then(|o| o.get(name))
            && defines(origin, name)
        {
            return prepoly_hir::qualify(name, origin);
        }
        if let Some((declared, origin)) = self.aliased_global(module, name)
            && defines(&origin, &declared)
        {
            return prepoly_hir::qualify(&declared, &origin);
        }
        if let Some(owner) = self.prelude_globals.get(name) {
            return prepoly_hir::qualify(name, owner);
        }
        prepoly_hir::qualify(name, module)
    }

    /// The (declared name, defining module) behind a global referenced by a name
    /// other than its own: a qualified use (`m.VERSION`, which the resolve pass
    /// rewrote to the dotted marker `m.VERSION`) or a renamed import
    /// (`import m.{ VERSION as V }`). Storage is keyed by the DECLARED name in its
    /// DEFINING module, so neither form finds its slot without this.
    fn aliased_global(&self, module: &[String], name: &str) -> Option<(String, Vec<String>)> {
        if let Some((alias, bare)) = name.split_once('.') {
            let origin = self.program.module_aliases.get(module)?.get(alias)?;
            return Some((bare.to_string(), origin.clone()));
        }
        let declared = self.program.import_renames.get(module)?.get(name)?;
        let origin = self.program.import_origins.get(module)?.get(name)?;
        Some((declared.clone(), origin.clone()))
    }

    /// The checker-resolved type recorded for the expression at `span`, if any.
    fn expr_type(&self, span: Span) -> Option<&Type> {
        self.expr_types.get(&span)
    }

    /// The type named `sym` (a storage symbol, falling back to a bare source
    /// name for types whose symbol is module-qualified), if any.
    pub(crate) fn type_info(&self, sym: &str) -> Option<&prepoly_hir::TypeInfo> {
        self.program
            .types
            .get(sym)
            .or_else(|| self.program.types.values().find(|i| i.name == sym))
    }

    /// The type with nominal id `id`, if any.
    pub(crate) fn type_info_by_id(&self, id: i32) -> Option<&prepoly_hir::TypeInfo> {
        self.program.types.values().find(|i| i.id == id)
    }

    /// Allocate the next globally-unique closure id.
    fn fresh_closure_id(&self) -> ClosureId {
        let id = self.next_closure.get();
        self.next_closure.set(id + 1);
        ClosureId(id)
    }

    /// Whether `name` denotes a type rather than a value: a user type, `Self`,
    /// the builtin `File`, or a primitive type word. Mirrors codegen's
    /// `is_type_word` so `Type.method(...)` routes as a static call. A dotted
    /// marker (`alias.T`) and a renamed import (`import m.{ T as name }`)
    /// appear in no table under `name` and resolve through the module-aware
    /// lookup instead.
    fn is_type_word_in(&self, module: &[String], name: &str) -> bool {
        // Module-aware for every form of the name: bare (which alone misses a
        // type whose symbol went module-qualified because another module declares
        // the same name -- e.g. an alias of it), dotted markers, and renames.
        // Locals shadowing a type name are already excluded by the caller.
        self.program.types.contains_key(name)
            || self.program.resolve_type(module, name).is_some()
            || name == "Self"
            || prepoly_hir::IntKind::from_name(name).is_some()
            || matches!(name, "float32" | "float64" | "string" | "bool")
    }

    /// Whether ANY type in the program (or the primitive-method table, or the
    /// built-in slice mutators) declares a method named `name`. `recv.name(..)`
    /// routes as a method call only then; otherwise the name is a record FIELD
    /// holding a function value, loaded and called indirectly.
    fn method_name_exists(&self, name: &str) -> bool {
        // Built-in slice mutators, which have no user-level declaration to
        // find in the type table.
        if matches!(name, "push" | "insert" | "remove" | "pop" | "len") {
            return true;
        }
        if self
            .program
            .primitive_methods
            .keys()
            .any(|(_, m)| m == name)
        {
            return true;
        }
        self.program.types.values().any(|info| match &info.kind {
            TypeKind::Record { methods, .. } => methods.contains_key(name),
            TypeKind::Sum { variants } => variants.iter().any(|v| v.methods.contains_key(name)),
        })
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
    /// used to pad omitted trailing nullable arguments with `null` at call sites. `None` if `name` is not a known free function.
    /// The parameter count of free function `name` as seen from `module`, used to
    /// eta-expand a bare function-name value into a forwarding closure. `None` if
    /// `name` is not a known free function.
    fn function_arity(&self, module: &[String], name: &str) -> Option<usize> {
        self.program
            .resolve_function(module, name)
            .map(|info| info.signature.params.len())
    }

    fn fn_param_nullability(&self, module: &[String], name: &str) -> Option<Vec<bool>> {
        self.program.resolve_function(module, name).map(|info| {
            info.signature
                .params
                .iter()
                .map(|p| matches!(p.ty, Some(prepoly_parser::ast::TypeExpr::Nullable(..))))
                .collect()
        })
    }

    /// Whether an annotated parameter type is passed by deep copy: a non-reference
    /// heap aggregate (array/slice, tuple, anonymous structure, named record/sum,
    /// nullable/fallible of one, or `infer`). A `ref(...)`/`ref(mut(..))`
    /// parameter borrows. The copy is applied on entry to the callee (see
    /// [`FnLower::entry_param_copies`]). Delegates to the shared predicate in
    /// `prepoly_hir` so the runtime copy decision and the const checker's
    /// write-through analysis never disagree.
    fn type_needs_copy(&self, module: &[String], t: &prepoly_parser::ast::TypeExpr) -> bool {
        prepoly_hir::annotated_type_passes_by_copy(self.program, module, t)
    }
}

/// One active loop: the `continue`/`break` jump targets, plus the `for`-loop
/// element write-back (if any) that every edge leaving the iteration must emit.
pub(crate) struct LoopFrame {
    pub(crate) cont: BlockId,
    pub(crate) brk: BlockId,
    /// `Some((arr, idx, var))` when the body reassigns the `for` variable `var`:
    /// its current value is stored back to `arr[idx]` before the iteration ends
    /// (fall-through, `continue`, or `break` -- not just the fall-through tail).
    pub(crate) writeback: Option<(LocalId, LocalId, String)>,
}

/// Per-body lowering state.
pub(crate) struct FnLower<'a, 'p> {
    pub(crate) b: BodyBuilder,
    pub(crate) ctx: &'a ProgramCtx<'p>,
    pub(crate) module: Vec<String>,
    pub(crate) self_type: Option<String>,
    /// Whether a failed `expr!` in this body ABORTS the program (printing the
    /// error and exiting non-zero) instead of returning the error `Result`
    /// (or null) from the enclosing callable. True for the entry `main` and
    /// for module-init bodies (top-level statements): both have no caller to
    /// propagate to. A closure lowered inside such a body gets its own
    /// `FnLower` and propagates normally.
    pub(crate) abort_error_prop: bool,
    /// Lexical scopes mapping source names to bindings; innermost last.
    scopes: Vec<HashMap<String, ScopeBinding>>,
    /// Active loops; innermost last.
    pub(crate) loops: Vec<LoopFrame>,
    /// Candidate names for heap promotion to a shared cell (a one-element
    /// array): a captured and mutated local. Whether a given *binding* of such
    /// a name is actually a cell is decided at its binder and recorded on the
    /// [`ScopeBinding`] (a parameter binds plainly even when a shadowing `let`
    /// of the same name is promoted). Reads/writes of a cell binding go through
    /// the cell's element 0; the closure captures the shared cell pointer.
    pub(crate) cells: std::collections::HashSet<String>,
}

/// A name bound in a lexical scope: its local slot, plus whether this
/// particular binding is a heap-promoted shared cell. Cell-ness is per
/// binding, not per name -- a `let` shadowing a non-cell parameter of the same
/// name may itself be a cell.
#[derive(Clone, Copy)]
struct ScopeBinding {
    local: LocalId,
    cell: bool,
}

impl<'a, 'p> FnLower<'a, 'p> {
    fn new(ctx: &'a ProgramCtx<'p>, module: Vec<String>, self_type: Option<String>) -> Self {
        FnLower {
            b: BodyBuilder::new(),
            ctx,
            module,
            self_type,
            abort_error_prop: false,
            scopes: vec![HashMap::new()],
            loops: Vec::new(),
            cells: std::collections::HashSet::new(),
        }
    }

    /// Whether the binding `name` currently resolves to is a heap-promoted
    /// shared cell. A name with no local binding may still be a
    /// captured-and-mutated module global, which is in the candidate set but is
    /// accessed through global storage rather than a cell local.
    pub(crate) fn is_cell(&self, name: &str) -> bool {
        match self.lookup_binding(name) {
            Some(b) => b.cell,
            None => self.cells.contains(name),
        }
    }

    // ----- scopes -----

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    pub(crate) fn bind(&mut self, name: &str, local: LocalId) {
        self.bind_as(name, local, false);
    }

    /// Bind `name` to `local` in the innermost scope, recording whether this
    /// binding is a shared cell (`local` then holds the one-element cell array).
    pub(crate) fn bind_as(&mut self, name: &str, local: LocalId, cell: bool) {
        self.scopes
            .last_mut()
            .expect("a scope is always open")
            .insert(name.to_string(), ScopeBinding { local, cell });
    }

    pub(crate) fn lookup(&self, name: &str) -> Option<LocalId> {
        self.lookup_binding(name).map(|b| b.local)
    }

    fn lookup_binding(&self, name: &str) -> Option<ScopeBinding> {
        self.scopes.iter().rev().find_map(|s| s.get(name).copied())
    }

    /// Create a freshly named local, copy `op` into it, and bind `name` to it.
    /// Used for `let`, `for`, and pattern bindings so a bound name gets its own
    /// slot (writes to the binding never alias the source value).
    ///
    /// A captured-and-mutated binding (`is_cell`) is heap-promoted to a
    /// one-element cell array shared with the closures that capture it, with the
    /// value stored at element 0. Routing every binder through
    /// here applies the wrap uniformly: a `for` variable or a destructured field
    /// that a closure captures and mutates is promoted exactly like a `let`,
    /// instead of being stored as a scalar that read/write/capture sites then
    /// wrongly index as an array.
    pub(crate) fn bind_value(&mut self, name: &str, op: crate::value::Operand) {
        // Cell-ness is decided here, per binder, from the body-wide candidate
        // set: this fresh binding is the one closures capture, regardless of
        // whether an outer binding (e.g. a non-cell parameter) shares its name.
        let cell = self.cells.contains(name);
        let local = if cell {
            let cell_arr = self.b.emit(crate::value::Rvalue::Array(vec![op]));
            self.b.make_local(cell_arr)
        } else {
            let local = self.b.fresh_local(Some(name.to_string()));
            self.b.push(crate::cfg::MirStmt::Assign(
                local,
                crate::value::Rvalue::Use(op),
            ));
            local
        };
        self.bind_as(name, local, cell);
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
        // Candidate names for heap promotion to shared cells. Each binder
        // decides for its own binding: a parameter has no `let` to wrap, so it
        // binds plainly (via `bind`, never a cell) -- but a `let` that shadows a
        // parameter's name is a different binding and is still promoted.
        self.cells = crate::analysis::cell_promotions(body);
        let copies = self.entry_param_copies(params, body);
        let param_locals = self.bind_params(params, &copies);
        self.lower_body_stmts(&body.stmts);
        self.close_void();
        param_locals
    }

    /// Which parameters are received by deep copy (a private value the callee
    /// owns) rather than by shared reference. The copy is applied on entry, so it
    /// is uniform across free functions, methods, and every dispatch: a callee
    /// mutating a value it received by copy never writes through to the caller.
    ///
    /// - `self` is a reference by default (a shared borrow, or `ref(mut(Self))`
    ///   when it mutates itself), never copied -- including when a primitive-type
    ///   method (`fun infer[].m(self, ..)`) carries a synthesized receiver-type
    ///   annotation on `self`. The one exception is an explicit `self: Self` (or
    ///   the concrete type name) on a user record/sum method, requesting an owned
    ///   deep copy.
    /// - An annotated non-`self` parameter follows its annotation: a non-reference
    ///   heap aggregate or `infer` copies; a `ref`/`ref(mut)` borrows.
    /// - An unannotated non-`self` parameter is inferred: the body mutating it
    ///   through its reference makes it a private `mut` copy, otherwise a shared
    ///   `ref` borrow.
    fn entry_param_copies(&self, params: &[Param], body: &Block) -> Vec<bool> {
        params
            .iter()
            .map(|p| {
                if p.name == "self" {
                    return matches!(&p.ty, Some(prepoly_parser::ast::TypeExpr::Named(n, _))
                        if self.self_type.is_some()
                            && (n == "Self" || Some(n.as_str()) == self.self_type.as_deref()));
                }
                match &p.ty {
                    Some(t) => self.ctx.type_needs_copy(&self.module, t),
                    None => prepoly_hir::mutates_value(
                        self.ctx.program,
                        &self.module,
                        body,
                        &p.name,
                        &self.ctx.mutation,
                    ),
                }
            })
            .collect()
    }

    /// Bind each parameter to a fresh named local, returning the formals in order.
    /// A parameter received by copy is bound to a private `__deep_copy` of the
    /// formal, so the body works on its own value; the formal still receives the
    /// caller's argument for monomorphization.
    fn bind_params(&mut self, params: &[Param], copies: &[bool]) -> Vec<LocalId> {
        params
            .iter()
            .zip(copies)
            .map(|(p, &copy)| {
                // A parameter with a resolvable annotation is bound to a typed local
                // so monomorphization uses its declared type, not each call's argument
                // type. A nullable parameter thus stays nullable when a value or an
                // omitted-null argument is passed; the instance's parameter types
                // (set in monomorphization) drive the caller's argument coercion.
                let formal = match p.ty.as_ref().and_then(stmt::resolve_simple_type) {
                    Some(t) => self.b.fresh_local_typed(Some(p.name.clone()), t),
                    None => self.b.fresh_local(Some(p.name.clone())),
                };
                if copy {
                    let copied = self.b.emit(crate::value::Rvalue::Call(
                        crate::value::Callee::Builtin("__deep_copy".into()),
                        vec![crate::value::Operand::Local(formal)],
                    ));
                    let local = self.b.make_local(copied);
                    self.bind(&p.name, local);
                } else {
                    self.bind(&p.name, formal);
                }
                formal
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

/// Collect the global names a top-level `let` pattern binds, mirroring the
/// binding forms `store_global_pattern` writes (a bare name, or an array
/// pattern destructured element-wise).
fn collect_global_names(
    pat: &prepoly_parser::ast::Pattern,
    out: &mut std::collections::HashSet<String>,
) {
    use prepoly_parser::ast::Pattern;
    match pat {
        Pattern::Binding(name, _) => {
            out.insert(name.clone());
        }
        Pattern::Array(pats, _) => {
            for p in pats {
                collect_global_names(p, out);
            }
        }
        Pattern::Record(..) | Pattern::Wildcard(_) | Pattern::Literal(..) => {}
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
    let no_types = HashMap::new();
    let no_views = std::collections::HashSet::new();
    let no_sum_views = HashMap::new();
    let no_call_locations = HashMap::new();
    let no_lift_errs = std::collections::HashSet::new();
    let no_fields_loops = HashMap::new();
    let no_type_names = HashMap::new();
    let no_typeof_types = HashMap::new();
    let no_null_props = std::collections::HashSet::new();
    let ctx = ProgramCtx::new(
        program,
        &no_types,
        &no_views,
        &no_sum_views,
        &no_call_locations,
        &no_lift_errs,
        &no_fields_loops,
        &no_type_names,
        &no_typeof_types,
        &no_null_props,
    );
    let body = lower_one(
        &ctx,
        module.to_vec(),
        self_type.map(str::to_string),
        params,
        body,
        false,
    );
    let mut closures = ctx.closures.into_inner();
    closures.sort_by_key(|c| c.id.0);
    (body, closures)
}

/// The full parameter count when the last parameter is the implicit
/// caller-location (annotated with the prelude's `Location` record).
fn params_want_location(params: &[prepoly_hir::ParamInfo]) -> Option<usize> {
    let last = params.last()?;
    matches!(&last.resolved_ty, Some(Type::Record(n)) if n.is_name("Location"))
        .then_some(params.len())
}

/// Lower one callable into a [`MirBody`] using a shared context.
/// `abort_error_prop` is true only for the entry `main` (see
/// [`FnLower::abort_error_prop`]).
fn lower_one(
    ctx: &ProgramCtx,
    module: Vec<String>,
    self_type: Option<String>,
    params: &[Param],
    body: &Block,
    abort_error_prop: bool,
) -> MirBody {
    let mut fl = FnLower::new(ctx, module, self_type);
    fl.abort_error_prop = abort_error_prop;
    let param_locals = fl.lower_callable(params, body);
    fl.b.finish(param_locals, BlockId(0))
}

/// Lower a whole program to MIR: every function, method, init body, and the
/// closures they spawn. Item enumeration mirrors `codegen::gen_functions` /
/// `gen_inits`, including the `Name@module` storage-symbol keys.
pub fn lower_program(program: &Program) -> MirProgram {
    lower_program_with_types(
        program,
        &HashMap::new(),
        &std::collections::HashSet::new(),
        &HashMap::new(),
        &HashMap::new(),
        &std::collections::HashSet::new(),
        &HashMap::new(),
        &HashMap::new(),
        &HashMap::new(),
        &std::collections::HashSet::new(),
    )
}

/// Lower a whole program with the checker's outputs available: resolved
/// expression types, so call results that construct an aggregate are seeded
/// with their instance type (see [`ProgramCtx::expr_types`]); and the spans of
/// view-convertible anonymous arguments (see [`ProgramCtx::view_args`]). The
/// real execution paths pass the checker's data; [`lower_program`] is the
/// inputs-free form used by tests and by runtime re-lowering, where the back
/// end re-derives types on its own and keeps full argument values.
#[allow(clippy::too_many_arguments)] // mirrors the checker's channel outputs
pub fn lower_program_with_types(
    program: &Program,
    expr_types: &HashMap<Span, Type>,
    view_args: &std::collections::HashSet<Span>,
    sum_views: &HashMap<Span, Type>,
    call_locations: &HashMap<Span, (String, u32, u32)>,
    lift_errs: &std::collections::HashSet<Span>,
    fields_loops: &HashMap<Span, Vec<String>>,
    type_names: &HashMap<Span, String>,
    typeof_types: &HashMap<Span, Type>,
    null_props: &std::collections::HashSet<Span>,
) -> MirProgram {
    let ctx = ProgramCtx::new(
        program,
        expr_types,
        view_args,
        sum_views,
        call_locations,
        lift_errs,
        fields_loops,
        type_names,
        typeof_types,
        null_props,
    );
    let mut out = MirProgram::default();

    let mut fn_names: Vec<&String> = program.functions.keys().collect();
    fn_names.sort();
    for name in fn_names {
        let info = &program.functions[name];
        // The entry `main` (the root module's bare `main` symbol) is the
        // program: a failed `expr!` there aborts with the error instead of
        // propagating (there is no caller to receive a Result), so `!` alone
        // does not make `main` fallible -- only an explicit `error(...)` does.
        let entry_main = info.symbol == "main";
        let body = lower_one(
            &ctx,
            info.module.clone(),
            None,
            &info.decl.params,
            &info.decl.body,
            entry_main,
        );
        let fallible = if entry_main && info.decl.ret.is_none() {
            crate::analysis::constructs_error_block(&info.decl.body)
        } else {
            function_fallible(info.decl.ret.as_ref(), &info.decl.body, null_props)
        };
        out.functions.push(MirFunction {
            name: info.decl.name.clone(),
            symbol: info.symbol.clone(),
            module: info.module.clone(),
            fallible,
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
                    // A reflective `-> infer!` template is never lowered (generic
                    // over the key); the driver injected concrete specializations.
                    if prepoly_hir::keyed_return(method.decl.ret.as_ref()) {
                        continue;
                    }
                    if let Some(body) = &method.decl.body {
                        out.methods.push(lower_method(
                            &ctx,
                            info,
                            None,
                            &method.decl.name,
                            &method.decl.params,
                            method.decl.ret.as_ref(),
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
                        if prepoly_hir::keyed_return(method.decl.ret.as_ref()) {
                            continue;
                        }
                        if let Some(body) = &method.decl.body {
                            out.methods.push(lower_method(
                                &ctx,
                                info,
                                Some(v.name.clone()),
                                &method.decl.name,
                                &method.decl.params,
                                method.decl.ret.as_ref(),
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
    // Constant array literals whose value is only ever read become
    // once-initialized globals (see [`crate::promote`]); running on the shared
    // MIR keeps the JIT and the REPL interpreter behaviorally identical.
    crate::promote::promote_const_array_literals(&mut out);
    out
}

#[allow(clippy::too_many_arguments)]
fn lower_method(
    ctx: &ProgramCtx,
    info: &prepoly_hir::TypeInfo,
    variant: Option<String>,
    method: &str,
    params: &[Param],
    ret: Option<&prepoly_parser::ast::TypeExpr>,
    body: &Block,
    self_type: Option<String>,
) -> MirMethod {
    let mir_body = lower_one(
        ctx,
        info.module.clone(),
        self_type.clone(),
        params,
        body,
        false,
    );
    MirMethod {
        type_name: info.name.clone(),
        type_symbol: info.symbol.clone(),
        variant,
        method: method.to_string(),
        self_type,
        module: info.module.clone(),
        // A method's fallibility follows exactly the same rule as a free
        // function's: a declared `-> T!` wraps plain returns in `Result.Ok` even
        // when the body never builds an error itself. Judging a method by its body
        // alone left `fun C.k(self) -> string[]!` returning the bare array where
        // the caller's `!` expected a `Result` -- the value read back as `never`
        // (or, for a scalar payload, as `null`).
        fallible: function_fallible(ret, body, ctx.null_props),
        body: mir_body,
    }
}

/// A free function auto-wraps plain returns in `Result.Ok` (and propagates
/// errors) when its return type is `T!` (explicitly fallible), or when it has no
/// return annotation and its body uses `error(...)`/`expr!` (inferred fallible).
/// An explicit non-`T!` return type means the body builds its own value, so bare
/// returns are not wrapped. An `expr!` on a nullable operand (a `null_props`
/// span) does not count: its failure arm returns `null`, making the return
/// type nullable rather than a `Result`.
fn function_fallible(
    ret: Option<&prepoly_parser::ast::TypeExpr>,
    body: &Block,
    null_props: &std::collections::HashSet<Span>,
) -> bool {
    match ret {
        Some(prepoly_parser::ast::TypeExpr::Fallible(..)) => true,
        Some(_) => false,
        None => crate::analysis::fallible_block_except(body, null_props),
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
    // Top-level statements are an entry point: a failed `expr!` aborts (see
    // `FnLower::abort_error_prop`) -- an init body's return type is void, so
    // there is no Result to propagate into.
    fl.abort_error_prop = true;
    for s in stmts {
        if fl.b.terminated() {
            break;
        }
        match s {
            Stmt::Let { pat, ty, value, .. } => {
                // A module-level `let` needs an initializer (the checker
                // rejects the uninitialized form at top level); skip defensively.
                let Some(value) = value else { continue };
                let v = fl.lower_expr(value);
                // A resolvable annotation fixes the global's type exactly as it
                // fixes a function-local slot: routing the value through a typed
                // local makes the store coerce (nullable wrap, numeric flow) and
                // monomorphization record the annotated type -- otherwise
                // `let g: int32? = 5` records a bare int32 global whose reads
                // then mismatch the nullable representation the checker assumed.
                let v = match ty
                    .as_ref()
                    .and_then(crate::lower::stmt::resolve_simple_type)
                {
                    Some(t) => {
                        use crate::value::Rvalue;
                        let local = fl.b.fresh_local_typed(None, t);
                        fl.b.push(crate::cfg::MirStmt::Assign(local, Rvalue::Use(v)));
                        crate::value::Operand::Local(local)
                    }
                    None => v,
                };
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
                let key = self.ctx.global_symbol(&self.module, name);
                self.b.push(MirStmt::SetGlobal(key, v));
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
