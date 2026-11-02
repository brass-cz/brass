//! HIR (AST-bearing) -> MIR lowering: building the type-independent CFG.
//!
//! [`lower_program_with_types`] walks a `brass_hir::Program` (free functions,
//! record/sum methods, module inits, nested closures) and produces a
//! [`MirProgram`]; the lazy pipeline lowers the same items on demand through
//! [`SubsetLowering`]. Each callable body becomes a [`MirBody`] via a
//! [`FnLower`], which keeps a [`BodyBuilder`] cursor plus the lexical scope and
//! loop-target stacks needed to place branches.
//!
//! The lowering performs three jobs and infers no types:
//!  - control flow (`if`/`while`/`for`/`match`/`if let`/`&&`/`||`/`expr!`) is
//!    decomposed into basic blocks (see [`stmt`]);
//!  - expressions are flattened to three-address form, every value named by a
//!    local (see [`expr`]);
//!  - calls, places, and globals are resolved structurally, by name, scope and
//!    declaration.
//!
//! Where a body's shape depends on a type decision (a seeded literal, a view
//! argument, a sum-subtype rebuild, a nullable `!`), the lowering reads the
//! checker's decision from its span-keyed channels ([`CheckerChannels`]).

mod closure;
mod expr;
mod order;
mod pattern;
mod stmt;

pub use stmt::resolve_simple_type;

use fxhash::FxHashMap as HashMap;
use std::cell::{Cell, RefCell};

use brass_hir::{Program, Type, TypeKind};
use brass_parser::Span;
use brass_parser::ast::{AssignOp, BinOp, Block, Param};

use crate::builder::BodyBuilder;
use crate::cfg::MirBody;
use crate::ids::{BlockId, ClosureId, LocalId};
use crate::program::{MirClosure, MirFunction, MirInit, MirMethod, MirProgram};

/// The program-wide tables lowering derives from the HIR alone (no checker
/// channels): computed once and shared across every `ProgramCtx`. The lazy
/// pipeline builds a fresh context per lowered body -- and rebuilds the whole
/// lowering when the channel state moves -- so recomputing these each time
/// would re-run the whole-program mutation analysis per body.
pub struct LowerTables {
    /// The program's mutation facts (self-mutating methods, write-through
    /// positions): the entry-copy decision for an unannotated parameter needs
    /// them to count handing the parameter to a mutating position (a
    /// `m.set(..)` receiver) as a mutation, exactly like the const checker.
    mutation: brass_hir::MutationInfo,
    /// Names each module's init binds as module-level globals (top-level
    /// `let`s), used to key global storage per defining module.
    module_globals: HashMap<Vec<String>, fxhash::FxHashSet<String>>,
    /// Defining module of each standard-library global (the implicit prelude:
    /// `INT64_MAX` etc. are visible everywhere without an import). First
    /// definition in sorted module order wins, deterministically.
    prelude_globals: HashMap<String, Vec<String>>,
    /// The binding spans of the program's generalized closure bindings
    /// (`brass_hir::generalized_closure_bindings`, the checker's rule): each
    /// use of such a binding builds its own closure value.
    generalized: fxhash::FxHashSet<Span>,
    /// The module-level generalized closure bindings, by global storage
    /// symbol: their defining module, parameters and body. They have no
    /// storage; every use, in any body, rebuilds the closure from these.
    global_templates: HashMap<String, GlobalTemplate>,
}

impl LowerTables {
    /// Derive the tables from `program`'s HIR (this runs the whole-program
    /// mutation analysis).
    pub fn new(program: &Program) -> Self {
        let mut module_globals: HashMap<Vec<String>, fxhash::FxHashSet<String>> =
            HashMap::default();
        for init in &program.inits {
            let names = module_globals.entry(init.path.clone()).or_default();
            for s in &init.stmts {
                if let brass_parser::ast::Stmt::Let { pat, .. } = s {
                    collect_global_names(pat, names);
                }
            }
        }
        let mut prelude_globals: HashMap<String, Vec<String>> = HashMap::default();
        let mut core_paths: Vec<&Vec<String>> = module_globals
            .keys()
            .filter(|p| p.first().is_some_and(|seg| seg == "core"))
            .collect();
        core_paths.sort();
        for path in core_paths {
            for name in &module_globals[path] {
                prelude_globals
                    .entry(name.clone())
                    .or_insert_with(|| path.clone());
            }
        }
        let generalized = brass_hir::generalized_closure_bindings(program);
        let mut global_templates = HashMap::default();
        for init in &program.inits {
            for s in &init.stmts {
                if let brass_parser::ast::Stmt::Let {
                    pat: brass_parser::ast::Pattern::Binding(name, None, span),
                    value: Some(brass_parser::ast::Expr::Closure(params, body, _)),
                    ..
                } = s
                    && generalized.contains(span)
                {
                    global_templates.insert(
                        brass_hir::qualify(name, &init.path),
                        (
                            init.path.clone(),
                            params.clone(),
                            std::rc::Rc::new((**body).clone()),
                        ),
                    );
                }
            }
        }
        LowerTables {
            mutation: brass_hir::MutationInfo::analyze(program),
            module_globals,
            prelude_globals,
            generalized,
            global_templates,
        }
    }
}

/// A module-level generalized closure binding: its defining module, its
/// parameters and its body.
type GlobalTemplate = (
    Vec<String>,
    Vec<Param>,
    std::rc::Rc<brass_parser::ast::Expr>,
);

/// Shared, immutable-by-reference state for one lowering run. Interior
/// mutability holds the growing closure table and the global closure-id counter,
/// so deeply nested closure lowering can borrow this context immutably and still
/// register the closures it discovers without a borrow conflict.
pub(crate) struct ProgramCtx<'p> {
    selected_bodies: Option<&'p fxhash::FxHashSet<Span>>,
    program: &'p Program,
    /// The shared program-wide tables (see [`LowerTables`]).
    tables: &'p LowerTables,
    // The checker's channels, borrowed from [`CheckerChannels`]; each field
    // is documented there under the same name.
    expr_types: &'p HashMap<Span, Type>,
    instance_seeds: &'p brass_hir::InstanceChannel<Type>,
    receiver_types: &'p HashMap<Span, Type>,
    receiver_owners: &'p HashMap<Span, Vec<Type>>,
    view_args: &'p fxhash::FxHashSet<Span>,
    numeric_calls: &'p brass_hir::NumericCalls,
    field_calls: &'p HashMap<Span, Option<Vec<Type>>>,
    sum_views: &'p HashMap<Span, Type>,
    call_locations: &'p HashMap<Span, (String, u32, u32)>,
    lift_errs: &'p fxhash::FxHashSet<Span>,
    fields_loops: &'p HashMap<Span, Vec<String>>,
    instance_fields: &'p brass_hir::InstanceChannel<Vec<String>>,
    type_names: &'p HashMap<Span, String>,
    typeof_types: &'p HashMap<Span, Type>,
    null_props: &'p fxhash::FxHashSet<Span>,
    type_tests: &'p HashMap<Span, Type>,
    keyed_dispatch: &'p HashMap<Span, String>,
    instance_dispatch: &'p brass_hir::InstanceChannel<String>,
    closures: RefCell<Vec<MirClosure>>,
    next_closure: Cell<u32>,
}

impl<'p> ProgramCtx<'p> {
    fn new(program: &'p Program, tables: &'p LowerTables, channels: &CheckerChannels<'p>) -> Self {
        ProgramCtx {
            selected_bodies: channels.selected_bodies,
            program,
            tables,
            expr_types: channels.expr_types,
            instance_seeds: channels.instance_seeds,
            receiver_types: channels.receiver_types,
            receiver_owners: channels.receiver_owners,
            view_args: channels.view_args,
            numeric_calls: channels.numeric_calls,
            field_calls: channels.field_calls,
            sum_views: channels.sum_views,
            call_locations: channels.call_locations,
            lift_errs: channels.lift_errs,
            fields_loops: channels.fields_loops,
            instance_fields: channels.instance_fields,
            type_names: channels.type_names,
            typeof_types: channels.typeof_types,
            null_props: channels.null_props,
            type_tests: channels.type_tests,
            keyed_dispatch: channels.keyed_dispatch,
            instance_dispatch: channels.instance_dispatch,
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

    /// The inner value at a call the checker resolved as nullable. Method
    /// lowering uses this evidence to distinguish the compiler-owned nullable
    /// `context` from the ordinary `Result.context` declaration with the same
    /// name.
    fn nullable_receiver_inner(&self, span: Span) -> Option<Type> {
        let receiver = self.receiver_types.get(&span)?;
        match brass_hir::peel_modes(receiver) {
            Type::Nullable(inner) => Some((**inner).clone()),
            _ => None,
        }
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
        if let Some(alias) = self.program.resolve_type_alias(module, name) {
            return brass_hir::is_fully_known(&alias.ty).then(|| alias.ty.clone());
        }
        let info = if let Some(id) = brass_hir::generated_type_id(name) {
            self.program.type_by_id(id)?
        } else {
            self.program.resolve_type(module, name)?
        };
        if !info.slots.is_empty() {
            return None;
        }
        let concrete_fields = |fields: &[brass_hir::FieldInfo]| {
            fields.iter().all(|f| {
                f.resolved_ty
                    .as_ref()
                    .is_some_and(brass_hir::is_fully_known)
            })
        };
        let concrete = match &info.kind {
            TypeKind::Record { fields, .. } => concrete_fields(fields),
            TypeKind::Sum { variants } => variants.iter().all(|v| concrete_fields(&v.fields)),
        };
        concrete.then(|| info.type_ref())
    }

    /// The source position of the call (or `!`, or construction) at `span`,
    /// or a placeholder when lowering without a checked program (unit
    /// tests). A span inside a compiler-made copy of source
    /// code -- an unrolled `fields` loop, a reflective specialization -- is
    /// located at the position it was copied from.
    fn call_location(&self, span: Span) -> (String, u32, u32) {
        self.call_locations
            .get(&span)
            .or_else(|| self.call_locations.get(&span.source_span()))
            .cloned()
            .unwrap_or_else(|| ("<unknown>".to_string(), 0, 0))
    }

    fn free_call_defaults(&self, module: &[String], name: &str) -> Option<Vec<CallDefault>> {
        let info = self.program.resolve_function(module, name)?;
        Some(call_defaults(self.program, &info.signature.params))
    }

    /// Defaults for the static method selected by `qualifier` in `module`.
    /// Sum methods are duplicated on their variants, whose declarations share
    /// the signature checked for this call.
    fn static_call_defaults(
        &self,
        module: &[String],
        qualifier: &str,
        method: &str,
    ) -> Option<Vec<CallDefault>> {
        let info = self
            .program
            .resolve_type_or_alias(module, qualifier)
            .or_else(|| {
                let (sum, _) = qualifier.split_once('.')?;
                self.program.resolve_type_or_alias(module, sum)
            })?;
        let signature = match &info.kind {
            TypeKind::Record { methods, .. } => &methods.get(method)?.signature,
            TypeKind::Sum { variants } => {
                &variants
                    .iter()
                    .find_map(|v| v.methods.get(method))?
                    .signature
            }
        };
        Some(call_defaults(self.program, &signature.params))
    }

    /// Defaults for the instance method resolved at this call site. The
    /// receiver's checker type is keyed by its source span, so an unrelated
    /// same-named method elsewhere cannot suppress completion.
    fn instance_call_defaults(&self, call: Span, method: &str) -> Option<Vec<CallDefault>> {
        self.owner_call_defaults(self.receiver_types.get(&call)?, method)
    }

    /// Defaults for instance method `method` declared on `owner` (a nominal
    /// or a primitive receiver type).
    fn owner_call_defaults(&self, owner: &Type, method: &str) -> Option<Vec<CallDefault>> {
        let receiver_ty = brass_hir::peel_modes(owner);
        let params = match receiver_ty {
            Type::Record(n) => {
                let info = self.program.type_by_id(n.id)?;
                let TypeKind::Record { methods, .. } = &info.kind else {
                    return None;
                };
                &methods.get(method)?.signature.params
            }
            Type::Sum(n) => {
                let info = self.program.type_by_id(n.id)?;
                let TypeKind::Sum { variants } = &info.kind else {
                    return None;
                };
                &variants
                    .iter()
                    .find_map(|v| v.methods.get(method))?
                    .signature
                    .params
            }
            ty => {
                let class = ty.primitive_class()?;
                let symbol = self
                    .program
                    .primitive_methods
                    .get(&(class.to_string(), method.to_string()))?;
                &self.program.functions.get(symbol)?.signature.params
            }
        };
        Some(call_defaults(self.program, params))
    }

    /// The owners of the method call at `call`, each with its signature's
    /// omitted-argument defaults, when the call's instances resolve the
    /// method on different owners (in the checker's order, most specific
    /// first). `None` for a call with one owner, and for one reaching a
    /// nullable receiver (the compiler-owned `context` hook), which has no
    /// declared signature to complete from.
    fn owner_defaults(
        &self,
        call: Span,
        method: &str,
    ) -> Option<Vec<(Type, Option<Vec<CallDefault>>)>> {
        let owners = self.receiver_owners.get(&call)?;
        if owners
            .iter()
            .any(|owner| matches!(owner, Type::Nullable(_)))
        {
            return None;
        }
        Some(
            owners
                .iter()
                .map(|owner| (owner.clone(), self.owner_call_defaults(owner, method)))
                .collect(),
        )
    }

    /// Whether `name` resolves to a module-level global visible from `module`
    /// (its own, an import origin's, or a stdlib prelude global) -- the same
    /// resolution [`Self::global_symbol`] keys storage by.
    fn is_global_name(&self, module: &[String], name: &str) -> bool {
        let defines = |m: &[String], n: &str| {
            self.tables
                .module_globals
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
            || self.tables.prelude_globals.contains_key(name)
    }

    /// The storage key of module-level global `name` as referenced from
    /// `module`. Globals are keyed per *defining* module (`name@a/b`, like
    /// function storage symbols), so two modules' same-named top-level `let`s
    /// never share a slot. A name the referencing module does not define itself
    /// resolves through its import origin, then through the stdlib prelude
    /// (`INT64_MAX` and friends are visible without an import); an unresolved
    /// name keys under the referencing module (the checker rejects genuinely
    /// unknown names).
    fn global_symbol(&self, module: &[String], name: &str) -> String {
        let defines = |m: &[String], n: &str| {
            self.tables
                .module_globals
                .get(m)
                .is_some_and(|names| names.contains(n))
        };
        if defines(module, name) {
            return brass_hir::qualify(name, module);
        }
        if let Some(origin) = self
            .program
            .import_origins
            .get(module)
            .and_then(|o| o.get(name))
            && defines(origin, name)
        {
            return brass_hir::qualify(name, origin);
        }
        if let Some((declared, origin)) = self.aliased_global(module, name)
            && defines(&origin, &declared)
        {
            return brass_hir::qualify(&declared, &origin);
        }
        if let Some(owner) = self.tables.prelude_globals.get(name) {
            return brass_hir::qualify(name, owner);
        }
        brass_hir::qualify(name, module)
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

    /// The type named `sym` as visible from `module`. A direct storage symbol
    /// remains authoritative; a bare source name follows the program's module
    /// and import resolution instead of selecting an unrelated definition.
    pub(crate) fn type_info(&self, module: &[String], sym: &str) -> Option<&brass_hir::TypeInfo> {
        self.program
            .types
            .get(sym)
            .or_else(|| self.program.resolve_type_or_alias(module, sym))
    }

    /// The type with nominal id `id`, if any.
    pub(crate) fn type_info_by_id(&self, id: i32) -> Option<&brass_hir::TypeInfo> {
        self.program.type_by_id(id)
    }

    /// Allocate the next globally-unique closure id.
    fn fresh_closure_id(&self) -> ClosureId {
        let id = self.next_closure.get();
        self.next_closure.set(id + 1);
        ClosureId(id)
    }

    /// Whether `name` denotes a type rather than a value: a user type, `Self`,
    /// the builtin `File`, or a primitive type word. Mirrors the checker's
    /// `is_type_word` so `Type.method(...)` routes as a static call. A dotted
    /// marker (`alias.T`) and a renamed import (`import m.{ T as name }`)
    /// appear in no table under `name` and resolve through the module-aware
    /// lookup instead.
    fn is_type_word_in(&self, module: &[String], name: &str) -> bool {
        // Module-aware for every form of the name: bare (which alone misses a
        // type whose symbol went module-qualified because another module declares
        // the same name -- e.g. an alias of it), dotted markers, renames, and
        // `type Alias = <nominal>` bindings (a static call through an alias
        // dispatches on the alias's target).
        // Locals shadowing a type name are already excluded by the caller.
        self.program.types.contains_key(name)
            || self.program.resolve_type_or_alias(module, name).is_some()
            || name == "Self"
            || brass_hir::IntKind::from_name(name).is_some()
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

    /// Whether `ty.from(v)` (as seen from `module`) is the builtin structural
    /// conversion, which lowers to a record built from `v`'s fields: `ty` is a
    /// record declaring no static `from` of its own (see
    /// [`brass_hir::TypeInfo::has_structural_from`]).
    fn has_structural_from(&self, module: &[String], ty: &str) -> bool {
        self.program
            .resolve_type_or_alias(module, ty)
            .is_some_and(brass_hir::TypeInfo::has_structural_from)
    }

    /// The dispatch key for a static call `ty.method(...)`: a user type's unique
    /// symbol (an alias qualifier dispatches on its target type), or the
    /// primitive type word unchanged.
    fn static_qualifier(&self, module: &[String], ty: &str) -> String {
        self.program
            .resolve_type_or_alias(module, ty)
            .map(|t| t.symbol.clone())
            .unwrap_or_else(|| ty.to_string())
    }

    /// Resolve a bare free-function name to its storage symbol as seen from
    /// `module` (own/unique, this module's qualified, or imported), using the
    /// program's central resolver.
    fn resolve_fn_symbol(&self, module: &[String], name: &str) -> Option<String> {
        self.program.resolve_fn_symbol(module, name)
    }

    /// The parameter count of free function `name` as seen from `module`, used to
    /// eta-expand a bare function-name value into a forwarding closure. `None` if
    /// `name` is not a known free function.
    fn function_arity(&self, module: &[String], name: &str) -> Option<usize> {
        self.program
            .resolve_function(module, name)
            .map(|info| info.signature.params.len())
    }

    /// Whether an annotated parameter type is passed by deep copy: a non-reference
    /// heap aggregate (array/slice, tuple, anonymous structure, named record/sum,
    /// nullable/fallible of one, or `infer`). A `ref(...)`/`ref(mut(..))`
    /// parameter borrows. The copy is applied on entry to the callee (see
    /// [`FnLower::entry_param_copies`]). Delegates to the shared predicate in
    /// `brass_hir` so the runtime copy decision and the const checker's
    /// write-through analysis never disagree.
    fn type_needs_copy(&self, module: &[String], t: &brass_parser::ast::TypeExpr) -> bool {
        brass_hir::annotated_type_passes_by_copy(self.program, module, t)
    }
}

/// One active loop: the `continue`/`break` jump targets, plus the `for`-loop
/// element write-back (if any) that every edge leaving the iteration must emit.
pub(crate) struct LoopFrame {
    pub(crate) cont: BlockId,
    pub(crate) brk: BlockId,
    /// Present when the body reassigns the `for` variable: its current value
    /// is stored back into the iterated element on every edge that ends the
    /// iteration -- the fall-through tail, `continue`, `break`, `return`, and
    /// a failed `!` returning from the callable.
    pub(crate) writeback: Option<LoopWriteBack>,
}

/// A `for` loop's pending element write-back: the loop variable's binding is
/// stored into `arr[idx]` when an iteration ends.
#[derive(Clone, Copy)]
pub(crate) struct LoopWriteBack {
    /// The iterated array.
    pub(crate) arr: LocalId,
    /// The current element index.
    pub(crate) idx: LocalId,
    /// The loop variable's own binding. Held by slot rather than by name, so
    /// a body `let` shadowing the variable cannot redirect the write-back.
    pub(crate) var: LocalId,
    /// Whether that binding is a heap-promoted cell (its value is element 0).
    pub(crate) cell: bool,
}

/// Per-body lowering state.
pub(crate) struct FnLower<'a, 'p> {
    pub(crate) b: BodyBuilder,
    pub(crate) ctx: &'a ProgramCtx<'p>,
    pub(crate) module: Vec<String>,
    /// Shared declaration facts for this body's fixed module.
    patterns: std::cell::OnceCell<brass_hir::PatternScope<'p>>,
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
    pub(crate) cells: fxhash::FxHashSet<String>,
}

/// A name bound in a lexical scope.
#[derive(Clone)]
enum ScopeBinding {
    /// A value in a local slot, plus whether this particular binding is a
    /// heap-promoted shared cell. Cell-ness is per binding, not per name -- a
    /// `let` shadowing a non-cell parameter of the same name may itself be a
    /// cell.
    Local { local: LocalId, cell: bool },
    /// A generalized closure binding: no slot, every use builds its own
    /// closure value (see [`closure`]).
    Template(std::rc::Rc<closure::ClosureTemplate>),
}

impl<'a, 'p> FnLower<'a, 'p> {
    fn new(ctx: &'a ProgramCtx<'p>, module: Vec<String>, self_type: Option<String>) -> Self {
        FnLower {
            b: BodyBuilder::new(),
            ctx,
            patterns: std::cell::OnceCell::new(),
            module,
            self_type,
            abort_error_prop: false,
            scopes: vec![HashMap::default()],
            loops: Vec::new(),
            cells: fxhash::FxHashSet::default(),
        }
    }

    /// Whether the binding `name` currently resolves to is a heap-promoted
    /// shared cell. A name with no local binding may still be a
    /// captured-and-mutated module global, which is in the candidate set but is
    /// accessed through global storage rather than a cell local.
    pub(crate) fn is_cell(&self, name: &str) -> bool {
        match self.lookup_binding(name) {
            Some(ScopeBinding::Local { cell, .. }) => cell,
            Some(ScopeBinding::Template(_)) => false,
            None => self.cells.contains(name),
        }
    }

    // ----- scopes -----

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(HashMap::default());
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
            .insert(name.to_string(), ScopeBinding::Local { local, cell });
    }

    /// Bind `name` to a generalized closure binding's template in the
    /// innermost scope.
    fn bind_template(&mut self, name: &str, template: std::rc::Rc<closure::ClosureTemplate>) {
        self.scopes
            .last_mut()
            .expect("a scope is always open")
            .insert(name.to_string(), ScopeBinding::Template(template));
    }

    /// The local slot `name` is bound to, when it names a local value.
    pub(crate) fn lookup(&self, name: &str) -> Option<LocalId> {
        self.local_binding(name).map(|(local, _)| local)
    }

    /// The local slot `name` is bound to and whether it is a shared cell,
    /// when it names a local value.
    pub(crate) fn local_binding(&self, name: &str) -> Option<(LocalId, bool)> {
        match self.lookup_binding(name)? {
            ScopeBinding::Local { local, cell } => Some((local, cell)),
            ScopeBinding::Template(_) => None,
        }
    }

    /// The template `name` is bound to, when it names a generalized closure
    /// binding.
    fn lookup_template(&self, name: &str) -> Option<std::rc::Rc<closure::ClosureTemplate>> {
        match self.lookup_binding(name)? {
            ScopeBinding::Template(template) => Some(template),
            ScopeBinding::Local { .. } => None,
        }
    }

    /// Whether `name` is bound in a lexical scope at all (a local value or a
    /// generalized closure binding), so it shadows any global, function or
    /// type of the same name.
    pub(crate) fn is_bound(&self, name: &str) -> bool {
        self.lookup_binding(name).is_some()
    }

    fn lookup_binding(&self, name: &str) -> Option<ScopeBinding> {
        self.scopes.iter().rev().find_map(|s| s.get(name).cloned())
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
        // Candidate names for heap promotion to shared cells. Each binder,
        // including a parameter, decides for its own binding; a shadowing `let`
        // is a distinct binding and is promoted independently.
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
                    return matches!(&p.ty, Some(brass_parser::ast::TypeExpr::Named(n, _))
                        if self.self_type.is_some()
                            && (n == "Self" || Some(n.as_str()) == self.self_type.as_deref()));
                }
                match &p.ty {
                    Some(t) => self.ctx.type_needs_copy(&self.module, t),
                    None => brass_hir::mutates_value(
                        self.ctx.program,
                        &self.module,
                        params,
                        body,
                        &p.name,
                        &self.ctx.tables.mutation,
                    ),
                }
            })
            .collect()
    }

    /// Bind each parameter to a fresh named local, returning the formals in order.
    /// A parameter received by copy is bound to a private `__deep_copy` of the
    /// formal, so the body works on its own value. A captured-and-mutated
    /// parameter is then wrapped in the same shared cell as a local binding;
    /// the formal remains in `body.params` for the callable ABI.
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
                // Anonymous arguments retain their ABI slot but introduce no local name.
                if p.name == "_" {
                    return formal;
                }
                let value = if copy {
                    self.b.emit(crate::value::Rvalue::Call(
                        crate::value::Callee::Builtin("__deep_copy".into()),
                        vec![crate::value::Operand::Local(formal)],
                    ))
                } else {
                    crate::value::Operand::Local(formal)
                };
                if self.cells.contains(&p.name) {
                    let cell = self.b.emit(crate::value::Rvalue::Array(vec![value]));
                    let local = self.b.make_local(cell);
                    self.bind_as(&p.name, local, true);
                } else if copy {
                    let local = self.b.make_local(value);
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

/// Collect the global names a top-level `let` pattern binds: every name the
/// pattern binds, exactly as the local form would (see `store_global_pattern`).
/// A top-level pattern is irrefutable, so no name in it is a variant test.
fn collect_global_names(pat: &brass_parser::ast::Pattern, out: &mut fxhash::FxHashSet<String>) {
    out.extend(pat.bound_names().into_iter().map(str::to_string));
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

/// Lower a single callable body standalone, without checker channels,
/// returning the body and any closures it spawned (for tests);
/// [`lower_program`] keeps closure ids unique across the whole program instead.
pub fn lower_body(
    program: &Program,
    module: &[String],
    self_type: Option<&str>,
    params: &[Param],
    body: &Block,
) -> (MirBody, Vec<MirClosure>) {
    let no_types = HashMap::default();
    let no_views = fxhash::FxHashSet::default();
    let no_sum_views = HashMap::default();
    let no_call_locations = HashMap::default();
    let no_lift_errs = fxhash::FxHashSet::default();
    let no_fields_loops = HashMap::default();
    let no_type_names = HashMap::default();
    let no_typeof_types = HashMap::default();
    let no_null_props = fxhash::FxHashSet::default();
    let no_type_tests = HashMap::default();
    let tables = LowerTables::new(program);
    let channels = CheckerChannels {
        selected_bodies: None,
        expr_types: &no_types,
        receiver_types: &no_types,
        receiver_owners: &HashMap::default(),
        view_args: &no_views,
        numeric_calls: &HashMap::default(),
        field_calls: &HashMap::default(),
        sum_views: &no_sum_views,
        call_locations: &no_call_locations,
        lift_errs: &no_lift_errs,
        fields_loops: &no_fields_loops,
        instance_fields: &HashMap::default(),
        type_names: &no_type_names,
        typeof_types: &no_typeof_types,
        null_props: &no_null_props,
        type_tests: &no_type_tests,
        keyed_dispatch: &HashMap::default(),
        instance_seeds: &HashMap::default(),
        instance_dispatch: &HashMap::default(),
        instance_returns: &HashMap::default(),
    };
    let ctx = ProgramCtx::new(program, &tables, &channels);
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum CallDefault {
    Required,
    Nullable,
    Location,
}

/// Classify a resolved callable's parameters for source-level omission. MIR
/// needs only the default kind and declaration order; the checker already
/// validated every explicit argument against the full parameter types.
fn call_defaults(program: &Program, params: &[brass_hir::ParamInfo]) -> Vec<CallDefault> {
    params
        .iter()
        .map(|param| {
            if matches!(&param.resolved_ty, Some(Type::Record(n)) if program.is_prelude_type(n.id, "Location")) {
                CallDefault::Location
            } else if matches!(param.resolved_ty, Some(Type::Nullable(_)))
                || matches!(param.ty, Some(brass_parser::ast::TypeExpr::Nullable(..)))
            {
                CallDefault::Nullable
            } else {
                CallDefault::Required
            }
        })
        .collect()
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

/// Lower a whole program to MIR without checker channels: every function,
/// method, init body, and the closures they spawn, each item under its
/// `Name@module` storage-symbol key. For tests and other programs that never
/// ran the checker; see [`lower_program_with_types`].
pub fn lower_program(program: &Program) -> MirProgram {
    lower_program_with_types(
        program,
        &CheckerChannels {
            selected_bodies: None,
            expr_types: &HashMap::default(),
            receiver_types: &HashMap::default(),
            receiver_owners: &HashMap::default(),
            view_args: &fxhash::FxHashSet::default(),
            numeric_calls: &HashMap::default(),
            field_calls: &HashMap::default(),
            sum_views: &HashMap::default(),
            call_locations: &HashMap::default(),
            lift_errs: &fxhash::FxHashSet::default(),
            fields_loops: &HashMap::default(),
            instance_fields: &HashMap::default(),
            type_names: &HashMap::default(),
            typeof_types: &HashMap::default(),
            null_props: &fxhash::FxHashSet::default(),
            type_tests: &HashMap::default(),
            keyed_dispatch: &HashMap::default(),
            instance_seeds: &HashMap::default(),
            instance_dispatch: &HashMap::default(),
            instance_returns: &HashMap::default(),
        },
    )
}

/// The checker's span-keyed outputs borrowed as one lowering input.
///
/// Keeping these related tables in one value prevents back ends from silently
/// reordering or omitting a channel as the checker grows another output. The
/// lazy pipeline can also re-borrow its changing channel state without
/// rebuilding a positional argument list at every lowering boundary.
///
/// Every table is empty when lowering without a checked program (unit tests,
/// [`lower_program`]); the constructs that need one (a fields-loop, a
/// nullable `!`) are then unsupported, and a call-site `Location` degrades to
/// a placeholder.
pub struct CheckerChannels<'a> {
    /// Optional eligible body spans. Absence retains whole-program lowering;
    /// omitted method declarations still participate in HIR presence and dispatch.
    pub selected_bodies: Option<&'a fxhash::FxHashSet<Span>>,
    /// Checker-resolved expression types, keyed by source span, that every
    /// instance of the enclosing body agrees on. They seed the MIR locals
    /// whose type cannot be reconstructed from their operands: the result of
    /// a call or a literal that builds an aggregate, a closure's function
    /// type, a range's element type, and the numeric type a literal-branch
    /// `if`/`match` joins at.
    pub expr_types: &'a HashMap<Span, Type>,
    /// Checker-resolved method receiver types, keyed by the enclosing call
    /// span. Kept separate from result seeds so receiver evidence can never
    /// force the representation of an unrelated MIR local; lowering completes
    /// a method call's omitted trailing arguments from the receiver's method.
    pub receiver_types: &'a HashMap<Span, Type>,
    /// The method calls whose instances resolve the method on different
    /// owners, with every owner. Their omitted trailing arguments are
    /// completed per owner, behind a type test on the receiver that each
    /// instance folds (see `FnLower::lower_method_call`).
    pub receiver_owners: &'a HashMap<Span, Vec<Type>>,
    /// Spans of free-call arguments the checker verified as anonymous
    /// structural values fitting a view-ELIGIBLE callee parameter's row. Only
    /// these arguments are wrapped in [`crate::Rvalue::RecordView`]; lowering
    /// itself stays type-free -- the checker decided, this set is the channel.
    pub view_args: &'a fxhash::FxHashSet<Span>,
    /// Settled numeric call contracts, by call span and enclosing instance.
    pub numeric_calls: &'a brass_hir::NumericCalls,
    /// The `recv.name(..)` calls the checker resolved to calling the
    /// function value a record field holds: `None` when every instantiation
    /// does, else the type-test patterns of the receivers that do (the
    /// others call a method). These lower to a field load and an indirect
    /// call even when some type in the program declares a method of that
    /// name.
    pub field_calls: &'a HashMap<Span, Option<Vec<Type>>>,
    /// Value expressions the checker accepted as a declared sum subtype at a
    /// flow site, keyed by the expression's span, mapped to the PARENT sum
    /// instance the site required. Lowering rebuilds exactly these values as
    /// the parent (per-variant tag test + reconstruction); the child's variant
    /// payloads may be wider, so identity flow would misread the unboxed
    /// layout.
    pub sum_views: &'a HashMap<Span, Type>,
    /// Source positions of every call expression (diagnostic label, 1-based
    /// line/col), keyed by the call's span. A call that omits a callee's
    /// trailing `Location` parameter is completed from this map.
    pub call_locations: &'a HashMap<Span, (String, u32, u32)>,
    /// `expr!` sites whose propagated Err payload is re-raised wrapped into
    /// the prelude `Error` (gaining the site's location); the propagation arm
    /// rebuilds the value.
    pub lift_errs: &'a fxhash::FxHashSet<Span>,
    /// Field lists of `for f in fields(x)` loops, keyed by the loop statement's
    /// span: the checker resolved the record type and checked one expanded copy
    /// per field; lowering unrolls the same copies (`brass_hir::expand`).
    /// A divergent span retains a representative here; `instance_fields` owns its selections.
    pub fields_loops: &'a HashMap<Span, Vec<String>>,
    /// Checked field lists for divergent callable instances.
    pub instance_fields: &'a brass_hir::InstanceChannel<Vec<String>>,
    /// Type names the checker resolved for expressions, keyed by span: a
    /// `typeof(x)` call's static type (`typeof(x).method(..)` routes as a
    /// static call on it), and the declared record an anonymous record
    /// literal is built as (the literal lowers as a construction of that
    /// record).
    pub type_names: &'a HashMap<Span, String>,
    /// Resolved binding types of `typeof`-bearing local annotations, keyed by
    /// the annotation span; a `let x: typeof(v)` slot is seeded from this.
    pub typeof_types: &'a HashMap<Span, Type>,
    /// Spans of `expr!` operators the checker resolved with a NULLABLE
    /// operand: those lower to a presence test (`__present`/`__nonnull`) whose
    /// null arm returns `null` from the callable (or aborts at an entry
    /// point), instead of the `Result` tag-test shape.
    pub null_props: &'a fxhash::FxHashSet<Span>,
    /// Resolved type-test patterns (`if v: T`), keyed by the test's span: the
    /// annotation with `infer` holes pinned by the tested arm or left as
    /// wildcards. Embedded into the test's `Rvalue::TypeTest` so each
    /// monomorphized instance folds the branch. A missing entry (a body no
    /// instantiation ever decided) falls back to the syntactic annotation
    /// with every hole a wildcard.
    pub type_tests: &'a HashMap<Span, Type>,
    /// Keyed (`-> infer!`) call span -> the generated specialization it
    /// dispatches to; for a call whose instances key it differently,
    /// `instance_dispatch` decides per instance.
    pub keyed_dispatch: &'a HashMap<Span, String>,
    /// Per-instance aggregate seeds of the spans `expr_types` leaves unseeded
    /// because their instances disagree; carried into
    /// [`MirProgram::instance_seeds`].
    pub instance_seeds: &'a brass_hir::InstanceChannel<Type>,
    /// The per-instance dispatch of keyed calls whose instances key them
    /// differently (lowered as [`crate::Callee::Keyed`]); carried into
    /// [`MirProgram::instance_dispatch`].
    pub instance_dispatch: &'a brass_hir::InstanceChannel<String>,
    /// The checker's fully-known returns of unannotated function instances,
    /// keyed by (function symbol, argument types); carried into
    /// [`MirProgram::instance_returns`].
    pub instance_returns: &'a HashMap<(String, Vec<Type>), Type>,
}

mod region;
mod subset;
pub use region::LoweringRegion;
pub use subset::SubsetLowering;

/// A lowering context over the bundled channels, with the closure-id counter
/// seeded so ids stay unique across separately lowered batches.
fn subset_ctx<'p>(
    program: &'p Program,
    tables: &'p LowerTables,
    channels: &CheckerChannels<'p>,
    closure_base: u32,
) -> ProgramCtx<'p> {
    let ctx = ProgramCtx::new(program, tables, channels);
    ctx.next_closure.set(closure_base);
    ctx
}

/// Lower one free function into `out` (the per-function core of
/// [`lower_program_with_types`]).
fn lower_function_into(ctx: &ProgramCtx, out: &mut MirProgram, info: &brass_hir::FunInfo) {
    // The entry module's `main`, identified by the lowered program, is the
    // program: a failed `expr!` there aborts with the error instead of
    // propagating (there is no caller to receive a Result), so `!` alone
    // does not make `main` fallible -- only an explicit `error(...)` does.
    let entry_main = ctx.program.entry_function() == Some(info.symbol.as_str());
    let mut body = lower_one(
        ctx,
        info.module.clone(),
        None,
        &info.decl.params,
        &info.decl.body,
        entry_main,
    );
    body.declared_fallible = info.decl.ret.as_ref().is_some_and(annotation_is_fallible);
    body.declared_nullable_result = info
        .decl
        .ret
        .as_ref()
        .is_some_and(annotation_is_nullable_result);
    let fallible = if entry_main && info.decl.ret.is_none() {
        crate::analysis::constructs_error_block(&info.decl.body)
    } else {
        function_fallible(info.decl.ret.as_ref(), &info.decl.body, ctx.null_props)
    };
    out.functions.push(MirFunction {
        name: info.decl.name.clone(),
        symbol: info.symbol.clone(),
        module: info.module.clone(),
        fallible,
        body,
    });
}

/// Lower every record and sum method into `out` (the method block of
/// [`lower_program_with_types`]), in sorted order.
fn lower_methods_into(ctx: &ProgramCtx, out: &mut MirProgram, program: &Program) {
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
                    if ctx
                        .selected_bodies
                        .is_some_and(|spans| !spans.contains(&method.decl.span))
                    {
                        continue;
                    }
                    // A reflective `-> infer!` template is never lowered (generic
                    // over the key); the driver injected concrete specializations.
                    if brass_hir::keyed_return(method.decl.ret.as_ref()) {
                        continue;
                    }
                    if let Some(body) = &method.decl.body {
                        out.methods.push(lower_method(
                            ctx,
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
                        if ctx
                            .selected_bodies
                            .is_some_and(|spans| !spans.contains(&method.decl.span))
                        {
                            continue;
                        }
                        if brass_hir::keyed_return(method.decl.ret.as_ref()) {
                            continue;
                        }
                        if let Some(body) = &method.decl.body {
                            out.methods.push(lower_method(
                                ctx,
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
}

/// Lower a whole program against the checker's outputs (`channels`, see
/// [`CheckerChannels`]): every function, method and init body, and the
/// closures they spawn, followed by constant-array promotion. The
/// whole-program pipelines (`--eager`, the REPL interpreter) lower this way;
/// the lazy pipeline uses [`SubsetLowering`], and [`lower_program`] is the
/// channel-free form for tests.
pub fn lower_program_with_types(program: &Program, channels: &CheckerChannels<'_>) -> MirProgram {
    let tables = LowerTables::new(program);
    let ctx = ProgramCtx::new(program, &tables, channels);
    let mut out = MirProgram::default();

    let mut fn_names: Vec<&String> = program.functions.keys().collect();
    fn_names.sort();
    for name in fn_names {
        if channels
            .selected_bodies
            .is_some_and(|spans| !spans.contains(&program.functions[name].decl.span))
        {
            continue;
        }
        lower_function_into(&ctx, &mut out, &program.functions[name]);
    }

    lower_methods_into(&ctx, &mut out, program);

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
    out.instance_returns = channels.instance_returns.clone();
    out.instance_seeds = channels.instance_seeds.clone();
    out.instance_dispatch = channels.instance_dispatch.clone();
    out.instance_fields = channels.instance_fields.clone();
    out.numeric_calls = channels.numeric_calls.clone();
    // Constant array literals whose value is only ever read become
    // once-initialized globals (see the `promote` module); running on the shared
    // MIR keeps the JIT and the REPL interpreter behaviorally identical.
    crate::promote::promote_const_array_literals(&mut out);
    out
}

#[allow(clippy::too_many_arguments)]
fn lower_method(
    ctx: &ProgramCtx,
    info: &brass_hir::TypeInfo,
    variant: Option<String>,
    method: &str,
    params: &[Param],
    ret: Option<&brass_parser::ast::TypeExpr>,
    body: &Block,
    self_type: Option<String>,
) -> MirMethod {
    let mut mir_body = lower_one(
        ctx,
        info.module.clone(),
        self_type.clone(),
        params,
        body,
        false,
    );
    mir_body.declared_fallible = ret.is_some_and(annotation_is_fallible);
    mir_body.declared_nullable_result = ret.is_some_and(annotation_is_nullable_result);
    MirMethod {
        type_name: info.name.clone(),
        type_symbol: info.symbol.clone(),
        variant,
        method: method.to_string(),
        self_type,
        module: info.module.clone(),
        // A method's fallibility follows exactly the same rule as a free
        // function's: a declared `-> T!` wraps plain returns in `Result.Ok` even
        // when the body never builds an error itself, so
        // `fun C.k(self) -> string[]!` returns the `Result` its caller's `!`
        // expects rather than the bare array.
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
    ret: Option<&brass_parser::ast::TypeExpr>,
    body: &Block,
    null_props: &fxhash::FxHashSet<Span>,
) -> bool {
    match ret {
        Some(ret) if annotation_is_fallible(ret) => true,
        Some(_) => false,
        None => crate::analysis::fallible_block_except(body, null_props),
    }
}

/// Whether a return annotation explicitly contains the Result layer. The
/// nullable suffix may wrap it (`T!?`), but that outer layer must not disable
/// the ordinary fallible return and propagation lowering.
fn annotation_is_fallible(ret: &brass_parser::ast::TypeExpr) -> bool {
    match ret {
        brass_parser::ast::TypeExpr::Fallible(..) => true,
        brass_parser::ast::TypeExpr::Nullable(inner, _) => annotation_is_fallible(inner),
        _ => false,
    }
}

/// Whether a return annotation is a nullable fallible type (`T!?`): a
/// `Result` behind an outer `?` layer.
fn annotation_is_nullable_result(ret: &brass_parser::ast::TypeExpr) -> bool {
    matches!(
        ret,
        brass_parser::ast::TypeExpr::Nullable(inner, _)
            if matches!(**inner, brass_parser::ast::TypeExpr::Fallible(..))
    )
}

/// Lower a module init body: top-level `let`/`const` initialize module globals;
/// every other statement runs as ordinary code.
fn lower_init(ctx: &ProgramCtx, module: Vec<String>, stmts: &[brass_parser::ast::Stmt]) -> MirBody {
    use brass_parser::ast::{Pattern, Stmt};

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
                // A generalized closure binding has no storage: every use
                // rebuilds the closure (`LowerTables::global_templates`).
                if let Pattern::Binding(_, None, span) = pat
                    && ctx.tables.generalized.contains(span)
                {
                    continue;
                }
                let v = fl.lower_expr(value);
                // A resolvable annotation fixes the global's type exactly as it
                // fixes a function-local slot (the same `slot_type`): routing the
                // value through a typed local makes the store coerce (nullable
                // wrap, numeric flow) and monomorphization record the annotated
                // type -- otherwise `let g: int32? = 5` records a bare int32
                // global, and `let cache: P? = null` a `never?` one, whose reads
                // then mismatch the representation the checker assumed.
                let slot = ty
                    .as_ref()
                    .and_then(|t| fl.slot_type(t))
                    .or_else(|| match pat {
                        Pattern::Binding(_, None, span) => ctx.expr_type(*span).cloned(),
                        _ => None,
                    });
                let v = match slot {
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
    /// Store a top-level binding into module globals. A bare name binds
    /// directly. A destructuring pattern (array, tuple, record, or the variant
    /// of a one-variant sum) binds exactly as the local form does, in a scope
    /// of its own, and each bound name's value is then stored into its global
    /// -- so `let P { x, y } = p` or `let [i, s] = [1, "s"]` at module level
    /// makes `x`/`y` or `i`/`s` globals. The scope is closed again so later
    /// top-level statements read and write the globals, not the temporaries.
    fn store_global_pattern(&mut self, pat: &brass_parser::ast::Pattern, v: crate::value::Operand) {
        use crate::cfg::MirStmt;
        use brass_parser::ast::Pattern;
        match pat {
            Pattern::Binding(name, _, _) => {
                let key = self.ctx.global_symbol(&self.module, name);
                self.b.push(MirStmt::SetGlobal(key, v));
            }
            // The value was already evaluated for its effects.
            Pattern::Wildcard(_) | Pattern::Literal(..) => {}
            Pattern::Array(..) | Pattern::Record(..) => {
                let subj = self.b.make_local(v);
                self.push_scope();
                self.lower_pattern_bind(pat, subj);
                for name in pat.bound_names() {
                    if self.lookup(name).is_some() {
                        let value = self.lower_ident(name);
                        let key = self.ctx.global_symbol(&self.module, name);
                        self.b.push(MirStmt::SetGlobal(key, value));
                    }
                }
                self.pop_scope();
            }
        }
    }
}
