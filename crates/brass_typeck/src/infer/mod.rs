//! The authoritative type checker: call-site re-elaborating inference.
//!
//! Every function, method, closure and module initializer body is checked
//! with unification variables standing for what the source leaves open. A
//! call re-elaborates the callee's body at the call's argument types
//! (memoized per instantiation), so a generic body is checked once per
//! distinct instantiation -- the same instances monomorphization later
//! builds -- and the call's result is the return that instantiation
//! produces. (Under the lazy profile a call to a fully annotated free function
//! is typed from its signature instead.) Before the bodies, the pre-pass
//! (`precompute` and the error-free light pass) discovers unannotated
//! returns, record schemes and global bindings the bodies start from.
//!
//! Besides the diagnostics, the pass records what MIR lowering and
//! monomorphization need and cannot re-derive from types alone: the typed
//! expression sidecar and the channels of `crate::Analysis` (aggregate seeds,
//! views, keyed reflective calls, type tests, ...), keyed by span and, where
//! the instances of a generic body need different answers, by instance. Under
//! [`crate::analyze_streaming`] the bodies are checked in execution-first
//! order and those channels are flushed per body (see `crate::stream`).
//!
//! Map of the submodules: `driver` runs the pass (body order, streaming, the
//! per-body drivers); `precompute` (with its return-table fixpoint) and the
//! `light` walk are the pre-pass; `instantiate` re-elaborates a callee at a
//! call site, `journal` memoizes and replays those elaborations, and
//! `instances` attributes their observations to callable instances; `returns`
//! joins the values that leave a body; `context` loads a context seed and
//! `delta` builds the per-body stream deltas. The other modules type the
//! language's constructs (expressions, statements, calls, patterns, literals,
//! narrowing, closures, conversions, ...).

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

use brass_hir::{
    CallableSignature, Constness, FloatKind, FunInfo, IntKind, ModuleInit, NominalType, ParamInfo,
    Program, SchemeMethod, Substitution, Type, TypeInfo, TypeKind, TypeScheme, TypedProgram,
    peel_modes,
};
use brass_parser::Span;
use brass_parser::ast::*;
use brass_typesys::numeric_flows_into;

use crate::TypeError;
use crate::constraint::ShapeConstraint;
use crate::narrow;
use crate::solver::{InferenceVarKind, Solver};
use crate::stream::{self, StreamCtl};
use crate::unify::Subst;

mod assign;
mod binding_joins;
mod builtins;
mod call;
mod channel_changes;
mod cleanup;
mod closure_applications;
mod closure_check;
mod closure_light;
mod closure_memo;
mod closure_schemes;
mod co_replay;
mod completion_order;
mod const_calls;
mod context;
mod conversion;
mod delta;
mod driver;
mod expr;
mod fields;
mod function_values;
mod helpers;
mod instances;
mod instantiate;
mod journal;
mod light;
mod literals;
mod lookup;
mod narrowing;
mod numeric_calls;
mod patterns;
mod precompute;
mod preparation;
pub(crate) mod publication;
mod resolve;
mod returns;
mod stats;
mod stmt;
mod storage;

pub(crate) use cleanup::InferenceCleanup;

use journal::{
    ElaborationJournalEntry, ElaborationJournalFrame, ElaborationMemoContext, ElaborationMemoEntry,
    ElaborationMemoKey,
};
use narrowing::{ArmExit, is_null_test};

use assign::{common_nullable_type, integer_literal_fits};
use builtins::primitive_static_return;
use helpers::{
    Pipe, apply_method_substitution, apply_nominal_substitution, assign_binop,
    block_always_returns, block_literal, const_index, contains_typeof, expr_always_returns,
    expr_may_branch, field_substitution_key, int_literal_type, is_concrete_primitive,
    is_concrete_type, is_maybe_indexable, is_null_comparison, is_result_return_type,
    is_runtime_builtin_value, is_self_expr, literal_pattern_matches, literal_pattern_type,
    method_param_substitution_key, method_return_substitution_key, next_unknown_after_program,
    numeric_literal_repr, overlay_nominal_substitution, param_expected_type, param_is_location,
    peel_ref_mut, peel_value_wrappers, presence_binding_truth, required_arg_count,
    same_nominal_instance, stmt_may_branch, substitute_self, value_literal,
};
use storage::FlowSite;

pub use context::ContextTables;
use delta::flush_delta;
pub(crate) use driver::analyze_inner;
pub use driver::{analyze, analyze_generated, analyze_with, check};

/// One lexical frame: its value bindings (shared copy-on-write, so cloning a
/// scope stack for a branch is cheap), plus the nullable bindings proven
/// non-null for the region the frame covers (see [`narrowing`]).
#[derive(Clone, Default)]
struct Scope {
    numeric: binding_joins::numeric::Origins,
    values: Rc<HashMap<String, Type>>,
    narrowings: Vec<narrowing::Narrowing>,
    /// Field paths (`p.n`) a condition of this frame's region tested for
    /// presence. A field is never narrowed; these only explain an unchecked
    /// read of a tested field (see `Checker::report_nullable_use`).
    tested_fields: Vec<String>,
}

impl Scope {
    fn new(values: HashMap<String, Type>) -> Self {
        Self::shared(Rc::new(values))
    }

    fn shared(values: Rc<HashMap<String, Type>>) -> Self {
        Self {
            values,
            numeric: Default::default(),
            narrowings: Vec::new(),
            tested_fields: Vec::new(),
        }
    }

    fn into_map(self) -> HashMap<String, Type> {
        match Rc::try_unwrap(self.values) {
            Ok(values) => values,
            Err(values) => values.as_ref().clone(),
        }
    }

    /// Bind `name` in this frame. The new binding is not narrowed, so a
    /// narrowing this frame recorded for an earlier same-named binding ends.
    fn insert(&mut self, name: String, ty: Type) -> Option<Type> {
        self.numeric.remove(&name);
        self.narrowings.retain(|n| n.name() != name);
        self.tested_fields
            .retain(|path| path.split('.').next() != Some(name.as_str()));
        Rc::make_mut(&mut self.values).insert(name, ty)
    }
}

impl Deref for Scope {
    type Target = HashMap<String, Type>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl DerefMut for Scope {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Rc::make_mut(&mut self.values)
    }
}

type ScopeStack = Vec<Scope>;

/// A method call the call checker resolved, with everything
/// `Checker::instantiate_method_call` needs to elaborate the method's body
/// at it: the method, its receiver and argument types, and the returns to
/// fall back on.
struct MethodCall<'a> {
    owner: &'a str,
    self_type: &'a str,
    name: &'a str,
    method: &'a Method,
    signature_params: &'a [ParamInfo],
    receiver_ty: Option<Type>,
    declared_ret: Option<Type>,
    fallback_ret: Type,
    arg_types: &'a [Type],
    /// The call site, so a re-elaboration that runs out of budget is reported
    /// somewhere the user can act on.
    span: brass_parser::Span,
    /// For each non-`self` parameter, the type it instantiates to for this
    /// receiver instance (from the type's scheme), when fully known. An
    /// unannotated parameter takes this over the argument's own type, so the
    /// body sees the receiver-pinned type (a `string -> int64` map's `set`
    /// value is `int64`, not the `int32` a bare literal argument would default
    /// to) and the argument widens at the call boundary.
    scheme_params: &'a [Option<Type>],
}

/// A method a lookup resolved (see `Checker::method_for_qualifier`): the
/// qualifier whose table holds it (a record's storage symbol, or
/// `Sum.Variant`), the receiver type's symbol, its signature and declaration.
#[derive(Clone)]
struct ResolvedMethod {
    qualifier: String,
    self_type: String,
    signature: CallableSignature,
    method: Rc<Method>,
}

/// Propagation signals the light pass collects while walking a body: the
/// `Err` payload types of its error sites (`error(...)`, a Result-operand
/// `expr!`, a returned `Result` with no Ok value), and the spans of
/// nullable-operand `expr!` sites (whose null case returns null, making the
/// enclosing callable's return type nullable).
#[derive(Clone, Default)]
pub(super) struct LightProps {
    pub(super) errors: Vec<(Type, Span)>,
    pub(super) nulls: Vec<Span>,
    /// Whether a `!` propagates an operand whose type the walk left open:
    /// such a body may be fallible in its instances even though no error site
    /// was typed here.
    pub(super) open_errors: bool,
    /// Whether a member-presence test's subject is a binding whose type the
    /// walk left open: each instance decides the test (and so which arm's
    /// returns and error sites count), so the open walk must not judge the
    /// arms' disagreement.
    pub(super) open_static_test: bool,
}

/// What the `return`s of the body being checked are checked against: an
/// inferred return, or the declared type.
#[derive(Clone)]
enum ReturnContext {
    Inferred,
    Explicit(Type),
}

/// A stdlib method on a primitive or array receiver
/// (`fun string.m(self, ..)`, lowered as a free function whose first
/// parameter is the receiver; see `Program::primitive_methods`), cloned out
/// of its `FunInfo` so the call can be checked while the checker is mutably
/// borrowed (see `Checker::check_receiver_call`).
struct ReceiverCall {
    symbol: String,
    module: Vec<String>,
    signature_params: Vec<ParamInfo>,
    declared_ret: Option<Type>,
    decl: Rc<FunDecl>,
}

impl ReceiverCall {
    fn from_fun(info: &FunInfo) -> Self {
        Self {
            symbol: info.symbol.clone(),
            module: info.module.clone(),
            signature_params: info.signature.params.clone(),
            declared_ret: info.signature.ret_ty.clone(),
            decl: info.decl.clone(),
        }
    }
}

/// The result of the infer pass: its diagnostics, the typed sidecar and the
/// channels it recorded. [`crate::analyze`] merges it with the
/// declaration-level passes' diagnostics into the same-named fields of
/// [`crate::Analysis`].
pub struct Inference {
    pub errors: Vec<TypeError>,
    pub warnings: Vec<TypeError>,
    pub typed: TypedProgram,
    /// The aggregate-seed observations of `typed` made inside an instance
    /// elaboration, attributed to that instance (see
    /// [`stream::InstanceObservations`]).
    pub instance_typed: stream::InstanceObservations,
    /// The `recv.name(..)` calls the checker resolved to calling the
    /// function value a record field holds: `None` when every instantiation
    /// does, else the type-test patterns of the receivers that do (the
    /// others call a method). MIR lowering emits a field load and an indirect
    /// call for them, a method of the same name elsewhere notwithstanding.
    pub field_calls: HashMap<Span, Option<Vec<Type>>>,
    /// The per-instance targets of the reflective calls whose instances key
    /// them differently (see `Checker::settled_keyed_calls`).
    pub instance_keyed_calls: brass_hir::InstanceChannel<(String, String, Type)>,
    /// Per record-type generalized scheme (its inferred type parameters and the
    /// field/method signatures over them), keyed by the type's storage symbol. Read
    /// by the language server to render a method generically; see `build_schemes`.
    pub schemes: HashMap<String, TypeScheme>,
    /// Spans of anonymous structural arguments that passed the callee-row check
    /// for a view-eligible parameter (see `brass_typesys::rows`). MIR lowering
    /// converts exactly these arguments into the parameter's view.
    pub view_args: HashSet<Span>,
    /// Expressions accepted as a declared sum subtype at a flow site, keyed by
    /// the value expression's span, mapped to the PARENT sum instance the site
    /// requires. MIR lowering rebuilds exactly these values as the parent
    /// (SumView).
    pub sum_views: HashMap<Span, Type>,
    /// `expr!` sites whose propagated Err payload is re-raised wrapped into
    /// the prelude `Error` (gaining the site's location); MIR's propagation
    /// arm rebuilds the value.
    pub lift_errs: HashSet<Span>,
    /// Field lists of `for f in fields(x)` loops, keyed by the loop statement's
    /// span. The checker resolved `x`'s record type and checked one expanded
    /// copy per field; MIR lowering unrolls the same copies from this list.
    /// A divergent span retains a representative here; `instance_fields` owns its selections.
    pub fields_loops: HashMap<Span, Vec<String>>,
    /// Field lists at loops whose callable instances disagree.
    pub instance_fields: brass_hir::InstanceChannel<Vec<String>>,
    /// Type symbols resolved for expressions, keyed by span: the type a
    /// `typeof(v).method(..)` static call names (keyed by the inner
    /// `typeof(v)`), and the declared record an anonymous record literal or a
    /// literal written through a record alias is built as. MIR lowering
    /// routes the call and builds the literal by these.
    pub type_names: HashMap<Span, String>,
    /// Reflective (`-> infer!`) method calls keyed by the caller's expectation:
    /// call span -> (canonical receiver type symbol, method, target key). The driver
    /// generates a concrete specialization per (receiver, method, key) and
    /// rewrites the call to it.
    pub keyed_calls: HashMap<Span, (String, String, Type)>,
    /// Concrete return-origin contracts, keyed by call and enclosing instance.
    pub numeric_calls: brass_hir::NumericCalls,
    /// Resolved binding types of local annotations that contain a `typeof(v)`,
    /// keyed by the annotation's span; MIR seeds the slot from this (the type
    /// is not recoverable from a `null`/inferred initializer alone). Disagreeing
    /// instances use the typed annotation observations in `instance_seeds`.
    pub typeof_types: HashMap<Span, Type>,
    /// Resolved type-test patterns (`if v: T`), keyed by the test's span; MIR
    /// lowering embeds each into the test's rvalue so monomorphization can
    /// fold the branch per instance (see `Checker::type_tests`).
    pub type_tests: HashMap<Span, Type>,
    /// Spans of `expr!` operators whose operand is a nullable rather than a
    /// `Result`: the value case unwraps, the null case propagates as
    /// `Result.Null`. MIR lowering emits the presence-test shape for these.
    pub null_props: HashSet<Span>,
    /// The inferred return type of every free function, keyed by symbol and
    /// resolved. A function with no `-> T` annotation has none in its signature,
    /// so this is the only record of what the checker settled on; the language
    /// server renders it.
    pub function_returns: HashMap<String, Type>,
    /// The same for methods, keyed by (type symbol, method name). Covers both an
    /// unannotated return and the open Err payload of a `T!` one.
    pub method_returns: HashMap<(String, String), Type>,
    /// Unambiguous display-only closure-parameter instantiations, var id ->
    /// observed type (see `Checker::record_closure_binding`). The language
    /// server substitutes these into the typed sidecar before rendering; the
    /// compile pipeline ignores them.
    pub closure_bindings: HashMap<u32, Type>,
    /// The fully-known return of each unannotated function instance a clean
    /// call-site elaboration settled, keyed by (function symbol, resolved
    /// argument types). Monomorphization types against it what an instance's
    /// body alone cannot give: a call into an instance it is still typing (an
    /// unannotated mutual recursion), a returned closure, and in the lazy JIT
    /// a call compiled as a runtime-deferred site without lowering the callee.
    pub instance_returns: HashMap<(String, Vec<Type>), Type>,
    /// This run's cross-module tables (see [`ContextTables`]): a context seed
    /// for later runs when this was a context-only run (whole, or restricted
    /// to its modules without diagnostics), and what [`analyze_generated`]
    /// continues a completed run from.
    pub context_tables: ContextTables,
}

/// A closure's source and lexical environment for concrete body checking.
struct ClosureBody {
    expr: Expr,
    /// Whether the syntax has only local primitive arithmetic dependencies.
    numeric_replay: bool,
    /// Whether the body has a contextual return contract.
    explicit_return: bool,
    scopes: ScopeStack,
    /// The narrowing facts of the callable the literal belongs to.
    narrowing_facts: Rc<narrowing::NarrowingFacts>,
    const_scopes: Vec<HashSet<String>>,
    module: Vec<String>,
    self_type: Option<String>,
    self_variant: Option<(String, String)>,
}

/// The state of one run of the infer pass (see `driver`): the diagnostics and
/// channels being recorded, the pre-pass tables the bodies start from
/// (returns, schemes, globals), the solver, and the bookkeeping of the body
/// checks and call-site elaborations in progress.
#[derive(Clone)]
struct Checker<'a> {
    channel_changes: std::cell::RefCell<channel_changes::ChannelChanges>,
    program: &'a Program,
    errors: Vec<TypeError>,
    warnings: Vec<TypeError>,
    typed: TypedProgram,
    /// Exact typed observations already present in `typed`, bucketed by their
    /// fxhash so replay remains idempotent without a linear scan of the sidecar.
    typed_seen: HashMap<u64, Vec<usize>>,
    const_scopes: Vec<HashSet<String>>,
    next_unknown: u32,
    self_type: Option<String>,
    self_variant: Option<(String, String)>,
    return_contexts: Vec<ReturnContext>,
    /// The resolved type of each `return` value, collected per enclosing callable
    /// (one frame per `return_contexts` frame). The full check observes the stores
    /// and pushes a body performs, so its inferred return is more precise than the
    /// light pass -- a witness-free constructor's nullable slot element resolves
    /// here. Consumed by `check_block_root` for an inferred-return body.
    return_values: Vec<Vec<(Type, brass_parser::Span)>>,
    /// The `return` types the last [`Self::check_block_root`] collected, so a
    /// caller can reconcile them itself (see `prefer_full_return`).
    last_returns: Vec<(Type, brass_parser::Span)>,
    /// Expressions checked as `never` in the current callable body. Return
    /// completeness reads these facts without changing branch value inference.
    diverging_exprs: HashSet<Span>,
    /// The statically decided `if`/`if let` tests of each body being checked
    /// (innermost last), by the expression's span: the arm the full check
    /// selected when the condition's type alone decides it. Type tests use
    /// their condition span.
    static_fold_frames: Vec<HashMap<Span, bool>>,
    /// The decisions the last [`Self::check_block_root`] made (see
    /// `static_fold_frames`), for the light walk of the same elaboration.
    last_static_folds: HashMap<Span, bool>,
    /// The full check's decisions the current light walk follows (see
    /// `prefer_full_return`), so a per-instance walk prunes exactly the arms
    /// the full check -- and the back end -- never run: their returns and
    /// error sites belong to no path of the instance.
    light_folds: HashMap<Span, bool>,
    /// The numeric-literal value of each collected `return` written as a
    /// literal, keyed by the span the return was collected under, so the
    /// return join can let the literal adapt (see `returns.rs`).
    return_literals: HashMap<brass_parser::Span, brass_typesys::NumericLiteral>,
    /// The span of each `return` statement's value expression, keyed by the
    /// statement span its type is collected under: where a joined return
    /// that must be rebuilt as a parent sum records the rebuild.
    return_value_spans: HashMap<brass_parser::Span, brass_parser::Span>,
    /// While an instantiation that called itself is re-elaborated (see
    /// `returns::settle_recursive_return`), keyed like `instantiating`: the
    /// argument types and the return its recursive calls read.
    recursion_assumptions: HashMap<String, (Vec<Type>, Type)>,
    /// What the most recent check of a closure body against an expected
    /// function type returned (its expression value or joined `return`s,
    /// with the propagation layers), read back by `check_callable_body` for
    /// the application's result.
    last_closure_result: Option<Type>,
    /// The instantiation whose body's returns and error payloads are being
    /// reconciled, while a re-elaboration reports its conflicts; `None`
    /// outside one (a conflict is then the definition's own).
    conflict_site: Option<returns::InstanceSite>,
    /// Instantiations (callable + resolved inputs) whose return or
    /// error-payload conflict was already reported, so a later call site or
    /// re-elaboration of the same instantiation stays quiet.
    reported_instances: HashSet<(String, Vec<Type>)>,
    /// The span of the trailing expression statement of the block being
    /// checked in expression position (its value is the block's value, not
    /// discarded); `None` in a statement block.
    block_value_tail: Option<Span>,
    /// The requirement the value of the `if`/`match`/block expression about
    /// to be checked flows into (set by `check_expr_against_at`, taken by that
    /// expression): each branch value is checked against it, so a construction
    /// in a branch adapts to the slot exactly as a direct initializer does.
    branch_expectation: Option<(Type, storage::FlowSite)>,
    /// The requirement the trailing value of the block being checked in
    /// expression position flows into, when its enclosing branching
    /// expression had one (see `branch_expectation`).
    tail_expectation: Option<(Type, storage::FlowSite)>,
    /// Whether the branching expression `check_expr_against_at` handed
    /// `branch_expectation` to passed it on to its branch values (a type-test
    /// `if` drops it instead).
    branch_expectation_taken: bool,
    /// Spans of the expressions whose value the enclosing statement discards
    /// (see `walk::discarded_value_spans`): a `!` there only propagates.
    discarded_values: HashSet<Span>,
    /// Spans of the expressions in statement position and, through their
    /// arms, of each arm's trailing expression (see
    /// `walk::discarded_value_spans`): an `if`/`if let`/`match` there yields
    /// no value, so its arms' values are not joined -- `if c { f() }` with an
    /// `int32`-returning `f` is fine as a statement.
    statement_values: HashSet<Span>,
    /// Set while checking the operand of `typeof(..)`, which reads only the
    /// operand's type.
    type_only_read: bool,
    /// Top-level bindings keyed by their DEFINING module. Globals are per-module
    /// (the back end keys their storage that way too), so two modules' same-named
    /// `const`s are two different globals with two different types -- a single
    /// name-keyed table would hand one module the other's type and let the back
    /// end read the wrong slot at it.
    global_defs: HashMap<Vec<String>, HashMap<String, Type>>,
    /// Memoized `globals_visible_from`, keyed by the referencing module.
    global_scopes: HashMap<Vec<String>, Rc<HashMap<String, Type>>>,
    function_returns: HashMap<String, Type>,
    /// (method qualifier, method name) -> return type.
    /// Record qualifiers are storage symbols; variant qualifiers append `.Variant`.
    method_returns: HashMap<(String, String), Type>,
    /// Methods whose `method_returns` entry carries propagation (`error(...)` /
    /// nullable `!`) wrapping from the light assembly; the co-check's plain
    /// return reconciliation must not replace those (see `co_method_returns`).
    method_return_props: HashSet<(String, String)>,
    /// (record storage symbol, method name) -> the return type the full co-check of
    /// the method bodies reconciled in the shared per-type environment. Unlike
    /// the light-pass `method_returns`, these are expressed over the same
    /// variables as the record's fields, so scheme generalization ties a
    /// method's return to the type's parameters (`get -> V?`). Only recorded
    /// for inferred-return, non-propagating record methods.
    co_method_returns: HashMap<(String, String), Type>,
    /// Whether the co-check pass (every record type's method bodies, checked in
    /// one shared environment before scheme generalization) is running. Return
    /// reconciliation RECORDS unifiable return paths as links (see
    /// `co_return_links`) only then: the scheme must record two unifiable
    /// returns as one parameter (`get_or`'s `dflt` IS the map's value type),
    /// while a free function's returns stay loose -- its signature keeps its
    /// own variables, bound per call site.
    co_checking: bool,
    /// The `(type symbol, method name)` whose body the co-check pass is
    /// currently checking, so return reconciliation can attribute the links it
    /// records (see `co_return_links`).
    current_co_method: Option<(String, String)>,
    /// Pairs of return-path types the co-check found unifiable within one
    /// method body. Scheme generalization ties each pair's inference variables
    /// together (`get_or`'s `dflt` IS the map's value type) -- as a rewrite
    /// local to that type's scheme, never a shared-solver binding, which would
    /// leak into unrelated bodies' cached signature variables.
    co_return_links: HashMap<(String, String), Vec<(Type, Type)>>,
    /// Callables whose body is currently being re-elaborated at a call site,
    /// keyed by `fn:<symbol>` / `method:<self type>.<name>`, qualified by
    /// argument types for distinct recursive instances that can reach field
    /// reflection. Re-entering the same key is a
    /// recursive call: re-checking the body again would not terminate, so the
    /// call is typed against the return the elaboration in progress assumes
    /// (see `recursion_assumptions`, `recursion_provisional`), else the
    /// declared or precomputed one.
    ///
    /// A method is keyed by its RECEIVER TYPE, not by the `Sum.Variant` qualifier
    /// the call resolved through. A sum's methods are lowered into every variant's
    /// table, so one `v.render()` resolves to one candidate per variant, all
    /// sharing the same body. Keyed per qualifier, a recursive call could
    /// re-enter through another variant's key, and each level would
    /// re-elaborate the body once per variant not yet entered: work factorial
    /// in the variant count.
    instantiating: HashSet<String>,
    /// Set when a context seed was applied: every module except the entry
    /// (`main`) was checked by the run that produced the seed, so the per-item
    /// passes skip it and read the seeded tables instead.
    entry_only: bool,
    /// Requested item work; context-only requests omit ordinary dedicated passes.
    preparation: Option<Rc<crate::reachability::AnalysisView>>,
    /// A selected return dependency reuses one immutable catalog in this analysis.
    selection_index: Option<Rc<crate::reachability::ItemIndex<'a>>>,
    /// Item-granular facts tied to the producing context's storage identities.
    item_seed: Option<Rc<crate::reachability::AnalysisView>>,
    /// Elaborations in progress (keyed like `instantiating`) that a recursive
    /// call re-entered. Only those need what their recursive calls were typed
    /// against -- the instance's provisional return (see
    /// `recursion_provisional`) -- tied to what the body really returns (see
    /// `link_inferred_return`), and an unsettled recursive return reported.
    recursed: HashSet<String>,
    /// Names the method co-check read from the global scope. The co-check runs
    /// before the module initializers settle the globals' types, so a method
    /// that read one was checked against its provisional type (see
    /// `settle_global`).
    co_global_reads: HashSet<String>,
    /// The callables whose call-site elaborations are in progress, innermost
    /// last (the order `instantiating` does not keep).
    elaboration_stack: Vec<String>,
    /// Elaborations in progress (keyed like `instantiating`) that a recursive
    /// call re-entered through ANOTHER callable's elaboration.
    mutually_recursed: HashSet<String>,
    /// The return-table entries the light pass read while inferring the
    /// precompute entry in progress, `None` outside that pass. The precompute
    /// fixpoint re-infers an entry only when one of these changed (see
    /// `precompute_return_entries`). A cell because the read in
    /// `instantiate_annotated_type` happens behind a shared borrow.
    light_reads: std::cell::RefCell<Option<HashSet<precompute::ReturnKey>>>,
    /// The provisional return of each call-site elaboration in progress of an
    /// unannotated function, keyed like `instantiating`, with the resolved
    /// argument types it is for: what a recursive call at those arguments is
    /// typed against until the body's own return is known. Instance-specific
    /// (see `instance_provisional_return`), and tied to the real return when
    /// the elaboration finishes (see `link_inferred_return`).
    recursion_provisional: HashMap<String, (Vec<Type>, Type)>,
    /// Callables (keyed like `generic_error_returns`) whose body has at least one
    /// error site (an `error(..)`, an `expr!` propagation, or a forwarded
    /// `Result`). A `T!` with NO site is fine -- nothing ever reads its Err --
    /// but one whose sites all came back with an unknown error type has nothing
    /// to infer it from, and is reported.
    error_sites: HashSet<String>,
    /// How many callable bodies have been re-elaborated at call sites so far, and
    /// whether the budget below has already been reported. Inference that fails to
    /// converge must not hang the compiler: it stops re-elaborating and says so.
    elaborations: u64,
    /// Observations owned by this checker; speculative clones keep their own counts.
    stats: stats::ElaborationStats,
    elaboration_budget_reported: bool,
    /// How many calls were typed from their fallback return because the
    /// elaboration nesting was too deep (see `elaboration_allowed`). A
    /// fallback is only an approximation of the instance's return (the
    /// definitional return, not one checked at these argument types), so an
    /// elaboration that saw the count grow is neither memoized nor reported
    /// as an instance's return.
    depth_capped: u64,
    /// Dependency observations made only by committed priority passes.
    completion: completion_order::CompletionGraph,
    /// Deferred structural constraints on inference variables, keyed by the
    /// variable's `Unknown` id. Recorded while checking a body that uses an
    /// unknown-typed value (a closure parameter) and verified when the variable
    /// is solved at a call site (see `crate::constraint`).
    shape_constraints: HashMap<u32, Vec<ShapeConstraint>>,
    /// Generic closure definitions and their lexical environment. Callable
    /// values retain their parameter variables, so applications can check the
    /// body again with concrete arguments just like a named generic function.
    closure_bodies: HashMap<Vec<Type>, Rc<ClosureBody>>,
    /// Bodies identified by an open result, including closures with no open
    /// parameters whose bracket shape depends on captured values.
    closure_result_bodies: HashMap<u32, Rc<ClosureBody>>,
    /// The inference solver: a persistent substitution for variables pinned
    /// across expressions (such as an empty array's element type once a `push`
    /// fixes it) plus variable classification. `resolve` follows the
    /// substitution so all later uses of the same binding see the solved type,
    /// and `kind_of` tells the variables that cannot satisfy a required
    /// position while unconstrained (an empty array's element, the Ok payload
    /// of a body that only fails; see `InferenceVarKind`) from source-level
    /// unknowns.
    solver: Solver,
    /// The module whose body is currently being checked, used to enforce
    /// per-module name visibility. Set per function, method, and module-init,
    /// and swapped while a called body is re-checked.
    current_module: Vec<String>,
    /// Nominal ids of shadowing `type Result` declarations whose shape problem
    /// was already reported, so every `T!`/`error(..)` in the module does not
    /// repeat the same diagnostic (`i32::MIN` marks the alias-shadow report).
    reported_result_shadow: HashSet<i32>,
    /// The lazy (streaming) profile: a call to a FULLY-ANNOTATED free function
    /// -- concrete declared return, every parameter's type declared and fully
    /// known -- is typed from the signature alone, skipping the callee-body
    /// re-elaboration (`check_call` lists the remaining conditions). Such a
    /// body is instantiation-independent and its own dedicated pass records
    /// its channels, so per-call re-checking would only re-derive what the
    /// signature already states; the lazy JIT can likewise compile a call to
    /// it as a runtime-deferred site from the signature. The complete
    /// diagnostic verdict stays with the eager (non-streaming) run, where this
    /// is off.
    lazy_profile: bool,
    /// Memoized call-site body elaborations. Open input variables are numbered by
    /// first occurrence and tagged with their solver kind, preserving aliases
    /// without making checker-local ids part of the key. A method key also covers
    /// its receiver and receiver-derived scheme inputs.
    ///
    /// Each clean entry retains the return skeleton, constraints imposed on its
    /// canonical inputs, non-input placeholders, deferred shape constraints, and
    /// semantic channel observations. A hit freshens placeholders, applies input
    /// bindings, registers shapes, and replays every channel through its normal
    /// helper. This keeps nested windows and poison rules equivalent to a body
    /// walk while collapsing repeated subtrees of inferred call chains.
    elaboration_memo: HashMap<ElaborationMemoKey, Rc<ElaborationMemoEntry>>,
    /// Keep co-check reuse disabled when a numeric probe temporarily adopts
    /// an ordinary frame for a structurally zero-growth annotated body.
    co_memo_suspended: bool,
    /// Nested co-effect observers, empty unless memo differential checks run.
    co_validation: Vec<co_replay::CoEffects>,
    /// Opt-in nested dependency windows used only for inventory reporting.
    method_inventory: Option<Box<co_replay::MethodInventory>>,
    /// Version of the shared scheme table, local to this checker.
    method_scheme_revision: u64,
    /// Canonical method co keys already missed in this checker. Only repeated
    /// misses may open their own storage window; enclosing journals stay active.
    method_co_seen: HashSet<ElaborationMemoKey>,
    /// Completed checks of lexically closed numeric closures. Entries retain
    /// exact concrete observations in their original enclosing instance.
    closure_memo: HashMap<closure_memo::ClosureMemoKey, Rc<ElaborationMemoEntry>>,
    /// Differential checking can force every concrete closure body walk.
    closure_memo_disabled: bool,
    #[cfg(test)]
    closure_memo_hits: usize,
    /// How many speculative walks -- checks whose solver bindings are rolled
    /// back afterwards (a type-test probe, a closure body checked at one
    /// application's types) -- enclose the current point. An elaboration
    /// finished inside one is not memoized: its entry would describe bindings
    /// the rollback undoes, and a later real call would replay them as if they
    /// had happened.
    speculation_depth: u32,
    /// The imported context was checked without widening any numeric origin.
    numeric_seed_ordinary: bool,
    /// Whether this attempt solves unsatisfied numeric-origin demands.
    numeric_enabled: bool,
    /// A completed private walk certified this entire subtree at its ordinary types.
    numeric_zero_growth: bool,
    numeric: binding_joins::numeric::NumericState,
    numeric_pure_bodies: Rc<HashSet<String>>,
    numeric_pure_spans: Rc<std::cell::OnceCell<HashSet<Span>>>,
    /// Reachable field loops used to distinguish reflected recursive instances.
    fields_reflection: Rc<std::cell::OnceCell<fields::recursion::Reflection>>,
    numeric_eligibility: Rc<std::cell::OnceCell<binding_joins::numeric::eligibility::Eligibility>>,
    numeric_closed_bodies: Rc<HashSet<String>>,
    /// Nested elaboration windows isolate their own observations while still
    /// composing complete child subtrees into an enclosing memo entry.
    elaboration_journals: Vec<ElaborationJournalFrame>,
    /// Fully-known returns from clean call-site elaborations of unannotated
    /// functions. Unlike the memo, these are part of the streaming contract:
    /// nested callees can remain runtime-deferred when their caller resolves.
    instance_returns: HashMap<(String, Vec<Type>), Type>,
    /// Free functions that can transitively reach a reflective keyed
    /// (`-> infer!`) method call (see `taint::keyed_reachable`). The lazy
    /// profile never types a call to one from its signature alone: the keyed
    /// call must be SEEN while its caller is checked, or it could first be
    /// reported after execution began, too late to specialize (see `taint`).
    /// Empty outside the lazy profile.
    keyed_tainted: HashSet<String>,
    /// The module paths a PARTIAL seed covers (see `ContextTables::covered`);
    /// `None` under a full seed or no seed.
    seeded_set: Option<HashSet<Vec<String>>>,
    /// Callables (`fn:<symbol>` / `m:<qualifier>.<name>`) whose inferred Err
    /// payload is one of their own parameter variables: a generic error type
    /// named per call site, exempt from the uninferable-error report.
    generic_error_returns: HashSet<String>,
    /// Per record-type generalized scheme, keyed by storage symbol. Built after the
    /// method bodies are co-checked (the co-check itself runs against a
    /// preliminary set, see `seed_schemes`) and consulted at call sites to type a
    /// method call's result by instantiating the method's scheme against the
    /// receiver.
    schemes: HashMap<String, TypeScheme>,
    /// One-shot marker set while checking the direct array-literal initializer
    /// of an unannotated `const` binding: the binding is immutable, so the
    /// literal types as a fixed-length array (`int32[3]`) rather than a growable
    /// slice. Consumed (reset) by the literal itself, so nested literals and any
    /// other position stay slices.
    fixed_array_binding: bool,
    /// The type a call-position expression is expected to produce, set by
    /// `check_expr_against` and consumed at the start of `check_call`; keys a
    /// reflective `-> infer!` method by its result.
    call_expected: Option<Type>,
    /// Reflective method calls discovered so far (see [`Inference::keyed_calls`]).
    keyed_calls: HashMap<Span, (String, String, Type)>,
    numeric_observations: Vec<numeric_calls::Observation>,
    numeric_observed: HashSet<numeric_calls::Observation>,
    /// How each `recv.name(..)` call resolved across its elaborations (see
    /// `Checker::record_call_kind`).
    call_sites: HashMap<Span, instances::CallSite>,
    /// Every reflective call observation, attributed to its instance (see
    /// `Checker::settled_keyed_calls`); `keyed_calls` only tracks which
    /// spans are reflective.
    keyed_observations: Vec<instances::KeyedObservation>,
    /// The callable instances being elaborated, innermost last (see
    /// [`instances`]): channel observations are attributed to the top one.
    instance_stack: Vec<instances::TagRef>,
    /// The interned instance tags by hash (see `instances::TagRef`).
    instance_tags: HashMap<u64, Vec<Rc<instances::InstanceTag>>>,
    /// Recursive-call spans already reported as polymorphic recursion
    /// (see `Checker::check_polymorphic_recursion`).
    polymorphic_recursion_reported: HashSet<Span>,
    /// Aggregate-seed observations made inside an instance elaboration, in
    /// record order, deduplicated (see `Checker::record_instance_typed`).
    instance_typed: Vec<instances::InstanceTyped>,
    /// The members of `instance_typed`, for deduplication.
    instance_typed_seen: HashSet<instances::InstanceTyped>,
    /// Resolved binding types of `typeof`-bearing local annotations, keyed by
    /// the annotation span (see [`Inference::typeof_types`]).
    typeof_types: HashMap<Span, Type>,
    /// `typeof`-bearing annotation spans whose resolved type DIFFERED between
    /// two checks -- a generic body's instantiations disagreeing. One MIR body
    /// is shared by every instantiation, so no single slot type is right;
    /// the shared entry is dropped and the binding's slot reads its
    /// per-instance seed from the typed annotation observations.
    typeof_poisoned: HashSet<Span>,
    /// The narrowings ended on the path being checked in the current callable
    /// (see [`narrowing`]): a branch arm's entries are taken out and put back
    /// at the join, a loop's stay to end them at its head.
    narrowing_kills: Vec<narrowing::NarrowId>,
    /// Nullable field reads inside a region whose condition tested the same
    /// field path, by the read's span, with that path: their nullable-use
    /// diagnostic explains that testing a field does not narrow it.
    tested_field_reads: HashMap<Span, String>,
    /// The next fresh [`narrowing::NarrowId`].
    next_narrowing: narrowing::NarrowId,
    /// Syntactic facts of the callable body being checked that bound how long
    /// a narrowing survives calls and closure capture.
    narrowing_facts: Rc<narrowing::NarrowingFacts>,
    /// The loops of the current path being checked, innermost last, with the
    /// narrowings in force at each loop head (see `Checker::check_loop`).
    loop_frames: Vec<narrowing::LoopFrame>,
    /// Set while typing the operand of a null test (`if x`, `!x`,
    /// `x == null`), which is not a value use of a narrowing.
    null_test_operand: bool,
    /// Depth of walks whose diagnostics are discarded (statically dead arms,
    /// speculative probes); their uses are not judged by loop verification.
    discarded_walks: u32,
    /// Per-parameter rows (field presence/type requirements) of every free
    /// function and method, derived once per program. An anonymous structural
    /// argument to a row-covered parameter is checked against the row at the
    /// argument's own span (the value is where the mismatch lives).
    rows: Rc<brass_typesys::RowInfo>,
    /// The method calls const checking found touching a const value; each is
    /// judged against its resolved receiver (see `check_const_method_call`).
    const_calls: Rc<crate::constck::ConstCalls>,
    /// Spans of anonymous structural arguments that passed their callee row
    /// check for a view-ELIGIBLE parameter: exactly the call sites where MIR
    /// lowering may convert the argument into the parameter's view.
    view_args: HashSet<Span>,
    /// Value expressions accepted as a declared sum subtype at a flow site,
    /// keyed by the expression's span, mapped to the PARENT sum instance the
    /// site requires (see [`Inference::sum_views`]).
    sum_views: HashMap<Span, Type>,
    /// `expr!` sites whose propagated Err payload is re-raised wrapped into
    /// the prelude `Error` (see [`Inference::lift_errs`]).
    lift_errs: HashSet<Span>,
    /// Field lists of checked fields-loops, keyed by loop-statement span; the
    /// channel MIR lowering unrolls from (see [`Inference::fields_loops`]).
    fields_loops: HashMap<Span, Vec<String>>,
    /// Replayable field lists with their enclosing callable identities.
    fields_observations: HashMap<Span, Vec<fields::FieldsObservation>>,
    /// Type symbols resolved for `typeof(v).method(..)` static calls and for
    /// record literals built as a declared record (see
    /// [`Inference::type_names`]).
    type_names: HashMap<Span, String>,
    /// Display-only observations of what each application of a Fun-typed value
    /// instantiated its open parameter variables to, var id -> observed type.
    /// The solver deliberately never learns these (see
    /// `Checker::record_closure_binding`); `None` poisons a variable observed
    /// at two different types (a genuinely polymorphic closure).
    closure_bindings: HashMap<u32, Option<Type>>,
    /// The binding spans of the generalized closure bindings of the program
    /// (`brass_hir::generalized_closure_bindings`): the rule MIR lowering
    /// applies too, so both agree on which bindings are let-polymorphic.
    generalizable: Rc<HashSet<Span>>,
    /// Quantified variable -> every variable of the closure scheme it belongs
    /// to (see `closure_schemes`). A type mentioning one is a use of a
    /// generalized closure binding and is instantiated at each lookup.
    closure_schemes: HashMap<u32, Rc<[u32]>>,
    /// The light walk collecting a monomorphic closure binding's direct
    /// applications, while one runs (see
    /// `Checker::pin_closure_parameters`).
    application_probe: Option<closure_applications::ApplicationProbe>,
    /// (scheme variable, the fresh variable one use instantiated it to), for
    /// the display-only `closure_bindings` observations made at the end.
    closure_instantiations: Vec<(u32, u32)>,
    /// Functions named as values with optional trailing parameters, by the
    /// inference variable standing for each occurrence (see
    /// `function_values`).
    function_values: HashMap<u32, function_values::FunctionValue>,
    /// Closure literals a concrete instance returned with parameters its body
    /// did not determine (see `settle_escaping_closures`).
    undetermined_closures: Vec<Span>,
    /// The inference variables minted for unannotated closure parameters: an
    /// arithmetic operation on one next to a literal is typed by the
    /// parameter (see `check_binary_expr`).
    closure_param_vars: HashSet<u32>,
    /// Spans of `expr!` operators whose operand is a NULLABLE (not a `Result`):
    /// the null case propagates as `Result.Null`. MIR lowering emits the
    /// presence-test shape for exactly these spans (see [`Inference::null_props`]).
    null_props: HashSet<Span>,
    /// The propagation kind each checked `expr!` span resolved to. The
    /// `null_props` channel is a span SET while one MIR body is shared across a
    /// generic's instantiations, so a `!` whose operand is a nullable in one
    /// instantiation and a `Result` in another has no single correct lowering;
    /// the kinds are tracked here and a disagreement is a checker error
    /// (`None` marks a span already reported, so re-elaborations stay quiet).
    prop_kinds: HashMap<Span, Option<PropKind>>,
    /// The error payload (lifted into the prelude `Error`) the latest full
    /// check of each `!` site found it propagating from a `Result` operand.
    /// The light return walk of a per-instance elaboration runs right after
    /// the full check of the same body and reads it for an operand it cannot
    /// type itself -- a callee that is fallible only at this instance (a
    /// method on an open parameter, a closure parameter) -- so the instance
    /// is fallible exactly when one of its live `!` sites propagates an error.
    full_err_props: HashMap<Span, Type>,
    /// The element type of every empty array literal (`[]`) checked outside
    /// a speculative walk, by the literal's span. A body checked at concrete
    /// inputs judges its own literals once it is done (see
    /// [`Checker::report_unfixed_empty_arrays`]).
    empty_array_elems: Vec<(Span, Type)>,
    /// The empty array literals of module top-level code, judged after every
    /// body is checked (see [`Checker::report_unfixed_init_arrays`]).
    init_empty_arrays: Vec<(Span, Type)>,
    /// Per-span evidence of how each sum flow site lowered in this
    /// elaboration: `Some(parent)` = coerced (rebuilt) to that declared-parent
    /// instance, `None` = same-nominal flow needing no rebuild. `sum_views` is
    /// keyed by span while one MIR body is shared across a generic's
    /// instantiations and the baked rebuild has no per-instance escape hatch,
    /// so instantiations that disagree -- different parent instances, or
    /// view in one and identity in another -- are rejected like `prop_kinds`.
    /// Unresolved observations stay here until their payloads settle.
    sum_view_seen: HashMap<Span, Vec<Option<Type>>>,
    /// Sum-view spans whose cross-instantiation conflict is already reported.
    sum_view_poisoned: HashSet<Span>,
    /// Whether each `!`/forwarded-return span re-wraps a raw error payload
    /// into the prelude `Error` (`true`) or propagates one that already is
    /// (`false`). `lift_errs` is a span SET under the same shared-body
    /// constraint, so a kind that differs across instantiations is rejected.
    lift_kinds: HashMap<Span, bool>,
    /// Lift spans whose cross-instantiation conflict is already reported.
    lift_poisoned: HashSet<Span>,
    /// Whether the body currently being checked is the entry `main` (the root
    /// module's bare `main` symbol). Its `!` propagations abort at runtime
    /// instead of returning a `Result`, so the return-context requirement is
    /// waived for its own body (depth 1 -- closures inside it still propagate).
    in_entry_main: bool,
    /// Set by the `if` checker when the condition folded STATICALLY and the arm
    /// that condition selects always returns: everything after that `if` in the
    /// enclosing block is then unreachable. `check_block` reads it to stop
    /// reporting there, exactly as it already stops reporting inside the dead
    /// ARM of such an `if` -- the back end folds the branch to a direct jump and
    /// never emits the fall-through either. The unreachable statements'
    /// `return`s do not join the instance's return type.
    static_divergence: bool,
    /// Resolved patterns of checked type tests (`if v: T`), keyed by the test's
    /// span: the annotation with each `infer` hole either pinned by the tested
    /// arm's own requirements or left a wildcard. MIR lowering embeds the
    /// pattern into the test's rvalue and monomorphization re-decides the match
    /// per instance through the same `brass_typesys::type_test_accepts` the
    /// checker folded with. Recorded only by a pass whose subject type is fully
    /// known (an open definitional sighting is less information, not a
    /// decision), and shared-body instantiations that resolve a hole
    /// differently are rejected.
    type_tests: HashMap<Span, Type>,
    /// Type-test spans whose cross-instantiation pattern conflict is already
    /// reported; the entry is dropped and stays dropped.
    type_test_poisoned: HashSet<Span>,
    /// Hole variables of the type-test pattern currently being probed.
    /// Assignability normally only probes (a polymorphic value checked at many
    /// positions must not be pinned), but a probe hole EXISTS to be pinned by
    /// the tested arm's requirements -- `if v: infer { to_bytes(v) }` means
    /// "the type `to_bytes` accepts" -- so `expect_assignable` commits an
    /// accepted hole-to-concrete flow while this set is non-empty.
    type_test_holes: HashSet<u32>,
    /// Pattern-only walks cannot publish a concrete record field expansion.
    fields_probe_depth: usize,
}

/// What a checked `expr!` propagates on failure: the null of a nullable
/// operand, or the `Err` of a `Result` operand. See `Checker::prop_kinds`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum PropKind {
    Null,
    Err,
}

/// Find one direct nullable propagation and one direct error source in a
/// callable body: the first `expr!` that propagates a null, and the first
/// `expr!` that propagates an `Err` or `error(..)` call (returned or not --
/// every evaluated `error(..)` makes the body fallible). Closure spans are
/// excluded because a closure owns its return flow even when the light
/// return-inference walk visits it while checking the surrounding callable.
fn mixed_propagation_sites(
    body: &Block,
    kinds: &HashMap<Span, Option<PropKind>>,
) -> Option<(Span, Span)> {
    #[derive(Default)]
    struct Sites {
        props: Vec<Span>,
        raises: Vec<Span>,
        closures: Vec<Span>,
    }

    impl crate::walk::ExprVisitor for Sites {
        fn visit(&mut self, expr: &Expr) {
            match expr {
                Expr::ErrorProp(_, span) => self.props.push(*span),
                Expr::Call(callee, _, span) if matches!(&**callee, Expr::Ident(name, _) if name == "error") => {
                    self.raises.push(*span)
                }
                Expr::Closure(_, _, span) => self.closures.push(*span),
                _ => {}
            }
        }
    }

    let mut sites = Sites::default();
    crate::walk::walk_block(body, &mut sites);
    let direct = |span: &Span| {
        !sites
            .closures
            .iter()
            .any(|closure| closure.lo <= span.lo && span.hi <= closure.hi)
    };
    let first_prop = |kind: PropKind| {
        sites
            .props
            .iter()
            .filter(|span| direct(span) && kinds.get(*span) == Some(&Some(kind)))
            .min_by_key(|span| span.lo)
            .copied()
    };
    let null = first_prop(PropKind::Null)?;
    let raise = sites
        .raises
        .iter()
        .filter(|span| direct(span))
        .min_by_key(|span| span.lo)
        .copied();
    let error = [first_prop(PropKind::Err), raise]
        .into_iter()
        .flatten()
        .min_by_key(|span| span.lo)?;
    Some((null, error))
}

impl<'a> Checker<'a> {
    /// Settle an unannotated method's precomputed return against the body the
    /// co-check just walked (see `settle_definitional_return`).
    fn settle_method_return(&mut self, key: &(String, String), body: &Block, unannotated: bool) {
        let collected = std::mem::take(&mut self.last_returns);
        if !unannotated {
            return;
        }
        if let Some(entry) = self.method_returns.get(key).cloned()
            && let Some(settled) = self.settle_definitional_return(&entry, body, collected)
        {
            self.method_returns.insert(key.clone(), settled);
        }
    }

    /// Warn that an unannotated callable's inferred return `inferred` is a
    /// nullable `Result` (callers must unwrap two layers) -- only when its own
    /// direct `!` sites inferred both layers. A nullable Result merely
    /// forwarded from an annotated callee has no mixed pair here and remains
    /// deliberate plumbing.
    fn warn_implicit_nullable_result(
        &mut self,
        signature: &CallableSignature,
        body: &Block,
        inferred: &Type,
    ) {
        if signature.ret.is_some() {
            return;
        }
        let resolved = self.resolve(inferred);
        let Type::Nullable(inner) = &resolved else {
            return;
        };
        let Type::Sum(result) = inner.as_ref() else {
            return;
        };
        if result.id != brass_hir::RESULT_TYPE_ID {
            return;
        }
        let Some((null, error)) = mixed_propagation_sites(body, &self.prop_kinds) else {
            return;
        };
        // The Err payload is almost always the prelude `Error`, whose rendered
        // substitution restates its own field layout and drowns the message.
        // The warning is about the two layers, not the payload internals, so
        // that nominal renders bare; any other error type keeps its full form.
        let error_id = self.program.prelude_type("Error").map(|info| info.id);
        let type_text = match result.result_payloads() {
            Some((ok, err)) => {
                let err_text = match err {
                    Type::Record(n) | Type::Sum(n) if Some(n.id) == error_id => {
                        n.name().to_string()
                    }
                    other => other.display(),
                };
                format!("Result<{}, {err_text}>?", ok.display())
            }
            None => resolved.display(),
        };
        self.warnings.push(TypeError {
            message: format!(
                "`{}` returns `{}`: the body propagates both null ({}) and errors ({}), so \
                 callers must unwrap two layers; convert the null with `.context(message)` or \
                 annotate the return type",
                signature.name,
                type_text,
                crate::source_location(null),
                crate::source_location(error),
            ),
            span: signature.span,
        });
    }

    #[cfg(test)]
    fn new(program: &'a Program, rows: Rc<brass_typesys::RowInfo>) -> Self {
        Self::new_with_numeric(program, rows, true)
    }

    fn new_with_numeric(
        program: &'a Program,
        rows: Rc<brass_typesys::RowInfo>,
        numeric_enabled: bool,
    ) -> Self {
        let numeric_pure_bodies = if numeric_enabled {
            binding_joins::numeric::pure::bodies(program)
        } else {
            HashSet::default()
        };
        let numeric_closed_bodies = if numeric_enabled {
            binding_joins::numeric::pure::closed_bodies(program)
        } else {
            HashSet::default()
        };
        Self {
            program,
            errors: Vec::new(),
            warnings: Vec::new(),
            channel_changes: Default::default(),
            typed: TypedProgram::default(),
            typed_seen: HashMap::default(),
            const_scopes: Vec::new(),
            next_unknown: next_unknown_after_program(program),
            self_type: None,
            self_variant: None,
            return_contexts: Vec::new(),
            return_values: Vec::new(),
            last_returns: Vec::new(),
            diverging_exprs: HashSet::default(),
            static_fold_frames: Vec::new(),
            last_static_folds: HashMap::default(),
            light_folds: HashMap::default(),
            return_literals: HashMap::default(),
            return_value_spans: HashMap::default(),
            recursion_assumptions: HashMap::default(),
            last_closure_result: None,
            conflict_site: None,
            reported_instances: HashSet::default(),
            block_value_tail: None,
            branch_expectation: None,
            tail_expectation: None,
            branch_expectation_taken: false,
            discarded_values: HashSet::default(),
            statement_values: HashSet::default(),
            type_only_read: false,
            global_defs: HashMap::default(),
            global_scopes: HashMap::default(),
            function_returns: HashMap::default(),
            method_returns: HashMap::default(),
            method_return_props: HashSet::default(),
            co_method_returns: HashMap::default(),
            co_checking: false,
            current_co_method: None,
            co_return_links: HashMap::default(),
            instantiating: HashSet::default(),
            entry_only: false,
            preparation: None,
            selection_index: None,
            item_seed: None,
            recursed: HashSet::default(),
            recursion_provisional: HashMap::default(),
            light_reads: std::cell::RefCell::new(None),
            elaboration_stack: Vec::new(),
            mutually_recursed: HashSet::default(),
            co_global_reads: HashSet::default(),
            error_sites: HashSet::default(),
            elaborations: 0,
            stats: stats::ElaborationStats::default(),
            elaboration_budget_reported: false,
            depth_capped: 0,
            completion: completion_order::CompletionGraph::default(),
            shape_constraints: HashMap::default(),
            closure_bodies: HashMap::default(),
            closure_result_bodies: HashMap::default(),
            solver: {
                // Fresh variables must not collide with the ids lowering
                // embedded in the program's resolved types (see
                // `Program::next_infer_var`): a collision would alias a fresh
                // variable with an unrelated declaration's type.
                let mut s = Solver::new();
                s.seed_var_counter(program.next_infer_var);
                s
            },
            current_module: Vec::new(),
            reported_result_shadow: HashSet::default(),
            lazy_profile: false,
            elaboration_memo: HashMap::default(),
            co_memo_suspended: false,
            co_validation: Vec::new(),
            method_scheme_revision: 0,
            method_co_seen: HashSet::default(),
            method_inventory:
                (tracing::enabled!(target: "brass::method_inventory", tracing::Level::TRACE)
                    || tracing::enabled!(target: "brass::item_inventory", tracing::Level::TRACE))
                .then(|| Box::new(co_replay::MethodInventory::default())),
            closure_memo: HashMap::default(),
            closure_memo_disabled: std::env::var("BRASS_CLOSURE_MEMO").as_deref() == Ok("off")
                || std::env::var("BRASS_MEMO_CHECK").as_deref() == Ok("1"),
            #[cfg(test)]
            closure_memo_hits: 0,
            elaboration_journals: Vec::new(),
            speculation_depth: 0,
            numeric_seed_ordinary: true,
            numeric_enabled,
            numeric: Default::default(),
            numeric_pure_spans: Rc::new(if numeric_enabled {
                std::cell::OnceCell::from(
                    program
                        .functions
                        .values()
                        .filter(|info| {
                            numeric_pure_bodies.contains(&info.symbol)
                                || numeric_closed_bodies.contains(&info.symbol)
                        })
                        .map(|info| info.decl.body.span)
                        .collect::<HashSet<_>>(),
                )
            } else {
                std::cell::OnceCell::new()
            }),
            numeric_zero_growth: false,
            fields_reflection: Default::default(),
            numeric_eligibility: Default::default(),
            numeric_pure_bodies: Rc::new(numeric_pure_bodies),
            numeric_closed_bodies: Rc::new(numeric_closed_bodies),
            instance_returns: HashMap::default(),
            keyed_tainted: HashSet::default(),
            seeded_set: None,
            generic_error_returns: HashSet::default(),
            schemes: HashMap::default(),
            fixed_array_binding: false,
            call_expected: None,
            keyed_calls: HashMap::default(),
            numeric_observations: Vec::new(),
            numeric_observed: HashSet::default(),
            keyed_observations: Vec::new(),
            call_sites: HashMap::default(),
            instance_stack: Vec::new(),
            instance_tags: HashMap::default(),
            polymorphic_recursion_reported: HashSet::default(),
            instance_typed: Vec::new(),
            instance_typed_seen: HashSet::default(),
            typeof_types: HashMap::default(),
            typeof_poisoned: HashSet::default(),
            prop_kinds: HashMap::default(),
            full_err_props: HashMap::default(),
            empty_array_elems: Vec::new(),
            init_empty_arrays: Vec::new(),
            sum_view_seen: HashMap::default(),
            sum_view_poisoned: HashSet::default(),
            lift_kinds: HashMap::default(),
            lift_poisoned: HashSet::default(),
            narrowing_kills: Vec::new(),
            tested_field_reads: HashMap::default(),
            next_narrowing: 0,
            narrowing_facts: Rc::default(),
            loop_frames: Vec::new(),
            null_test_operand: false,
            discarded_walks: 0,
            rows,
            const_calls: Rc::default(),
            view_args: HashSet::default(),
            lift_errs: HashSet::default(),
            sum_views: HashMap::default(),
            fields_loops: HashMap::default(),
            fields_observations: HashMap::default(),
            type_names: HashMap::default(),
            closure_bindings: HashMap::default(),
            generalizable: Rc::new(brass_hir::generalized_closure_bindings(program)),
            closure_schemes: HashMap::default(),
            application_probe: None,
            closure_instantiations: Vec::new(),
            closure_param_vars: HashSet::default(),
            undetermined_closures: Vec::new(),
            function_values: HashMap::default(),
            null_props: HashSet::default(),
            in_entry_main: false,
            static_divergence: false,
            type_tests: HashMap::default(),
            type_test_poisoned: HashSet::default(),
            type_test_holes: HashSet::default(),
            fields_probe_depth: 0,
        }
    }

    fn primitive_static_type(&self, tname: &str, method: &str) -> Option<Type> {
        primitive_static_return(tname, method)
    }

    fn fresh_unknown(&mut self) -> Type {
        let id = self.next_unknown;
        self.next_unknown += 1;
        Type::Unknown(id)
    }

    /// `ty` with every inference variable replaced by a fresh one. A type read
    /// out of a precompute table describes ONE shared instantiation, so a site
    /// that uses it must take its own copy or it will constrain every other site
    /// that reads the same entry.
    fn freshen(&mut self, ty: &Type) -> Type {
        let next = &mut self.next_unknown;
        let mut fresh = || {
            let id = *next;
            *next += 1;
            Type::Unknown(id)
        };
        brass_hir::freshen_unknowns(ty, &mut fresh)
    }

    /// Judge the empty array literals recorded since `from` (see
    /// `empty_array_elems`), then forget them. With `body` -- the span of a
    /// body checked at concrete inputs -- a literal inside it whose element
    /// type nothing fixed (no annotation, no push, no use that pins it) is an
    /// error: the array has no element type to be built with. Literals of
    /// other bodies elaborated meanwhile are judged by their own pass.
    fn report_unfixed_empty_arrays(&mut self, from: usize, body: Option<Span>) {
        let recorded: Vec<(Span, Type)> = self.empty_array_elems.drain(from..).collect();
        let Some(body) = body else {
            return;
        };
        for (span, elem) in recorded {
            if span.lo >= body.lo && span.hi <= body.hi {
                self.report_unfixed_empty_array(span, &elem);
            }
        }
    }

    /// Judge the empty array literals of module top-level code (see
    /// `check_init_body`) once every body is checked: a global's element type
    /// may be fixed by a function that pushes into it.
    fn report_unfixed_init_arrays(&mut self) {
        for (span, elem) in std::mem::take(&mut self.init_empty_arrays) {
            self.report_unfixed_empty_array(span, &elem);
        }
    }

    fn report_unfixed_empty_array(&mut self, span: Span, elem: &Type) {
        if self.resolve(elem).is_unknown() {
            self.errors.push(TypeError {
                message: "the element type of this empty array literal is never fixed: \
                          annotate the binding (e.g. `let xs: int32[] = []`) or push a value \
                          into it"
                    .to_string(),
                span,
            });
        }
    }

    /// A fresh inference variable for the element type of a bare `[]` literal,
    /// classified so that an unconstrained empty array escaping into a required
    /// position is reported instead of silently unifying with the required type.
    fn fresh_empty_array_elem(&mut self) -> Type {
        let id = self.next_unknown;
        self.next_unknown += 1;
        self.solver.record_var(id, InferenceVarKind::EmptyArrayElem);
        Type::Unknown(id)
    }

    /// A fresh inference variable for the `Ok` payload of a function that only
    /// returns `error(...)`. The payload type is unknowable, so it is reported
    /// if it escapes into a required position rather than silently unifying.
    fn fresh_error_only_ok(&mut self) -> Type {
        let id = self.next_unknown;
        self.next_unknown += 1;
        self.solver.record_var(id, InferenceVarKind::ErrorOnlyOk);
        Type::Unknown(id)
    }

    /// A fresh inference variable for the `Ok` payload of an instantiation
    /// that can only fail (see `InferenceVarKind::UninhabitedOk`).
    fn fresh_uninhabited_ok(&mut self) -> Type {
        let id = self.next_unknown;
        self.next_unknown += 1;
        self.solver.record_var(id, InferenceVarKind::UninhabitedOk);
        Type::Unknown(id)
    }

    fn check_expr(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        let ty = self.check_expr_inner(e, scopes);
        if self.numeric.probing {
            self.note_numeric_expression(e, scopes);
        }
        self.record_inferred_expr_type(e, &ty);
        ty
    }

    fn record_expr_type(&mut self, expr: &Expr, ty: &Type) {
        let constness = self.expr_constness(expr);
        self.record_expr_type_with(expr, ty, constness);
    }

    /// Record a pattern binding's type at the binding identifier's own span, as
    /// a typed `Ident` entry. The binding name is not an expression, so without
    /// this the declaration site has no typed node and hover falls back to
    /// borrowing a *use*'s type -- wrong when the annotated binding type differs
    /// from the initializer's (`let b: int64 = an_int32`), and absent entirely
    /// for an unused binding. The type may still be open here; `finalize_typed`
    /// re-resolves it against the final substitution like every other entry.
    fn record_binding(&mut self, name: &str, span: Span, ty: &Type) {
        let ty = self.resolve(ty);
        self.record_typed(
            brass_hir::TypedExprKind::Ident(name.to_string()),
            span,
            ty,
            Constness::Unknown,
        );
    }

    fn record_expr_type_with(&mut self, expr: &Expr, ty: &Type, constness: Constness) {
        let ty = self.resolve(ty);
        if matches!(ty, Type::Never) {
            self.diverging_exprs.insert(expr.span());
        } else {
            self.diverging_exprs.remove(&expr.span());
        }
        let ty = if constness == Constness::Const {
            Type::ConstOf(Box::new(ty))
        } else {
            ty
        };
        self.record_typed(
            brass_hir::TypedExprKind::from_expr(expr),
            expr.span(),
            ty,
            constness,
        );
    }

    /// The unambiguous closure-parameter observations, resolved against the
    /// final substitution (later unification may have pinned parts of an
    /// observed type). Conflict-poisoned and still-open observations are
    /// dropped; consumers fall back to rendering the variable as unknown.
    fn finalized_closure_bindings(&self) -> HashMap<u32, Type> {
        self.closure_bindings
            .iter()
            .filter_map(|(var, ty)| {
                let ty = self.solver.resolve(ty.as_ref()?);
                (!matches!(ty, Type::Unknown(_))).then_some((*var, ty))
            })
            .collect()
    }

    /// Move the `len` typed entries recorded from `start` behind every entry
    /// recorded after them, keeping each group's own order. The editor
    /// features read the FIRST entry at a span as the generic view of the
    /// body it belongs to -- the one its definitional pass records -- so the
    /// module initializers' call-site elaborations of those bodies, checked
    /// first because they type the globals, must not stay in front of it.
    fn defer_typed_entries(&mut self, start: usize, len: usize) {
        if len == 0 {
            return;
        }
        let total = self.typed.expressions.len();
        self.typed.expressions[start..].rotate_left(len);
        self.typed_seen.clear();
        for (index, e) in self.typed.expressions.iter().enumerate() {
            let hash = journal::typed_hash(&e.kind, e.span, &e.ty, e.constness);
            self.typed_seen.entry(hash).or_default().push(index);
        }
        // The instance observations name typed entries by index: follow the
        // rotation.
        let moved = |index: usize| match index {
            i if i < start => i,
            i if i < start + len => i + (total - start - len),
            i => i - len,
        };
        for entry in &mut self.instance_typed {
            entry.index = moved(entry.index as usize) as u32;
        }
        self.instance_typed_seen = self.instance_typed.iter().cloned().collect();
    }

    /// Re-resolve every recorded expression type against the final substitution.
    /// Run once after all checking, so a type recorded before one of its
    /// variables was pinned (an array element fixed by a later `push`) still
    /// reflects the solved type; hover and the other editor features read the
    /// typed program directly. `resolve` is deep --
    /// it follows variables nested inside arrays, function types, and a nominal's
    /// substitution (so a `HashMap`'s `_entries` element pinned by a later `push`
    /// shows its concrete type) -- and preserves the `ConstOf` wrapper, so
    /// constness is unchanged.
    fn finalize_typed(&mut self) {
        self.report_fields_conflicts();
        self.settle_sum_views();
        let resolved: Vec<Type> = self
            .typed
            .expressions
            .iter()
            .map(|e| self.solver.resolve(&e.ty))
            .collect();
        for (e, ty) in self.typed.expressions.iter_mut().zip(resolved) {
            e.ty = ty;
        }
    }

    fn expr_constness(&self, expr: &Expr) -> Constness {
        match expr {
            Expr::Ident(name, _) if self.is_const_binding(name) => Constness::Const,
            Expr::Field(base, _, _) | Expr::Index(base, _, _)
                if self.expr_constness(base) == Constness::Const =>
            {
                Constness::Const
            }
            _ => Constness::Unknown,
        }
    }

    fn is_const_binding(&self, name: &str) -> bool {
        self.const_scopes
            .iter()
            .rev()
            .any(|scope| scope.contains(name))
    }

    fn bind_const_pattern(&mut self, pat: &Pattern) {
        let mut names = Vec::new();
        self.collect_const_bindings(pat, &mut names);
        if let Some(scope) = self.const_scopes.last_mut() {
            scope.extend(names);
        }
    }

    fn collect_const_bindings(&self, pat: &Pattern, out: &mut Vec<String>) {
        match pat {
            Pattern::Binding(name, qualifier, _) => {
                if qualifier.is_none() && !self.is_unit_variant_name(name) {
                    out.push(name.clone());
                }
            }
            Pattern::Record(_, _, fields, _) => {
                for field in fields {
                    if let Some(pat) = &field.pat {
                        self.collect_const_bindings(pat, out);
                    } else {
                        out.push(field.name.clone());
                    }
                }
            }
            Pattern::Array(items, _) => {
                for item in items {
                    self.collect_const_bindings(item, out);
                }
            }
            Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
        }
    }

    /// Whether `a` and `b` unify on their own, or one is structurally
    /// compatible with the other (either direction). A probe: nothing is
    /// committed to the solver.
    fn can_unify(&self, a: &Type, b: &Type) -> bool {
        Subst::new().unify(a, b).is_ok()
            || crate::structural::types_compatible(self.program, a, b)
            || crate::structural::types_compatible(self.program, b, a)
    }

    /// Resolve a type through the solver's substitution, following solved
    /// inference variables (including nested ones); a variable nothing has
    /// bound is returned as it is.
    fn resolve(&self, ty: &Type) -> Type {
        self.solver.resolve(ty)
    }

    /// Follow the outer inference-variable chain without resolving components.
    /// This is for control flow that only inspects the head constructor.
    fn resolve_head(&self, ty: &Type) -> Type {
        self.solver.resolve_head(ty)
    }
}

mod closure_instances;
