//! Local static type checks.
//!
//! This pass intentionally remains conservative around genuinely polymorphic or
//! structurally inferred code, but every type that is explicit in source is
//! enforced before execution. It checks annotations, constructor fields,
//! annotated function/method calls, nullable use-before-check, and operators.
//! Unknown values are represented with unification variables so uncertain code
//! can still be deferred to the runtime without accepting contradictions against
//! explicit types.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use brass_hir::{
    CallableSignature, Constness, FloatKind, FunInfo, IntKind, ModuleInit, NominalType, ParamInfo,
    Program, SchemeMethod, Substitution, Type, TypeInfo, TypeKind, TypeScheme, TypedProgram,
    int_literal_kind, peel_modes,
};
use brass_parser::Span;
use brass_parser::ast::*;
use brass_typesys::{common_numeric_type, numeric_flows_into};

use crate::TypeError;
use crate::constraint::ShapeConstraint;
use crate::narrow;
use crate::solver::{InferenceVarKind, Solver};
use crate::stream::{self, StreamCtl};
use crate::unify::Subst;

mod assign;
mod builtins;
mod call;
mod expr;
pub(crate) mod helpers;
mod instantiate;
mod light;
mod literals;
mod lookup;
mod patterns;
mod precompute;
mod resolve;

use assign::{common_nullable_type, integer_literal_fits};
use builtins::primitive_static_return;
use helpers::{
    Pipe, apply_method_substitution, apply_nominal_substitution, assign_binop,
    block_always_returns, block_rebinds, closure_write_targets_block, collect_closure_writes_stmt,
    const_index, contains_typeof, env_from_scopes, expr_always_returns, expr_may_branch,
    field_substitution_key, int_fits_kind, is_concrete_primitive, is_concrete_type,
    is_maybe_indexable, is_null_comparison, is_result_return_type, is_runtime_builtin_value,
    is_self_expr, literal_pattern_matches, literal_pattern_type, method_param_substitution_key,
    method_return_substitution_key, next_unknown_after_program, numeric_literal_repr,
    param_expected_type, param_is_location, peel_ref_mut, peel_value_wrappers, required_arg_count,
    same_nominal_instance, stmt_may_branch, substitute_self,
};

type ScopeStack = Vec<HashMap<String, Type>>;

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

#[derive(Clone)]
struct ResolvedMethod {
    qualifier: String,
    self_type: String,
    signature: CallableSignature,
    method: Method,
}

/// Propagation signals the light pass collects while walking a body: the
/// `Err` payload types of `error(...)` / Result-operand `expr!` sites, and
/// the spans of nullable-operand `expr!` sites (whose null case returns null,
/// making the enclosing callable's return type nullable).
#[derive(Default)]
pub(super) struct LightProps {
    pub(super) errors: Vec<(Type, Span)>,
    pub(super) nulls: Vec<Span>,
}

#[derive(Clone)]
enum ReturnContext {
    Inferred,
    Explicit(Type),
}

/// The pieces of a callable whose first parameter is filled by a receiver,
/// cloned out of a `FunInfo` so the call can be checked while the checker is
/// mutably borrowed. Shared by UFCS and primitive-method dispatch.
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

pub fn check(program: &Program) -> Vec<TypeError> {
    analyze(program).errors
}

/// The cross-module tables a CONTEXT-ONLY analysis (every module except the
/// entry) leaves behind, fully resolved against its own solver. Applied to a
/// later run as a seed, they let that run check ONLY the entry module: the
/// context's schemes, inferred returns, and globals are read from here instead
/// of being re-derived, which is where a library-heavy program spends almost
/// all of its inference time.
///
/// The tables are span-free by construction (keyed by symbol, type name, or
/// module path), so they survive the entry file changing size. Inference
/// VARIABLE ids are not portable -- a consuming run mints its own -- so
/// [`ContextTables::remapped`] renumbers every open variable into the consumer's
/// namespace first, one map across all tables so linked entries stay linked.
#[derive(Clone, Debug, Default, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ContextTables {
    pub schemes: HashMap<String, TypeScheme>,
    pub function_returns: HashMap<String, Type>,
    pub method_returns: HashMap<(String, String), Type>,
    pub method_return_props: HashSet<(String, String)>,
    pub co_method_returns: HashMap<(String, String), Type>,
    pub global_defs: HashMap<Vec<String>, HashMap<String, Type>>,
    /// One past the highest variable id the tables mention.
    pub next_var: u32,
    /// Every bare top-level name the context defines. An entry defining one of
    /// these would QUALIFY the context's symbols in the combined program,
    /// detaching every table key -- the consumer must bail to an unseeded run.
    pub bare_names: HashSet<String>,
    /// The module paths these tables cover. `None` means the whole context
    /// (every module but the entry) -- the full-seed case. `Some` marks a
    /// PARTIAL seed (see [`ContextTables::retain_modules`]): only the listed
    /// modules skip their passes; the rest re-analyze against the seed.
    pub covered: Option<HashSet<Vec<String>>>,
    /// The program-wide storage symbols and nominal IDs these tables were
    /// built against. Both can change when an otherwise unrelated module
    /// adds a declaration, so partial reuse requires an exact match.
    program_identity: ContextProgramIdentity,
}

/// The parts of HIR identity embedded in context table keys and values.
#[derive(Clone, Debug, Default, PartialEq, serde::Serialize, serde::Deserialize)]
struct ContextProgramIdentity {
    functions: std::collections::BTreeMap<String, Vec<String>>,
    types: std::collections::BTreeMap<String, (Vec<String>, i32)>,
}

impl ContextProgramIdentity {
    fn of(program: &Program) -> Self {
        Self {
            functions: program
                .functions
                .iter()
                .map(|(symbol, info)| (symbol.clone(), info.module.clone()))
                .collect(),
            types: program
                .types
                .iter()
                .map(|(symbol, info)| (symbol.clone(), (info.module.clone(), info.id)))
                .collect(),
        }
    }
}

impl ContextTables {
    /// The tables with every inference variable renumbered densely from `base`,
    /// and the first id past them. One mapping is applied across all tables, so
    /// a variable shared between entries (a scheme parameter appearing in a
    /// method return) stays shared.
    pub fn remapped(&self, base: u32) -> (ContextTables, u32) {
        use std::collections::BTreeMap;
        let mut vars: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
        for scheme in self.schemes.values() {
            vars.extend(scheme.params.iter().copied());
            for (_, t) in &scheme.fields {
                vars.extend(brass_hir::type_vars(t));
            }
            for m in scheme.methods.values() {
                for (_, t) in &m.params {
                    vars.extend(brass_hir::type_vars(t));
                }
                vars.extend(brass_hir::type_vars(&m.ret));
            }
        }
        for t in self
            .function_returns
            .values()
            .chain(self.method_returns.values())
            .chain(self.co_method_returns.values())
            .chain(self.global_defs.values().flat_map(|defs| defs.values()))
        {
            vars.extend(brass_hir::type_vars(t));
        }
        let map_id: HashMap<u32, u32> = vars
            .iter()
            .enumerate()
            .map(|(i, v)| (*v, base + i as u32))
            .collect();
        let subst: BTreeMap<u32, Type> = map_id
            .iter()
            .map(|(old, new)| (*old, Type::Unknown(*new)))
            .collect();
        let re = |t: &Type| brass_hir::substitute_vars(t, &subst);
        let out = ContextTables {
            schemes: self
                .schemes
                .iter()
                .map(|(name, scheme)| {
                    let mut s = scheme.clone();
                    s.params = s.params.iter().map(|v| map_id[v]).collect();
                    s.fields = s.fields.iter().map(|(n, t)| (n.clone(), re(t))).collect();
                    for m in s.methods.values_mut() {
                        m.params = m.params.iter().map(|(n, t)| (n.clone(), re(t))).collect();
                        m.ret = re(&m.ret);
                    }
                    (name.clone(), s)
                })
                .collect(),
            function_returns: self
                .function_returns
                .iter()
                .map(|(k, t)| (k.clone(), re(t)))
                .collect(),
            method_returns: self
                .method_returns
                .iter()
                .map(|(k, t)| (k.clone(), re(t)))
                .collect(),
            method_return_props: self.method_return_props.clone(),
            co_method_returns: self
                .co_method_returns
                .iter()
                .map(|(k, t)| (k.clone(), re(t)))
                .collect(),
            global_defs: self
                .global_defs
                .iter()
                .map(|(m, defs)| {
                    (
                        m.clone(),
                        defs.iter().map(|(n, t)| (n.clone(), re(t))).collect(),
                    )
                })
                .collect(),
            next_var: base + map_id.len() as u32,
            bare_names: self.bare_names.clone(),
            covered: self.covered.clone(),
            program_identity: self.program_identity.clone(),
        };
        let next = out.next_var;
        (out, next)
    }

    /// Restrict these tables to the entries owned by `keep` modules,
    /// attributing each entry through `program` (a context program over the
    /// same modules): a function return by its symbol's defining module, a
    /// scheme and the method tables by the type's, `global_defs` by its own
    /// key. The identity guard below rejects a program whose storage symbols
    /// or nominal IDs changed, so every retained key still names the same HIR
    /// item. `bare_names` is kept WHOLE: the declaration set is unchanged,
    /// and shrinking it would weaken the consumer's collision bail.
    /// `next_var` is kept too -- the retained entries keep
    /// their one coherent variable space, and the re-analysis of the dropped
    /// modules allocates past it. Sound because a retained (clean) module
    /// cannot reference a dropped (dirty) one: references follow imports,
    /// and the dirty closure includes every transitive importer.
    ///
    /// Returns `false` without changing the tables when the current program's
    /// storage symbols or nominal IDs differ. Those identities are global to
    /// lowering rather than module-local, so even an unchanged module cannot
    /// safely retain tables across such a change.
    pub fn retain_modules(&mut self, program: &Program, keep: &HashSet<Vec<String>>) -> bool {
        if self.program_identity != ContextProgramIdentity::of(program) {
            return false;
        }
        let fn_kept = |sym: &String| {
            program
                .functions
                .get(sym)
                .is_some_and(|f| keep.contains(&f.module))
        };
        let ty_kept = |name: &String| {
            program
                .types
                .get(name)
                .is_some_and(|t| keep.contains(&t.module))
        };
        self.function_returns.retain(|sym, _| fn_kept(sym));
        self.schemes.retain(|name, _| ty_kept(name));
        self.method_returns.retain(|(ty, _), _| ty_kept(ty));
        self.co_method_returns.retain(|(ty, _), _| ty_kept(ty));
        self.method_return_props.retain(|(ty, _)| ty_kept(ty));
        self.global_defs.retain(|module, _| keep.contains(module));
        self.covered = Some(keep.clone());
        true
    }
}

pub struct Inference {
    pub errors: Vec<TypeError>,
    pub typed: TypedProgram,
    /// Per record-type generalized scheme (its inferred type parameters and the
    /// field/method signatures over them), keyed by the type's source name. Read
    /// by the language server to render a method generically; see `build_schemes`.
    pub schemes: HashMap<String, TypeScheme>,
    /// Spans of anonymous structural arguments that passed the callee-row check
    /// for a view-eligible parameter (see `brass_typesys::rows`). MIR lowering
    /// converts exactly these arguments into the parameter's view.
    pub view_args: HashSet<Span>,
    /// Expressions accepted as a declared sum subtype at a flow site, keyed by
    /// the value expression's span, mapped to the PARENT sum's table symbol.
    /// MIR lowering rebuilds exactly these values as the parent (SumView).
    pub sum_views: HashMap<Span, Type>,
    /// `expr!` sites whose propagated Err payload is re-raised wrapped into
    /// the prelude `Error` (gaining the site's location); MIR's propagation
    /// arm rebuilds the value.
    pub lift_errs: HashSet<Span>,
    /// Field lists of `for f in fields(x)` loops, keyed by the loop statement's
    /// span. The checker resolved `x`'s record type and checked one expanded
    /// copy per field; MIR lowering unrolls the same copies from this list.
    pub fields_loops: HashMap<Span, Vec<String>>,
    /// Resolved type names of `typeof(x)` calls, keyed by the call span. MIR
    /// lowering replaces each such call with this string constant.
    pub type_names: HashMap<Span, String>,
    /// Reflective (`-> infer!`) method calls keyed by the caller's expectation:
    /// call span -> (receiver type name, method, target key). The driver
    /// generates a concrete specialization per (receiver, method, key) and
    /// rewrites the call to it.
    pub keyed_calls: HashMap<Span, (String, String, Type)>,
    /// Resolved binding types of local annotations that contain a `typeof(v)`,
    /// keyed by the annotation's span; MIR seeds the slot from this (the type
    /// is not recoverable from a `null`/inferred initializer alone).
    pub typeof_types: HashMap<Span, Type>,
    /// Spans of `expr!` operators whose operand is a nullable rather than a
    /// `Result`: the value case unwraps, the null case propagates as
    /// `Result.Null`. MIR lowering emits the presence-test shape for these.
    pub null_props: HashSet<Span>,
    /// The inferred return type of every free function, keyed by symbol and
    /// resolved. A function with no `-> T` annotation has none in its signature,
    /// so this is the only record of what the checker settled on; the language
    /// server renders it.
    pub function_returns: HashMap<String, Type>,
    /// The same for methods, keyed by (type name, method name). Covers both an
    /// unannotated return and the open Err payload of a `T!` one.
    pub method_returns: HashMap<(String, String), Type>,
    /// This run's cross-module tables, extracted for reuse as a context seed
    /// (see [`ContextTables`]); meaningful to reapply only when this was a
    /// context-only, error-free run.
    pub context_tables: ContextTables,
}

/// Check every type's method bodies in the shared per-type environment. Binding
/// `self` to the bare type makes a type's methods share one field variable, so
/// the bodies' stores and reads link each field's element to the methods'
/// parameter and return variables -- the linkage [`Checker::build_schemes`] then
/// generalizes.
impl Checker<'_> {
    /// Load remapped context tables into this checker and confine the per-item
    /// passes to the entry module. The caller has already renumbered the
    /// tables' variables past this checker's counter.
    fn apply_seed(&mut self, seed: ContextTables, next_var: u32) {
        self.schemes = seed.schemes;
        self.function_returns = seed.function_returns;
        self.method_returns = seed.method_returns;
        self.method_return_props = seed.method_return_props;
        self.co_method_returns = seed.co_method_returns;
        self.global_defs = seed.global_defs;
        self.seeded_set = seed.covered;
        self.next_unknown = self.next_unknown.max(next_var);
        self.entry_only = true;
    }

    /// Whether `module` was covered by the applied seed: anything but the
    /// entry (whose module path is always `main`) for a full seed, or the
    /// seed's own module list for a partial one (an incremental context
    /// rebuild -- the uncovered modules get real passes here).
    fn seeded_module(&self, module: &[String]) -> bool {
        if !self.entry_only {
            return false;
        }
        match &self.seeded_set {
            Some(set) => set.contains(module),
            None => !matches!(module, [m] if m == "main"),
        }
    }
}

fn check_method_bodies(checker: &mut Checker, program: &Program) {
    let mut perf = brass_utils::PerfLog::start("typeck/method-body");
    checker.co_checking = true;
    for t in program.types.values() {
        // A seeded run reads the context's schemes and co-checked returns from
        // the seed; only the entry's own types are co-checked here.
        if checker.seeded_module(&t.module) {
            continue;
        }
        checker.current_module = t.module.clone();
        match &t.kind {
            TypeKind::Record { methods, .. } => {
                for m in methods.values() {
                    // A reflective `-> infer!` template has no fixed body type;
                    // it is specialized per key by the driver, so skip it here.
                    if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                        continue;
                    }
                    if let Some(body) = &m.decl.body {
                        let m_started = std::time::Instant::now();
                        let mut scopes = checker.signature_scopes(&m.signature.params);
                        let ret = m.signature.ret_ty.clone();
                        checker.current_co_method =
                            Some((t.name.clone(), m.signature.name.clone()));
                        let full =
                            checker.check_block_with_self(body, &mut scopes, ret.as_ref(), &t.name);
                        checker.current_co_method = None;
                        perf.item(
                            format!("{}.{}", t.name, m.signature.name),
                            m_started.elapsed(),
                        );
                        // Keep the return the full check reconciled here, in the
                        // shared per-type environment, for scheme generalization
                        // (see `co_method_returns`). A propagating body's shape
                        // (`Result`/`?`) only the light assembly builds, so it
                        // keeps its precomputed type.
                        let key = (t.name.clone(), m.signature.name.clone());
                        if let Some(full) = full
                            && !checker.method_return_props.contains(&key)
                        {
                            checker.co_method_returns.insert(key, full);
                        }
                    }
                }
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    for m in v.methods.values() {
                        if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                            continue;
                        }
                        if let Some(body) = &m.decl.body {
                            let mut scopes = checker.signature_scopes(&m.signature.params);
                            let ret = m.signature.ret_ty.clone();
                            checker.check_block_with_self_variant(
                                body,
                                &mut scopes,
                                ret.as_ref(),
                                &t.name,
                                &v.name,
                            );
                        }
                    }
                }
            }
        }
    }
    checker.co_checking = false;
    perf.report();
}

/// Generalize every record into a [`TypeScheme`] on a throwaway checker, so the
/// real pass has the schemes in hand *while* it checks method bodies.
///
/// A scheme can only be built after the method bodies have been checked (that is
/// what links a field's element type to its methods' parameter variables), so the
/// real pass cannot build them any earlier than it already does. But a method
/// body that calls ANOTHER type's method needs that type's scheme to pin the
/// call's parameters from the receiver -- `map.set(k, 100)` on a width-pinned
/// `HashMap` types the bare literal as the map's `int64`, not the literal's
/// default `int32`. Until the schemes existed only from the function-body phase
/// onward, so the same call inside a method body typed the literal from the
/// argument and clashed with the receiver's slot.
///
/// The preliminary run's diagnostics and solver are discarded; only the schemes
/// are kept, and the real pass rebuilds them once its own method bodies are done.
/// It therefore does only the work a scheme needs: the declaration validation is
/// pure diagnostics, and the second `precompute_method_returns` exists to converge
/// cross-type *return* chains, which generalization does not read -- both are the
/// real pass's job.
fn seed_schemes(
    program: &Program,
    seed: Option<&(ContextTables, u32)>,
) -> HashMap<String, TypeScheme> {
    let mut pre = Checker::new(program);
    if let Some((tables, next)) = seed {
        pre.apply_seed(tables.clone(), *next);
    }
    pre.precompute_global_bindings();
    pre.precompute_function_returns();
    pre.precompute_method_returns();
    check_method_bodies(&mut pre, program);
    pre.build_schemes()
}

pub fn analyze(program: &Program) -> Inference {
    analyze_with(program, None)
}

/// [`analyze`], optionally seeded with the tables of a prior CONTEXT-ONLY run
/// (see [`ContextTables`]): the seeded modules' per-item passes are skipped and
/// their schemes, inferred returns, and globals are read from the seed, so the
/// run costs roughly what checking the entry module alone costs.
pub fn analyze_with(program: &Program, seed: Option<&ContextTables>) -> Inference {
    analyze_inner(program, seed, None).0
}

/// [`analyze_with`] with optional streaming control (the lazy-check
/// pipeline): with a [`StreamCtl`], bodies are checked in an execution-first
/// order -- module initializers, then `main`, then the remaining functions,
/// reprioritized between bodies by the scheduler's requests -- and a channel
/// delta is emitted after each body. Without one, the body order is the
/// eager pipeline's. The second return value is the terminal delta (flushed
/// after the finalize re-resolution), for the caller to emit once the
/// remaining whole-program passes are done.
pub(crate) fn analyze_inner(
    program: &Program,
    seed: Option<&ContextTables>,
    mut ctl: Option<&mut StreamCtl>,
) -> (Inference, Option<stream::ChannelDelta>) {
    let phase = |name: &'static str, at: std::time::Instant| {
        brass_utils::perf_phase(name, at.elapsed());
    };
    // One remapping serves both checkers below, so the preliminary scheme pass
    // and the real pass agree on every seeded variable id.
    let remapped = seed.map(|s| s.remapped(next_unknown_after_program(program)));
    let t = std::time::Instant::now();
    let seeded = seed_schemes(program, remapped.as_ref());
    phase("typeck/seed-schemes", t);
    let mut checker = Checker::new(program);
    checker.lazy_profile = ctl.is_some();
    if checker.lazy_profile {
        checker.keyed_tainted = crate::taint::keyed_reachable(program);
    }
    if let Some((tables, next)) = &remapped {
        checker.apply_seed(tables.clone(), *next);
    }
    checker.schemes = seeded;
    let t = std::time::Instant::now();
    checker.validate_param_declarations();
    checker.precompute_global_bindings();
    checker.precompute_function_returns();
    // The method pass runs twice: a method's inferred return may depend on
    // another type's method (`Tcp.close` propagating `File.close`), and the
    // second pass sees every first-pass entry, so cross-type chains converge.
    checker.precompute_method_returns();
    checker.precompute_method_returns();
    // The free functions were inferred before any method return existed (the
    // method pass needs theirs, so it cannot go first), which leaves a function
    // whose value flows OUT of a method call with nothing to read: `http`'s
    // `fetch` returns `client.fetch(path)`. Re-infer them now that the methods
    // have converged -- and re-run the methods once more over the result, so a
    // method reading a function that only just resolved (`QueryPair.parse_all`
    // propagating `_decode_form`, which propagates `percent.decode`) sees it.
    checker.refresh_function_returns();
    checker.precompute_method_returns();
    checker.precompute_method_returns();
    phase("typeck/precompute", t);
    // Check each type's method bodies, then generalize each record type into a
    // scheme. Generalizing before the function bodies are checked makes the
    // schemes available at call sites (a function instantiates a method's scheme
    // to type the call's result) and keeps the generic field variable read here
    // free of any concrete use. The bodies below are checked against the seeded
    // schemes; this rebuild replaces them with the ones this pass linked.
    let t = std::time::Instant::now();
    check_method_bodies(&mut checker, program);
    checker.schemes = checker.build_schemes();
    phase("typeck/method-bodies", t);
    if let Some(ctl) = ctl.as_deref_mut() {
        let delta = flush_delta(&checker, &mut ctl.state, false);
        ctl.sched.emit(stream::CheckEvent::ContextReady(delta));
    }

    match ctl.as_deref_mut() {
        // The eager order: every function body, then the module initializers.
        None => {
            let mut perf = brass_utils::PerfLog::start("typeck/fn-bodies");
            for (symbol, f) in &program.functions {
                // Context bodies were checked by the run that produced the seed;
                // their call-site behavior is still exact, because a call from the
                // entry re-elaborates the callee body at the call's own types.
                if checker.seeded_module(&f.module) {
                    continue;
                }
                let fn_started = std::time::Instant::now();
                check_function_body(&mut checker, symbol, f);
                perf.item(symbol.clone(), fn_started.elapsed());
            }
            perf.report();
            checker.in_entry_main = false;

            let t = std::time::Instant::now();
            checker.const_scopes = vec![HashSet::new()];
            for init in &program.inits {
                check_init_body(&mut checker, init);
            }
            checker.const_scopes.clear();
            phase("typeck/inits", t);
        }
        // The streaming (execution-first) order: initializers, then `main`,
        // then the remaining functions, with the scheduler's priority
        // requests jumping the queue between bodies. Body results are
        // order-tolerant by construction (the eager order is a HashMap's),
        // so the reorder changes when a body's entries become available,
        // not what they end up being.
        Some(ctl) => {
            // Method bodies were checked in the shared phase above; their
            // matches get the same early exhaustiveness verdict bodies get
            // below, so a broken method on the execution path reports
            // deterministically (the terminal whole-program pass may never
            // run under a stopped lazy run).
            for info in program.types.values() {
                let mut method_bodies: Vec<&Block> = Vec::new();
                match &info.kind {
                    TypeKind::Record { methods, .. } => {
                        method_bodies.extend(methods.values().filter_map(|m| m.decl.body.as_ref()));
                    }
                    TypeKind::Sum { variants } => {
                        for v in variants {
                            method_bodies
                                .extend(v.methods.values().filter_map(|m| m.decl.body.as_ref()));
                        }
                    }
                }
                for body in method_bodies {
                    let errs = crate::exhaustive::check_block(program, &checker.typed, body);
                    checker.errors.extend(errs);
                }
            }
            // Execution runs every module initializer before `main`, so the
            // inits are the entry code the lazy driver needs first, in
            // execution (module-load) order.
            let t = std::time::Instant::now();
            checker.const_scopes = vec![HashSet::new()];
            for (i, init) in program.inits.iter().enumerate() {
                // A resumed run's snapshot settled the leading inits: their
                // delivered state was seeded, so announce and move on.
                if i < ctl.skip_inits {
                    ctl.sched.emit(stream::CheckEvent::BodyChecked(
                        stream::BodyId::Init(i),
                        stream::ChannelDelta::default(),
                    ));
                    continue;
                }
                check_init_body(&mut checker, init);
                let errs = crate::exhaustive::check_stmts(program, &checker.typed, &init.stmts);
                checker.errors.extend(errs);
                let delta = flush_delta(&checker, &mut ctl.state, false);
                ctl.sched.emit(stream::CheckEvent::BodyChecked(
                    stream::BodyId::Init(i),
                    delta,
                ));
            }
            checker.const_scopes.clear();
            phase("typeck/inits", t);

            // `main` first, the rest sorted so the static order is
            // deterministic. Seeded (context) bodies skip the check like in
            // the eager order but still emit their event immediately: the
            // event means "this body is settled", and a seeded body is --
            // its entries stream in through the re-elaboration a caller's
            // own check performs. Without the event, a consumer waiting on
            // a context function would wait forever.
            let mut queue: std::collections::VecDeque<String> = {
                let mut symbols: Vec<String> = program.functions.keys().cloned().collect();
                symbols.sort();
                if let Some(pos) = symbols.iter().position(|s| s == "main") {
                    let main = symbols.remove(pos);
                    symbols.insert(0, main);
                }
                symbols.into()
            };
            let mut done: HashSet<String> = HashSet::new();
            // The concrete argument types each priority request carried: the
            // demanded body is checked at ITS INSTANCE (see
            // `check_function_body_at`) rather than the open signature frame.
            // A queue body without a request keeps the definitional pass.
            let mut demanded_at: HashMap<String, Vec<Type>> = HashMap::new();
            // Bodies the consumer explicitly asked for. These are the only
            // ones checked while the scheduler is paused; `main` counts as
            // requested (the gate waits on it without sending a request).
            let mut priority: HashSet<String> = HashSet::new();
            priority.insert("main".to_string());
            let mut perf = brass_utils::PerfLog::start("typeck/fn-bodies");
            loop {
                // The consumer no longer needs anything (its program ended):
                // stop at the body boundary. What was checked stays reported;
                // the complete verdict is the eager pipeline's job.
                if ctl.sched.stopped() {
                    break;
                }
                // Priority requests land at the front in request order; a
                // request for an unknown or already-checked symbol is spent.
                for request in ctl.sched.drain_requests().into_iter().rev() {
                    let fresh = !done.contains(&request.symbol)
                        && program.functions.contains_key(&request.symbol);
                    // A request naming a snapshot-settled body means the
                    // consumer found its cached state insufficient, so the
                    // real pass runs after all.
                    let revived = !fresh && ctl.skip_fns.remove(&request.symbol);
                    if revived {
                        done.remove(&request.symbol);
                    }
                    if fresh || revived {
                        if !request.type_args.is_empty() {
                            demanded_at.insert(request.symbol.clone(), request.type_args);
                        }
                        priority.insert(request.symbol.clone());
                        queue.push_front(request.symbol);
                    }
                }
                // While the consumer is settling its entry, hold the
                // background queue and wait for its next request (see
                // `Scheduler::paused`); the wait is a poll because requests
                // arrive on the consumer's own cadence.
                if ctl.sched.paused() && queue.front().is_some_and(|s| !priority.contains(s)) {
                    std::thread::sleep(std::time::Duration::from_micros(300));
                    continue;
                }
                let Some(symbol) = queue.pop_front() else {
                    break;
                };
                if !done.insert(symbol.clone()) {
                    continue;
                }
                let f = &program.functions[&symbol];
                // A demanded body checks at the instance the demand named
                // when its types align with the signature; anything else
                // (stale request, mismatched arity, an open type) falls back
                // to the definitional pass. So does a STRUCTURAL argument:
                // an anonymous record that does not fit the body degrades to
                // the call's fallback by design -- the row check at the
                // value's span is its error source -- and a dedicated pass
                // at such an instance would hard-error where the call site
                // deliberately does not.
                let instance_args = demanded_at.remove(&symbol).filter(|args| {
                    args.len() == f.signature.params.len()
                        && args.iter().all(brass_hir::is_fully_known)
                        && !args.iter().any(contains_structural_record)
                });
                if instance_args.is_none()
                    && (checker.seeded_module(&f.module) || ctl.skip_fns.contains(&symbol))
                {
                    // A seeded (context) body is settled without a check of
                    // its own -- callers re-elaborate it at their call sites
                    // -- but the event must still go out: a consumer waiting
                    // on a context function would otherwise wait forever.
                    // A resume-snapshot body is settled the same way: its
                    // delivered state was seeded from the prior run.
                    ctl.sched.emit(stream::CheckEvent::BodyChecked(
                        stream::BodyId::Function(symbol),
                        stream::ChannelDelta::default(),
                    ));
                    continue;
                }
                let fn_started = std::time::Instant::now();
                match &instance_args {
                    Some(args) => check_function_body_at(&mut checker, &symbol, f, args),
                    None => check_function_body(&mut checker, &symbol, f),
                }
                let errs = crate::exhaustive::check_block(program, &checker.typed, &f.decl.body);
                checker.errors.extend(errs);
                perf.item(symbol.clone(), fn_started.elapsed());
                let delta = flush_delta(&checker, &mut ctl.state, false);
                ctl.sched.emit(stream::CheckEvent::BodyChecked(
                    stream::BodyId::Function(symbol),
                    delta,
                ));
            }
            perf.report();
            checker.in_entry_main = false;
            // A stopped run hands its settled state back for the partial
            // cache: what this run checked resumes the next one.
            if ctl.sched.stopped() {
                let snapshot = ctl.state.snapshot(
                    done.into_iter().collect(),
                    program.inits.len(),
                    &checker.fields_loops,
                );
                ctl.sched.emit(stream::CheckEvent::Interrupted(snapshot));
            }
        }
    }
    let t = std::time::Instant::now();
    // Each expression's type was resolved against the substitution as it was
    // recorded, but a variable can be pinned *after* an expression that mentions
    // it was checked (e.g. an array element fixed by a later `push`). Re-resolve
    // every recorded type against the final substitution so the typed program
    // reflects the fully solved types -- which hover and the other LSP features
    // read directly.
    checker.report_uninferable_error_types();
    checker.finalize_typed();
    phase("typeck/finalize", t);
    // The terminal flush: finalize re-resolved the recorded types in place,
    // so this delta settles every entry the earlier flushes withheld or
    // emitted provisionally. Emitted by the caller (as `Finished`) once the
    // remaining whole-program passes contribute their errors.
    let final_delta = ctl.map(|ctl| flush_delta(&checker, &mut ctl.state, true));
    let function_returns: HashMap<String, Type> = checker
        .function_returns
        .clone()
        .into_iter()
        .map(|(name, ty)| {
            let ty = checker.resolve(&ty);
            (name, ty)
        })
        .collect();
    let method_returns: HashMap<(String, String), Type> = checker
        .method_returns
        .clone()
        .into_iter()
        .map(|(key, ty)| {
            let ty = checker.resolve(&ty);
            (key, ty)
        })
        .collect();
    // The cross-module tables, deep-resolved so a consumer without this run's
    // solver sees exactly what this run's `resolve` would have shown; whatever
    // stays open is genuinely generic.
    let context_tables = ContextTables {
        schemes: checker
            .schemes
            .iter()
            .map(|(name, scheme)| {
                let mut s = scheme.clone();
                s.fields = s
                    .fields
                    .iter()
                    .map(|(n, t)| (n.clone(), checker.resolve(t)))
                    .collect();
                for m in s.methods.values_mut() {
                    m.params = m
                        .params
                        .iter()
                        .map(|(n, t)| (n.clone(), checker.resolve(t)))
                        .collect();
                    m.ret = checker.resolve(&m.ret);
                }
                (name.clone(), s)
            })
            .collect(),
        function_returns: function_returns.clone(),
        method_returns: method_returns.clone(),
        method_return_props: checker.method_return_props.clone(),
        co_method_returns: checker
            .co_method_returns
            .iter()
            .map(|(k, t)| (k.clone(), checker.resolve(t)))
            .collect(),
        global_defs: checker
            .global_defs
            .iter()
            .map(|(m, defs)| {
                (
                    m.clone(),
                    defs.iter()
                        .map(|(n, t)| (n.clone(), checker.resolve(t)))
                        .collect(),
                )
            })
            .collect(),
        next_var: checker.next_unknown,
        bare_names: program
            .functions
            .values()
            .map(|f| f.signature.name.clone())
            .chain(program.types.values().map(|t| t.name.clone()))
            .collect(),
        covered: None,
        program_identity: ContextProgramIdentity::of(program),
    };
    // Re-resolve the coercion targets against the final substitution: a
    // variable pinned after the site was recorded (an err payload bound by a
    // later return) must reach MIR fully known so the rebuilt value's locals
    // can be seeded. A Result payload slot still open here was pinned by
    // NOTHING anywhere -- the value never carries data in it (an Err-only
    // flow's Ok side) -- so it defaults to void IN THE CHANNEL COPY only; no
    // solver binding can leak to other callers.
    let sum_views = checker
        .sum_views
        .iter()
        .map(|(s, t)| {
            let mut t = checker.resolve(t);
            if let Type::Sum(n) = &mut t
                && n.is_result_type()
            {
                for key in [
                    brass_hir::types::RESULT_OK_VALUE,
                    brass_hir::types::RESULT_ERR_ERROR,
                ] {
                    if n.substitution.get(key).is_none_or(|t| t.is_unknown()) {
                        n.substitution.insert(key, Type::Void);
                    }
                }
            }
            (*s, t)
        })
        .collect();
    (
        Inference {
            errors: checker.errors,
            typed: checker.typed,
            schemes: checker.schemes,
            view_args: checker.view_args,
            lift_errs: checker.lift_errs,
            sum_views,
            fields_loops: checker.fields_loops,
            type_names: checker.type_names,
            keyed_calls: checker.keyed_calls,
            typeof_types: checker.typeof_types,
            null_props: checker.null_props,
            function_returns,
            method_returns,
            context_tables,
        },
        final_delta,
    )
}

/// One free function's dedicated body pass -- the per-body core both body
/// orders share. The caller decides ordering and skips seeded modules.
fn check_function_body(checker: &mut Checker, symbol: &str, f: &FunInfo) {
    tracing::debug!(function = %f.signature.name, "inferring function body");
    // The module comes first: the body's bottom scope is the globals visible
    // from IT, so building the scope before setting it would hand the function
    // some other module's globals.
    checker.current_module = f.module.clone();
    let mut scopes = checker.signature_scopes(&f.signature.params);
    let ret = f.signature.ret_ty.clone();
    // The root module's bare `main` symbol is the program entry; its `!`
    // propagations abort at runtime, waiving the fallible-return-context
    // requirement for its own body.
    checker.in_entry_main = symbol == "main";
    checker.check_block_root(&f.decl.body, &mut scopes, ret.as_ref());
}

/// A demanded body's dedicated pass, run at the concrete argument types the
/// demand carried -- the instance the program is about to execute -- instead
/// of the open signature frame. Checking at the instance's types is what the
/// lazy run needs (its verdict is per executed instance, and the recorded
/// channel entries are the instance's), and it makes the pass cheap: the
/// call tree was already elaborated at these same types by the caller's own
/// pass, so the nested calls hit the elaboration memo instead of re-checking
/// an open frame, where nothing memoizes and a call chain re-expands
/// exponentially. Annotated parameters keep their annotations (the frame
/// instantiates them against the arguments, annotation winning), so a fully
/// annotated body checks exactly as its definitional pass would.
/// Whether a type mentions an anonymous structural record anywhere: such an
/// argument is served by the call-site row machinery (fit-or-degrade), so a
/// demanded instance carrying one keeps the definitional pass instead of
/// `check_function_body_at`.
fn contains_structural_record(ty: &Type) -> bool {
    match ty {
        Type::Record(n) if n.id == brass_hir::STRUCTURAL_RECORD_ID => true,
        Type::Record(n) | Type::Sum(n) => n
            .substitution
            .iter()
            .any(|(_, t)| contains_structural_record(t)),
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Nullable(inner)
        | Type::ConstOf(inner)
        | Type::Mut(inner)
        | Type::Ref(inner) => contains_structural_record(inner),
        Type::Fun(params, ret) => {
            params.iter().any(contains_structural_record) || contains_structural_record(ret)
        }
        Type::Tuple(elems) => elems.iter().any(contains_structural_record),
        _ => false,
    }
}

fn check_function_body_at(checker: &mut Checker, symbol: &str, f: &FunInfo, arg_types: &[Type]) {
    tracing::debug!(function = %f.signature.name, "inferring function body at demanded types");
    checker.current_module = f.module.clone();
    let frame = checker.signature_call_frame(&f.signature.params, arg_types, &[], None);
    let mut scopes = vec![frame];
    checker.in_entry_main = symbol == "main";
    checker.check_block_root(&f.decl.body, &mut scopes, f.signature.ret_ty.as_ref());
}

/// One module initializer's dedicated pass -- the per-init core both body
/// orders share. The caller brackets the whole init sequence with the shared
/// `const_scopes` frame.
fn check_init_body(checker: &mut Checker, init: &ModuleInit) {
    checker.current_module = init.path.clone();
    // The globals of OTHER modules this one can see. Its own are left out so
    // they still accumulate as its statements are checked -- a later global is
    // not visible to an earlier initializer.
    let mut scopes = vec![checker.globals_visible_from(&init.path)];
    if let Some(own) = checker.global_defs.get(&init.path) {
        for name in own.keys() {
            scopes[0].remove(name);
        }
    }
    checker.narrowed_bindings.clear();
    checker.closure_write_targets = init
        .stmts
        .iter()
        .flat_map(|s| {
            let mut acc = HashSet::new();
            collect_closure_writes_stmt(s, false, &mut acc);
            acc
        })
        .collect();
    for s in &init.stmts {
        checker.check_stmt(s, &mut scopes);
    }
}

/// Flush the channel entries recorded since the previous flush into a
/// [`stream::ChannelDelta`] (see the field notes there). `terminal` is the
/// flush after `finalize_typed`: the recorded types were re-resolved in
/// place -- which a prefix cursor cannot see -- so the aggregate scan
/// restarts from scratch, and a still-open `Result` payload in `sum_views`
/// defaults to `void` exactly like the channel copy the eager tail builds.
fn flush_delta(
    checker: &Checker,
    state: &mut stream::FlushState,
    terminal: bool,
) -> stream::ChannelDelta {
    let mut delta = stream::ChannelDelta::default();
    // Aggregate result types: fold the newly recorded typed expressions into
    // the running per-span agreement, then diff the seedable view against
    // what was already delivered. A span can gain a seed (it resolved, or
    // was first seen), change it (superseded value), or lose it (a later
    // instantiation disagreed).
    if terminal {
        state.typed_seen = 0;
        state.agg = Default::default();
    }
    for e in &checker.typed.expressions[state.typed_seen..] {
        // An entry was resolved when it was RECORDED, which can be mid-body:
        // a constructor's open slots are pinned by the statements after it
        // (`HashMap.new()` then `set`). Resolve against the substitution as
        // it stands NOW -- at a body boundary, with the whole body's pins
        // committed -- or the entry would stay invisible to the aggregate
        // until the terminal flush, far too late for a consumer that lowers
        // the body's MIR from this delta.
        let mut e = e.clone();
        e.ty = checker.resolve(&e.ty);
        state.agg.observe(&e, checker.program);
    }
    state.typed_seen = checker.typed.expressions.len();
    let want = state.agg.seedable_map();
    for (span, ty) in &want {
        if state.expr_flushed.get(span) != Some(ty) {
            delta.expr_types.push((*span, ty.clone()));
        }
    }
    for span in state.expr_flushed.keys() {
        if !want.contains_key(span) {
            delta.expr_types_removed.push(*span);
        }
    }
    state.expr_flushed = want;
    // Append-only span sets.
    for s in checker.view_args.difference(&state.view_args) {
        delta.view_args.push(*s);
    }
    state.view_args.extend(delta.view_args.iter().copied());
    for s in checker.lift_errs.difference(&state.lift_errs) {
        delta.lift_errs.push(*s);
    }
    state.lift_errs.extend(delta.lift_errs.iter().copied());
    for s in checker.null_props.difference(&state.null_props) {
        delta.null_props.push(*s);
    }
    state.null_props.extend(delta.null_props.iter().copied());
    for (span, fields) in &checker.fields_loops {
        if state.fields_loops.insert(*span) {
            delta.fields_loops.push((*span, fields.clone()));
        }
    }
    // Last-write-wins maps. `sum_views` values mirror the eager channel
    // copy: resolved against the current substitution, with a still-open
    // `Result` payload defaulted to `void` -- an Err-only flow may leave the
    // Ok slot pinned by nothing, ever, so waiting for it to close would
    // withhold the entry forever. The default is provisional: a later body
    // that does pin the slot changes the resolved value, and the revision is
    // re-emitted for the consumer to re-lower against.
    for (span, t) in &checker.sum_views {
        let mut t = checker.resolve(t);
        if let Type::Sum(n) = &mut t
            && n.is_result_type()
        {
            for key in [
                brass_hir::types::RESULT_OK_VALUE,
                brass_hir::types::RESULT_ERR_ERROR,
            ] {
                if n.substitution.get(key).is_none_or(|t| t.is_unknown()) {
                    n.substitution.insert(key, Type::Void);
                }
            }
        }
        if state.sum_views.get(span) != Some(&t) {
            delta.sum_views.push((*span, t.clone()));
            state.sum_views.insert(*span, t);
        }
    }
    for (span, name) in &checker.type_names {
        if state.type_names.get(span) != Some(name) {
            delta.type_names.push((*span, name.clone()));
            state.type_names.insert(*span, name.clone());
        }
    }
    for (span, t) in &checker.typeof_types {
        if state.typeof_types.get(span) != Some(t) {
            delta.typeof_types.push((*span, t.clone()));
            state.typeof_types.insert(*span, t.clone());
        }
    }
    // A typeof entry disappears when disagreeing instantiations poison it.
    let poisoned: Vec<Span> = state
        .typeof_types
        .keys()
        .filter(|s| !checker.typeof_types.contains_key(*s))
        .copied()
        .collect();
    for span in poisoned {
        state.typeof_types.remove(&span);
        delta.typeof_types_removed.push(span);
    }
    // The errors reported in this window (raw report order; the final
    // analysis sorts and dedups the full set).
    delta.errors = checker.errors[state.errors_seen..].to_vec();
    state.errors_seen = checker.errors.len();
    delta
}

struct Checker<'a> {
    program: &'a Program,
    errors: Vec<TypeError>,
    typed: TypedProgram,
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
    /// Top-level bindings keyed by their DEFINING module. Globals are per-module
    /// (the back end keys their storage that way too), so two modules' same-named
    /// `const`s are two different globals with two different types -- a single
    /// name-keyed table would hand one module the other's type and let the back
    /// end read the wrong slot at it.
    global_defs: HashMap<Vec<String>, HashMap<String, Type>>,
    /// Memoized `globals_visible_from`, keyed by the referencing module.
    global_scopes: HashMap<Vec<String>, HashMap<String, Type>>,
    function_returns: HashMap<String, Type>,
    /// (method qualifier, method name) -> return type.
    /// Record qualifiers are the type name; variant qualifiers are `Type.Variant`.
    method_returns: HashMap<(String, String), Type>,
    /// Methods whose `method_returns` entry carries propagation (`error(...)` /
    /// nullable `!`) wrapping from the light assembly; the co-check's plain
    /// return reconciliation must not replace those (see `co_method_returns`).
    method_return_props: HashSet<(String, String)>,
    /// (record type name, method name) -> the return type the full co-check of
    /// the method bodies reconciled in the shared per-type environment. Unlike
    /// the light-pass `method_returns`, these are expressed over the same
    /// variables as the record's fields, so scheme generalization ties a
    /// method's return to the type's parameters (`get -> V?`). Only recorded
    /// for inferred-return, non-propagating record methods.
    co_method_returns: HashMap<(String, String), Type>,
    /// Whether the co-check pass (every record type's method bodies, checked in
    /// one shared environment before scheme generalization) is running. Return
    /// reconciliation COMMITS unifications only then: the scheme must record two
    /// unifiable returns as one parameter (`get_or`'s `dflt` IS the map's value
    /// type), while a free function's returns stay loose -- its signature keeps
    /// its own variables, bound per call site.
    co_checking: bool,
    /// The `(type name, method name)` whose body the co-check pass is
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
    /// keyed by `fn:<symbol>` / `method:<self type>.<name>`. Re-entering one is a
    /// recursive call: re-checking the body again would not terminate, so the
    /// call falls back to the declared (or precomputed) return type.
    ///
    /// A method is keyed by its RECEIVER TYPE, not by the `Sum.Variant` qualifier
    /// the call resolved through. A sum's methods are lowered into every variant's
    /// table, so one `v.render()` resolves to one candidate per variant, all
    /// sharing the same body. Keyed per qualifier, a recursive call re-entered
    /// through a *different* variant's key and the guard never fired: each level
    /// re-elaborated the body once per not-yet-entered variant, so the work grew
    /// factorially in the variant count and a wide sum's self-recursive method
    /// effectively hung the compiler.
    instantiating: HashSet<String>,
    /// Set when a context seed was applied: every module except the entry
    /// (`main`) was checked by the run that produced the seed, so the per-item
    /// passes skip it and read the seeded tables instead.
    entry_only: bool,
    /// Symbols whose RECURSIVE call fell back to the precomputed return during an
    /// elaboration in progress. Only those need their shared table entry tied back
    /// to what the body really returns (see `link_inferred_return`); doing it for
    /// every function would pin a GENERIC one's shared entry to whichever call site
    /// ran first, and every other call would then conflict with it.
    recursed: HashSet<String>,
    /// Callables whose body has at least one error site (an `error(..)`, an `expr!`
    /// propagation, or a forwarded `Result`). A `T!` with NO site is fine -- nothing
    /// ever reads its Err -- but one whose sites all came back with an unknown error
    /// type has nothing to infer it from, and is reported.
    error_sites: HashSet<String>,
    /// How many callable bodies have been re-elaborated at call sites so far, and
    /// whether the budget below has already been reported. Inference that fails to
    /// converge must not hang the compiler: it stops re-elaborating and says so.
    elaborations: u64,
    elaboration_budget_reported: bool,
    /// Deferred structural constraints on inference variables, keyed by the
    /// variable's `Unknown` id. Recorded while checking a body that uses an
    /// unknown-typed value (a closure parameter) and verified when the variable
    /// is solved at a call site (see `crate::constraint`).
    shape_constraints: HashMap<u32, Vec<ShapeConstraint>>,
    /// The inference solver: a persistent substitution for variables pinned
    /// across expressions (such as an empty array's element type once a `push`
    /// fixes it) plus variable classification. `resolve` follows the
    /// substitution so all later uses of the same binding see the solved type,
    /// and `kind_of` distinguishes a bare empty-array element (which cannot
    /// satisfy a required position while unconstrained) from other unknowns
    /// used by the local inference and monomorphization passes.
    solver: Solver,
    /// The module whose body is currently being checked, used to enforce
    /// per-module name visibility. Set per function,
    /// method, and module-init, and swapped while a called body is re-checked.
    current_module: Vec<String>,
    /// Nominal ids of shadowing `type Result` declarations whose shape problem
    /// was already reported, so every `T!`/`error(..)` in the module does not
    /// repeat the same diagnostic (`i32::MIN` marks the alias-shadow report).
    reported_result_shadow: HashSet<i32>,
    /// The lazy (run) profile: calls to FULLY-ANNOTATED free functions --
    /// concrete declared return, every parameter's type declared and fully
    /// known -- are typed from the signature alone, skipping the callee-body
    /// re-elaboration. That is exactly the class the JIT compiles as
    /// runtime-deferred sites: such a body is instantiation-independent (its
    /// own dedicated pass records its channels), so per-call re-checking
    /// only re-derives what the signature already states. The complete
    /// diagnostic verdict stays `check`'s (eager's) job, where this is off.
    lazy_profile: bool,
    /// Memoized returns of call-site body re-elaborations, keyed by callee
    /// symbol and the fully-resolved argument types. The same callee at the
    /// same argument types re-derives the same span-keyed channel entries and
    /// the same return, so the first elaboration's answer is reused -- without
    /// this the repeated subtrees of an unannotated call chain are re-checked
    /// once per call site, which grows exponentially with chain depth. Only
    /// clean (error-free) elaborations with fully-known keys and returns land
    /// here: an open argument means the elaboration would constrain the
    /// caller's own variables, an open return must stay the shared table entry
    /// so later pinning reaches every reader, and an erroring body keeps
    /// reporting at every call site.
    elaboration_memo: HashMap<String, Type>,
    /// Free functions that can transitively reach a reflective keyed
    /// (`-> infer!`) method call (see `taint::keyed_reachable`). The lazy
    /// profile never types a call to one from its signature alone: the keyed
    /// call must be SEEN by this pass, or its discovery would restart the
    /// analysis after execution began. Empty outside the lazy profile.
    keyed_tainted: HashSet<String>,
    /// The module paths a PARTIAL seed covers (see `ContextTables::covered`);
    /// `None` under a full seed or no seed.
    seeded_set: Option<HashSet<Vec<String>>>,
    /// Callables (`fn:<symbol>` / `m:<qualifier>.<name>`) whose inferred Err
    /// payload is one of their own parameter variables: a generic error type
    /// named per call site, exempt from the uninferable-error report.
    generic_error_returns: HashSet<String>,
    /// Per record-type generalized scheme, keyed by type name. Built after the
    /// method bodies are co-checked and consulted at call sites to type a method
    /// call's result by instantiating the method's scheme against the receiver.
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
    /// Resolved binding types of `typeof`-bearing local annotations, keyed by
    /// the annotation span (see [`Inference::typeof_types`]).
    typeof_types: HashMap<Span, Type>,
    /// `typeof`-bearing annotation spans whose resolved type DIFFERED between
    /// two checks -- a generic body's instantiations disagreeing. One MIR body
    /// is shared by every instantiation, so no single slot type is right;
    /// the entry is dropped (and stays dropped) and the binding's slot is left
    /// to per-instance inference from its assignments.
    typeof_poisoned: HashSet<Span>,
    /// Bindings narrowed non-null in the current callable, with their original
    /// nullable types. A call can re-null a narrowed GLOBAL (any callee may
    /// write it) or a narrowed local ASSIGNED INSIDE A CLOSURE of this body (a
    /// closure value may run during the call), so those narrowings are undone
    /// after every call (`invalidate_narrowed_after_call`). Plain locals are
    /// unaffected: no callee can rebind them.
    narrowed_bindings: Vec<(String, Type)>,
    /// Names assigned anywhere inside a closure literal of the callable body
    /// currently being checked; see `narrowed_bindings`.
    closure_write_targets: HashSet<String>,
    /// Per-parameter rows (field presence/type requirements) of every free
    /// function and method, derived once per program. An anonymous structural
    /// argument to a row-covered parameter is checked against the row at the
    /// argument's own span (the value is where the mismatch lives).
    rows: brass_typesys::RowInfo,
    /// Spans of anonymous structural arguments that passed their callee row
    /// check for a view-ELIGIBLE parameter: exactly the call sites where MIR
    /// lowering may convert the argument into the parameter's view.
    view_args: HashSet<Span>,
    /// Value expressions accepted as a declared sum subtype at a flow site,
    /// keyed by the expression's span, mapped to the PARENT sum's table
    /// symbol; MIR lowering rebuilds exactly these values as the parent.
    sum_views: HashMap<Span, Type>,
    /// `expr!` sites whose propagated Err payload is re-raised wrapped into
    /// the prelude `Error` (see [`Inference::lift_errs`]).
    lift_errs: HashSet<Span>,
    /// Field lists of checked fields-loops, keyed by loop-statement span; the
    /// channel MIR lowering unrolls from (see [`Inference::fields_loops`]).
    fields_loops: HashMap<Span, Vec<String>>,
    /// Resolved type names of checked `typeof(x)` calls, keyed by call span.
    type_names: HashMap<Span, String>,
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
    /// Per-span evidence of how each sum flow site lowered in this
    /// elaboration: `Some(parent)` = coerced (rebuilt) to that declared-parent
    /// instance, `None` = same-nominal flow needing no rebuild. `sum_views` is
    /// keyed by span while one MIR body is shared across a generic's
    /// instantiations and the baked rebuild has no per-instance escape hatch,
    /// so instantiations that disagree -- different parent instances, or
    /// view in one and identity in another -- are rejected like `prop_kinds`.
    sum_view_seen: HashMap<Span, Option<NominalType>>,
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
    /// never emits the fall-through either.
    static_divergence: bool,
}

/// What a checked `expr!` propagates on failure: the null of a nullable
/// operand, or the `Err` of a `Result` operand. See `Checker::prop_kinds`.
#[derive(Clone, Copy, PartialEq)]
enum PropKind {
    Null,
    Err,
}

impl<'a> Checker<'a> {
    fn new(program: &'a Program) -> Self {
        Self {
            program,
            errors: Vec::new(),
            typed: TypedProgram::default(),
            const_scopes: Vec::new(),
            next_unknown: next_unknown_after_program(program),
            self_type: None,
            self_variant: None,
            return_contexts: Vec::new(),
            return_values: Vec::new(),
            last_returns: Vec::new(),
            global_defs: HashMap::new(),
            global_scopes: HashMap::new(),
            function_returns: HashMap::new(),
            method_returns: HashMap::new(),
            method_return_props: HashSet::new(),
            co_method_returns: HashMap::new(),
            co_checking: false,
            current_co_method: None,
            co_return_links: HashMap::new(),
            instantiating: HashSet::new(),
            entry_only: false,
            recursed: HashSet::new(),
            error_sites: HashSet::new(),
            elaborations: 0,
            elaboration_budget_reported: false,
            shape_constraints: HashMap::new(),
            solver: {
                // Fresh variables must not collide with the ids lowering
                // embedded in the program's resolved types (see
                // `Program::next_infer_var`); a collision aliases an
                // unrelated type and surfaced as order-dependent phantom
                // type errors.
                let mut s = Solver::new();
                s.seed_var_counter(program.next_infer_var);
                s
            },
            current_module: Vec::new(),
            reported_result_shadow: HashSet::new(),
            lazy_profile: false,
            elaboration_memo: HashMap::new(),
            keyed_tainted: HashSet::new(),
            seeded_set: None,
            generic_error_returns: HashSet::new(),
            schemes: HashMap::new(),
            fixed_array_binding: false,
            call_expected: None,
            keyed_calls: HashMap::new(),
            typeof_types: HashMap::new(),
            typeof_poisoned: HashSet::new(),
            prop_kinds: HashMap::new(),
            sum_view_seen: HashMap::new(),
            sum_view_poisoned: HashSet::new(),
            lift_kinds: HashMap::new(),
            lift_poisoned: HashSet::new(),
            narrowed_bindings: Vec::new(),
            closure_write_targets: HashSet::new(),
            rows: brass_typesys::RowInfo::analyze(program),
            view_args: HashSet::new(),
            lift_errs: HashSet::new(),
            sum_views: HashMap::new(),
            fields_loops: HashMap::new(),
            type_names: HashMap::new(),
            null_props: HashSet::new(),
            in_entry_main: false,
            static_divergence: false,
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

    /// A fresh inference variable for the element type of a bare `[]` literal,
    /// remembered so that an unconstrained empty array escaping into a required
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

    /// Check a method body with `self` bound to the bare type. For an
    /// inferred-return body, returns the reconciled return type like
    /// [`Self::check_block_root`].
    fn check_block_with_self(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
        self_type: &str,
    ) -> Option<Type> {
        self.check_block_with_self_context(b, scopes, ret, self_type, None)
    }

    fn check_block_with_self_variant(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
        self_type: &str,
        variant: &str,
    ) {
        self.check_block_with_self_context(b, scopes, ret, self_type, Some(variant));
    }

    fn check_block_with_self_context(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
        self_type: &str,
        variant: Option<&str>,
    ) -> Option<Type> {
        let saved = self.self_type.replace(self_type.to_string());
        let saved_variant = self.self_variant.clone();
        self.self_variant = variant.map(|v| (self_type.to_string(), v.to_string()));
        if let Some(scope) = scopes.last_mut() {
            scope.insert("self".to_string(), self.type_by_name(self_type));
        }
        let full = self.check_block_root(b, scopes, ret);
        self.self_type = saved;
        self.self_variant = saved_variant;
        full
    }

    /// Check a function/method body. For an inferred-return body (`ret` is `None`)
    /// returns the reconciled type of its `return` values as observed by the full
    /// check (so a constructor whose slot array is filled with `null` returns the
    /// nullable element type), or `None` for an explicit-return body.
    fn check_block_root(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
    ) -> Option<Type> {
        let saved = std::mem::replace(&mut self.const_scopes, vec![HashSet::new()]);
        let saved_narrowed = std::mem::take(&mut self.narrowed_bindings);
        let saved_closure_writes = std::mem::replace(
            &mut self.closure_write_targets,
            closure_write_targets_block(b),
        );
        self.return_contexts.push(match ret {
            Some(ty) => ReturnContext::Explicit(ty.clone()),
            None => ReturnContext::Inferred,
        });
        self.return_values.push(Vec::new());
        self.check_block(b, scopes);
        let collected = self.return_values.pop().unwrap_or_default();
        self.last_returns = collected.clone();
        self.return_contexts.pop();
        self.closure_write_targets = saved_closure_writes;
        self.narrowed_bindings = saved_narrowed;
        self.const_scopes = saved;
        if ret.is_none() {
            // The co-check RECORDS the unifiable-return links (see
            // `reconcile_return_types_with`): this is what ties a method's
            // open-parameter return to the value it joins with, so the scheme
            // records them as one parameter (`get_or`'s `dflt` IS the map's
            // value type).
            let common = self.reconcile_return_types_with(&collected, false, self.co_checking);
            // The join helper leaves an open variable bare when joined with a
            // literal `return null` (eager wrapping could nest once the
            // variable resolves to a nullable type), which understates a
            // generic body's return (`get`'s value-or-null is `V?`, not `V`).
            // Re-wrap here: a body with a null return is nullable. Consumers
            // collapse a nested `T??` to `T?` after instantiation (see
            // `brass_hir::collapse_nullable`).
            match common {
                Some(t) if collected.iter().any(|(r, _)| r.is_null()) => {
                    Some(match self.resolve(&t) {
                        resolved @ Type::Nullable(_) => resolved,
                        other => Type::Nullable(Box::new(other)),
                    })
                }
                other => other,
            }
        } else {
            None
        }
    }

    /// Check every statement of a block.
    ///
    /// Statements after a statically-folded `if` whose taken arm always returns
    /// are UNREACHABLE (see [`Checker::static_divergence`]). They are still
    /// walked -- so the calls they make still reach monomorphization -- but their
    /// type errors are dropped, the same treatment the dead arm of such an `if`
    /// already gets. This is what lets a generic body pick the arm that fits its
    /// instantiation and fall through for the others:
    ///
    /// ```text
    /// fun as_text(v) -> string {
    ///     if v._components { return v.to_string() }   // a Path: returns here
    ///     return v                                    // a string: unreachable above
    /// }
    /// ```
    ///
    /// A `bool` condition never folds, so ordinary control flow is unaffected:
    /// only a condition whose truthiness the type alone decides (a present member
    /// vs an absent one) can make a fall-through dead.
    fn check_block(&mut self, b: &Block, scopes: &mut ScopeStack) {
        scopes.push(HashMap::new());
        self.const_scopes.push(HashSet::new());
        let mut unreachable = false;
        for s in &b.stmts {
            let mark = self.errors.len();
            self.static_divergence = false;
            self.check_stmt(s, scopes);
            if unreachable {
                self.errors.truncate(mark);
            } else {
                unreachable = self.static_divergence;
            }
        }
        self.static_divergence = false;
        self.const_scopes.pop();
        scopes.pop();
    }

    /// Check a `return` against the active return context. The context is the
    /// top of `return_contexts`, pushed by `check_block_root` for a function or
    /// method body and by the closure checker for a closure body. Consulting
    /// the stack rather than a positionally-threaded parameter means a `return`
    /// nested inside an `if`/bare block/`match`-arm that is evaluated as an
    /// expression is still checked against the enclosing callable's declared
    /// type, and a `return` inside a closure is checked against the closure's
    /// own (inferred) context rather than the outer function.
    fn check_return(
        &mut self,
        value: Option<&Expr>,
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) {
        let returned = match self.return_contexts.last().cloned() {
            Some(ReturnContext::Explicit(want)) => match value {
                Some(e) => {
                    // A fallible return type (`-> T!`, or any `Result`) auto-wraps a
                    // bare value as `Ok { value }`: check it against the Ok payload.
                    // A `Result`-typed value flows whole. This mirrors the inferred
                    // fallible path and the HM checker (`hm::Stmt::Return`).
                    let resolved = self.resolve(&want);
                    if let Some((ok, _err)) = resolved.result_payloads() {
                        let ok = ok.clone();
                        // `return e!` where the enclosing return is `T!` keys a
                        // reflective method inside `e` by the Ok payload `ok`
                        // (or by `want` when `e` is itself a `Result`). Set the
                        // channel narrowly for a direct call / `call!`.
                        if matches!(e, Expr::Call(..) | Expr::ErrorProp(..)) {
                            self.call_expected = Some(ok.clone());
                        }
                        let got = self.check_expr(e, scopes);
                        self.call_expected = None;
                        // A declared subtype of the return's Result also flows
                        // whole (the flow site coerces it); only a genuinely
                        // bare value is checked against the Ok payload.
                        let got_res = self.resolve(&got);
                        let whole = got_res.is_result_type()
                            || matches!((&got_res, &resolved), (Type::Sum(h), Type::Sum(w))
                                if crate::structural::declares_sum_parent(self.program, h.id, w.id, 0));
                        if whole {
                            let flowed = self.link_forwarded_error(&got_res, &resolved, e.span());
                            self.expect_expr_assignable(&flowed, &want, e);
                        } else {
                            self.expect_expr_assignable(&got, &ok, e);
                        }
                        got
                    } else {
                        self.check_expr_against(e, &want, scopes)
                    }
                }
                None => {
                    // A fallible return wraps a bare `return` exactly like a
                    // bare value: no value is a void payload, so `-> void!`
                    // accepts it as the Ok exit (and `-> int32!` reports the
                    // payload mismatch, not a mismatch against the whole
                    // `Result`). Mirrors the HM checker, which skips the
                    // void-return unification in a fallible body.
                    let resolved = self.resolve(&want);
                    if let Some((ok, _err)) = resolved.result_payloads() {
                        let ok = ok.clone();
                        self.expect_assignable(&Type::Void, &ok, span);
                    } else {
                        self.expect_assignable(&Type::Void, &want, span);
                    }
                    Type::Void
                }
            },
            // Inferred context (closure or unannotated function) or no context
            // (module top level): type the value but do not constrain it; the
            // return type is reconciled separately.
            _ => match value {
                Some(e) => self.check_expr(e, scopes),
                None => Type::Void,
            },
        };
        // Collect the resolved return type for the enclosing callable's inferred
        // return (see `return_values`); harmless for an explicit-return body, whose
        // collected values `check_block_root` discards.
        let resolved = self.resolve(&returned);
        if let Some(frame) = self.return_values.last_mut() {
            frame.push((resolved, span));
        }
    }

    /// Commit the return annotation's OPEN Err payload to a forwarded
    /// Result's. `T!` infers its Err from the body's error sources; a body
    /// whose only source is a forwarded callee Result (`return helper()`)
    /// names the type only at this return, and the ordinary assignability
    /// probe is deliberately non-committing, so the binding is made here.
    fn link_forwarded_error(&mut self, got: &Type, want: &Type, span: Span) -> Type {
        // The Err slot alone decides: an Err-only construction has no
        // `Ok.value` entry, so `result_payloads` (which demands both keys)
        // would miss it.
        let g_err = match got {
            Type::Sum(n) if n.is_result_type() => n
                .substitution
                .get(brass_hir::types::RESULT_ERR_ERROR)
                .cloned(),
            _ => None,
        };
        let Some(g_err) = g_err else {
            return got.clone();
        };
        let g_err = self.resolve(&g_err);
        if g_err.is_unknown() {
            return got.clone();
        }
        // A forwarded payload that is not the prelude Error is re-raised
        // wrapped into one at this return (MIR rebuilds the Err arm), so
        // every error a fallible body hands back has one shape. The flowed
        // type -- what the return is checked at -- carries the lifted slot.
        let lifted = crate::lift_err_payload(self.program, g_err.clone());
        self.record_lift_kind(span, lifted != g_err);
        let flowed = if lifted != g_err {
            self.lift_errs.insert(span);
            match got {
                Type::Sum(n) => {
                    let mut n = n.clone();
                    n.substitution
                        .insert(brass_hir::types::RESULT_ERR_ERROR, lifted.clone());
                    Type::Sum(n)
                }
                other => other.clone(),
            }
        } else {
            got.clone()
        };
        if let Some((_, w_err)) = want.result_payloads()
            && self.resolve(w_err).is_unknown()
        {
            let w_err = w_err.clone();
            let _ = self.solver.unify(&w_err, &lifted);
        }
        flowed
    }

    fn check_stmt(&mut self, s: &Stmt, scopes: &mut ScopeStack) {
        match s {
            Stmt::Let {
                pat,
                ty,
                value,
                is_const,
                ..
            } => {
                let Some(value) = value else {
                    // `let x: T` without an initializer: the annotation alone
                    // types the binding; the definite-assignment pass rejects
                    // any read before the binding is fully assigned.
                    self.bind_uninit_let(pat, ty.as_ref(), scopes);
                    return;
                };
                let binding_ty = if let Some(te) = ty {
                    match self.resolve_annotation_scoped(te, scopes) {
                        Ok(annotated) => {
                            let got = self.check_expr_against(value, &annotated, scopes);
                            // Pin an open constructor result to the annotation, so
                            // the back end seeds the concrete instance: `let m: SI =
                            // HashMap.new()` fixes the witness-free map's key/value
                            // from `SI` (its inferred fields would otherwise stay
                            // open and its slot array read as `never`). Same-nominal
                            // only, rolled back on a genuine mismatch (already
                            // reported by `check_expr_against`).
                            let g = self.resolve(&got);
                            let a = self.resolve(&annotated);
                            if same_nominal_instance(&g, &a) {
                                let snap = self.solver.snapshot();
                                if self.solver.unify(&got, &annotated).is_err() {
                                    self.solver.rollback(snap);
                                }
                            }
                            self.instantiate_annotated_type(&annotated, &got)
                        }
                        Err(message) => {
                            self.errors.push(TypeError {
                                message,
                                span: te.span(),
                            });
                            self.check_expr(value, scopes)
                        }
                    }
                } else {
                    // An unannotated `const` bound directly to a non-empty array
                    // literal is immutable, so the literal types as a
                    // fixed-length array; a `let` binding stays a growable
                    // slice. An annotation (above) always wins.
                    self.fixed_array_binding =
                        *is_const && matches!(value, Expr::Array(es, _) if !es.is_empty());
                    let t = self.check_expr(value, scopes);
                    self.fixed_array_binding = false;
                    t
                };
                // Binding a NAME to a `void` value is a mistake with no
                // representable value behind it -- classically a block-bodied
                // closure that forgot `return`, whose call site would otherwise
                // fail much later with an opaque unsupported-construct error.
                // A wildcard (`let _ = f()`) still discards a void result.
                if let Pattern::Binding(name, span) = pat
                    && matches!(self.resolve(&binding_ty), Type::Void)
                {
                    self.errors.push(TypeError {
                        message: format!(
                            "cannot bind `{name}` to a `void` value (a block-bodied \
                             closure or function returns `void` without an explicit \
                             `return`)"
                        ),
                        span: *span,
                    });
                }
                self.check_let_pattern_against(&binding_ty, pat, value);
                self.bind_pattern(pat, &binding_ty, scopes);
                if *is_const {
                    self.record_expr_type_with(value, &binding_ty, Constness::Const);
                    self.bind_const_pattern(pat);
                }
            }
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => {
                let target_ty = self.check_place(target, scopes);
                if matches!(op, AssignOp::Eq) {
                    // A store into an array element whose type still carries an
                    // open inference variable commits the value into it (the way
                    // `push` does), so `arr[i] = v` pins an as-yet-unknown element
                    // -- including a record element with open fields (`_Entry<?,
                    // ?>`), whose key/value the stored value refines through the
                    // solver. A fully-concrete element keeps the ordinary
                    // bidirectional check (typed integer literals, structural
                    // compatibility).
                    let target_open = matches!(target, Expr::Index(..))
                        && !self.solver.free_vars(&self.resolve(&target_ty)).is_empty();
                    if target_open {
                        let value_ty = self.check_expr(value, scopes);
                        self.expect_element_assignable(&value_ty, &target_ty, value);
                    } else {
                        let value_ty = self.check_expr_against(value, &target_ty, scopes);
                        self.constrain_stored_value(&value_ty, &target_ty);
                    }
                } else {
                    let value_ty = self.check_expr(value, scopes);
                    let result = self.check_binary(assign_binop(*op), &target_ty, &value_ty, *span);
                    // The combined result is stored back into the target, so it
                    // must flow into the target's type: `int64 += int32` widens
                    // the operand, but `int32 += float64` would need a silent
                    // float -> int truncation on the write-back and is rejected.
                    self.expect_assignable(&result, &target_ty, *span);
                }
            }
            Stmt::Expr(e) => {
                self.check_expr(e, scopes);
            }
            Stmt::While { cond, body, .. } => {
                self.check_condition(cond, scopes);
                self.check_block(body, scopes);
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                if brass_hir::fields_loop_target(s).is_some() {
                    self.check_fields_loop(s, scopes);
                    return;
                }
                let iter_ty = self.check_expr(iter, scopes);
                // Iterating sees through reference/mutability wrappers and binds the
                // loop variable to the element of the same kind: over `ref(mut(T[]))`
                // each element is a `ref(mut(T))`, so mutating it writes through.
                let item_ty = self.for_element(&iter_ty).unwrap_or_else(|| {
                    self.errors.push(TypeError {
                        message: format!(
                            "cannot iterate over `{}`",
                            self.resolve(&iter_ty).display()
                        ),
                        span: iter.span(),
                    });
                    self.fresh_unknown()
                });
                scopes.push(HashMap::new());
                self.const_scopes.push(HashSet::new());
                // Check the loop variable's pattern against the element type, so a
                // destructuring of the wrong arity is a diagnostic here rather than
                // an out-of-bounds tuple read in the back end.
                self.check_pattern_against(&item_ty, pat);
                self.bind_pattern(pat, &item_ty, scopes);
                self.check_block(body, scopes);
                self.const_scopes.pop();
                scopes.pop();
            }
            Stmt::Return(value, span) => self.check_return(value.as_ref(), *span, scopes),
            Stmt::Break(_) | Stmt::Continue(_) => {}
        }
        self.apply_guard_narrowing(s, scopes);
    }

    /// Bind an uninitialized `let x: T`: the annotation is the binding's type.
    /// Only a single-name binding makes sense (there is no value to
    /// destructure); the definite-assignment pass enforces write-before-read.
    /// Resolve a local-binding annotation with the value scope in hand, so a
    /// `typeof(v)` node ties the binding to `v`'s inferred type (`let x:
    /// typeof(v)` gives x the same type as v). Structural wrappers around a
    /// `typeof` recurse; a `typeof`-free annotation delegates to `resolve_type`.
    /// `v` is type-checked (needed to know its type) but never lowered.
    fn resolve_annotation_scoped(
        &mut self,
        te: &TypeExpr,
        scopes: &mut ScopeStack,
    ) -> Result<Type, String> {
        let resolved = self.resolve_annotation_scoped_inner(te, scopes)?;
        // A `typeof`-bearing annotation is not recoverable by MIR's scope-free
        // resolver, so record the resolved type for the back end to seed the
        // binding's slot (needed when the initializer -- e.g. `null` -- does not
        // itself carry the type). The channel is keyed by span while one MIR
        // body is shared across a generic's instantiations, so it is kept only
        // while every fully-known observation agrees: a disagreement poisons
        // the span for good and the slot falls back to per-instance inference
        // from its assignments (correct whenever the initializer carries the
        // type). A not-yet-concrete observation -- the template elaboration of
        // a generic, before any instantiation -- is no information, neither
        // recorded nor a conflict.
        if contains_typeof(te) {
            let span = te.span();
            let concrete = self.resolve(&resolved);
            if is_concrete_type(&concrete) && !self.typeof_poisoned.contains(&span) {
                match self.typeof_types.get(&span) {
                    Some(prev) if peel_modes(prev) != peel_modes(&concrete) => {
                        self.typeof_types.remove(&span);
                        self.typeof_poisoned.insert(span);
                    }
                    _ => {
                        self.typeof_types.insert(span, concrete);
                    }
                }
            }
        }
        Ok(resolved)
    }

    fn resolve_annotation_scoped_inner(
        &mut self,
        te: &TypeExpr,
        scopes: &mut ScopeStack,
    ) -> Result<Type, String> {
        match te {
            TypeExpr::TypeOf(e, _) => Ok(self.check_expr(e, scopes)),
            TypeExpr::Nullable(inner, _) => Ok(Type::Nullable(Box::new(
                self.resolve_annotation_scoped_inner(inner, scopes)?,
            ))),
            TypeExpr::Array(inner, Some(n), _) => Ok(Type::Array(
                Box::new(self.resolve_annotation_scoped_inner(inner, scopes)?),
                *n,
            )),
            TypeExpr::Array(inner, None, _) => Ok(Type::Slice(Box::new(
                self.resolve_annotation_scoped_inner(inner, scopes)?,
            ))),
            TypeExpr::Fallible(inner, span) => {
                let ok = self.resolve_annotation_scoped_inner(inner, scopes)?;
                let err = self.fresh_unknown();
                Ok(self.scoped_result(ok, err, *span))
            }
            TypeExpr::Mut(inner, _) => Ok(Type::Mut(Box::new(
                self.resolve_annotation_scoped_inner(inner, scopes)?,
            ))),
            TypeExpr::Ref(inner, _) => Ok(Type::Ref(Box::new(
                self.resolve_annotation_scoped_inner(inner, scopes)?,
            ))),
            TypeExpr::Tuple(elems, _) => {
                let mut ts = Vec::with_capacity(elems.len());
                for e in elems {
                    ts.push(self.resolve_annotation_scoped_inner(e, scopes)?);
                }
                Ok(Type::Tuple(ts))
            }
            // Named / Anonymous / Fun carry no `typeof` in practice; resolve them
            // with the ordinary (scope-free) resolver.
            _ => self.resolve_type(te),
        }
    }

    fn bind_uninit_let(&mut self, pat: &Pattern, ty: Option<&TypeExpr>, scopes: &mut ScopeStack) {
        // The parser only omits the initializer when an annotation is present.
        let Some(te) = ty else { return };
        let binding_ty = match self.resolve_annotation_scoped(te, scopes) {
            Ok(t) => t,
            Err(message) => {
                self.errors.push(TypeError {
                    message,
                    span: te.span(),
                });
                return;
            }
        };
        if !matches!(pat, Pattern::Binding(..)) {
            self.errors.push(TypeError {
                message: "an uninitialized `let` must bind a single name".to_string(),
                span: te.span(),
            });
            return;
        }
        self.bind_pattern(pat, &binding_ty, scopes);
    }

    /// Check a `for f in fields(x)` loop: `x` must be a record; the body is
    /// expanded and checked once per field (declaration order for a nominal
    /// record, canonical key order for an anonymous one), with the loop
    /// variable decayed to the field name and `v[f]` to the field projection
    /// (see `brass_hir::expand`). The field list is recorded for MIR
    /// lowering, which unrolls the identical copies.
    fn check_fields_loop(&mut self, s: &Stmt, scopes: &mut ScopeStack) {
        let Some((var, arg, body)) = brass_hir::fields_loop_target(s) else {
            return;
        };
        let arg_ty = self.check_expr(arg, scopes);
        let resolved = self.resolve(&arg_ty);
        let (type_name, field_names) = match &resolved {
            Type::Record(n) if n.id == brass_hir::STRUCTURAL_RECORD_ID => (
                brass_hir::STRUCTURAL_RECORD_NAME.to_string(),
                n.substitution.iter().map(|(k, _)| k.to_string()).collect(),
            ),
            Type::Record(n) => {
                let Some(info) = self.program.type_by_id(n.id) else {
                    self.errors.push(TypeError {
                        message: format!(
                            "`fields(..)` requires a record value, got `{}`",
                            resolved.display()
                        ),
                        span: arg.span(),
                    });
                    return;
                };
                let TypeKind::Record { fields, .. } = &info.kind else {
                    self.errors.push(TypeError {
                        message: format!(
                            "`fields(..)` requires a record value, got `{}`",
                            resolved.display()
                        ),
                        span: arg.span(),
                    });
                    return;
                };
                (
                    info.name.clone(),
                    fields.iter().map(|f| f.name.clone()).collect::<Vec<_>>(),
                )
            }
            other => {
                self.errors.push(TypeError {
                    message: format!(
                        "`fields(..)` requires a record value, got `{}`",
                        other.display()
                    ),
                    span: arg.span(),
                });
                return;
            }
        };
        // The loop variable is substituted textually into every copy, so a
        // rebinding inside the body would silently change meaning.
        if block_rebinds(body, var) {
            self.errors.push(TypeError {
                message: format!(
                    "the fields-loop variable `{var}` must not be shadowed in the body"
                ),
                span: s.span(),
            });
            return;
        }
        // Defensive: the channel is span-keyed and consumed by one shared MIR
        // lowering. A generic `fields(..)` operand is rejected before reaching
        // here today, but a disagreement must never be baked silently.
        if let Some(prev) = self.fields_loops.get(&s.span())
            && prev != &field_names
        {
            self.errors.push(TypeError {
                message: "`fields(..)` expands different field sets across instantiations \
                          of this generic function (annotate the operand to fix it)"
                    .to_string(),
                span: s.span(),
            });
            return;
        }
        self.fields_loops.insert(s.span(), field_names.clone());
        for (i, field) in field_names.iter().enumerate() {
            let expanded = brass_hir::expand_fields_body(body, var, field, i);
            let err_start = self.errors.len();
            self.check_block(&expanded, scopes);
            // Copies carry shifted spans (so span-keyed sidecars stay distinct
            // per copy); surface diagnostics at the source position, naming
            // the field whose copy failed.
            for e in &mut self.errors[err_start..] {
                e.span = brass_hir::unshift_span(e.span);
                e.message = format!(
                    "{} (while expanding field `{field}` of `{type_name}`)",
                    e.message
                );
            }
        }
    }

    fn check_expr(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        let ty = self.check_expr_inner(e, scopes);
        self.record_expr_type(e, &ty);
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
        self.typed.push_kind(
            brass_hir::TypedExprKind::Ident(name.to_string()),
            span,
            ty,
            Constness::Unknown,
        );
    }

    fn record_expr_type_with(&mut self, expr: &Expr, ty: &Type, constness: Constness) {
        let ty = self.resolve(ty);
        let ty = if constness == Constness::Const {
            Type::ConstOf(Box::new(ty))
        } else {
            ty
        };
        self.typed.push_expr(expr, ty, constness);
    }

    /// Re-resolve every recorded expression type against the final substitution.
    /// Run once after all checking, so a type recorded before one of its
    /// variables was pinned still reflects the solved type. `resolve` is deep --
    /// it follows variables nested inside arrays, function types, and a nominal's
    /// substitution (so a `HashMap`'s `_entries` element pinned by a later `push`
    /// shows its concrete type) -- and preserves the `ConstOf` wrapper, so
    /// constness is unchanged.
    fn finalize_typed(&mut self) {
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
            Pattern::Binding(name, _) => {
                if !self.is_unit_variant_name(name) {
                    out.push(name.clone());
                }
            }
            Pattern::Record(_, fields, _) => {
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

    fn can_unify(&self, a: &Type, b: &Type) -> bool {
        Subst::new().unify(a, b).is_ok()
            || crate::structural::types_compatible(self.program, a, b)
            || crate::structural::types_compatible(self.program, b, a)
    }

    /// Resolve a type through the persistent substitution, following solved
    /// inference variables (including nested ones). The substitution is only
    /// populated where the checker pins a variable across uses (e.g. an empty
    /// array's element type after the first `push`), so an unconstrained type is
    /// returned structurally unchanged.
    fn resolve(&self, ty: &Type) -> Type {
        self.solver.resolve(ty)
    }
}
