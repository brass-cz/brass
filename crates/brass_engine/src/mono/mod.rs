//! Monomorphization: collecting the concrete instances a typed back end
//! compiles, and resolving every local and return type to a concrete type.
//!
//! This is *true* single-specialization: starting from the
//! zero-parameter entry functions, each call site's concrete argument types
//! select (and, on demand, create) a callee instance, so one polymorphic MIR
//! body yields a distinct instance per concrete type tuple. Functions, instance
//! methods, and static methods (constructors) are all instantiated this way, as
//! are records (a record's field-type substitution makes each layout a distinct
//! instance), sum types (with `match`), the generic `Result` (fallible functions
//! infer its payloads), nullables, strings, fixed arrays, module globals, and
//! closures -- both called in place (params from the call site) and passed to
//! higher-order functions (params recovered by probing the callee's use of the
//! parameter). Growable arrays (`[]` + `push`, the element type inferred from the
//! push) and typed `print`/`println` are handled too. Each instance gets a
//! collision-free symbol and a fully concrete type for every local. The pass also
//! *checks* the program: a body outside the typed subset (file I/O, concurrency,
//! and other Value-based stdlib primitives) is rejected, so the back end only
//! sees validated, concretely-typed MIR.

use std::collections::{HashMap, HashSet};

use brass_hir::{
    FloatKind, IntKind, NominalType, Program, RESULT_TYPE_ID, Substitution, Type, TypeKind,
    int_literal_kind,
};
use brass_mir::{
    Callee, ClosureId, Literal, LocalId, MirBody, MirClosure, MirFunction, MirMethod, MirProgram,
    MirStmt, Operand, Projection, Rvalue, Terminator,
};
use brass_parser::ast::{BinOp, UnaryOp};

use crate::mir_infer::{MirTypeError, Resolver, infer_body};

mod boundary;
mod closure;
mod fold;
mod rules;
mod scan;
mod symbols;

pub use boundary::{
    boundary_record_type, boundary_record_type_by_id, boundary_record_type_by_name,
    boundary_record_type_from_fields, parse_structural_descriptor,
};
pub use fold::{cond_static_truthiness, locals_only_in_dead_blocks, reachable_blocks};
pub use rules::binary_operand_type;
pub use rules::unwrap_nullable;
pub use scan::operand_type_of;

// `is_comparison` lives with the constraint generator; re-exported here so the
// monomorphizer's public API (and `brass_engine::is_comparison`) is unchanged.
pub use crate::mir_infer::is_comparison;
pub use symbols::{
    SYNTH_SIGIL, closure_symbol, instance_symbol, method_symbol, prim_method_instance,
    static_symbol,
};

use rules::{
    bin_validation_types, binary_operand_common, check_bin, const_type, is_refinement_of,
    is_supported, merge_return_types, resolve_nominal, variant_field_layoutable,
};
use scan::{
    binding_name_of, body_has_error_source, collect_array_pushes, collect_closure_passes,
    collect_indirect_args, collect_record_field_closures, method_ret_annotation, null_prop_returns,
    propagated_result_returns, result_concrete_ok, returns_only_err_constructions,
    seed_returned_aggregate,
};
use symbols::is_return_polymorphic_result;

/// A [`Resolver`] for the JIT-time verification pass: a call is typed by looking
/// up the instance the monomorphizer already built for it, and fields/nominals/
/// globals come from the program and the monomorphized global table.
struct MonoResolver<'a, 'm> {
    mono: &'a MonoProgram<'m>,
    program: &'a Program,
}

impl Resolver for MonoResolver<'_, '_> {
    /// A direct call's result is the return type of the callee instance built for
    /// these argument types; other call shapes (methods, builtins, indirect) are
    /// left open so the check never invents a wrong type.
    fn call_type(&mut self, callee: &Callee, args: &[Type]) -> Option<Type> {
        match callee {
            Callee::Free(base) => self
                .mono
                .lookup(&instance_symbol(base, args))
                .map(|f| f.ret.clone()),
            _ => None,
        }
    }

    fn field_type(&self, base: &Type, field: &str) -> Option<Type> {
        // A constructed value's substitution is authoritative; otherwise read the
        // field's declared type from the HIR, resolving a bare nominal so the field
        // is self-describing for the check.
        if let Type::Record(n) = base
            && let Some(t) = n.substitution.get(field)
        {
            return Some(resolve_nominal(self.program, t));
        }
        let info = match base {
            Type::Record(n) | Type::Sum(n) => self.program.type_by_id(n.id)?,
            _ => return None,
        };
        let declared = match &info.kind {
            TypeKind::Record { fields, .. } => fields
                .iter()
                .find(|f| f.name == field)
                .and_then(|f| f.resolved_ty.clone()),
            // A variant-qualified field (`Variant.field`) resolves in that variant;
            // a bare name must be common to every variant.
            TypeKind::Sum { variants } => match field.split_once('.') {
                Some((variant, fname)) => variants
                    .iter()
                    .find(|v| v.name == variant)
                    .and_then(|v| v.fields.iter().find(|f| f.name == fname))
                    .and_then(|f| f.resolved_ty.clone()),
                None => {
                    let mut common = None;
                    for v in variants {
                        let f = v.fields.iter().find(|f| f.name == field)?;
                        common = f.resolved_ty.clone();
                    }
                    common
                }
            },
        };
        declared.map(|t| resolve_nominal(self.program, &t))
    }

    fn nominal(&self, _name: &str) -> Option<Type> {
        // An unresolved nominal stays open (a fresh variable); the surrounding
        // constraints still solve, so the check neither rejects nor invents.
        None
    }

    fn global_type(&self, name: &str) -> Option<Type> {
        self.mono.global_type(name).cloned()
    }
}

/// The JIT-time type check: re-derive every monomorphized instance's
/// types by constraint solving and report any unification conflict. On a program
/// the front end already type-checked this finds nothing -- it is the deferred
/// model's consistency check over the concretely-typed IR, complementing the
/// monomorphizer's forward propagation. Fallible and closure instances are skipped
/// (their return/seed shapes need extra handling); they stay propagation-checked.
pub fn check_instances(mono: &MonoProgram, program: &Program) -> Vec<MirTypeError> {
    let mut errors = Vec::new();
    for f in &mono.functions {
        // A closure's captured locals are not parameters; seed them from their
        // monomorphized types so the body's uses of them are checked too.
        let captures: Vec<(LocalId, Type)> = f
            .captures
            .iter()
            .map(|c| (*c, f.local_types[c.index()].clone()))
            .collect();
        let mut resolver = MonoResolver { mono, program };
        if let Err(errs) = infer_body(
            f.body,
            &f.type_args,
            &captures,
            Some(&f.ret),
            f.fallible,
            &mut resolver,
        ) {
            errors.extend(errs);
        }
    }
    errors
}

/// One monomorphized callable instance (function, method, or closure): the
/// shared MIR body plus the concrete types that specialize it.
pub struct MonoFunction<'m> {
    pub body: &'m MirBody,
    /// Collision-free instance symbol; the back end derives its target function
    /// name from this.
    pub symbol: String,
    /// Concrete parameter types, in order (for an instance method, `[self, ..]`).
    pub type_args: Vec<Type>,
    /// Concrete return type.
    pub ret: Type,
    /// Concrete type of every local in the body, indexed by `LocalId`.
    pub local_types: Vec<Type>,
    /// For a closure instance, the captured locals (read from the environment);
    /// empty for functions, methods, and captureless closures.
    pub captures: Vec<LocalId>,
    /// Whether this is a closure instance: it takes a leading environment pointer
    /// and its parameters follow it, even when it captures nothing.
    pub is_closure: bool,
    /// Whether this is a fallible callable: a bare `return v` is implicitly
    /// wrapped as `Result.Ok { value: v }`.
    pub fallible: bool,
}

/// The concrete `Result<ok, err>` type with its payloads recorded in the nominal
/// substitution (the keys the back end and HIR agree on).
fn result_type(ok: Type, err: Type) -> Type {
    let mut subst = Substitution::empty();
    subst.insert(brass_hir::types::RESULT_OK_VALUE, ok);
    subst.insert(brass_hir::types::RESULT_ERR_ERROR, err);
    Type::Sum(NominalType::with_substitution(
        RESULT_TYPE_ID,
        "Result",
        subst,
    ))
}

/// The constant non-negative index carried by a tuple-position projection operand
/// (`t[0]`), or `None` when the index is not an integer constant. A tuple element
/// type is only known at a statically-known position.
pub(crate) fn const_operand_index(op: &Operand) -> Option<usize> {
    match op {
        Operand::Const(brass_mir::Literal::Int(n)) if *n >= 0 => Some(*n as usize),
        _ => None,
    }
}

/// The `IntKind` named by a primitive type name (`int32`, `uint8`, ...).
pub fn int_kind_name(s: &str) -> Option<IntKind> {
    Some(match s {
        "int8" => IntKind::I8,
        "int16" => IntKind::I16,
        "int32" => IntKind::I32,
        "int64" => IntKind::I64,
        "uint8" => IntKind::U8,
        "uint16" => IntKind::U16,
        "uint32" => IntKind::U32,
        "uint64" => IntKind::U64,
        _ => return None,
    })
}

/// The `FloatKind` named by a primitive type name.
pub fn float_kind_name(s: &str) -> Option<FloatKind> {
    match s {
        "float32" => Some(FloatKind::F32),
        "float64" => Some(FloatKind::F64),
        _ => None,
    }
}

/// The result type of a runtime-recognized numeric/string conversion
/// (`Type.from`/`Type.parse`), or `None` if `ty.method` isn't one.
pub fn numeric_conv_ret(ty: &str, method: &str) -> Option<Type> {
    if ty == "string" && method == "from" {
        return Some(Type::Str);
    }
    if let Some(k) = int_kind_name(ty) {
        return match method {
            "from" | "parse" => Some(result_type(Type::Int(k), Type::Str)),
            _ => None,
        };
    }
    if let Some(k) = float_kind_name(ty) {
        return match method {
            "from" => Some(Type::Float(k)),
            "parse" => Some(result_type(Type::Float(k), Type::Str)),
            _ => None,
        };
    }
    None
}

/// Whether a value can be printed on the typed I/O path: a string is written
/// directly, a scalar via its `to_string` conversion (which matches the boxed
/// path's formatting).
fn is_printable(ty: &Type) -> bool {
    match ty {
        Type::Str | Type::Bool | Type::Int(_) | Type::Float(_) => true,
        // A nullable of a printable prints its value, or `null`. A `never?` (the
        // null literal, or an absent structural field) is always null and prints so.
        Type::Nullable(inner) => matches!(**inner, Type::Never) || is_printable(inner),
        // An array/slice renders as `[e0, e1, ...]` when its elements are printable.
        Type::Slice(elem) | Type::Array(elem, _) => is_printable(elem),
        // A tuple renders as `[e0, e1, ...]` when every element is printable.
        Type::Tuple(elems) => elems.iter().all(is_printable),
        // Records and sums render through a generated per-type formatter
        // (`TypeName { field: value }` / `TypeName.Variant { field: value }`).
        Type::Record(_) | Type::Sum(_) => true,
        _ => false,
    }
}

impl MonoFunction<'_> {
    pub fn local_type(&self, id: brass_mir::LocalId) -> &Type {
        &self.local_types[id.index()]
    }
}

/// A whole program lowered to concrete typed instances, with a symbol index for
/// resolving call targets.
/// The recorded contract of a runtime-deferred call site (the lazy JIT): the
/// instance the site will ask the runtime resolver for, keyed in
/// [`MonoProgram::deferred`] by its instance symbol. `type_args` are the
/// concrete argument types the instance will be monomorphized at (they are
/// also the site's ABI parameter types -- instances are keyed by caller
/// argument types, so both sides agree by construction); `ret` is the
/// callee's declared, fully concrete return type.
#[derive(Clone, Debug)]
pub struct DeferredSig {
    pub base: String,
    pub type_args: Vec<Type>,
    /// The instance's ABI parameter types: the caller's argument types with
    /// every fully-annotated parameter replaced by its DECLARED type -- the
    /// same rule `type_and_store_inner` applies when it stores an instance's
    /// resolved parameters ("an annotated parameter keeps its declared
    /// type"), so the site's coercions and the eventual instance's signature
    /// agree.
    pub params: Vec<Type>,
    pub ret: Type,
}

pub struct MonoProgram<'m> {
    pub functions: Vec<MonoFunction<'m>>,
    /// The HIR program the instances were monomorphized against. The shared
    /// codegen consults it for declaration-level facts a concrete type alone
    /// cannot answer (e.g. whether an uncalled member is a declared method,
    /// so its load folds to the compile-time presence constant).
    pub hir: &'m Program,
    /// Module-level globals and their concrete types (declared by the back end,
    /// written by init instances, read via `Rvalue::Global`).
    pub globals: Vec<(String, Type)>,
    /// Init instance symbols, in run order (executed before `main`).
    pub init_symbols: Vec<String>,
    /// Why the `main` root was skipped, when it was: the first construct that
    /// fell outside the typed subset. Roots are best-effort, but for `main`
    /// (the program's entry point) the reason is the diagnostic the user needs.
    pub main_skip: Option<String>,
    /// Call sites compiled as runtime-resolved calls instead of direct calls
    /// (the lazy JIT's deferral), keyed by the target instance symbol. Empty
    /// under eager monomorphization.
    pub deferred: HashMap<String, DeferredSig>,
    index: HashMap<String, usize>,
    global_index: HashMap<String, Type>,
}

impl<'m> MonoProgram<'m> {
    /// The instance with the given symbol, if any.
    pub fn lookup(&self, symbol: &str) -> Option<&MonoFunction<'m>> {
        self.index.get(symbol).map(|&i| &self.functions[i])
    }

    /// The concrete type of global `name`, if any.
    pub fn global_type(&self, name: &str) -> Option<&Type> {
        self.global_index.get(name)
    }
}

/// Monomorphize a MIR program against its HIR program. Returns one concrete
/// instance per reachable (callable, type-tuple), or an error describing the
/// first construct outside the typed subset.
pub fn monomorphize<'m>(
    mir: &'m MirProgram,
    program: &'m Program,
) -> Result<MonoProgram<'m>, String> {
    let mut mono = Monomorphizer::new(mir, program);

    // Monomorphization is best-effort across roots: a root outside the typed
    // subset (e.g. a stdlib I/O function, or a `main` that does I/O) is skipped
    // rather than failing the whole program, so the typed path can still compile
    // everything reachable that *is* typeable. The driver decides per program
    // whether to run the typed path (when `main` typed) or fall back. `in_progress`
    // is cleared after each root so a skipped root leaves no stale recursion mark.
    //
    // The one exception is the main module's init: its top-level statements are the
    // program's entry point, the same role as a `main` function (which both back
    // ends already reject when it falls outside the typed subset). Dropping it
    // silently let a type-checked program run to a clean exit with no output, so a
    // failure there is surfaced rather than swallowed. Other modules' inits (stdlib
    // and imports) stay best-effort.
    let mut init_symbols = Vec::with_capacity(mir.inits.len());
    for (i, init) in mir.inits.iter().enumerate() {
        let sym = format!("{SYNTH_SIGIL}init{i}");
        let res = mono.type_and_store(
            sym.clone(),
            &init.body,
            &init.module,
            Vec::new(),
            Some(Type::Void),
            None,
            None,
            &[],
            Vec::new(),
            false,
            false,
        );
        mono.in_progress.clear();
        mono.assumed_rets.clear();
        match res {
            Ok(_) => init_symbols.push(sym),
            Err(e) if matches!(init.module.as_slice(), [m] if m == "main") => {
                return Err(format!("top-level code is outside the typed subset: {e}"));
            }
            Err(_) => {}
        }
    }

    // Roots: every zero-parameter function. Their bodies pull in the rest.
    let mut main_skip = None;
    for f in &mir.functions {
        if f.body.params.is_empty() {
            if let Err(e) = mono.instantiate_fn(&f.symbol, Vec::new()) {
                // Best-effort (see above), but the reason a root was skipped is
                // the first thing needed when a checked program is rejected as
                // "outside the typed subset" -- surface it in the debug trace,
                // and keep `main`'s reason for the driver's error message.
                tracing::debug!(root = %f.symbol, error = %e, "skipping untypeable root");
                if f.symbol == "main" {
                    main_skip = Some(e);
                }
            }
            mono.in_progress.clear();
            mono.assumed_rets.clear();
        }
    }

    let mut mono_program = mono.into_program(init_symbols, program);
    mono_program.main_skip = main_skip;
    Ok(mono_program)
}

/// Why entry-rooted monomorphization ([`monomorphize_entry`]) stopped.
#[derive(Debug)]
pub enum MonoStop {
    /// Reachable calls needed function bodies that are not in the MIR
    /// program (the lazy pipeline lowers function bodies on demand), each at
    /// the concrete argument types of the call that needed it. One pass
    /// collects EVERY missing body it can see -- a missing call's result is
    /// left unresolved and the walk continues -- so the caller lowers them
    /// all and retries: the retry count is the call graph's depth, not its
    /// node count. Never empty.
    MissingBodies(Vec<(String, Vec<Type>)>),
    /// Monomorphization genuinely failed (the same rejection
    /// [`monomorphize`] reports for the entry).
    Fail(String),
}

/// [`monomorphize`] with the LAZY pipeline's roots: the module initializers
/// and the entry `main` only, instead of every zero-parameter function. The
/// reachable graph is identical for code execution can reach -- execution
/// only enters through inits and `main` -- so unreachable functions are
/// never pulled in, which is the point: their bodies may not be checked or
/// lowered yet. A missing reachable body stops the run with
/// [`MonoStop::MissingBodies`] (even inside a best-effort init, which
/// [`monomorphize`] would silently skip) so the caller can supply the body
/// and retry rather than mis-classify it as untypeable.
pub fn monomorphize_entry<'m>(
    mir: &'m MirProgram,
    program: &'m Program,
    defer: bool,
) -> Result<MonoProgram<'m>, MonoStop> {
    let mut mono = Monomorphizer::new(mir, program);
    if defer {
        mono.defer = Some(HashMap::new());
    }
    let mut init_symbols = Vec::with_capacity(mir.inits.len());
    for (i, init) in mir.inits.iter().enumerate() {
        let sym = format!("{SYNTH_SIGIL}init{i}");
        // Demands recorded during a root that completes cleanly came from
        // dead branches or recovered speculative probes (a presence test):
        // roll them back to this watermark so dead code demands no body. A
        // failed root keeps its demands and the loop CONTINUES -- every
        // root's missing set is collected before the batch is returned.
        let watermark = mono.missing_demands.borrow().len();
        let res = mono.type_and_store(
            sym.clone(),
            &init.body,
            &init.module,
            Vec::new(),
            Some(Type::Void),
            None,
            None,
            &[],
            Vec::new(),
            false,
            false,
        );
        mono.in_progress.clear();
        mono.assumed_rets.clear();
        match res {
            Ok(_) => {
                mono.missing_demands.borrow_mut().truncate(watermark);
                init_symbols.push(sym);
            }
            Err(e) => {
                let missed = mono.missing_demands.borrow().len() > watermark;
                if !missed && matches!(init.module.as_slice(), [m] if m == "main") {
                    return Err(MonoStop::Fail(format!(
                        "top-level code is outside the typed subset: {e}"
                    )));
                }
            }
        }
    }
    let mut main_skip = None;
    if mir.functions.iter().any(|f| f.symbol == "main") || program.functions.contains_key("main") {
        let watermark = mono.missing_demands.borrow().len();
        match mono.instantiate_fn("main", Vec::new()) {
            Ok(_) => mono.missing_demands.borrow_mut().truncate(watermark),
            Err(e) => {
                // Only a miss-free failure is a genuine skip; a failure with
                // missing bodies is retried once they land.
                if mono.missing_demands.borrow().len() == watermark {
                    tracing::debug!(root = "main", error = %e, "skipping untypeable entry");
                    main_skip = Some(e);
                }
            }
        }
        mono.in_progress.clear();
        mono.assumed_rets.clear();
    }
    let missing = std::mem::take(&mut *mono.missing_demands.borrow_mut());
    if !missing.is_empty() {
        return Err(MonoStop::MissingBodies(missing));
    }
    let mut mono_program = mono.into_program(init_symbols, program);
    mono_program.main_skip = main_skip;
    Ok(mono_program)
}

/// Monomorphize a single callable on demand for a concrete argument-type tuple,
/// for deferred monomorphization: when a type is fixed at runtime,
/// the consumer is specialized for it then. Returns a [`MonoProgram`] containing
/// that instance and everything it transitively reaches, or an error if the body
/// cannot be typed for those types -- e.g. the runtime type lacks a field the
/// consumer reads. That error is the structural-requirement check enforced at the
/// boundary: an unfit type is rejected before specialization, never miscompiled.
pub fn monomorphize_instance<'m>(
    mir: &'m MirProgram,
    program: &'m Program,
    base: &str,
    type_args: Vec<Type>,
) -> Result<MonoProgram<'m>, String> {
    let mut mono = Monomorphizer::new(mir, program);
    mono.instantiate_fn(base, type_args)?;
    mono.in_progress.clear();
    mono.assumed_rets.clear();
    Ok(mono.into_program(Vec::new(), program))
}

/// [`monomorphize_instance`] with runtime deferral enabled (the lazy JIT's
/// resolver): calls out of the new instance may themselves compile to
/// runtime-resolved sites (collected in the result's `deferred`) instead of
/// pulling their bodies in, so one resolution compiles one call's worth of
/// code. A missing body that cannot defer surfaces as
/// [`MonoStop::MissingBodies`] for the resolver to supply and retry.
pub fn monomorphize_instance_deferred<'m>(
    mir: &'m MirProgram,
    program: &'m Program,
    base: &str,
    type_args: Vec<Type>,
    globals: &[(String, Type)],
) -> Result<MonoProgram<'m>, MonoStop> {
    let mut mono = Monomorphizer::new(mir, program);
    mono.defer = Some(HashMap::new());
    // Global types are discovered by typing init bodies, which a
    // single-instance run never does: the caller passes the startup run's
    // complete table (every init typed before execution began), or a body
    // reading a module global could not be typed.
    mono.global_types = globals.iter().cloned().collect();
    let res = mono.instantiate_fn(base, type_args);
    mono.in_progress.clear();
    mono.assumed_rets.clear();
    match res {
        // Demands a clean run recorded came from dead branches or recovered
        // probes; dead code needs no body.
        Ok(_) => Ok(mono.into_program(Vec::new(), program)),
        Err(e) => {
            let missing = std::mem::take(&mut *mono.missing_demands.borrow_mut());
            if !missing.is_empty() {
                return Err(MonoStop::MissingBodies(missing));
            }
            Err(MonoStop::Fail(e))
        }
    }
}

struct Monomorphizer<'m, 'p> {
    program: &'p Program,
    by_fn: HashMap<&'m str, &'m MirFunction>,
    by_method: HashMap<(&'m str, &'m str), &'m MirMethod>,
    by_closure: HashMap<ClosureId, &'m MirClosure>,
    /// Module-level global name -> concrete type, populated by typing init bodies.
    global_types: HashMap<String, Type>,
    instances: HashMap<String, MonoFunction<'m>>,
    /// Instances currently being typed (the instantiation stack), mapped to
    /// their provisional return type. The type is `Some` when the callable
    /// carries an authoritative return annotation (or, for a fallible callable
    /// with a declared Ok payload, the `Result<ok, string>` guess), in which
    /// case a call that reaches back into an in-progress instance (mutual
    /// recursion) can be typed against it; `None` means nothing sound is known
    /// yet and such a call is rejected with an annotation hint.
    in_progress: HashMap<String, Option<Type>>,
    /// Return types mutual recursion actually assumed, checked against the
    /// final inferred type when the assumed-about frame completes. This is what
    /// makes the fallible `Result<ok, string>` guess sound: a body whose error
    /// payload turns out different fails its frame instead of miscompiling.
    assumed_rets: HashMap<String, Type>,
    /// Completed instances in insertion order. Mutual recursion stores a callee
    /// before its caller, so when a frame fails, every instance stored during
    /// that frame is rolled back here -- otherwise a survivor could keep a call
    /// to a symbol that never materializes.
    instance_log: Vec<String>,
    /// The program's parameter-row table, derived on first `RecordView` (the
    /// same deterministic analysis the checker ran, so the view a call site was
    /// approved for is the view built here). `None` until then: programs
    /// without views never pay for the fixpoint.
    rows: Option<brass_typesys::RowInfo>,
    /// When `Some`, calls to functions whose MIR body is absent but whose
    /// whole ABI is annotation-determined compile to runtime-resolved calls
    /// recorded here (see [`DeferredSig`]) instead of failing the frame --
    /// the lazy JIT's deferral. `None` is eager/blocking monomorphization.
    defer: Option<HashMap<String, DeferredSig>>,
    /// Depth of closure-body instantiation frames. Deferral is disabled
    /// inside them: closure code can cross to worker threads (`spawn`), and
    /// only the main thread can compile.
    closure_depth: u32,
    /// Every function this run needed whose MIR body is absent, with the
    /// concrete argument types of the call that needed it (empty when the
    /// need arose in a `&self` probe that does not know them), deduplicated.
    /// Fed by the missing-call intercept in `resolve_free` (which leaves the
    /// call unresolved so the walk keeps collecting), the missing lookup in
    /// `instantiate_fn`, and the closure-contract probe;
    /// [`monomorphize_entry`] surfaces the set as
    /// [`MonoStop::MissingBodies`] so a demand-driven caller can lower the
    /// bodies and retry. Demands recorded during a root that completed
    /// cleanly are rolled back to the root's watermark: they came from dead
    /// branches or recovered probes, and dead code needs no body. A
    /// `RefCell` because the probes only hold `&self`.
    missing_demands: std::cell::RefCell<Vec<(String, Vec<Type>)>>,
}

impl<'m, 'p> Monomorphizer<'m, 'p> {
    /// Build a monomorphizer over a MIR program: index functions, record methods,
    /// and closures so instances can be created on demand.
    fn new(mir: &'m MirProgram, program: &'p Program) -> Self {
        let mut by_method: HashMap<(&str, &str), &MirMethod> = HashMap::new();
        for m in &mir.methods {
            // Record methods carry no variant. A whole-sum method (`fun Sum.m`)
            // is duplicated into every variant by HIR lowering, so any one copy
            // stands for the method; the checker requires a method called on a
            // bare sum value to be common to (and signature-consistent across)
            // all variants, so first-copy-wins is the whole-sum dispatch.
            by_method
                .entry((m.type_symbol.as_str(), m.method.as_str()))
                .or_insert(m);
        }
        Monomorphizer {
            program,
            by_fn: mir
                .functions
                .iter()
                .map(|f| (f.symbol.as_str(), f))
                .collect(),
            by_method,
            by_closure: mir.closures.iter().map(|c| (c.id, c)).collect(),
            global_types: HashMap::new(),
            instances: HashMap::new(),
            in_progress: HashMap::new(),
            assumed_rets: HashMap::new(),
            instance_log: Vec::new(),
            rows: None,
            defer: None,
            closure_depth: 0,
            missing_demands: std::cell::RefCell::new(Vec::new()),
        }
    }

    /// The row table, derived from the HIR program on first use.
    fn rows(&mut self) -> &brass_typesys::RowInfo {
        if self.rows.is_none() {
            self.rows = Some(brass_typesys::RowInfo::analyze(self.program));
        }
        self.rows.as_ref().expect("rows just initialized")
    }

    /// Collect the instances created so far into a [`MonoProgram`] with a symbol
    /// index and the discovered globals.
    fn into_program(self, init_symbols: Vec<String>, hir: &'m Program) -> MonoProgram<'m> {
        let mut globals: Vec<(String, Type)> = self
            .global_types
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        globals.sort_by(|a, b| a.0.cmp(&b.0));
        let global_index = self.global_types;

        let mut functions: Vec<MonoFunction<'m>> = self.instances.into_values().collect();
        functions.sort_by(|a, b| a.symbol.cmp(&b.symbol));
        let index = functions
            .iter()
            .enumerate()
            .map(|(i, f)| (f.symbol.clone(), i))
            .collect();
        MonoProgram {
            functions,
            hir,
            globals,
            init_symbols,
            main_skip: None,
            deferred: self.defer.unwrap_or_default(),
            index,
            global_index,
        }
    }

    /// Whether `ty` fully describes a value's layout on its own: no type
    /// slots, every declared member resolved and fully known. A bare
    /// `-> Box` annotation on a type with an open member (an unannotated
    /// field, a slot) is REFINED by each body's instance -- the annotation
    /// under-describes the return, so a call on it cannot defer; the body
    /// must be instantiated for its precise result.
    fn self_describing(&self, ty: &Type) -> bool {
        match ty {
            Type::Record(n) | Type::Sum(n) => {
                let Some(info) = self.program.type_by_id(n.id) else {
                    return false;
                };
                if !info.slots.is_empty() {
                    return false;
                }
                let fields_ok = |fields: &[brass_hir::FieldInfo]| {
                    fields.iter().all(|f| {
                        f.resolved_ty
                            .as_ref()
                            .is_some_and(brass_hir::is_fully_known)
                    })
                };
                match &info.kind {
                    TypeKind::Record { fields, .. } => fields_ok(fields),
                    TypeKind::Sum { variants } => variants.iter().all(|v| fields_ok(&v.fields)),
                }
            }
            Type::Slice(e) | Type::Array(e, _) | Type::Nullable(e) => self.self_describing(e),
            Type::Tuple(ts) => ts.iter().all(|t| self.self_describing(t)),
            // A function-typed return carries a call contract the annotation
            // syntax cannot fully pin; stay on the instantiating path.
            Type::Fun(..) => false,
            _ => true,
        }
    }

    /// Record a demand for `base` at `arg_types` (deduplicated): one of the
    /// missing bodies this pass collects (see `missing_demands`).
    fn note_missing(&self, base: &str, arg_types: &[Type]) {
        let mut demands = self.missing_demands.borrow_mut();
        if !demands.iter().any(|(b, a)| b == base && a == arg_types) {
            demands.push((base.to_string(), arg_types.to_vec()));
        }
    }

    /// Instantiate a free function `base` for `type_args` (memoized).
    fn instantiate_fn(&mut self, base: &str, type_args: Vec<Type>) -> Result<String, String> {
        let sym = instance_symbol(base, &type_args);
        if self.instances.contains_key(&sym) {
            return Ok(sym);
        }
        let Some(&func) = self.by_fn.get(base) else {
            // Record what a demand-driven caller (the lazy pipeline, which
            // lowers function bodies into the MIR program on demand) would
            // need to make this call instantiable.
            self.note_missing(base, &type_args);
            return Err(format!("unknown function `{base}`"));
        };
        let sig_ret = self
            .program
            .functions
            .get(base)
            .and_then(|info| info.signature.ret_ty.clone());
        // A `T!` return fixes the Ok payload `T` (even if the inferred error type
        // is left open); keep it so the body cannot redefine it.
        let declared_ok = sig_ret.as_ref().and_then(result_concrete_ok);
        let ret_ann = sig_ret.filter(is_supported);
        self.type_and_store(
            sym,
            &func.body,
            &func.module,
            type_args,
            ret_ann,
            declared_ok,
            None,
            &[],
            Vec::new(),
            false,
            func.fallible,
        )
    }

    /// Type a callable body for one instance and store it. Shared by functions,
    /// methods, and closures. `capture_seed` pre-types a closure's captured
    /// locals (read from its environment); `captures` records them for the back
    /// end.
    ///
    /// On failure every instance stored during this frame is rolled back:
    /// mutual recursion types a callee against this frame's provisional return
    /// and stores it first, so letting it survive a failed frame would leave an
    /// instance calling a symbol that never materializes.
    #[allow(clippy::too_many_arguments)]
    fn type_and_store(
        &mut self,
        sym: String,
        body: &'m MirBody,
        module: &[String],
        type_args: Vec<Type>,
        ret_ann: Option<Type>,
        declared_ok: Option<Type>,
        seed_ret: Option<Type>,
        capture_seed: &[(LocalId, Type)],
        captures: Vec<LocalId>,
        is_closure: bool,
        fallible: bool,
    ) -> Result<String, String> {
        let watermark = self.instance_log.len();
        let cleanup_sym = sym.clone();
        let res = self.type_and_store_inner(
            sym,
            body,
            module,
            type_args,
            ret_ann,
            declared_ok,
            seed_ret,
            capture_seed,
            captures,
            is_closure,
            fallible,
        );
        if res.is_err() {
            for stored in self.instance_log.drain(watermark..) {
                self.instances.remove(&stored);
            }
            self.in_progress.remove(&cleanup_sym);
            self.assumed_rets.remove(&cleanup_sym);
        }
        res
    }

    #[allow(clippy::too_many_arguments)]
    fn type_and_store_inner(
        &mut self,
        sym: String,
        body: &'m MirBody,
        module: &[String],
        type_args: Vec<Type>,
        ret_ann: Option<Type>,
        declared_ok: Option<Type>,
        seed_ret: Option<Type>,
        capture_seed: &[(LocalId, Type)],
        captures: Vec<LocalId>,
        is_closure: bool,
        fallible: bool,
    ) -> Result<String, String> {
        if self.instances.contains_key(&sym) {
            return Ok(sym);
        }
        if body.params.len() != type_args.len() {
            return Err(format!(
                "`{sym}` expects {} argument(s), got {}",
                body.params.len(),
                type_args.len()
            ));
        }
        // The provisional return type mutual recursion may type against: the
        // authoritative annotation when there is one. A fallible callable's
        // annotation (`T!`) leaves the error payload open, so it is guessed as
        // the payload `error(...)`/a lifted `!` produces (the prelude `Error`
        // wrapping a string); the guess is validated against the final
        // inferred type when this frame completes.
        let provisional = ret_ann.clone().or_else(|| {
            if fallible {
                let err = self.guessed_error_payload();
                declared_ok.clone().map(|ok| result_type(ok, err))
            } else {
                None
            }
        });
        self.in_progress.insert(sym.clone(), provisional);

        let mut local_types: Vec<Option<Type>> = vec![None; body.locals.len()];
        for (i, p) in body.params.iter().enumerate() {
            local_types[p.index()] = Some(type_args[i].clone());
        }
        for (local, ty) in capture_seed {
            local_types[local.index()] = Some(ty.clone());
        }
        // A `let x: T = ...` binding fixed its local's type during lowering; seed it
        // so monomorphization preserves an annotation the initializer alone cannot
        // express (e.g. `let x: int32? = null`). A nominal annotation (an
        // uninitialized `let x: Point`) is a bare reference; resolve its field
        // substitution from the declaration so the seed is self-describing.
        for (i, decl) in body.locals.iter().enumerate() {
            if let Some(t) = decl.ty.as_known() {
                local_types[i] = Some(resolve_nominal(self.program, t));
            }
        }
        let mut ret = ret_ann;
        // A supported return annotation is authoritative; without one the return
        // type is inferred by joining the return operands below.
        let annotated = ret.is_some();

        // Seed the locals that flow into the returned record/variant from a known
        // aggregate's field types: a declared aggregate return, or the caller's
        // expected result (a witness-free constructor). An empty array field built
        // without a later `push` (`items = []` returned by `new()`) then takes its
        // element type from the result the caller fixed. Seeding leaves the return
        // type to be inferred from the now-concrete body, so the constructed record
        // keeps its full field substitution -- the return type is not forced to the
        // (possibly sparser) expected type.
        if let Some(seed) = ret.clone().or(seed_ret)
            && is_return_polymorphic_result(&seed)
        {
            seed_returned_aggregate(body, &seed, &mut local_types);
        }

        // Closure parameter sources: a direct in-body call, being passed to a
        // higher-order function (probed from the callee), or initializing a
        // record field with a declared function type. Array pushes give the
        // element type of an empty `[]` literal.
        let indirect_args = collect_indirect_args(body);
        let closure_passes = collect_closure_passes(body);
        let record_field_closures = collect_record_field_closures(body);
        let array_pushes = collect_array_pushes(body);

        // Fixpoint: resolve local and return types until stable. Calls are
        // instantiated as they become resolvable; self-recursion reads the
        // provisional return type computed so far.
        // A statement's type error is held against its block rather than raised:
        // a block a statically-known `if` makes unreachable never runs, so an arm
        // that cannot type for this instantiation (`s.split(..)` where `s` is an
        // array) must not reject the program. Only the last fixpoint round's
        // errors stand -- earlier rounds fail merely because types are still
        // filling in -- and only those in blocks that survive `reachable_blocks`
        // are reported, below.
        let mut block_errors: Vec<Option<String>> = vec![None; body.blocks.len()];
        loop {
            let mut changed = false;
            block_errors.iter_mut().for_each(|e| *e = None);
            for (i, block) in body.blocks.iter().enumerate() {
                for stmt in &block.stmts {
                    if let Err(e) = self.type_stmt(
                        stmt,
                        body,
                        &sym,
                        module,
                        &indirect_args,
                        &closure_passes,
                        &record_field_closures,
                        &array_pushes,
                        &mut local_types,
                        &ret,
                        fallible,
                        &mut changed,
                    ) && block_errors[i].is_none()
                    {
                        block_errors[i] = Some(e);
                    }
                }
                // A non-fallible callable's return type is the join of its return
                // operands'; a fallible one's is `Result<ok, err>`, inferred below.
                // Joining (rather than freezing the first return seen) lets a
                // `return null` path -- typed `never?` -- combine with a
                // value-returning path to that value's nullable type, instead of one
                // path alone fixing the result. A supported annotation overrides this.
                if !fallible
                    && !annotated
                    && let Terminator::Return(op) = &block.term
                    && let Some(t) = self.operand_type(op, &local_types)?
                {
                    let merged = match &ret {
                        Some(prev) => merge_return_types(prev, &t),
                        None => t,
                    };
                    if ret.as_ref() != Some(&merged) {
                        ret = Some(merged);
                        changed = true;
                    }
                }
            }
            if fallible
                && let Some(t) = self.infer_result_ret(body, &local_types, declared_ok.as_ref())?
                && (ret.is_none()
                    || ret
                        .as_ref()
                        .is_some_and(|cur| self.result_err_upgrade(cur, &t)))
            {
                ret = Some(t);
                changed = true;
            }
            if !changed {
                break;
            }
        }

        // Which blocks actually run, judged against the types resolved so far. An
        // untyped local stands in as `Never`, whose truthiness is unknown, so a
        // block is called dead only on a condition that really did resolve.
        let probe: Vec<Type> = local_types
            .iter()
            .map(|t| t.clone().unwrap_or(Type::Never))
            .collect();
        let reachable = reachable_blocks(body, &probe);
        if let Some(e) = reachable
            .iter()
            .zip(&block_errors)
            .find_map(|(live, e)| live.then_some(e.as_ref()).flatten())
        {
            return Err(e.clone());
        }

        // A return annotation is authoritative for the nominal it names, but a
        // BARE nominal annotation carries no substitution for the slots only
        // the body's constructions can type (an unannotated closure field).
        // Freezing the bare annotation washes those types out: the caller's
        // local goes bare, `resolve_nominal` cannot supply an unannotated
        // field, and reading it yields `?`. So join the reachable returns the
        // way the unannotated path does and promote to the joined instance
        // when it merely REFINES the annotation -- the nominal identity the
        // annotation states is preserved, its open slots are filled. Anything
        // else keeps the annotation, exactly the pre-existing behavior.
        if annotated && !fallible {
            let mut merged: Option<Type> = None;
            for (i, block) in body.blocks.iter().enumerate() {
                if reachable[i]
                    && let Terminator::Return(op) = &block.term
                    && let Some(t) = self.operand_type(op, &local_types)?
                {
                    merged = Some(match &merged {
                        Some(prev) => merge_return_types(prev, &t),
                        None => t,
                    });
                }
            }
            if let (Some(ann), Some(m)) = (&ret, merged)
                && &m != ann
                && is_refinement_of(ann, &m)
            {
                ret = Some(m);
            }
        } else if fallible
            && declared_ok.is_some()
            && let Some(t) = self.infer_result_ret(body, &local_types, None)?
            && ret
                .as_ref()
                .is_some_and(|cur| cur != &t && is_refinement_of(cur, &t))
        {
            // The fallible mirror: `-> T!` fixes the Ok payload, but a bare
            // nominal `T` needs the body's inferred Ok instance the same way.
            // Gated on `declared_ok` (not `annotated`): a `T!` annotation with
            // an open error payload is filtered from `ret_ann` as unsupported
            // while its Ok side still froze the payload via `declared_ok`.
            ret = Some(t);
        }

        let dead_locals = locals_only_in_dead_blocks(body, &reachable);
        let local_types = local_types
            .into_iter()
            .enumerate()
            .map(|(i, t)| match t {
                Some(t) => Ok(t),
                // A local no reachable block writes has no runtime slot, so its
                // type never matters: an unreachable arm's temporaries stay
                // untyped once that arm's statements were allowed to fail.
                None if dead_locals[i] => Ok(Type::Void),
                None => Err({
                    // Name the binding whose type stayed unknown; a bare local
                    // index means nothing to the programmer.
                    match binding_name_of(body, LocalId(i as u32)) {
                        Some(n) => format!("cannot infer the type of `{n}` in `{sym}`"),
                        None => format!(
                            "cannot infer the type of an expression temporary (local _{i}) in `{sym}`"
                        ),
                    }
                }),
            })
            .collect::<Result<Vec<_>, _>>()?;

        // A non-fallible callable with a non-null declared return cannot return an
        // always-null value (`never?` -- a `null` literal or an absent structural
        // field). This is the back-end backstop that keeps the deferred boundary
        // sound: a runtime type lacking a field the consumer reads
        // at a non-null type is rejected here rather than returning a null
        // reinterpreted as that type. Only *reachable* returns count: an `if` on a
        // statically-false condition (an absent field reads as `never?`) makes its
        // then-branch unreachable, so a `return absent.field` there is pruned, not
        // an error. (A `T?` return is also not rejected -- it may be a narrowed,
        // sound value; the front end's null check governs statically-typed code.)
        if !fallible
            && let Some(declared) = &ret
            && !matches!(declared, Type::Nullable(_))
        {
            let reachable = reachable_blocks(body, &local_types);
            for (i, block) in body.blocks.iter().enumerate() {
                if reachable[i]
                    && let Terminator::Return(op) = &block.term
                    && matches!(operand_type_of(op, &local_types), Type::Nullable(inner) if matches!(*inner, Type::Never))
                {
                    return Err(format!(
                        "returns a null value where `{}` is required (in `{sym}`)",
                        declared.display()
                    ));
                }
            }
        }
        // The instance's parameter types are the parameters' resolved types, not the
        // raw argument types. An annotated parameter keeps its declared type -- a
        // nullable `int32?` stays nullable even when a value or an omitted-null
        // argument is passed -- so callers coerce each argument to it (a value is
        // wrapped into the nullable cell, `null` stays null) and the body sees a
        // consistent nullable, not a bare value.
        let type_args: Vec<Type> = body
            .params
            .iter()
            .map(|p| local_types[p.index()].clone())
            .collect();
        let ret = ret.ok_or_else(|| format!("cannot infer return type of `{sym}`"))?;
        for t in local_types.iter().chain(std::iter::once(&ret)) {
            if !is_supported(t) {
                return Err(format!(
                    "type `{}` is not supported by the typed backend (in `{sym}`)",
                    t.display()
                ));
            }
        }
        self.validate(
            body,
            &sym,
            &local_types,
            &reachable_blocks(body, &local_types),
        )?;

        // Validate what mutual recursion assumed about this instance while it
        // was in progress: a mismatch (e.g. a fallible body whose error payload
        // is not the guessed `string`) must fail the frame -- the consumer was
        // already typed against the assumption. An assumption taken from a
        // bare annotation that the final return merely refines is compatible:
        // the consumer typed against the same nominal, just with fewer slots
        // pinned (the reverse -- a concrete assumption, bare final -- stays an
        // error).
        if let Some(assumed) = self.assumed_rets.remove(&sym)
            && assumed != ret
            && !is_refinement_of(&assumed, &ret)
        {
            return Err(format!(
                "mutual recursion typed `{sym}` as returning `{}`, but its body returns `{}`",
                assumed.display(),
                ret.display()
            ));
        }
        self.in_progress.remove(&sym);
        self.instance_log.push(sym.clone());
        self.instances.insert(
            sym.clone(),
            MonoFunction {
                body,
                symbol: sym.clone(),
                type_args,
                ret,
                local_types,
                captures,
                is_closure,
                fallible,
            },
        );
        Ok(sym)
    }

    /// Infer a fallible callable's `Result<ok, err>` return type: the `ok`
    /// payload from bare (non-`Result`) returns or explicit `Ok` constructions,
    /// the `err` payload from `error(...)` / `Err` constructions, and either from
    /// a directly-returned `Result`. `None` until both payloads are resolvable.
    ///
    /// `declared_ok` is the Ok payload fixed by a `T!` return annotation; when
    /// present it is authoritative (the body's own bare returns do not override it),
    /// so a then-branch returning a wrong type does not redefine the Ok payload --
    /// essential for the structural fold, which folds that branch away by comparing
    /// the return against the *declared* Ok type.
    fn infer_result_ret(
        &self,
        body: &MirBody,
        local_types: &[Option<Type>],
        declared_ok: Option<&Type>,
    ) -> Result<Option<Type>, String> {
        let mut ok_t: Option<Type> = declared_ok.cloned();
        let mut err_e: Option<Type> = None;
        // Whether some nullable-operand `expr!` returns `null` from this body:
        // the fallible return type is then wrapped in an outer `?`.
        let mut saw_null_prop = false;
        // Ok-slot notes merge instead of freezing on the first sighting: a
        // directly-returned `error(...)` Result carries an UNINHABITED Ok
        // payload (`void`), which must yield to the real payload of a bare
        // return elsewhere in the body -- first-come froze `ok` to void and
        // the real value was read back as 0. A later sighting that merely
        // REFINES the current one (same nominal, more slots pinned) also
        // upgrades it, mirroring the bare-annotation promotion.
        let note = |slot: &mut Option<Type>, t: Option<Type>| {
            let Some(t) = t else {
                return;
            };
            match slot {
                None => *slot = Some(t),
                Some(existing)
                    if matches!(existing, Type::Void | Type::Never)
                        && !matches!(t, Type::Void | Type::Never) =>
                {
                    *slot = Some(t)
                }
                Some(existing) if *existing != t && is_refinement_of(existing, &t) => {
                    *slot = Some(t)
                }
                _ => {}
            }
        };
        // The Err slot prefers the LIFTED payload (the prelude `Error`): a
        // body whose propagation/return rebuilds its Err arm contains both
        // the pre-lift construction and the lifted one, and the lifted one is
        // what the body hands back.
        let error_id = self.program.types.get("Error").map(|i| i.id);
        let note_err = |slot: &mut Option<Type>, t: Option<Type>| {
            let Some(t) = t else {
                return;
            };
            let is_error = |t: &Type| matches!(t, Type::Record(n) if Some(n.id) == error_id);
            match slot {
                None => *slot = Some(t),
                Some(existing) if !is_error(existing) && is_error(&t) => *slot = Some(t),
                _ => {}
            }
        };
        let propagated_returns = propagated_result_returns(body);
        let null_prop_blocks = null_prop_returns(body);
        let err_constructions = scan::err_construction_locals(body);
        // A construction defines this callable's payloads only when its value
        // can actually be RETURNED as the callable's result: seeds are the
        // return operands outside the propagate/null arms (whose payloads the
        // return scan below notes), expanded backward through `Use` copies.
        // Without the gate, the `!`-on-declared-subtype REBUILD -- an Ok/Err
        // reconstruction of the OPERAND, consumed by the propagation test --
        // would note the operand's Ok payload as this callable's.
        let mut returned: HashSet<LocalId> = HashSet::new();
        for (idx, block) in body.blocks.iter().enumerate() {
            if null_prop_blocks.contains(&idx) {
                continue;
            }
            if let Terminator::Return(Operand::Local(l)) = &block.term
                && !propagated_returns.contains(&(idx, *l))
            {
                returned.insert(*l);
            }
        }
        loop {
            let mut grew = false;
            for block in &body.blocks {
                for stmt in &block.stmts {
                    if let MirStmt::Assign(dest, Rvalue::Use(Operand::Local(src))) = stmt
                        && returned.contains(dest)
                        && returned.insert(*src)
                    {
                        grew = true;
                    }
                }
            }
            if !grew {
                break;
            }
        }
        for (block_idx, block) in body.blocks.iter().enumerate() {
            for stmt in &block.stmts {
                if let MirStmt::Assign(
                    dest,
                    Rvalue::Variant {
                        ty,
                        variant,
                        fields,
                    },
                ) = stmt
                    && ty == "Result"
                    && returned.contains(dest)
                {
                    for (fname, op) in fields {
                        let t = self.operand_type(op, local_types)?;
                        match (variant.as_str(), fname.as_str()) {
                            ("Ok", "value") => note(&mut ok_t, t),
                            ("Err", "error") => note_err(&mut err_e, t),
                            _ => {}
                        }
                    }
                }
            }
            if let Terminator::Return(op) = &block.term {
                // The null arm of a nullable `expr!` returns `null` itself; it
                // carries no Ok/Err payload, only the outer nullability.
                if null_prop_blocks.contains(&block_idx) {
                    saw_null_prop = true;
                    continue;
                }
                match self.operand_type(op, local_types)? {
                    // `expr!` lowers its error arm to `return <the original Result>`.
                    // That return can only execute for the `Err` variant, so it must
                    // not define this callable's `Ok` payload. The previous
                    // implementation treated the propagated `Result<File, string>`
                    // from `open(...)!` as evidence that the surrounding function
                    // returned `File!`, which made helpers such as `read_file`
                    // return a `Result<File, string>` at the typed back end even
                    // though their successful bare return was a `string`.
                    Some(Type::Sum(n))
                        if n.id == RESULT_TYPE_ID
                            && matches!(
                                op,
                                Operand::Local(local)
                                    if propagated_returns.contains(&(block_idx, *local))
                            ) =>
                    {
                        if let Some((_, err)) = n.result_payloads() {
                            note_err(&mut err_e, Some(err.clone()));
                        }
                    }
                    // A directly-returned Result carries both payloads -- unless
                    // the returned local is an `Err { .. }` construction (the `!`
                    // lift arm's rebuild): that return only executes an error
                    // path, and its Ok slot (seeded from the propagated operand)
                    // must not define this callable's Ok payload.
                    Some(Type::Sum(n)) if n.id == RESULT_TYPE_ID => {
                        if let Some((ok, err)) = n.result_payloads() {
                            if !matches!(op, Operand::Local(l) if err_constructions.contains(l)) {
                                note(&mut ok_t, Some(ok.clone()));
                            }
                            note_err(&mut err_e, Some(err.clone()));
                        }
                    }
                    // A bare value is the implicit Ok payload.
                    Some(other) => note(&mut ok_t, Some(other)),
                    None => {}
                }
            }
        }
        // A body that also returns `null` (a nullable `expr!`'s failure arm)
        // has a NULLABLE fallible return: `Result<ok, err>?`.
        let wrap = |t: Type| {
            if saw_null_prop {
                Type::Nullable(Box::new(t))
            } else {
                t
            }
        };
        match (ok_t, err_e) {
            (Some(ok), Some(err)) => Ok(Some(wrap(result_type(ok, err)))),
            // A callable made fallible only by a `T!` return annotation never
            // produces an error, so its error payload is unconstrained: default it
            // to `string` (the conventional error type) once the Ok payload is
            // known. Guarded by the absence of any error source, so a fallible body
            // that does raise errors still waits for the real error type.
            (Some(ok), None) if !body_has_error_source(body) => {
                Ok(Some(wrap(result_type(ok, Type::Str))))
            }
            // The mirror: a body whose every non-propagated return is an `Err`
            // construction produces no Ok value at all, so its Ok payload is
            // uninhabited for this instance and defaults to void. Guarded
            // conservatively -- any other return operand (a call the fixpoint
            // has not resolved yet) keeps the payload open.
            (None, Some(err))
                if returns_only_err_constructions(body, &propagated_returns, &null_prop_blocks) =>
            {
                Ok(Some(wrap(result_type(Type::Void, err))))
            }
            _ => Ok(None),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn type_stmt(
        &mut self,
        stmt: &MirStmt,
        body: &MirBody,
        cur_sym: &str,
        module: &[String],
        indirect_args: &HashMap<LocalId, Vec<Vec<Operand>>>,
        closure_passes: &HashMap<LocalId, (String, Vec<Operand>, usize)>,
        record_field_closures: &HashMap<LocalId, (LocalId, String, String)>,
        array_pushes: &HashMap<LocalId, Operand>,
        local_types: &mut [Option<Type>],
        cur_ret: &Option<Type>,
        fallible: bool,
        changed: &mut bool,
    ) -> Result<(), String> {
        match stmt {
            // An empty array literal `[]` gets its element type from a later
            // `push` (it is filled before use).
            MirStmt::Assign(local, Rvalue::Array(es)) if es.is_empty() => {
                if local_types[local.index()].is_none() {
                    // A literal copied straight into an annotated binding
                    // (`let frames: Frame[] = []` lowers through a temp) takes
                    // the binding's seeded type.
                    for block in &body.blocks {
                        for stmt in &block.stmts {
                            if let MirStmt::Assign(dst, Rvalue::Use(Operand::Local(src))) = stmt
                                && src == local
                                && let Some(t @ (Type::Slice(_) | Type::Array(..))) =
                                    &local_types[dst.index()]
                            {
                                local_types[local.index()] = Some(t.clone());
                                *changed = true;
                                return Ok(());
                            }
                        }
                    }
                    let Some(elem_op) = array_pushes.get(local) else {
                        let binding = match binding_name_of(body, *local) {
                            Some(n) => format!(" bound to `{n}`"),
                            None => String::new(),
                        };
                        // A synthetic symbol (an init body) means top-level
                        // code; the wrapper already says so, and the mangled
                        // name would only confuse.
                        let context = if cur_sym.starts_with(SYNTH_SIGIL) {
                            String::new()
                        } else {
                            format!(" (in `{cur_sym}`)")
                        };
                        return Err(format!(
                            "the element type of the empty array literal{binding} is unknown: \
                             annotate the binding (e.g. `let x: T[] = []`) or push a value into \
                             it first{context}"
                        ));
                    };
                    if let Some(elem) = self.operand_type(elem_op, local_types)? {
                        local_types[local.index()] = Some(Type::Slice(Box::new(elem)));
                        *changed = true;
                    }
                }
                Ok(())
            }
            // A closure local is typed from how it is used -- an in-body call or
            // being passed to a higher-order function; this also instantiates the
            // closure body.
            MirStmt::Assign(local, Rvalue::Closure { id, captures }) => {
                if local_types[local.index()].is_none()
                    && let Some(t) = self.closure_local_type(
                        *id,
                        captures,
                        *local,
                        module,
                        indirect_args,
                        closure_passes,
                        record_field_closures,
                        local_types,
                    )?
                {
                    local_types[local.index()] = Some(t);
                    *changed = true;
                }
                Ok(())
            }
            MirStmt::Assign(local, rv) => {
                // The destination's already-known type (a `let x: T` annotation, or
                // a call result seeded from the checker via a `Known` local) is the
                // expected type for the rvalue -- in particular a static call's
                // return-polymorphic result.
                let expected = local_types[local.index()].clone();
                let t = self.rvalue_type(
                    rv,
                    cur_sym,
                    module,
                    local_types,
                    cur_ret,
                    fallible,
                    expected.as_ref(),
                )?;
                match (expected, t) {
                    (None, Some(t)) => {
                        local_types[local.index()] = Some(t);
                        *changed = true;
                    }
                    // A Result local retypes when its Err payload upgrades to
                    // the lifted (prelude `Error`) shape: the pre-lift typing
                    // was provisional (see `infer_result_ret`).
                    (Some(cur), Some(t)) if self.result_err_upgrade(&cur, &t) => {
                        local_types[local.index()] = Some(t);
                        *changed = true;
                    }
                    // A destination seeded with a BARE nominal (the checker's
                    // seed of a call whose callee declares a bare `-> T`)
                    // upgrades to the rvalue's REFINEMENT of it: the nominal
                    // is unchanged, the slots only the callee's body could
                    // type (unannotated fields) fill in. Refinement strictly
                    // adds information, so the fixpoint stays monotone.
                    (Some(cur), Some(t)) if cur != t && is_refinement_of(&cur, &t) => {
                        local_types[local.index()] = Some(t);
                        *changed = true;
                    }
                    // A local first assigned `null` types as bare `never?`; a
                    // later concrete assignment upgrades it to that type's
                    // nullable (`let a: A? = null` then `a = A { .. }` makes
                    // the local `A?`). Without the upgrade the stale `never`
                    // element reaches codegen, where a nullable wrap of a
                    // "never" payload skips the retain and double-frees.
                    (Some(cur), Some(t)) if cur.is_null() && !t.is_null() => {
                        local_types[local.index()] = Some(match t {
                            t @ Type::Nullable(_) => t,
                            other => Type::Nullable(Box::new(other)),
                        });
                        *changed = true;
                    }
                    // Symmetrically, assigning `null` into a local first typed
                    // concrete makes it nullable, so the null representation
                    // (a null cell pointer) matches the local's element type.
                    (Some(cur), Some(t))
                        if t.is_null() && !cur.is_null() && !matches!(cur, Type::Nullable(_)) =>
                    {
                        local_types[local.index()] = Some(Type::Nullable(Box::new(cur)));
                        *changed = true;
                    }
                    _ => {}
                }
                Ok(())
            }
            // A call run for its side effect (the result is discarded).
            MirStmt::Eval(rv @ Rvalue::Call(..)) => {
                self.rvalue_type(rv, cur_sym, module, local_types, cur_ret, fallible, None)?;
                Ok(())
            }
            MirStmt::Eval(_) => {
                Err("unsupported statement (non-call eval) on the typed backend".into())
            }
            // `obj.field = v` / `arr[i] = v` stores: validated, no local type.
            MirStmt::Store(place, _) => match place.proj.as_slice() {
                [Projection::Field(_)] | [Projection::Index(_)] => Ok(()),
                _ => Err("nested projection stores are unsupported on the typed backend".into()),
            },
            // A top-level `let g = v`: record the global's concrete type (from
            // its initializer) for reads elsewhere.
            MirStmt::SetGlobal(name, op) => {
                if !self.global_types.contains_key(name)
                    && let Some(t) = self.operand_type(op, local_types)?
                {
                    if !is_supported(&t) {
                        return Err(format!(
                            "global `{name}` has unsupported type `{}`",
                            t.display()
                        ));
                    }
                    self.global_types.insert(name.clone(), t);
                    *changed = true;
                }
                Ok(())
            }
        }
    }

    /// The concrete type an rvalue produces (or `None` if not yet resolvable this
    /// pass). Errors on any rvalue outside the typed subset.
    /// Whether `new` is `old` with the Err payload upgraded to the lifted
    /// (prelude `Error`) shape. The pre-lift typing a fixpoint round derived
    /// from the raw construction is provisional; the lifted one is what the
    /// body actually hands back once the rebuild arm types.
    fn result_err_upgrade(&self, old: &Type, new: &Type) -> bool {
        let error_id = match self.program.types.get("Error") {
            Some(i) => i.id,
            None => return false,
        };
        let err_of = |t: &Type| match t {
            Type::Sum(n) if n.is_result_type() => n
                .substitution
                .get(brass_hir::types::RESULT_ERR_ERROR)
                .cloned(),
            _ => None,
        };
        match (err_of(old), err_of(new)) {
            (Some(o), Some(n)) => {
                !matches!(&o, Type::Record(r) if r.id == error_id)
                    && matches!(&n, Type::Record(r) if r.id == error_id)
            }
            _ => false,
        }
    }

    /// The error payload a fallible body is assumed to produce before its
    /// own inference completes: the prelude `Error` record wrapping a string,
    /// instantiated the way record construction types it (deep field
    /// substitution), so a mutual-recursion guess equals the final instance.
    /// Bare `string` in a program without the prelude.
    fn guessed_error_payload(&self) -> Type {
        let Some(info) = self.program.types.get("Error") else {
            return Type::Str;
        };
        let TypeKind::Record { fields, .. } = &info.kind else {
            return Type::Str;
        };
        let mut subst = brass_hir::Substitution::empty();
        for f in fields {
            if f.name == "value" {
                subst.insert("value", Type::Str);
            } else if let Some(t) = &f.resolved_ty {
                subst.insert(f.name.clone(), resolve_nominal(self.program, t));
            }
        }
        Type::Record(brass_hir::NominalType::with_substitution(
            info.id,
            info.name.clone(),
            subst,
        ))
    }

    #[allow(clippy::too_many_arguments)] // the fixpoint's full typing context
    fn rvalue_type(
        &mut self,
        rv: &Rvalue,
        cur_sym: &str,
        module: &[String],
        local_types: &[Option<Type>],
        cur_ret: &Option<Type>,
        fallible: bool,
        expected: Option<&Type>,
    ) -> Result<Option<Type>, String> {
        match rv {
            Rvalue::Use(op) => self.operand_type(op, local_types),
            // `typeof(x)`: always a string. The name itself is derived from the
            // operand's concrete type by the back ends once the instance is
            // fully typed; nothing here depends on the operand being resolved
            // yet, so the result does not wait on it.
            Rvalue::TypeName(_) => Ok(Some(Type::Str)),
            Rvalue::Bin(op, a, b) => {
                if is_comparison(*op) || matches!(op, BinOp::And | BinOp::Or) {
                    Ok(Some(Type::Bool))
                } else {
                    self.binary_operand_type(a, b, local_types)
                }
            }
            Rvalue::Un(UnaryOp::Not, _) => Ok(Some(Type::Bool)),
            Rvalue::Un(_, a) => self.operand_type(a, local_types),
            // `print`/`println` are intercepted as typed I/O rather than
            // instantiating the stdlib's Value-based bodies.
            Rvalue::Call(Callee::Free(base), args) if base == "print" || base == "println" => {
                self.io_call_type(args, local_types)
            }
            Rvalue::Call(Callee::Free(base), args) => {
                let Some(arg_types) = self.arg_types(args, local_types)? else {
                    return Ok(None);
                };
                self.resolve_free(cur_sym, cur_ret, base, arg_types)
            }
            // `arr.push(v)`/`arr.insert(i, v)` are growable-array mutations (void),
            // not user methods.
            // The receiver may be a narrowed nullable array (`int32[]?` proven
            // non-null by an `if a` / `if a != null` guard). A guard does not retype
            // the MIR local, so it still carries the declared nullable; strip the
            // top-level nullable here, exactly as the back end unwraps the cell.
            Rvalue::Call(Callee::Method(name), args) if name == "push" || name == "insert" => {
                match self.operand_type(args.first().unwrap_or(&Operand::void()), local_types)? {
                    Some(t) => match unwrap_nullable(&t) {
                        Type::Slice(_) => Ok(Some(Type::Void)),
                        other => Err(format!("{name} on non-array `{}`", other.display())),
                    },
                    None => Ok(None),
                }
            }
            // `arr.remove(i) -> T` returns the removed element.
            Rvalue::Call(Callee::Method(name), args) if name == "remove" => {
                match self.operand_type(args.first().unwrap_or(&Operand::void()), local_types)? {
                    Some(t) => match unwrap_nullable(&t) {
                        Type::Slice(inner) => Ok(Some((**inner).clone())),
                        other => Err(format!("remove on non-array `{}`", other.display())),
                    },
                    None => Ok(None),
                }
            }
            // `arr.pop() -> T?` returns the last element as a nullable (`_array_pop`).
            Rvalue::Call(Callee::Method(name), args) if name == "pop" => {
                match self.operand_type(args.first().unwrap_or(&Operand::void()), local_types)? {
                    Some(t) => match unwrap_nullable(&t) {
                        Type::Slice(inner) => Ok(Some(Type::Nullable(inner.clone()))),
                        other => Err(format!("pop on non-array `{}`", other.display())),
                    },
                    None => Ok(None),
                }
            }
            // `arr.len()` / `s.len()`: the array/string length builtin in UFCS method
            // form (`len(x)` and `x.len()` are equivalent), an `int64`.
            Rvalue::Call(Callee::Method(name), args) if name == "len" => {
                match self.operand_type(args.first().unwrap_or(&Operand::void()), local_types)? {
                    Some(t) => match unwrap_nullable(&t) {
                        Type::Slice(_) | Type::Array(..) | Type::Str => {
                            Ok(Some(Type::Int(IntKind::I64)))
                        }
                        other => Err(format!(
                            "len on `{}` (expected an array or string)",
                            other.display()
                        )),
                    },
                    None => Ok(None),
                }
            }
            Rvalue::Call(Callee::Method(name), args) => {
                self.method_call_type(name, args, cur_sym, cur_ret, local_types)
            }
            Rvalue::Call(Callee::Static { ty, method }, args) => self.static_call_type(
                ty,
                method,
                args,
                cur_sym,
                cur_ret,
                module,
                local_types,
                expected,
            ),
            // `value_matches` (variant test) yields bool; `panic` yields void;
            // other builtins are out of scope.
            Rvalue::Call(Callee::Builtin(name), args) => match name.as_str() {
                "value_matches" => Ok(Some(Type::Bool)),
                // `__deep_copy(x)` produces a value of the same type as `x` (a fresh
                // copy of an aggregate; a balanced pass-through otherwise).
                "__deep_copy" => match args.first() {
                    Some(op) => self.operand_type(op, local_types),
                    None => Ok(Some(Type::Void)),
                },
                // `__present(x)` is the `if let x = e` presence test: false for a
                // null, true for anything else. Non-nullable subjects fold
                // statically (see `cond_static_truthiness`).
                "__present" => Ok(Some(Type::Bool)),
                // `__nonnull(x)` narrows a nullable to its inner type (the if-let
                // binding of a nullable, proven non-null); a non-nullable is itself.
                "__nonnull" => match args.first() {
                    Some(op) => Ok(self
                        .operand_type(op, local_types)?
                        .map(|t| unwrap_nullable(&t).clone())),
                    None => Ok(Some(Type::Void)),
                },
                // `r!` lowers to `result_is_ok(r)` + an Ok-payload load + Err
                // propagation; the first is a tag test (bool).
                "result_is_ok" => Ok(Some(Type::Bool)),
                "panic" => Ok(Some(Type::Void)),
                // `_panic(msg)`: the user-facing runtime abort (std `assert`), with
                // a runtime string message (vs. the codegen-internal `panic`).
                "_panic" => Ok(Some(Type::Void)),
                "len" | "array_len" => Ok(Some(Type::Int(IntKind::I64))),
                // Pure float math primitives map to LLVM intrinsics.
                "_float_sqrt" | "_float_floor" | "_float_ceil" | "_float_pow" => {
                    Ok(Some(Type::Float(FloatKind::F64)))
                }
                // Integer width conversions: widen is infallible
                // (int64), narrow yields a range-checked Result.
                "_int_widen" => Ok(Some(Type::Int(IntKind::I64))),
                "_int_narrow" => Ok(Some(result_type(Type::Int(IntKind::I64), Type::Str))),
                // String primitives over typed strings/arrays (no boxed Value).
                "_string_slice" => Ok(Some(Type::Str)),
                "_string_bytes" => Ok(Some(Type::Slice(Box::new(Type::Int(IntKind::U8))))),
                // `_string_find` -> position or null.
                "_string_find" => Ok(Some(Type::Nullable(Box::new(Type::Int(IntKind::I64))))),
                "_string_char_at" => Ok(Some(Type::Nullable(Box::new(Type::Str)))),
                "_string_from_bytes" => Ok(Some(result_type(Type::Str, Type::Str))),
                // Named numeric/string conversion primitives,
                // callable directly as well as through the `Type.from`/`parse` and
                // `+` forms.
                "_string_concat" => Ok(Some(Type::Str)),
                "_string_cmp" => Ok(Some(Type::Int(IntKind::I32))),
                "_int_to_string" | "_float_to_string" => Ok(Some(Type::Str)),
                "_int_parse" => Ok(Some(result_type(Type::Int(IntKind::I64), Type::Str))),
                "_float_parse" => Ok(Some(result_type(Type::Float(FloatKind::F64), Type::Str))),
                "_int_to_float" => Ok(Some(Type::Float(FloatKind::F64))),
                "_float_to_int" => Ok(Some(result_type(Type::Int(IntKind::I64), Type::Str))),
                // Standalone stdio primitives (the prelude's `print`/`println`
                // bodies and `input`), no `File` involved.
                "_print_str" | "_println_str" => Ok(Some(Type::Void)),
                "_stdin_read" => Ok(Some(result_type(
                    Type::Slice(Box::new(Type::Int(IntKind::U8))),
                    Type::Str,
                ))),
                "_argv" => Ok(Some(Type::Slice(Box::new(Type::Str)))),
                "_flush" => Ok(Some(Type::Void)),
                // `to_string` only has a typed conversion for scalars/strings;
                // other arguments fall back so formatting stays correct.
                "to_string" => match args.first() {
                    Some(op) => match self.operand_type(op, local_types)? {
                        Some(t) if is_printable(&t) => Ok(Some(Type::Str)),
                        Some(t) => Err(format!(
                            "to_string of `{}` is unsupported on the typed backend",
                            t.display()
                        )),
                        None => Ok(None),
                    },
                    None => Ok(Some(Type::Str)),
                },
                "print" | "println" => self.io_call_type(args, local_types),
                // `spawn(f)` runs `f` on a thread and yields nothing. `with(obj,
                // f)` acquires `obj` and yields `f`'s result (its closure return).
                "spawn" => Ok(Some(Type::Void)),
                // `sync()` joins all spawned threads (R6 value-observability).
                "sync" => Ok(Some(Type::Void)),
                // `_cown(c)` / `_freeze(c)` promote a spawn capture to a shared
                // owner before the spawn; each yields nothing.
                "_cown" | "_freeze" => Ok(Some(Type::Void)),
                // Deferred dispatch: resolves+calls a consumer at
                // runtime, yielding `int32`; not a user function to instantiate.
                "__rt_dispatch" => Ok(Some(Type::Int(IntKind::I32))),
                "with" => match args.get(1) {
                    Some(op) => match self.operand_type(op, local_types)? {
                        Some(Type::Fun(_, ret)) => Ok(Some(*ret)),
                        Some(other) => Err(format!(
                            "`with` expects a closure, found `{}`",
                            other.display()
                        )),
                        None => Ok(None),
                    },
                    None => Err("`with` expects (cown, closure)".into()),
                },
                // `_with_all(f, c0, ...)` yields the guarded body closure's result.
                "_with_all" => match args.first() {
                    Some(op) => match self.operand_type(op, local_types)? {
                        Some(Type::Fun(_, ret)) => Ok(Some(*ret)),
                        Some(other) => Err(format!(
                            "`_with_all` expects a closure, found `{}`",
                            other.display()
                        )),
                        None => Ok(None),
                    },
                    None => Err("`_with_all` expects (closure, cowns...)".into()),
                },
                // Native-plugin dispatch (`_plugin_[f]call_<t>`) carries its
                // return in the name's suffix; see the shared decoder. Read in
                // the fallthrough so the name decodes once, and a name that is
                // neither still reports as unsupported.
                other => match brass_hir::plugin_builtin_return(other) {
                    Some(ret) => Ok(Some(ret)),
                    None => Err(format!(
                        "builtin `{other}` is unsupported on the typed backend"
                    )),
                },
            },
            // Indirect (closure) call: the callee local's `Fun` type gives the
            // result. The closure instance was created when the local was typed.
            Rvalue::Call(Callee::Indirect(callee), _) => {
                match self.operand_type(callee, local_types)? {
                    Some(Type::Fun(_, ret)) => Ok(Some(*ret)),
                    Some(other) => Err(format!(
                        "indirect call of non-function `{}`",
                        other.display()
                    )),
                    None => Ok(None),
                }
            }
            // A narrowed nullable aggregate (`p: P?` / `a: int32[]?` proven non-null
            // by a guard) keeps its declared nullable on the MIR local, so strip the
            // top-level nullable before reading a field or element.
            Rvalue::Load(place) => match place.proj.as_slice() {
                [Projection::Field(field)] => {
                    match local_types[place.local.index()]
                        .as_ref()
                        .map(unwrap_nullable)
                    {
                        // A member that can only be a method is the compile-time
                        // presence value the checker typed: the method's own name,
                        // or null when a primitive class has no such member (see
                        // `Program::member_presence`). Everything else is an
                        // ordinary record/sum field read.
                        Some(ty) => match self.program.member_presence(ty, field) {
                            Some(true) => Ok(Some(Type::Str)),
                            Some(false) => Ok(Some(Type::null())),
                            None => match ty {
                                Type::Record(n) => self.record_field_type(n, field),
                                Type::Sum(n) => self.sum_field_type(n, field),
                                other => Err(format!(
                                    "field access `.{field}` on non-aggregate `{}`",
                                    other.display()
                                )),
                            },
                        },
                        None => Ok(None),
                    }
                }
                // Array/slice element read: the element type is the sequence's. A
                // tuple is read at a constant position, yielding that element's type.
                [Projection::Index(idx)] => {
                    match local_types[place.local.index()]
                        .as_ref()
                        .map(unwrap_nullable)
                    {
                        Some(Type::Slice(elem) | Type::Array(elem, _)) => {
                            Ok(Some((**elem).clone()))
                        }
                        Some(Type::Tuple(elems)) => match const_operand_index(idx) {
                            Some(k) if k < elems.len() => Ok(Some(elems[k].clone())),
                            Some(k) => Err(format!("tuple index {k} out of bounds")),
                            None => Err("a tuple must be indexed by a constant integer".into()),
                        },
                        Some(other) => Err(format!("indexing non-array `{}`", other.display())),
                        None => Ok(None),
                    }
                }
                _ => Err("nested projections are unsupported on the typed backend".into()),
            },
            Rvalue::Record { ty, fields } => self.record_type(module, ty, fields, local_types),
            // `T.from(v)` always types `T?`; the per-instance codegen yields the
            // record (when the concrete source has every field) or null. Build `T`'s
            // declared record type (the deserialize-boundary type) and wrap nullable.
            Rvalue::RecordFrom { ty, .. } => match boundary_record_type(self.program, module, ty) {
                Some(t) => Ok(Some(Type::Nullable(Box::new(t)))),
                None => Err(format!(
                    "`{ty}.from`: every field of the target record needs a declared type"
                )),
            },
            // The view of a callee parameter's row over this instance's concrete
            // structural source: the canonical structural record whose type_key
            // collapses every argument shape with the same view into one callee
            // instance. Guarded fields are nullable slots (absent/mismatched ->
            // null at construction). A non-structural or row-less source (a
            // defensive case lowering should not produce) passes through as the
            // identity, keeping type and value in agreement with codegen.
            Rvalue::RecordView {
                callee,
                param,
                source,
            } => {
                let Some(src) = self.operand_type(source, local_types)? else {
                    return Ok(None);
                };
                match (
                    brass_hir::peel_modes(&src),
                    self.rows().function_param(callee, *param),
                ) {
                    (Type::Record(n), Some(prow))
                        if n.id == brass_hir::STRUCTURAL_RECORD_ID && prow.eligible =>
                    {
                        brass_typesys::view_type(&prow.row, n).map(Some)
                    }
                    _ => Ok(Some(src)),
                }
            }
            // A `Result` construction takes its destination's or the enclosing
            // fallible callable's inferred `Result` type; other (annotated)
            // sums resolve directly.
            Rvalue::Variant {
                ty,
                variant,
                fields,
            } => {
                if ty == "Result" {
                    // The enclosing return may be `Result<..>?` (a body that
                    // also propagates a null); the construction is the Result.
                    let ctx = expected
                        .filter(|t| t.is_result_type())
                        .cloned()
                        .or_else(|| {
                            cur_ret
                                .as_ref()
                                .map(|t| unwrap_nullable(t).clone())
                                .filter(|t| t.is_result_type())
                        });
                    if ctx.is_some() {
                        return Ok(ctx);
                    }
                    // A fallible body's ret is still forming: wait for it
                    // (the fixpoint supplies it, including for an err-only
                    // body -- see `infer_result_ret`'s defaults). Only a
                    // NON-fallible context (`println(error(..))` at a top
                    // level) never gets one, so the construction itself
                    // carries its variant's payload and the OTHER side --
                    // uninhabited for this value -- defaults to void.
                    if fallible {
                        return Ok(None);
                    }
                    let (mut ok, mut err) = (Type::Void, Type::Void);
                    for (fname, op) in fields {
                        let Some(t) = self.operand_type(op, local_types)? else {
                            return Ok(None);
                        };
                        match (variant.as_str(), fname.as_str()) {
                            ("Ok", "value") => ok = t,
                            ("Err", "error") => err = t,
                            _ => {}
                        }
                    }
                    Ok(Some(result_type(ok, err)))
                } else {
                    self.variant_type(module, ty, variant, fields, local_types)
                }
            }
            Rvalue::Array(es) => self.array_type(es, cur_sym, local_types),
            // A global read: its type is recorded when its init body is typed.
            Rvalue::Global(name) => Ok(self.global_types.get(name).cloned()),
            Rvalue::Closure { .. } => Err("closures are unsupported on the typed backend".into()),
        }
    }

    /// Type an instance-method call `recv.name(args)`.
    fn method_call_type(
        &mut self,
        name: &str,
        args: &[Operand],
        cur_sym: &str,
        cur_ret: &Option<Type>,
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        let Some(mut arg_types) = self.arg_types(args, local_types)? else {
            return Ok(None);
        };
        // A narrowed `T?` receiver dispatches as `T`: the checker only lets a
        // method call through when a guard proved the receiver non-null, and
        // the call boundary unwraps the cell, so the instance is created for
        // the inner type (matching `method_symbol`'s keying).
        if let Type::Nullable(inner) = &arg_types[0] {
            arg_types[0] = (**inner).clone();
        }
        // A genuine record or whole-sum method takes priority.
        if let Type::Record(n) | Type::Sum(n) = &arg_types[0]
            && let Some(info) = self.program.type_by_id(n.id)
        {
            let type_symbol = info.symbol.clone();
            if let Some(&method) = self.by_method.get(&(type_symbol.as_str(), name)) {
                let ret_ann = method_ret_annotation(self.program, &type_symbol, name);
                let target = method_symbol(name, &arg_types);
                let body = &method.body;
                let module = method.module.clone();
                let fallible = method.fallible;
                return self.resolve_callable(
                    cur_sym, cur_ret, target, body, &module, arg_types, ret_ann, None, fallible,
                );
            }
        }
        // A STRUCTURAL (anonymous) receiver resolves a method by satisfaction:
        // the record type declaring `name` whose declared fields the value
        // provides. The checker has already enforced that exactly one
        // module-visible candidate exists; candidates are scanned in sorted
        // symbol order so the pick is deterministic here too.
        if let Type::Record(n) = &arg_types[0]
            && n.id == brass_hir::STRUCTURAL_RECORD_ID
        {
            let mut symbols: Vec<&String> = self
                .program
                .types
                .values()
                .filter_map(|info| {
                    let TypeKind::Record { fields, methods } = &info.kind else {
                        return None;
                    };
                    if !methods.contains_key(name) {
                        return None;
                    }
                    let satisfied = fields.iter().all(|f| match n.substitution.get(&f.name) {
                        None => false,
                        Some(have) => match &f.resolved_ty {
                            Some(decl) if brass_hir::is_fully_known(decl) => have == decl,
                            _ => true,
                        },
                    });
                    satisfied.then_some(&info.symbol)
                })
                .collect();
            symbols.sort();
            if let Some(&symbol) = symbols.first()
                && let Some(&method) = self.by_method.get(&(symbol.as_str(), name))
            {
                let ret_ann = method_ret_annotation(self.program, symbol, name);
                let target = method_symbol(name, &arg_types);
                let body = &method.body;
                let module = method.module.clone();
                let fallible = method.fallible;
                return self.resolve_callable(
                    cur_sym, cur_ret, target, body, &module, arg_types, ret_ann, None, fallible,
                );
            }
        }
        // A stdlib method on a primitive/array receiver (`fun string.split`,
        // `fun infer[].map`), dispatched by the receiver's class. Its body is an
        // ordinary function stored under a class-qualified symbol; instantiate it
        // for the call's argument tuple.
        if let Some(class) = arg_types[0].primitive_class()
            && let Some(sym) = self
                .program
                .primitive_methods
                .get(&(class.to_string(), name.to_string()))
        {
            let sym = sym.clone();
            return self.resolve_free(cur_sym, cur_ret, &sym, arg_types);
        }
        Err(format!(
            "no method `{name}` for `{}`",
            arg_types[0].display()
        ))
    }

    /// Type a static call `Type.method(args)`.
    #[allow(clippy::too_many_arguments)]
    fn static_call_type(
        &mut self,
        ty: &str,
        method_name: &str,
        args: &[Operand],
        cur_sym: &str,
        cur_ret: &Option<Type>,
        module: &[String],
        local_types: &[Option<Type>],
        expected: Option<&Type>,
    ) -> Result<Option<Type>, String> {
        let Some(arg_types) = self.arg_types(args, local_types)? else {
            return Ok(None);
        };
        // Numeric/string conversions (`Type.from`/`Type.parse`) are runtime-
        // recognized, not user static methods.
        if let Some(ret) = numeric_conv_ret(ty, method_name) {
            return Ok(Some(ret));
        }
        // `File.stdin/stdout/stderr` are runtime standard streams.
        let info = self
            .program
            .resolve_type(module, ty)
            .ok_or_else(|| format!("unknown type `{ty}`"))?;
        let type_symbol = info.symbol.clone();
        let method = *self
            .by_method
            .get(&(type_symbol.as_str(), method_name))
            .ok_or_else(|| format!("type `{ty}` has no static method `{method_name}`"))?;
        let ret_ann = method_ret_annotation(self.program, &type_symbol, method_name);
        // The caller's expected result type (the destination local's resolved type,
        // seeded from the checker) seeds a witness-free constructor's empty array
        // fields and keys a return-polymorphic, no-argument constructor by its
        // result. It does *not* override the body-inferred return: seeding makes the
        // body's own return concrete, and the constructed record carries the full
        // field substitution the back end lays out from.
        let seed = expected
            .filter(|t| is_return_polymorphic_result(t))
            .cloned();
        let target = static_symbol(ty, method_name, &arg_types, seed.as_ref());
        let body = &method.body;
        let mmodule = method.module.clone();
        let fallible = method.fallible;
        self.resolve_callable(
            cur_sym, cur_ret, target, body, &mmodule, arg_types, ret_ann, seed, fallible,
        )
    }

    /// Resolve a call to an already-located method/static body: handle
    /// self-recursion and mutual recursion, instantiate, and return the instance
    /// return type.
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::too_many_arguments)]
    fn resolve_callable(
        &mut self,
        cur_sym: &str,
        cur_ret: &Option<Type>,
        target: String,
        body: &'m MirBody,
        module: &[String],
        type_args: Vec<Type>,
        ret_ann: Option<Type>,
        seed_ret: Option<Type>,
        fallible: bool,
    ) -> Result<Option<Type>, String> {
        if target == cur_sym {
            return Ok(cur_ret.clone());
        }
        // The target is an ancestor on the instantiation stack (mutual
        // recursion). With an authoritative return annotation the instance type
        // is already fixed, so this call types against it and the ancestor frame
        // completes the instance itself; without one nothing sound is known.
        if let Some(provisional) = self.in_progress.get(&target) {
            return match provisional.clone() {
                Some(t) => {
                    self.assumed_rets.insert(target, t.clone());
                    Ok(Some(t))
                }
                None => Err(format!(
                    "mutual recursion (`{cur_sym}` <-> `{target}`) needs an explicit return type annotation on `{target}`"
                )),
            };
        }
        // The Ok payload of a `T!` return is authoritative even when the full
        // annotation is unsupported (open error payload); compute it from the
        // raw annotation, then filter for the provisional/return type.
        let declared_ok = ret_ann.as_ref().and_then(result_concrete_ok);
        let ret_ann = ret_ann.filter(is_supported);
        let sym = self.type_and_store(
            target,
            body,
            module,
            type_args,
            ret_ann,
            declared_ok,
            seed_ret,
            &[],
            Vec::new(),
            false,
            fallible,
        )?;
        Ok(self.instances.get(&sym).map(|i| i.ret.clone()))
    }

    /// Resolve a free-function call, returning its instance return type (or
    /// `None` when an argument type is not yet known and the caller should retry).
    fn resolve_free(
        &mut self,
        cur_sym: &str,
        cur_ret: &Option<Type>,
        base: &str,
        arg_types: Vec<Type>,
    ) -> Result<Option<Type>, String> {
        let target = instance_symbol(base, &arg_types);
        if target == cur_sym {
            return Ok(cur_ret.clone());
        }
        // Mutual recursion; see resolve_callable for the provisional contract.
        if let Some(provisional) = self.in_progress.get(&target) {
            return match provisional.clone() {
                Some(t) => {
                    self.assumed_rets.insert(target, t.clone());
                    Ok(Some(t))
                }
                None => Err(format!(
                    "mutual recursion (`{cur_sym}` <-> `{target}`) needs an explicit return type annotation on `{target}`"
                )),
            };
        }
        if let Some(sig) = self.deferrable(base, &arg_types) {
            let ret = sig.ret.clone();
            let symbol = instance_symbol(base, &arg_types);
            if let Some(targets) = self.defer.as_mut() {
                targets.insert(symbol, sig);
            }
            return Ok(Some(ret));
        }
        // A missing body in a demand-driven run: record the demand and fail
        // the STATEMENT (a held block error) rather than the frame, so this
        // same pass keeps walking and collects every other missing body it
        // can see -- the retry count becomes the call graph's depth, not its
        // node count. The existing block-error rules keep this sound: a
        // reachable block's held error fails the frame after the walk (so
        // nothing typed under a live miss is ever emitted -- an annotated
        // destination local would otherwise satisfy the unresolved-temporary
        // validation), while a statically dead block's is dropped, and the
        // clean root then rolls the dead demand back at its watermark.
        if self.defer.is_some()
            && !self.by_fn.contains_key(base)
            && self.program.functions.contains_key(base)
        {
            self.note_missing(base, &arg_types);
            return Err(format!("missing body `{base}` (demanded)"));
        }
        let sym = self.instantiate_fn(base, arg_types)?;
        Ok(self.instances.get(&sym).map(|i| i.ret.clone()))
    }

    /// The deferral contract (the lazy JIT): a call to `base`, whose MIR body
    /// is not in the program, compiles to a runtime-resolved call when its
    /// whole ABI is annotation-determined -- a fully concrete DECLARED return
    /// (an inferred or fallible return needs the body; a body that raises
    /// errors changes the ABI to a `Result`), and fully known argument types
    /// (instances are keyed by them). Never inside a closure body: closure
    /// code can cross to worker threads, which cannot compile.
    fn deferrable(&self, base: &str, arg_types: &[Type]) -> Option<DeferredSig> {
        self.defer.as_ref()?;
        if self.closure_depth > 0 || self.by_fn.contains_key(base) {
            return None;
        }
        let info = self.program.functions.get(base)?;
        let ret = info.signature.ret_ty.clone()?;
        if !brass_hir::is_fully_known(&ret) || !is_supported(&ret) {
            return None;
        }
        if !self.self_describing(&ret) {
            return None;
        }
        if brass_mir::constructs_error_block(&info.decl.body) {
            return None;
        }
        if !arg_types.iter().all(brass_hir::is_fully_known) {
            return None;
        }
        if info.decl.params.len() != arg_types.len() {
            return None;
        }
        // The site's ABI mirrors the instance's parameter typing exactly:
        // lowering seeds a parameter local's type only from a SIMPLE
        // annotation (`resolve_simple_type` -- scalars, strings, arrays and
        // nullables of them), and monomorphization's declared-type override
        // reads that local. So a simple annotation wins here (an `int64`
        // parameter widens an `int32` argument at the site), while a nominal
        // annotation leaves the CALLER's argument type in charge -- the
        // instance is specialized per caller type, `Node?` taking a non-null
        // `Node` argument included.
        let mut params = Vec::with_capacity(arg_types.len());
        for (arg, p) in arg_types.iter().zip(&info.decl.params) {
            match p.ty.as_ref().and_then(brass_mir::resolve_simple_type) {
                Some(decl) => params.push(decl),
                None => params.push(arg.clone()),
            }
        }
        Some(DeferredSig {
            base: base.to_string(),
            type_args: arg_types.to_vec(),
            params,
            ret,
        })
    }

    /// Type a `print`/`println` call: void, accepted only for a printable
    /// (scalar or string) argument so its output matches the boxed path.
    fn io_call_type(
        &self,
        args: &[Operand],
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        match args.first() {
            None => Ok(Some(Type::Void)),
            Some(op) => match self.operand_type(op, local_types)? {
                Some(t) if is_printable(&t) => Ok(Some(Type::Void)),
                Some(t) => Err(format!(
                    "print of `{}` is unsupported on the typed backend",
                    t.display()
                )),
                None => Ok(None),
            },
        }
    }

    /// Concrete types of every argument operand, or `None` if one is not yet
    /// resolvable.
    fn arg_types(
        &self,
        args: &[Operand],
        local_types: &[Option<Type>],
    ) -> Result<Option<Vec<Type>>, String> {
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            match self.operand_type(a, local_types)? {
                Some(t) => out.push(t),
                None => return Ok(None),
            }
        }
        Ok(Some(out))
    }

    fn operand_type(
        &self,
        op: &Operand,
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        match op {
            Operand::Local(id) => Ok(local_types[id.index()].clone()),
            Operand::Const(lit) => const_type(lit).map(Some),
        }
    }

    fn binary_operand_type(
        &self,
        a: &Operand,
        b: &Operand,
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        let ta = self.operand_type(a, local_types)?;
        let tb = self.operand_type(b, local_types)?;
        let a_local = matches!(a, Operand::Local(_));
        let b_local = matches!(b, Operand::Local(_));
        // Both operand types known: the shared operand rule (also used by the
        // back ends for comparison operands) decides, so the typer and codegen
        // can never disagree on literal adaptation or the common numeric type.
        if let (Some(ta), Some(tb)) = (&ta, &tb) {
            return Ok(Some(binary_operand_common(ta, tb, a_local, b_local)));
        }
        let pick = if a_local && ta.is_some() {
            ta
        } else if b_local && tb.is_some() {
            tb
        } else {
            ta.or(tb)
        };
        // This types the *result* of an arithmetic/bitwise op. Operating on a
        // (guarded) nullable narrows to its element type -- e.g. `value + 1` for
        // `value: int32?` yields `int32`, not `int32?` -- matching the free
        // `binary_operand_type` the back end uses for the operands.
        Ok(pick.map(|t| unwrap_nullable(&t).clone()))
    }

    /// The concrete record type produced by constructing `ty { fields }`: the
    /// nominal type with a substitution mapping each declared field to its value's
    /// type.
    fn record_type(
        &self,
        module: &[String],
        ty: &str,
        fields: &[(String, Operand)],
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        // An anonymous structure literal `{ f: v, ... }` (empty type name) is a
        // structural record: its field types come straight from the field values.
        if ty.is_empty() {
            let mut out = Vec::with_capacity(fields.len());
            for (name, op) in fields {
                match self.operand_type(op, local_types)? {
                    Some(t) => out.push((name.clone(), t)),
                    None => return Ok(None),
                }
            }
            return Ok(Some(brass_hir::structural_record(out)));
        }
        let info = self
            .program
            .resolve_type(module, ty)
            .ok_or_else(|| format!("unknown type `{ty}`"))?;
        let TypeKind::Record { fields: decl, .. } = &info.kind else {
            return Err(format!("`{ty}` is not a record type"));
        };
        let mut subst = Substitution::empty();
        for fdecl in decl {
            let value = fields
                .iter()
                .find(|(n, _)| *n == fdecl.name)
                .ok_or_else(|| format!("missing field `{}` of `{ty}`", fdecl.name))?;
            let t = match self.operand_type(&value.1, local_types)? {
                // A declared-nullable field keeps its declared type whatever
                // initializes it: a `null` carries the bare `Nullable(Never)` and
                // coerces to it, and a NON-null value is wrapped into the
                // nullable cell at the store -- recording the raw value type
                // (`Node { next: head }` recording `next=Node`) would make every
                // reader reinterpret the cell as the bare value and crash.
                // Essential for self-referential records. A declared type that
                // is not fully concrete (an `infer?` slot) still takes its type
                // from the constructed value.
                Some(got)
                    if matches!(&fdecl.resolved_ty,
                        Some(decl @ Type::Nullable(_)) if brass_hir::is_fully_known(decl))
                        && !matches!(&got,
                            Type::Nullable(inner) if !matches!(**inner, Type::Never)) =>
                {
                    fdecl.resolved_ty.clone().unwrap()
                }
                Some(t) => t,
                None => return Ok(None),
            };
            subst.insert(fdecl.name.clone(), t);
        }
        Ok(Some(Type::Record(NominalType::with_substitution(
            info.id,
            info.name.clone(),
            subst,
        ))))
    }

    /// The concrete sum type produced by constructing `ty.variant { fields }`. An
    /// annotated variant field's layout comes from the HIR, so only this variant's
    /// *unannotated* (dynamic) fields are recorded in the substitution -- keyed
    /// `Variant.field` -- with their constructed value's type, so a later match
    /// reads the field at its real type (mirrors `record_type` for records, and the
    /// front end's `check_lit_fields`).
    fn variant_type(
        &self,
        module: &[String],
        ty: &str,
        variant: &str,
        fields: &[(String, Operand)],
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        let info = self
            .program
            .resolve_type(module, ty)
            .ok_or_else(|| format!("unknown type `{ty}`"))?;
        let TypeKind::Sum { variants } = &info.kind else {
            return Err(format!("`{ty}` is not a sum type"));
        };
        let v = variants
            .iter()
            .find(|v| v.name == variant)
            .ok_or_else(|| format!("`{ty}` has no variant `{variant}`"))?;
        // Every variant field must be layoutable by the typed back end (a sized
        // scalar, a heap pointer, or an opaque unaccessed slot).
        for var in variants {
            for fld in &var.fields {
                if !variant_field_layoutable(self.program, &fld.resolved_ty) {
                    return Err(format!(
                        "variant field `{}.{}` has no concrete typed layout",
                        var.name, fld.name
                    ));
                }
            }
        }
        let mut subst = Substitution::empty();
        for fld in &v.fields {
            if fld.resolved_ty.as_ref().is_none_or(|t| t.is_unknown())
                && let Some((_, op)) = fields.iter().find(|(n, _)| n == &fld.name)
            {
                match self.operand_type(op, local_types)? {
                    Some(t) => subst.insert(format!("{variant}.{}", fld.name), t),
                    None => return Ok(None),
                }
            }
        }
        Ok(Some(Type::Sum(NominalType::with_substitution(
            info.id,
            info.name.clone(),
            subst,
        ))))
    }

    /// The concrete slice type of an array literal: a slice of the (uniform)
    /// element type. An empty literal cannot be typed on the typed backend.
    fn array_type(
        &self,
        es: &[Operand],
        cur_sym: &str,
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        if es.is_empty() {
            return Err(format!(
                "the element type of an empty array literal in expression position is unknown: \
                 bind it first with an annotated `let` (e.g. `let x: T[] = []`) (in `{cur_sym}`)"
            ));
        }
        let mut tys = Vec::with_capacity(es.len());
        for e in es {
            match self.operand_type(e, local_types)? {
                Some(t) => tys.push(t),
                None => return Ok(None),
            }
        }
        // A bracket literal whose elements all share a type is an array; one with
        // differing element types is a fixed-length tuple (matches the type
        // checker's classification of `[1, "s"]`).
        if tys.windows(2).all(|w| w[0] == w[1]) {
            Ok(Some(Type::Slice(Box::new(tys.into_iter().next().unwrap()))))
        } else {
            Ok(Some(Type::Tuple(tys)))
        }
    }

    /// The concrete type of field `field` of sum type `n`: a generic `Result`
    /// reads it from the nominal substitution (keyed `Variant.field`); an
    /// annotated sum reads the declared type in whichever variant defines it.
    fn sum_field_type(&self, n: &NominalType, field: &str) -> Result<Option<Type>, String> {
        let info = self
            .program
            .type_by_id(n.id)
            .ok_or_else(|| format!("unknown sum type id {}", n.id))?;
        let TypeKind::Sum { variants } = &info.kind else {
            return Err(format!("type id {} is not a sum", n.id));
        };
        // A variant-qualified field (`Variant.field`, from a variant pattern
        // binding) resolves in that variant; a bare name resolves in the first
        // variant that declares it (a field common to every variant).
        let (want_variant, fname) = match field.split_once('.') {
            Some((v, f)) => (Some(v), f),
            None => (None, field),
        };
        for v in variants {
            if want_variant.is_some_and(|w| w != v.name) {
                continue;
            }
            if v.fields.iter().any(|f| f.name == fname) {
                if let Some(t) = n.substitution.get(&format!("{}.{fname}", v.name)) {
                    return Ok(Some(resolve_nominal(self.program, t)));
                }
                let fld = v.fields.iter().find(|f| f.name == fname).unwrap();
                return Ok(fld
                    .resolved_ty
                    .clone()
                    .map(|t| resolve_nominal(self.program, &t)));
            }
        }
        Err(format!("sum `{}` has no field `{field}`", info.name))
    }

    /// A record field's concrete type. A constructed/generic record carries it in
    /// the nominal substitution; a bare reference (a declared nominal field type,
    /// e.g. a sum variant's `center: Point` once bound) falls back to the field's
    /// declared type in the HIR, so reading a nested record field still resolves.
    fn record_field_type(&self, n: &NominalType, field: &str) -> Result<Option<Type>, String> {
        if let Some(t) = n.substitution.get(field) {
            return Ok(Some(resolve_nominal(self.program, t)));
        }
        // A declared record contributes its field's declared type (or `None` --
        // deferred -- for a present-but-unannotated field); a structural record (no
        // declaration, e.g. an anonymous structure) has only its substitution fields.
        if let Some(info) = self.program.type_by_id(n.id)
            && let TypeKind::Record { fields, .. } = &info.kind
            && let Some(f) = fields.iter().find(|f| f.name == field)
        {
            return Ok(f
                .resolved_ty
                .clone()
                .map(|t| resolve_nominal(self.program, &t)));
        }
        // Accessing a field the structure does not have reads as null (matches the
        // type checker, which types such an access nullable).
        Ok(Some(Type::null()))
    }

    /// Check operator/type constraints over a fully-typed body (the static
    /// checking half of monomorphization). Only blocks this instance can reach
    /// are checked: an arm a statically-known `if` folds away is not emitted, and
    /// its operators may well be ill-typed for *this* instantiation.
    fn validate(
        &self,
        body: &MirBody,
        sym: &str,
        local_types: &[Type],
        reachable: &[bool],
    ) -> Result<(), String> {
        let ty = |op: &Operand| -> Type {
            match op {
                Operand::Local(id) => local_types[id.index()].clone(),
                Operand::Const(lit) => const_type(lit).unwrap_or(Type::Void),
            }
        };
        for (block, _) in body.blocks.iter().zip(reachable).filter(|(_, r)| **r) {
            for stmt in &block.stmts {
                let (MirStmt::Assign(_, Rvalue::Bin(op, a, b))
                | MirStmt::Eval(Rvalue::Bin(op, a, b))) = stmt
                else {
                    continue;
                };
                // Validate the pair at the types codegen emits: a const
                // integer literal adapts to the local operand's kind (the
                // shared operand rule), so its magnitude default does not
                // fail a pair the back ends handle (`u64 + 1`, `i64 << 2`).
                let (ta, tb) = bin_validation_types(
                    &ty(a),
                    &ty(b),
                    matches!(a, Operand::Local(_)),
                    matches!(b, Operand::Local(_)),
                );
                check_bin(*op, &ta, &tb).map_err(|e| format!("{e} (in `{sym}`)"))?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{check_instances, instance_symbol, monomorphize};
    use brass_hir::{RESULT_TYPE_ID, Type};

    /// The JIT-time constraint check passes on a valid program: each
    /// monomorphized body (a free function, and a record method whose `self.x +
    /// self.y` resolves through field types) is type-consistent, so the deferred
    /// model's consistency check reports nothing.
    #[test]
    fn valid_program_passes_the_jit_time_check() {
        let src = "type Point = {\n  x: int32\n  y: int32\n}\n\
                   fun Point.sum(self) -> int32 {\n    return self.x + self.y\n  }\n\
                   fun add(a: int32, b: int32) -> int32 {\n  return a + b\n}\n\
                   fun main() {\n  let p = Point { x: 1, y: 2 }\n  let s = add(p.x, p.y)\n  println(string.from(s))\n}\n";
        let ast = brass_parser::parse(src).expect("parse");
        let (program, errs) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = brass_mir::lower_program(&program);
        let mono = monomorphize(&mir, &program).expect("monomorphize");
        let jit_errors = check_instances(&mono, &program);
        assert!(jit_errors.is_empty(), "valid program: {jit_errors:?}");
    }

    /// A fallible callable passes the check too: its result is `Result<int32,
    /// string>`, so a bare `return x` (the Ok payload `int32`) and a `return
    /// error("neg")` (a `Result`) both reconcile against the right target.
    #[test]
    fn valid_fallible_program_passes_the_jit_time_check() {
        let src = "fun checked(x: int32) {\n  if x < 0 {\n    return error(\"neg\")\n  }\n  return x\n}\n\
                   fun main() {\n  let r = checked(5)\n}\n";
        let ast = brass_parser::parse(src).expect("parse");
        let (program, errs) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = brass_mir::lower_program(&program);
        let mono = monomorphize(&mir, &program).expect("monomorphize");
        let jit_errors = check_instances(&mono, &program);
        assert!(
            jit_errors.is_empty(),
            "valid fallible program: {jit_errors:?}"
        );
    }

    /// Error propagation with `expr!` contributes only the propagated error type to
    /// the enclosing function. Its callee-side Ok payload must not override the
    /// enclosing function's successful bare return.
    #[test]
    fn propagated_result_does_not_define_enclosing_ok_payload() {
        let src = "fun read_text(path: string) {\n  let n = _int_parse(path)!\n  return \"done\"\n}\n\
                   fun main() {\n  let r = read_text(\"12\")\n}\n";
        let ast = brass_parser::parse(src).expect("parse");
        let (program, errs) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = brass_mir::lower_program(&program);
        let mono = monomorphize(&mir, &program).expect("monomorphize");
        let sym = instance_symbol("read_text", &[Type::Str]);
        let ret = &mono.lookup(&sym).expect("read_text instance").ret;
        let Type::Sum(result) = ret else {
            panic!("read_text should return Result, got {}", ret.display());
        };
        assert_eq!(result.id, RESULT_TYPE_ID);
        let (ok, err) = result.result_payloads().expect("Result payloads");
        assert_eq!(ok, &Type::Str);
        assert_eq!(err, &Type::Str);
    }
}
