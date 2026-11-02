//! Monomorphization: collecting the concrete instances a typed back end
//! compiles, and resolving every local and return type to a concrete type.
//!
//! This is *true* single-specialization: starting from the roots (see the
//! `entry` module), each call site's concrete argument types select (and, on
//! demand, create) a callee instance, so one polymorphic MIR body yields a
//! distinct instance per concrete type tuple. Functions, instance methods,
//! static methods (constructors) and closures are all instantiated this way;
//! records and sums are typed per instance by their field-type substitution,
//! the generic `Result` by the payloads a fallible body produces, growable
//! arrays by what is pushed into them. Each instance gets a collision-free
//! symbol and a fully concrete type for every local.
//!
//! The pass is not a second type checker. Where the operands do not determine
//! a type (a seeded literal, a closure's function type, a call into an
//! instance still being typed), it follows the checker's channels, and it
//! reads the facts that differ between instances under the instance it types
//! (see the `instance` module). A body it cannot type is refused with the
//! construct named; a refusal no checked program reaches reports an internal
//! error (see [`refusal`]).

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use brass_hir::{
    FloatKind, IntKind, NominalType, Program, RESULT_TYPE_ID, Substitution, Type, TypeKind,
};
use brass_mir::{
    Callee, ClosureId, Literal, LocalId, MirBody, MirClosure, MirFunction, MirMethod, MirProgram,
    MirStmt, Operand, Projection, Rvalue, Terminator,
};
use brass_parser::ast::{BinOp, UnaryOp};

mod aggregate;
mod call;
mod closure;
mod deferral;
mod dependencies;
mod entry;
mod fixpoint;
mod fold;
mod instance;
mod instantiate;
mod join;
mod params;
mod postpone;
mod record_from;
mod rendering;
mod result;
mod returns;
mod rules;
mod rvalue;
mod scan;
mod session;
pub use session::MonoSession;
mod stmt;
mod symbols;

pub use entry::{
    MonoStop, monomorphize, monomorphize_entry, monomorphize_entry_with_returns,
    monomorphize_instance_deferred, monomorphize_instance_deferred_with_returns, refusal,
};
pub use fold::{cond_static_truthiness, locals_only_in_dead_blocks, reachable_blocks};
use record_from::record_from_target;
use result::result_type;
pub use rules::{binary_operand_type, is_comparison, unwrap_nullable};
pub use scan::operand_type_of;
pub use symbols::{
    SYNTH_SIGIL, closure_symbol, display_instance, instance_symbol, method_symbol,
    nullable_display_instance, prim_method_instance, static_symbol,
};

use fixpoint::BodyScans;
use rules::{
    binary_operand_common, check_bin, const_type, is_refinement_of, is_supported, join_refinements,
    operand_literal, resolve_nominal, variant_field_layoutable,
};
use scan::{
    ClosurePass, binding_name_of, collect_array_pushes, collect_closure_passes,
    collect_indirect_args, collect_record_field_closures, method_ret_annotation, null_prop_returns,
    propagated_result_returns, result_concrete_ok, returns_only_err_constructions,
    seed_returned_aggregate, seed_returned_closure, seed_returned_tuple,
};
use symbols::is_return_polymorphic_result;

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
    /// The specialization each reflective call site of the body
    /// ([`Callee::Keyed`]) dispatches to in this instance.
    pub keyed: HashMap<brass_parser::Span, String>,
    /// Field sequences selected from checked observations for this instance.
    pub fields: HashMap<brass_parser::Span, Vec<String>>,
    /// Completed instance symbols of closure values created by this body.
    pub closure_targets: HashMap<ClosureId, String>,
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

/// Whether a value has a text rendering on the typed I/O path (`print`,
/// `println`, `"{v}"`, `string.from`): a string is written directly, any other
/// printable value through its `to_string` conversion.
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

    /// `callee` as this instance dispatches it: a [`Callee::Keyed`] site
    /// becomes the [`Callee::Method`] call of the specialization the instance
    /// resolved it to; every other callee is itself. Back ends route calls
    /// through this, so they never see a keyed site.
    pub fn dispatch<'c>(&self, callee: &'c Callee) -> std::borrow::Cow<'c, Callee> {
        match callee {
            Callee::Numeric { inner, site } if !self.keyed.contains_key(site) => {
                std::borrow::Cow::Borrowed(inner)
            }
            Callee::Keyed { site, .. } => match self.keyed.get(site) {
                Some(target) => std::borrow::Cow::Owned(Callee::Method(target.clone())),
                // Monomorphization resolves every keyed site of a stored
                // instance; an unresolved one cannot be reached here.
                None => std::borrow::Cow::Borrowed(callee),
            },
            other => std::borrow::Cow::Borrowed(other),
        }
    }
}

/// The recorded contract of a runtime-deferred call site (the lazy JIT): the
/// instance the site will ask the runtime resolver for, keyed in
/// [`MonoProgram::deferred`] by its instance symbol. `type_args` are the
/// concrete argument types the instance will be monomorphized at (they are
/// also the site's ABI parameter types -- instances are keyed by caller
/// argument types, so both sides agree by construction); `ret` is the
/// callee's declared, fully concrete return type.
#[derive(Clone, Debug, PartialEq, Eq)]
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

/// A whole program lowered to concrete typed instances, with a symbol index for
/// resolving call targets.
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

    /// The concrete entry instance named by the lowered program, when typed.
    pub fn entry_function(&self) -> Option<&MonoFunction<'m>> {
        self.hir
            .entry_function()
            .and_then(|symbol| self.lookup(symbol))
    }

    /// The concrete type of global `name`, if any.
    pub fn global_type(&self, name: &str) -> Option<&Type> {
        self.global_index.get(name)
    }
}

/// A callable frame that failed only because its transitive MIR subset was
/// incomplete. Replaying the demands preserves each root's watermark rules;
/// the frame itself cannot produce a different result until the caller adds
/// bodies and starts a new monomorphization pass.
#[derive(Clone)]
struct MissingFailure {
    error: String,
    demands: Vec<(String, Vec<Type>, bool)>,
}

struct Monomorphizer<'m, 'p> {
    session: session::Run<'m>,
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
    /// The return type each in-progress instance first handed its own
    /// recursive calls in the current attempt (the type their result locals
    /// were typed at). A body whose finished return differs from it is typed
    /// again with the recursive calls reading the wider type (see
    /// `type_and_store_inner`).
    self_call_rets: HashMap<String, Type>,
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
    missing_demands: std::cell::RefCell<Vec<(String, Vec<Type>, bool)>>,
    /// Pass-local memo of callable frames that observed a missing body. Mono's
    /// fixpoint can revisit the same failed method many times, but the MIR set
    /// cannot change during one pass, so only the demand replay is needed.
    missing_failures: HashMap<String, MissingFailure>,
    /// Counts every missing-body observation, including a deduplicated one,
    /// so an enclosing frame can tell that its failure was demand-driven.
    missing_observations: std::cell::Cell<u64>,
    /// Checker-reported instance returns for UNANNOTATED functions, keyed by
    /// `(base symbol, argument types)`: the runtime-deferral contract that
    /// lets a call to such a function compile as a runtime-resolved site
    /// without the body ever being lowered (see `deferrable`), and the
    /// provisional return of an unannotated instance a mutual recursion
    /// re-enters (see `resolve_free`). Populated by the lazy driver from the
    /// streamed `instance_returns` deltas, and from
    /// [`MirProgram::instance_returns`] everywhere else.
    instance_returns: HashMap<(String, Vec<Type>), Type>,
    /// The checker's per-instance aggregate seeds ([`MirProgram::instance_seeds`]),
    /// read for the instance on top of `instance_stack` (see `local_seed`).
    instance_seeds: &'m brass_hir::InstanceChannel<Type>,
    /// The checker's per-instance dispatch of keyed calls
    /// ([`MirProgram::instance_dispatch`]), read like `instance_seeds`.
    instance_dispatch: &'m brass_hir::InstanceChannel<String>,
    /// Checked alternatives used by compile-time field iteration.
    instance_fields: &'m brass_hir::InstanceChannel<Vec<String>>,
    numeric_calls: &'m brass_hir::NumericCalls,
    active_numeric_call: Option<(brass_parser::Span, Option<brass_hir::NumericLayout>)>,
    numeric_targets: HashMap<(brass_parser::Span, Option<brass_hir::InstanceKey>), String>,
    /// Set once instance nesting exceeded its bound (see `type_and_store`):
    /// the error every later instantiation fails with.
    nesting_overflow: Option<String>,
    /// How many instances of each callable (by its base symbol) are being
    /// typed nested inside one another (see `type_and_store`).
    callable_nesting: HashMap<String, usize>,
    /// The calls of the root being typed whose callees are typed after it
    /// (see [`postpone`]).
    postponed: postpone::Postponed,
    /// The checker instance of each body being typed, innermost last (see
    /// [`instance`]): `None` for a body outside any instance (a module
    /// initializer); a closure body inherits its creator's.
    instance_stack: Vec<Option<brass_hir::InstanceKey>>,
}

impl<'m, 'p> Monomorphizer<'m, 'p> {
    /// Build a monomorphizer over a MIR program: index functions, record methods,
    /// and closures so instances can be created on demand.
    fn new(mir: &'m MirProgram, program: &'p Program) -> Self {
        let mut by_method: HashMap<(&str, &str), &MirMethod> = HashMap::default();
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
            session: session::Run::default(),
            program,
            by_fn: mir
                .functions
                .iter()
                .map(|f| (f.symbol.as_str(), f))
                .collect(),
            by_method,
            by_closure: mir.closures.iter().map(|c| (c.id, c)).collect(),
            global_types: HashMap::default(),
            instances: HashMap::default(),
            in_progress: HashMap::default(),
            assumed_rets: HashMap::default(),
            self_call_rets: HashMap::default(),
            instance_log: Vec::new(),
            rows: None,
            defer: None,
            closure_depth: 0,
            missing_demands: std::cell::RefCell::new(Vec::new()),
            missing_failures: HashMap::default(),
            missing_observations: std::cell::Cell::new(0),
            instance_returns: mir.instance_returns.clone(),
            instance_seeds: &mir.instance_seeds,
            instance_dispatch: &mir.instance_dispatch,
            instance_fields: &mir.instance_fields,
            numeric_calls: &mir.numeric_calls,
            active_numeric_call: None,
            numeric_targets: HashMap::default(),
            instance_stack: Vec::new(),
            nesting_overflow: None,
            callable_nesting: HashMap::default(),
            postponed: postpone::Postponed::default(),
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
}

#[cfg(test)]
mod tests {
    use super::{
        HashMap, MonoStop, instance_symbol, monomorphize, monomorphize_entry_with_returns,
    };
    use brass_hir::{RESULT_TYPE_ID, Type};

    /// Once an unannotated return contract has arrived but cannot describe a
    /// deferred ABI, retrying without the body cannot change the result. The
    /// demand must therefore be upgraded from a contract candidate to a real
    /// MIR-body requirement.
    #[test]
    fn rejected_deferred_contract_demands_the_body() {
        let src = "fun value(x) {\n  return x\n}\n\
                   fun main() {\n  println(value(1))\n}\n";
        let ast = brass_parser::parse(src).expect("parse");
        let (program, errs) = brass_hir::lower(&[brass_hir::LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mut mir = brass_mir::lower_program(&program);
        mir.functions.retain(|function| function.symbol == "main");

        let mut missing =
            match monomorphize_entry_with_returns(&mir, &program, true, HashMap::default()) {
                Err(MonoStop::MissingBodies(missing)) => missing,
                Err(other) => panic!("expected missing bodies, got {other:?}"),
                Ok(_) => panic!("value body should be absent"),
            };
        let (symbol, args, needs_body) = missing.pop().expect("one missing value instance");
        assert_eq!(symbol, "value");
        assert!(!needs_body, "the first demand may request a contract");

        let mut returns = HashMap::default();
        returns.insert((symbol, args), Type::Unknown(0));
        let missing = match monomorphize_entry_with_returns(&mir, &program, true, returns) {
            Err(MonoStop::MissingBodies(missing)) => missing,
            Err(other) => panic!("expected missing bodies, got {other:?}"),
            Ok(_) => panic!("unknown return should not defer"),
        };
        assert!(
            missing
                .iter()
                .any(|(symbol, _, needs_body)| symbol == "value" && *needs_body),
            "a rejected contract must require the body: {missing:?}"
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
            source: None,
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
