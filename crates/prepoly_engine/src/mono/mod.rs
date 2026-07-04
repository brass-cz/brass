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

use prepoly_hir::{
    FloatKind, IntKind, NominalType, Program, RESULT_TYPE_ID, Substitution, Type, TypeKind,
    int_literal_kind,
};
use prepoly_mir::{
    BlockId, Callee, ClosureId, LocalId, MirBody, MirClosure, MirFunction, MirMethod, MirProgram,
    MirStmt, Operand, Projection, Rvalue, Terminator,
};
use prepoly_parser::ast::{BinOp, UnaryOp};

use crate::mir_infer::{MirTypeError, Resolver, infer_body};

mod boundary;
mod fold;
mod rules;
mod symbols;

pub use boundary::{
    boundary_record_type, boundary_record_type_by_id, boundary_record_type_by_name,
    boundary_record_type_from_fields, parse_structural_descriptor,
};
pub use fold::{cond_static_truthiness, reachable_blocks};
pub use rules::binary_operand_type;
pub(crate) use rules::unwrap_nullable;
pub use symbols::{
    SYNTH_SIGIL, closure_symbol, instance_symbol, method_symbol, prim_method_instance,
    static_symbol,
};

use rules::{
    bin_validation_types, binary_operand_common, check_bin, const_type, is_supported,
    merge_return_types, resolve_nominal, variant_field_layoutable,
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
    subst.insert(prepoly_hir::types::RESULT_OK_VALUE, ok);
    subst.insert(prepoly_hir::types::RESULT_ERR_ERROR, err);
    Type::Sum(NominalType::with_substitution(
        RESULT_TYPE_ID,
        "Result",
        subst,
    ))
}

/// Whether a type is a `Result`.
fn is_result(ty: &Type) -> bool {
    matches!(ty, Type::Sum(n) if n.id == RESULT_TYPE_ID)
}

/// The constant non-negative index carried by a tuple-position projection operand
/// (`t[0]`), or `None` when the index is not an integer constant. A tuple element
/// type is only known at a statically-known position.
pub(crate) fn const_operand_index(op: &Operand) -> Option<usize> {
    match op {
        Operand::Const(prepoly_mir::Literal::Int(n)) if *n >= 0 => Some(*n as usize),
        _ => None,
    }
}

/// The synthetic `File` record type. `File` is a builtin handle,
/// not a user-declared type, so it carries no registered id -- matching the type
/// checker, whose `type_by_name("File")` falls back to the same synthetic record.
fn file_type() -> Type {
    Type::Record(NominalType::new(-1, "File"))
}

/// The `Result` a `File` instance method returns: `read ->
/// uint8[]!`, `write`/`size -> int64!`, `close`/`seek -> void!`. `None` for a
/// non-File method name.
fn file_method_type(name: &str) -> Option<Type> {
    let ok = match name {
        "read" => Type::Slice(Box::new(Type::Int(IntKind::U8))),
        "write" | "size" => Type::Int(IntKind::I64),
        "close" | "seek" => Type::Void,
        _ => return None,
    };
    Some(result_type(ok, Type::Str))
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
    pub fn local_type(&self, id: prepoly_mir::LocalId) -> &Type {
        &self.local_types[id.index()]
    }
}

/// A whole program lowered to concrete typed instances, with a symbol index for
/// resolving call targets.
pub struct MonoProgram<'m> {
    pub functions: Vec<MonoFunction<'m>>,
    /// Module-level globals and their concrete types (declared by the back end,
    /// written by init instances, read via `Rvalue::Global`).
    pub globals: Vec<(String, Type)>,
    /// Init instance symbols, in run order (executed before `main`).
    pub init_symbols: Vec<String>,
    /// Why the `main` root was skipped, when it was: the first construct that
    /// fell outside the typed subset. Roots are best-effort, but for `main`
    /// (the program's entry point) the reason is the diagnostic the user needs.
    pub main_skip: Option<String>,
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
pub fn monomorphize<'m>(mir: &'m MirProgram, program: &Program) -> Result<MonoProgram<'m>, String> {
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

    let mut program = mono.into_program(init_symbols);
    program.main_skip = main_skip;
    Ok(program)
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
    program: &Program,
    base: &str,
    type_args: Vec<Type>,
) -> Result<MonoProgram<'m>, String> {
    let mut mono = Monomorphizer::new(mir, program);
    mono.instantiate_fn(base, type_args)?;
    mono.in_progress.clear();
    mono.assumed_rets.clear();
    Ok(mono.into_program(Vec::new()))
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
    rows: Option<prepoly_typesys::RowInfo>,
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
        }
    }

    /// The row table, derived from the HIR program on first use.
    fn rows(&mut self) -> &prepoly_typesys::RowInfo {
        if self.rows.is_none() {
            self.rows = Some(prepoly_typesys::RowInfo::analyze(self.program));
        }
        self.rows.as_ref().expect("rows just initialized")
    }

    /// Collect the instances created so far into a [`MonoProgram`] with a symbol
    /// index and the discovered globals.
    fn into_program(self, init_symbols: Vec<String>) -> MonoProgram<'m> {
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
            globals,
            init_symbols,
            main_skip: None,
            index,
            global_index,
        }
    }

    /// Instantiate a free function `base` for `type_args` (memoized).
    fn instantiate_fn(&mut self, base: &str, type_args: Vec<Type>) -> Result<String, String> {
        let sym = instance_symbol(base, &type_args);
        if self.instances.contains_key(&sym) {
            return Ok(sym);
        }
        let func = *self
            .by_fn
            .get(base)
            .ok_or_else(|| format!("unknown function `{base}`"))?;
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
        // `string` (the payload `error(...)` produces); the guess is validated
        // against the final inferred type when this frame completes.
        let provisional = ret_ann.clone().or_else(|| {
            if fallible {
                declared_ok.clone().map(|ok| result_type(ok, Type::Str))
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
        loop {
            let mut changed = false;
            for block in &body.blocks {
                for stmt in &block.stmts {
                    self.type_stmt(
                        stmt,
                        &sym,
                        module,
                        &indirect_args,
                        &closure_passes,
                        &record_field_closures,
                        &array_pushes,
                        &mut local_types,
                        &ret,
                        &mut changed,
                    )?;
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
                && ret.is_none()
                && let Some(t) = self.infer_result_ret(body, &local_types, declared_ok.as_ref())?
            {
                ret = Some(t);
                changed = true;
            }
            if !changed {
                break;
            }
        }

        let local_types = local_types
            .into_iter()
            .enumerate()
            .map(|(i, t)| t.ok_or_else(|| format!("cannot infer type of local _{i} in `{sym}`")))
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
            let reachable = reachable_blocks(body, &local_types, declared);
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
        self.validate(body, &sym, &local_types)?;

        // Validate what mutual recursion assumed about this instance while it
        // was in progress: a mismatch (e.g. a fallible body whose error payload
        // is not the guessed `string`) must fail the frame -- the consumer was
        // already typed against the assumption.
        if let Some(assumed) = self.assumed_rets.remove(&sym)
            && assumed != ret
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
        let note = |slot: &mut Option<Type>, t: Option<Type>| {
            if slot.is_none()
                && let Some(t) = t
            {
                *slot = Some(t);
            }
        };
        let propagated_returns = propagated_result_returns(body);
        for (block_idx, block) in body.blocks.iter().enumerate() {
            for stmt in &block.stmts {
                if let MirStmt::Assign(
                    _,
                    Rvalue::Variant {
                        ty,
                        variant,
                        fields,
                    },
                ) = stmt
                    && ty == "Result"
                {
                    for (fname, op) in fields {
                        let t = self.operand_type(op, local_types)?;
                        match (variant.as_str(), fname.as_str()) {
                            ("Ok", "value") => note(&mut ok_t, t),
                            ("Err", "error") => note(&mut err_e, t),
                            _ => {}
                        }
                    }
                }
            }
            if let Terminator::Return(op) = &block.term {
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
                            note(&mut err_e, Some(err.clone()));
                        }
                    }
                    // A directly-returned Result carries both payloads.
                    Some(Type::Sum(n)) if n.id == RESULT_TYPE_ID => {
                        if let Some((ok, err)) = n.result_payloads() {
                            note(&mut ok_t, Some(ok.clone()));
                            note(&mut err_e, Some(err.clone()));
                        }
                    }
                    // A bare value is the implicit Ok payload.
                    Some(other) => note(&mut ok_t, Some(other)),
                    None => {}
                }
            }
        }
        match (ok_t, err_e) {
            (Some(ok), Some(err)) => Ok(Some(result_type(ok, err))),
            // A callable made fallible only by a `T!` return annotation never
            // produces an error, so its error payload is unconstrained: default it
            // to `string` (the conventional error type) once the Ok payload is
            // known. Guarded by the absence of any error source, so a fallible body
            // that does raise errors still waits for the real error type.
            (Some(ok), None) if !body_has_error_source(body) => {
                Ok(Some(result_type(ok, Type::Str)))
            }
            _ => Ok(None),
        }
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::too_many_arguments)]
    fn type_stmt(
        &mut self,
        stmt: &MirStmt,
        cur_sym: &str,
        module: &[String],
        indirect_args: &HashMap<LocalId, Vec<Operand>>,
        closure_passes: &HashMap<LocalId, (String, Vec<Operand>, usize)>,
        record_field_closures: &HashMap<LocalId, (LocalId, String, String)>,
        array_pushes: &HashMap<LocalId, Operand>,
        local_types: &mut [Option<Type>],
        cur_ret: &Option<Type>,
        changed: &mut bool,
    ) -> Result<(), String> {
        match stmt {
            // An empty array literal `[]` gets its element type from a later
            // `push` (it is filled before use).
            MirStmt::Assign(local, Rvalue::Array(es)) if es.is_empty() => {
                if local_types[local.index()].is_none() {
                    let Some(elem_op) = array_pushes.get(local) else {
                        return Err(
                            "empty array literal with no element type on the typed backend".into(),
                        );
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
                let t =
                    self.rvalue_type(rv, cur_sym, module, local_types, cur_ret, expected.as_ref())?;
                if local_types[local.index()].is_none()
                    && let Some(t) = t
                {
                    local_types[local.index()] = Some(t);
                    *changed = true;
                }
                Ok(())
            }
            // A call run for its side effect (the result is discarded).
            MirStmt::Eval(rv @ Rvalue::Call(..)) => {
                self.rvalue_type(rv, cur_sym, module, local_types, cur_ret, None)?;
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
    fn rvalue_type(
        &mut self,
        rv: &Rvalue,
        cur_sym: &str,
        module: &[String],
        local_types: &[Option<Type>],
        cur_ret: &Option<Type>,
        expected: Option<&Type>,
    ) -> Result<Option<Type>, String> {
        match rv {
            Rvalue::Use(op) => self.operand_type(op, local_types),
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
                // `open(path, mode) -> File!`; a runtime primitive.
                "open" => Ok(Some(result_type(file_type(), Type::Str))),
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
                other => Err(format!(
                    "builtin `{other}` is unsupported on the typed backend"
                )),
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
                        Some(Type::Record(n)) => self.record_field_type(n, field),
                        Some(Type::Sum(n)) => self.sum_field_type(n, field),
                        Some(other) => Err(format!(
                            "field access `.{field}` on non-aggregate `{}`",
                            other.display()
                        )),
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
                    prepoly_hir::peel_modes(&src),
                    self.rows().function_param(callee, *param),
                ) {
                    (Type::Record(n), Some(prow))
                        if n.id == prepoly_hir::STRUCTURAL_RECORD_ID && prow.eligible =>
                    {
                        prepoly_typesys::view_type(&prow.row, n).map(Some)
                    }
                    _ => Ok(Some(src)),
                }
            }
            // A `Result` construction takes the enclosing fallible callable's
            // inferred `Result` type; other (annotated) sums resolve directly.
            Rvalue::Variant {
                ty,
                variant,
                fields,
            } => {
                if ty == "Result" {
                    Ok(cur_ret.clone().filter(is_result))
                } else {
                    self.variant_type(module, ty, variant, fields, local_types)
                }
            }
            Rvalue::Array(es) => self.array_type(es, local_types),
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
        let Some(arg_types) = self.arg_types(args, local_types)? else {
            return Ok(None);
        };
        // File I/O methods are runtime primitives over the builtin
        // `File` record, not user methods, so they return their Result directly with
        // no instance to monomorphize.
        if let Type::Record(n) = &arg_types[0]
            && n.is_name("File")
            && let Some(ret) = file_method_type(name)
        {
            return Ok(Some(ret));
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
            && n.id == prepoly_hir::STRUCTURAL_RECORD_ID
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
                            Some(decl) if prepoly_hir::is_fully_known(decl) => have == decl,
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
        if ty == "File" && matches!(method_name, "stdin" | "stdout" | "stderr") {
            return Ok(Some(file_type()));
        }
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
        let declared_ok = ret_ann.as_ref().and_then(result_concrete_ok);
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
        let sym = self.instantiate_fn(base, arg_types)?;
        Ok(self.instances.get(&sym).map(|i| i.ret.clone()))
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
            return Ok(Some(prepoly_hir::structural_record(out)));
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
                        Some(decl @ Type::Nullable(_)) if prepoly_hir::is_fully_known(decl))
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
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        if es.is_empty() {
            return Err("empty array literal has no element type on the typed backend".into());
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

    /// The closure's parameter types from its own annotations, when every parameter
    /// is annotated. This types an *escaping* closure (returned, so neither called
    /// in-body nor passed to a function) -- e.g. `make_accumulator`'s returned
    /// `(amount: int32) -> ...`. `None` if any parameter is unannotated.
    /// The declared parameter types of record `ty`'s field `field` when the
    /// field is annotated with a concrete function type -- the typing source for
    /// a closure stored into that field.
    fn record_field_fun_params(
        &self,
        module: &[String],
        ty: &str,
        field: &str,
    ) -> Option<Vec<Type>> {
        let info = self.program.resolve_type(module, ty)?;
        let TypeKind::Record { fields, .. } = &info.kind else {
            return None;
        };
        let f = fields.iter().find(|f| f.name == field)?;
        match f.resolved_ty.as_ref() {
            Some(Type::Fun(params, _)) if params.iter().all(prepoly_hir::is_fully_known) => {
                Some(params.clone())
            }
            _ => None,
        }
    }

    /// Derive an unannotated closure's parameter types from its OWN body: seed
    /// the capture locals with their (already resolved) types, lightly infer the
    /// body, and read what each parameter is CALLED with. An indirect call
    /// through a typed capture (`(x) -> func(g(x))` where `g: (int32) -> int32`
    /// is captured) pins `x` even though nothing outside the closure calls it.
    /// `None` when any parameter stays unpinned.
    fn closure_params_from_body(&self, id: ClosureId, capture_types: &[Type]) -> Option<Vec<Type>> {
        let clo = self.by_closure.get(&id)?;
        let body = &clo.body;
        let mut seeded: Vec<Option<Type>> = vec![None; body.locals.len()];
        for (cap, t) in clo.captures.iter().zip(capture_types) {
            seeded[cap.index()] = Some(t.clone());
        }
        for p in &body.params {
            if let Some(t) = body.locals[p.index()].ty.as_known() {
                seeded[p.index()] = Some(t.clone());
            }
        }
        let lt = self.probe_local_types(body, seeded);
        let mut out: Vec<Option<Type>> =
            body.params.iter().map(|p| lt[p.index()].clone()).collect();
        for block in &body.blocks {
            for stmt in &block.stmts {
                let (MirStmt::Assign(_, rv) | MirStmt::Eval(rv)) = stmt else {
                    continue;
                };
                if let Rvalue::Call(Callee::Indirect(Operand::Local(g)), args) = rv
                    && let Some(Type::Fun(ps, _)) = lt[g.index()].as_ref()
                {
                    for (a, pty) in args.iter().zip(ps) {
                        if let Operand::Local(al) = a
                            && let Some(slot) = body.params.iter().position(|p| p == al)
                            && out[slot].is_none()
                            && prepoly_hir::is_fully_known(pty)
                        {
                            out[slot] = Some(pty.clone());
                        }
                    }
                }
            }
        }
        out.into_iter().collect()
    }

    fn closure_annotated_params(&self, id: ClosureId) -> Option<Vec<Type>> {
        let clo = self.by_closure.get(&id)?;
        clo.params
            .iter()
            .map(|p| clo.body.locals[p.index()].ty.as_known().cloned())
            .collect()
    }

    /// Type a closure local: its captures come from the creation site and its
    /// parameter types from how it is used -- an in-body call (direct-call
    /// closures), being passed to a higher-order function (the callee's use of
    /// that parameter, recovered by probing), initializing a record field with a
    /// declared function type (the field's signature), or, for an escaping
    /// closure, its own parameter annotations. Also instantiates the closure
    /// body. `None` while any operand type is still unresolved.
    #[allow(clippy::too_many_arguments)]
    fn closure_local_type(
        &mut self,
        id: ClosureId,
        captures: &[Operand],
        local: LocalId,
        module: &[String],
        indirect_args: &HashMap<LocalId, Vec<Operand>>,
        closure_passes: &HashMap<LocalId, (String, Vec<Operand>, usize)>,
        record_field_closures: &HashMap<LocalId, (LocalId, String, String)>,
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        let mut capture_types = Vec::with_capacity(captures.len());
        for c in captures {
            match self.operand_type(c, local_types)? {
                Some(t) => capture_types.push(t),
                None => return Ok(None),
            }
        }
        // Parameter types: from a direct in-body call, else from a higher-order
        // callee's use of the parameter the closure is passed as.
        let param_types = if let Some(call_args) = indirect_args.get(&local) {
            let mut pt = Vec::with_capacity(call_args.len());
            for a in call_args {
                match self.operand_type(a, local_types)? {
                    Some(t) => pt.push(t),
                    None => return Ok(None),
                }
            }
            pt
        } else if let Some((base, pass_args, idx)) = closure_passes.get(&local) {
            match self.probe_callee_param_types(base, pass_args, *idx, local_types)? {
                Some(pt) => pt,
                // The probe cannot answer (the receiver is still untyped, or
                // the callee never calls the parameter directly -- e.g. it only
                // re-captures it into another closure). A fully annotated
                // closure falls back to its own signature, which the checker
                // has already verified against every use; an unannotated one
                // waits for a later pass.
                None => match self.closure_annotated_params(id) {
                    Some(annotated) => annotated,
                    None => return Ok(None),
                },
            }
        } else if let Some(pt) = record_field_closures
            .get(&local)
            .and_then(|(dest, ty, field)| {
                // The closure initializes a record field: the call contract is the
                // field's declared function signature, or -- for an unannotated
                // field -- the constructed instance's substitution entry when the
                // checker seeded the destination local (`Iter { trans: (x) -> .. }`
                // takes `trans`'s per-instance type from the seed).
                self.record_field_fun_params(module, ty, field).or_else(|| {
                    match local_types[dest.index()].as_ref() {
                        Some(Type::Record(n)) => match n.substitution.get(field) {
                            Some(Type::Fun(params, _))
                                if params.iter().all(prepoly_hir::is_fully_known) =>
                            {
                                Some(params.clone())
                            }
                            _ => None,
                        },
                        _ => None,
                    }
                })
            })
        {
            pt
        } else if let Some(annotated) = self.closure_annotated_params(id) {
            // An escaping closure (returned): type it from its own parameter
            // annotations rather than a call/pass site.
            annotated
        } else if let Some(pt) = self.closure_params_from_body(id, &capture_types) {
            // Derived from the closure's OWN body: an indirect call through a
            // typed capture pins the parameter it is called with.
            pt
        } else {
            return Err(format!(
                "closure _{} is neither called nor passed to a function nor fully \
                 annotated; unsupported on the typed backend",
                local.index()
            ));
        };
        let ret = self.instantiate_closure(id, &capture_types, &param_types)?;
        Ok(Some(Type::Fun(param_types, Box::new(ret))))
    }

    /// Recover the parameter types of a closure passed to free function `base` as
    /// argument `idx`: seed the callee's other parameters from the call's
    /// arguments, lightly infer its local types, and read what the closure
    /// parameter is called with inside the callee. `None` if not yet resolvable.
    fn probe_callee_param_types(
        &self,
        base: &str,
        pass_args: &[Operand],
        idx: usize,
        caller_local_types: &[Option<Type>],
    ) -> Result<Option<Vec<Type>>, String> {
        // `base` is the callee name. For a stdlib primitive/array method passed a
        // closure (`arr.map(f)`), its body lives under the class-qualified symbol;
        // for a user METHOD (`iter.map_lazy(f)`) it lives in the method table
        // keyed by the receiver's type symbol. Both are recovered from the
        // receiver argument (the first call operand).
        let body = match self.by_fn.get(base) {
            Some(f) => &f.body,
            None => {
                let recv_ty = pass_args
                    .first()
                    .and_then(|a| self.operand_type(a, caller_local_types).ok().flatten());
                let prim = recv_ty
                    .as_ref()
                    .and_then(|t| t.primitive_class())
                    .and_then(|class| {
                        self.program
                            .primitive_methods
                            .get(&(class.to_string(), base.to_string()))
                    })
                    .and_then(|s| self.by_fn.get(s.as_str()))
                    .map(|f| &f.body);
                let user = recv_ty
                    .as_ref()
                    .map(unwrap_nullable)
                    .and_then(|t| match t {
                        Type::Record(n) | Type::Sum(n) => self.program.type_by_id(n.id),
                        _ => None,
                    })
                    .and_then(|info| self.by_method.get(&(info.symbol.as_str(), base)))
                    .map(|m| &m.body);
                match prim.or(user) {
                    Some(b) => b,
                    None => return Ok(None),
                }
            }
        };
        let mut seeded: Vec<Option<Type>> = vec![None; body.locals.len()];
        for (i, p) in body.params.iter().enumerate() {
            if i == idx {
                continue;
            }
            if let Some(arg) = pass_args.get(i) {
                seeded[p.index()] = self.operand_type(arg, caller_local_types)?;
            }
        }
        let lt = self.probe_local_types(body, seeded);
        let Some(p_local) = body.params.get(idx) else {
            return Ok(None);
        };
        let indirect = collect_indirect_args(body);
        let Some(call_args) = indirect.get(p_local) else {
            return Ok(None);
        };
        let mut pt = Vec::with_capacity(call_args.len());
        for a in call_args {
            match self.operand_type(a, &lt)? {
                Some(t) => pt.push(t),
                None => return Ok(None),
            }
        }
        Ok(Some(pt))
    }

    /// A lightweight, non-instantiating fixpoint that resolves local types from
    /// simple rvalues (uses, binary ops, field/element loads). Used to probe a
    /// callee body without the side effects of full instantiation.
    fn probe_local_types(&self, body: &MirBody, seeded: Vec<Option<Type>>) -> Vec<Option<Type>> {
        let mut lt = seeded;
        loop {
            let mut changed = false;
            for block in &body.blocks {
                for stmt in &block.stmts {
                    if let MirStmt::Assign(local, rv) = stmt
                        && lt[local.index()].is_none()
                        && let Some(t) = self.probe_rvalue_type(rv, &lt)
                    {
                        lt[local.index()] = Some(t);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        lt
    }

    /// The type of a simple rvalue during a probe (no calls/constructions).
    fn probe_rvalue_type(&self, rv: &Rvalue, lt: &[Option<Type>]) -> Option<Type> {
        match rv {
            Rvalue::Use(op) => self.operand_type(op, lt).ok().flatten(),
            Rvalue::Bin(op, a, _) if is_comparison(*op) => {
                // A comparison's operands must be resolvable for the result bool
                // to be meaningful here.
                self.operand_type(a, lt).ok().flatten()?;
                Some(Type::Bool)
            }
            Rvalue::Bin(_, a, b) => self.binary_operand_type(a, b, lt).ok().flatten(),
            Rvalue::Load(place) => match place.proj.as_slice() {
                [Projection::Field(field)] => {
                    match unwrap_nullable(lt.get(place.local.index())?.as_ref()?) {
                        Type::Record(n) => self.record_field_type(n, field).ok().flatten(),
                        Type::Sum(n) => self.sum_field_type(n, field).ok().flatten(),
                        _ => None,
                    }
                }
                [Projection::Index(_)] => {
                    match unwrap_nullable(lt.get(place.local.index())?.as_ref()?) {
                        Type::Slice(elem) | Type::Array(elem, _) => Some((**elem).clone()),
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Instantiate a closure body for one (capture-types, param-types) tuple
    /// (memoized), returning its return type.
    fn instantiate_closure(
        &mut self,
        id: ClosureId,
        capture_types: &[Type],
        param_types: &[Type],
    ) -> Result<Type, String> {
        let clo = *self
            .by_closure
            .get(&id)
            .ok_or_else(|| format!("unknown closure {}", id.index()))?;
        let sym = closure_symbol(id, capture_types, param_types);
        if let Some(inst) = self.instances.get(&sym) {
            return Ok(inst.ret.clone());
        }
        if self.in_progress.contains_key(&sym) {
            return Err("recursive closures are unsupported on the typed backend".into());
        }
        let capture_seed: Vec<(LocalId, Type)> = clo
            .captures
            .iter()
            .copied()
            .zip(capture_types.iter().cloned())
            .collect();
        let stored = self.type_and_store(
            sym,
            &clo.body,
            &clo.module,
            param_types.to_vec(),
            None,
            None,
            None,
            &capture_seed,
            clo.captures.clone(),
            true,
            false,
        )?;
        Ok(self.instances[&stored].ret.clone())
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
    /// checking half of monomorphization).
    fn validate(&self, body: &MirBody, sym: &str, local_types: &[Type]) -> Result<(), String> {
        let ty = |op: &Operand| -> Type {
            match op {
                Operand::Local(id) => local_types[id.index()].clone(),
                Operand::Const(lit) => const_type(lit).unwrap_or(Type::Void),
            }
        };
        for block in &body.blocks {
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

/// The declared return type of a record method, if concrete.
/// Seed the locals that flow into a body's returned record/variant from the
/// expected return's field types. Used so a constructor's empty array fields take
/// their element type from the result the caller fixed (the witness-free
/// `new()`). Only fills locals still untyped, with supported field types, so it
/// never overrides an inference the body itself can make.
///
/// A field value usually arrives through a `let` binding (`let items = []; Self
/// { items: items }`), which lowers to a temporary holding the empty array and a
/// binding local copied from it. Seeding only the binding would leave the actual
/// empty-array temporary untyped, so the seed is propagated backward along
/// `Use`-copy chains to reach it.
fn seed_returned_aggregate(body: &MirBody, ret_ty: &Type, local_types: &mut [Option<Type>]) {
    let returned: Vec<LocalId> = body
        .blocks
        .iter()
        .filter_map(|b| match &b.term {
            Terminator::Return(Operand::Local(r)) => Some(*r),
            _ => None,
        })
        .collect();
    if returned.is_empty() {
        return;
    }
    // `dest -> src` for every `dest = Use(src)` copy, so a seed on a binding can
    // be carried back to the temporary it copied.
    let mut copy_of: HashMap<LocalId, LocalId> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let MirStmt::Assign(dest, Rvalue::Use(Operand::Local(src))) = stmt {
                copy_of.insert(*dest, *src);
            }
        }
    }
    for block in &body.blocks {
        for stmt in &block.stmts {
            let MirStmt::Assign(dest, rv) = stmt else {
                continue;
            };
            if !returned.contains(dest) {
                continue;
            }
            let fields = match rv {
                Rvalue::Record { fields, .. } | Rvalue::Variant { fields, .. } => fields,
                _ => continue,
            };
            for (fname, op) in fields {
                let Operand::Local(fl) = op else { continue };
                let Some(fty) = aggregate_field_type(ret_ty, fname) else {
                    continue;
                };
                if !is_supported(&fty) {
                    continue;
                }
                // Seed the field operand and every temporary it was copied from.
                let mut cur = *fl;
                loop {
                    if local_types[cur.index()].is_none() {
                        local_types[cur.index()] = Some(fty.clone());
                    }
                    match copy_of.get(&cur) {
                        Some(&src) => cur = src,
                        None => break,
                    }
                }
            }
        }
    }
}

/// A field's resolved type from an aggregate's instance substitution (the
/// checker-resolved record/variant carries each field's concrete type there).
fn aggregate_field_type(ty: &Type, field: &str) -> Option<Type> {
    match ty {
        Type::Record(n) | Type::Sum(n) => n.substitution.get(field).cloned(),
        _ => None,
    }
}

fn method_ret_annotation(program: &Program, type_symbol: &str, method: &str) -> Option<Type> {
    let info = program.types.get(type_symbol)?;
    let m = match &info.kind {
        TypeKind::Record { methods, .. } => methods.get(method)?,
        // A whole-sum method lives (duplicated) in the variants' tables; the
        // checker keeps the signatures consistent, so the first is canonical.
        TypeKind::Sum { variants } => variants.iter().find_map(|v| v.methods.get(method))?,
    };
    m.signature.ret_ty.clone().filter(is_supported)
}

pub fn is_comparison(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge
    )
}

/// The concrete type of an operand in a fully-typed body.
pub fn operand_type_of(op: &Operand, local_types: &[Type]) -> Type {
    match op {
        Operand::Local(id) => local_types[id.index()].clone(),
        Operand::Const(lit) => const_type(lit).unwrap_or(Type::Void),
    }
}

/// The concrete (supported) Ok payload of a `Result` return type fixed by a `T!`
/// annotation, or `None` if `t` is not such a `Result` or its Ok payload is not
/// yet concrete. Authoritative for the fallible return's Ok payload.
fn result_concrete_ok(t: &Type) -> Option<Type> {
    match t {
        Type::Sum(n) if n.id == RESULT_TYPE_ID => n
            .result_payloads()
            .map(|(ok, _)| ok.clone())
            .filter(is_supported),
        _ => None,
    }
}

/// The error arms created by `expr!` return the original Result value unchanged.
/// Those synthetic returns carry only the `Err` payload for the enclosing
/// callable; their `Ok` payload belongs to the callee that produced the Result.
fn propagated_result_returns(body: &MirBody) -> HashSet<(usize, LocalId)> {
    let mut tested_results: HashMap<LocalId, LocalId> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let MirStmt::Assign(test, Rvalue::Call(Callee::Builtin(name), args)) = stmt
                && name == "result_is_ok"
                && let Some(Operand::Local(result)) = args.first()
            {
                tested_results.insert(*test, *result);
            }
        }
    }

    let mut returns = HashSet::new();
    for block in &body.blocks {
        if let Terminator::CondBranch {
            cond: Operand::Local(test),
            els,
            ..
        } = &block.term
            && let Some(result) = tested_results.get(test)
            && let Terminator::Return(Operand::Local(returned)) = body.block(*els).term
            && returned == *result
        {
            returns.insert((els.index(), *result));
        }
    }
    returns
}

/// Whether a fallible body actually raises an error: an `error(...)` (an `Err`
/// construction) or an `expr!` propagation (a `result_is_ok` test). A body with
/// neither never produces an `Err`, so its `Result` error payload is free.
fn body_has_error_source(body: &MirBody) -> bool {
    body.blocks.iter().any(|b| {
        b.stmts.iter().any(|s| match s {
            MirStmt::Assign(_, Rvalue::Variant { ty, variant, .. }) => {
                ty == "Result" && variant == "Err"
            }
            MirStmt::Assign(_, Rvalue::Call(Callee::Builtin(n), _)) => n == "result_is_ok",
            _ => false,
        })
    })
}

/// Scan a body for indirect (closure) calls, mapping each *defining* closure
/// local to the argument operands of its call site. Used to type direct-call
/// closures, whose parameter types come from the call rather than the
/// definition. A `let g = <closure>` binds through a `Use` copy, so callee
/// locals are resolved back through `Use` aliases to the local actually holding
/// the `Closure` rvalue.
fn collect_indirect_args(body: &MirBody) -> HashMap<LocalId, Vec<Operand>> {
    let alias = use_aliases(body);
    let mut out: HashMap<LocalId, Vec<Operand>> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            let (MirStmt::Assign(_, rv) | MirStmt::Eval(rv)) = stmt else {
                continue;
            };
            if let Rvalue::Call(Callee::Indirect(Operand::Local(g)), args) = rv {
                out.entry(resolve_alias(&alias, *g))
                    .or_insert_with(|| args.clone());
            }
            // `spawn`/`with` call their closure argument: `spawn(f)` invokes a
            // zero-argument `f`; `with(obj, f)` invokes `f(obj)`. Recording the
            // call shape here types the closure through the same path as any other
            // directly-called closure.
            if let Rvalue::Call(Callee::Builtin(name), args) = rv {
                match name.as_str() {
                    "spawn" => {
                        if let Some(Operand::Local(c)) = args.first() {
                            out.entry(resolve_alias(&alias, *c)).or_default();
                        }
                    }
                    "with" => {
                        if let (Some(obj), Some(Operand::Local(c))) = (args.first(), args.get(1)) {
                            out.entry(resolve_alias(&alias, *c))
                                .or_insert_with(|| vec![obj.clone()]);
                        }
                    }
                    // `_with_all(f, c0, ...)` invokes a zero-argument `f` (the
                    // guarded body references the cowns as captures, not params).
                    "_with_all" => {
                        if let Some(Operand::Local(c)) = args.first() {
                            out.entry(resolve_alias(&alias, *c)).or_default();
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

/// Scan a body for locals stored as record-literal field values, mapping each
/// (alias-resolved) defining local to `(destination local, record type name,
/// field name)`. Used to type a closure that initializes a function-typed
/// field: it is neither called in the body nor passed to a function, so its
/// parameter types come from the field's declared signature, or -- for an
/// unannotated field -- from the constructed instance's checker-seeded
/// substitution on the destination local. Non-closure locals also land in the
/// map; only closure typing consults it, so the extra entries are inert.
fn collect_record_field_closures(body: &MirBody) -> HashMap<LocalId, (LocalId, String, String)> {
    let alias = use_aliases(body);
    let mut out: HashMap<LocalId, (LocalId, String, String)> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            let MirStmt::Assign(dest, Rvalue::Record { ty, fields }) = stmt else {
                continue;
            };
            for (fname, op) in fields {
                if let Operand::Local(l) = op {
                    out.entry(resolve_alias(&alias, *l))
                        .or_insert_with(|| (*dest, ty.clone(), fname.clone()));
                }
            }
        }
    }
    out
}

/// Scan a body for locals passed as arguments to free-function calls, mapping
/// each to `(callee, all call args, its argument index)`. Used to type a closure
/// that is *passed* to a higher-order function (rather than called in place): its
/// parameter types are recovered from how the callee uses that parameter.
#[allow(clippy::type_complexity)]
fn collect_closure_passes(body: &MirBody) -> HashMap<LocalId, (String, Vec<Operand>, usize)> {
    let alias = use_aliases(body);
    let mut out: HashMap<LocalId, (String, Vec<Operand>, usize)> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            let (MirStmt::Assign(_, rv) | MirStmt::Eval(rv)) = stmt else {
                continue;
            };
            // A closure passed to a free function, or to a UFCS method call
            // (`arr.map(closure)` resolves to the free function `map`); both recover
            // the closure's parameter types from the callee's use of it.
            if let Rvalue::Call(Callee::Free(base) | Callee::Method(base), args) = rv {
                for (i, a) in args.iter().enumerate() {
                    if let Operand::Local(g) = a {
                        // Resolve back through `Use` copies to the local that
                        // actually holds the `Closure` (`let g = <closure>`).
                        out.entry(resolve_alias(&alias, *g))
                            .or_insert_with(|| (base.clone(), args.clone(), i));
                    }
                }
            }
        }
    }
    out
}

/// type of an empty array literal `[]` from how it is later filled.
fn collect_array_pushes(body: &MirBody) -> HashMap<LocalId, Operand> {
    let alias = use_aliases(body);
    let mut out: HashMap<LocalId, Operand> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            let (MirStmt::Assign(_, rv) | MirStmt::Eval(rv)) = stmt else {
                continue;
            };
            if let Rvalue::Call(Callee::Method(name), args) = rv {
                // `push(arr, elem)` and `insert(arr, idx, elem)` both reveal the
                // element type of an otherwise-unconstrained `[]` literal; the
                // element operand is the last argument in each.
                let elem = match name.as_str() {
                    "push" => args.get(1),
                    "insert" => args.get(2),
                    _ => None,
                };
                if let (Some(Operand::Local(g)), Some(elem)) = (args.first(), elem) {
                    out.entry(resolve_alias(&alias, *g))
                        .or_insert_with(|| elem.clone());
                }
            }
        }
    }
    out
}

/// Map each `dst` of an `Assign(dst, Use(Local(src)))` to `src`.
fn use_aliases(body: &MirBody) -> HashMap<LocalId, LocalId> {
    let mut alias: HashMap<LocalId, LocalId> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let MirStmt::Assign(dst, Rvalue::Use(Operand::Local(src))) = stmt {
                alias.insert(*dst, *src);
            }
        }
    }
    alias
}

/// Follow a `Use`-alias chain to its root local.
fn resolve_alias(alias: &HashMap<LocalId, LocalId>, mut l: LocalId) -> LocalId {
    for _ in 0..alias.len() + 1 {
        match alias.get(&l) {
            Some(&s) => l = s,
            None => break,
        }
    }
    l
}

#[cfg(test)]
mod tests {
    use super::{check_instances, instance_symbol, monomorphize};
    use prepoly_hir::{NominalType, RESULT_TYPE_ID, Type};

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
        let ast = prepoly_parser::parse(src).expect("parse");
        let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = prepoly_mir::lower_program(&program);
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
        let ast = prepoly_parser::parse(src).expect("parse");
        let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = prepoly_mir::lower_program(&program);
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
        let src = "fun read_text(path: string) {\n  let f = open(path, \"r\")!\n  return \"done\"\n}\n\
                   fun main() {\n  let r = read_text(\"/tmp/missing\")\n}\n";
        let ast = prepoly_parser::parse(src).expect("parse");
        let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = prepoly_mir::lower_program(&program);
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
        assert_ne!(ok, &Type::Record(NominalType::new(-1, "File")));
    }
}
