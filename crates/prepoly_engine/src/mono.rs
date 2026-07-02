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

/// Strip one level of nullable: the inner type of a `T?`, else `ty` unchanged.
/// Used to narrow a value proven non-null by a guard (`if a`) -- the MIR local
/// still carries the declared nullable -- in arithmetic/comparison and as the
/// receiver of an aggregate operation (field/element/`len`/`push`/...).
pub(crate) fn unwrap_nullable(ty: &Type) -> &Type {
    match ty {
        Type::Nullable(inner) => inner,
        other => other,
    }
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

/// Marks a compiler-synthesized instance symbol (a module init, method, static,
/// or closure) so it occupies a namespace disjoint from user function symbols.
/// `$` cannot appear in a source identifier, so a user `fun init0` (symbol
/// `init0`) never collides with the first module init (`$init0`) in the instance
/// map, and the back end maps the two to distinct LLVM names. Must match the
/// prefix `prepoly_jit_llvm`'s `mangle_fn` recognizes.
pub const SYNTH_SIGIL: char = '$';

/// The canonical instance symbol for `base` specialized to `type_args`. Distinct
/// type tuples yield distinct strings, so instances never collide.
pub fn instance_symbol(base: &str, type_args: &[Type]) -> String {
    if type_args.is_empty() {
        base.to_string()
    } else {
        let args = type_args
            .iter()
            .map(|t| t.display())
            .collect::<Vec<_>>()
            .join("_");
        format!("{base}__{args}")
    }
}

/// Instance symbol of an instance-method call. `type_args[0]` is the receiver
/// type, so the symbol is unique per receiver layout; the method name keeps
/// distinct methods apart. Derivable from types alone (no HIR program), so the
/// monomorphizer and the back end agree.
pub fn method_symbol(method: &str, type_args: &[Type]) -> String {
    instance_symbol(&format!("{SYNTH_SIGIL}m_{method}"), type_args)
}

/// Instance symbol of a static call `Type.method(args)`.
///
/// A *no-argument* static that returns an aggregate (record/sum/array) is
/// return-polymorphic: a witness-free `HashMap.new()` whose element types are
/// fixed only by the caller. Its arguments alone do not distinguish
/// `HashMap<string,int32>` from `HashMap<int32,int32>`, so the result type is
/// folded into the key for those, giving each a distinct instance. Statics with
/// arguments are keyed by their arguments alone (the result is a function of
/// them), so non-generic statics are unaffected. The monomorphizer passes the
/// resolved result here; both back ends pass the call's destination type, which
/// is the same value, so all three derive the identical symbol.
pub fn static_symbol(ty: &str, method: &str, type_args: &[Type], result: Option<&Type>) -> String {
    let mut key = type_args.to_vec();
    if type_args.is_empty()
        && let Some(r) = result
        && is_return_polymorphic_result(r)
    {
        key.push(r.clone());
    }
    instance_symbol(&format!("{SYNTH_SIGIL}s_{ty}_{method}"), &key)
}

/// Whether a no-argument static's result type can vary by caller and so must be
/// folded into its instance key: a record/sum built around inferred field types
/// (a witness-free constructor). Scalars/strings/void/arrays are left out,
/// keeping their symbols unchanged. Matches the seeding filter so the
/// monomorphizer and both back ends key these constructors identically.
fn is_return_polymorphic_result(ty: &Type) -> bool {
    matches!(ty, Type::Record(_) | Type::Sum(_))
}

/// The monomorphized instance symbol for a `recv.name(args)` call that resolves
/// to a stdlib primitive/array method, when such an instance exists in
/// `program`. The receiver's class ([`Type::primitive_class`]) plus the method
/// name reconstruct the body's class-qualified symbol (the same scheme HIR
/// lowering used), which `instance_symbol` keys by argument types. Lets the back
/// ends route the call without carrying the HIR `primitive_methods` table.
pub fn prim_method_instance(
    program: &MonoProgram,
    name: &str,
    arg_types: &[Type],
) -> Option<String> {
    let class = arg_types.first()?.primitive_class()?;
    let sym = instance_symbol(&prepoly_hir::prim_method_symbol(class, name), arg_types);
    program.lookup(&sym).map(|_| sym)
}

/// Instance symbol of a closure: distinct per closure id, captured types, and
/// parameter types. Derivable from types alone so the monomorphizer and back end
/// agree.
pub fn closure_symbol(id: ClosureId, capture_types: &[Type], param_types: &[Type]) -> String {
    let mut args = capture_types.to_vec();
    args.extend_from_slice(param_types);
    instance_symbol(&format!("{SYNTH_SIGIL}clo{}", id.index()), &args)
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
        match res {
            Ok(_) => init_symbols.push(sym),
            Err(e) if matches!(init.module.as_slice(), [m] if m == "main") => {
                return Err(format!("top-level code is outside the typed subset: {e}"));
            }
            Err(_) => {}
        }
    }

    // Roots: every zero-parameter function. Their bodies pull in the rest.
    for f in &mir.functions {
        if f.body.params.is_empty() {
            let _ = mono.instantiate_fn(&f.symbol, Vec::new());
            mono.in_progress.clear();
        }
    }

    Ok(mono.into_program(init_symbols))
}

/// Build the concrete `Type` of a declared record as it arrives at the runtime
/// deserialize boundary: a nominal carrying every field's declared
/// type in its substitution, exactly as a constructed record does -- so it
/// satisfies the typed backend's support check and field reads resolve. Returns
/// `None` if `name` is not a record type in `module`, or a field type is unknown.
/// (A future structural deserializer builds the substitution from the data's
/// shape; for a declared target this derives it from the field declarations.)
pub fn boundary_record_type(program: &Program, module: &[String], name: &str) -> Option<Type> {
    boundary_record_type_of(program.resolve_type(module, name)?)
}

/// Like [`boundary_record_type`] but keyed by the type's id -- the tag a boundary
/// value carries at runtime. The dispatch trampoline rebuilds the consumer's
/// argument type from a runtime value's tag with this.
pub fn boundary_record_type_by_id(program: &Program, id: i32) -> Option<Type> {
    boundary_record_type_of(program.type_by_id(id)?)
}

/// Like [`boundary_record_type`] but found by the type's source name across all
/// modules (the deserialize boundary names its target type); the first match
/// wins. Used by the dispatch trampoline.
pub fn boundary_record_type_by_name(program: &Program, name: &str) -> Option<Type> {
    program
        .types
        .values()
        .find(|t| t.name == name)
        .and_then(boundary_record_type_of)
}

/// The sentinel type id for a *structural* record built at the deserialize boundary
/// from a value's shape rather than a declaration. No declared type
/// uses this id, so `type_by_id` misses and the typed backend lays the record out
/// from its substitution (sorted field order) instead of a declaration.
pub const STRUCTURAL_RECORD_ID: i32 = i32::MIN;

/// Build a `Type::Record` from a field list discovered at the deserialize
/// boundary: the data structure -- not a declared type name -- drives the
/// type. The resulting record has no declaration; its layout comes from the
/// substitution (the typed backend orders structural fields by name). The consumer
/// is then monomorphized against this type exactly like a declared one, and the
/// boundary's structural-requirement check rejects a value missing a read field.
pub fn boundary_record_type_from_fields(fields: &[(String, Type)]) -> Type {
    let mut subst = Substitution::empty();
    for (name, ty) in fields {
        subst.insert(name.clone(), ty.clone());
    }
    Type::Record(NominalType::with_substitution(
        STRUCTURAL_RECORD_ID,
        "<structural>",
        subst,
    ))
}

/// Parse a structural record descriptor `"field:tag,field:tag"` (optionally brace-
/// wrapped) into ordered `(field, Type)` pairs, the data-driven type description a
/// `deserialize` boundary produces. Returns `None` on a malformed
/// descriptor or an unknown field type tag.
pub fn parse_structural_descriptor(desc: &str) -> Option<Vec<(String, Type)>> {
    let body = desc
        .trim()
        .trim_start_matches('{')
        .trim_end_matches('}')
        .trim();
    if body.is_empty() {
        return None;
    }
    let mut out = Vec::new();
    for field in body.split(',') {
        let (name, tag) = field.split_once(':')?;
        out.push((name.trim().to_string(), type_from_tag(tag.trim())?));
    }
    Some(out)
}

/// The `Type` named by a structural-descriptor field tag.
fn type_from_tag(tag: &str) -> Option<Type> {
    if let Some(k) = IntKind::from_name(tag) {
        return Some(Type::Int(k));
    }
    Some(match tag {
        "float32" => Type::Float(FloatKind::F32),
        "float64" => Type::Float(FloatKind::F64),
        "string" => Type::Str,
        "bool" => Type::Bool,
        _ => return None,
    })
}

fn boundary_record_type_of(info: &prepoly_hir::TypeInfo) -> Option<Type> {
    let TypeKind::Record { fields, .. } = &info.kind else {
        return None;
    };
    let mut subst = Substitution::empty();
    for f in fields {
        subst.insert(f.name.clone(), f.resolved_ty.clone()?);
    }
    Some(Type::Record(NominalType::with_substitution(
        info.id,
        info.name.clone(),
        subst,
    )))
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
    in_progress: HashSet<String>,
}

impl<'m, 'p> Monomorphizer<'m, 'p> {
    /// Build a monomorphizer over a MIR program: index functions, record methods,
    /// and closures so instances can be created on demand.
    fn new(mir: &'m MirProgram, program: &'p Program) -> Self {
        let mut by_method: HashMap<(&str, &str), &MirMethod> = HashMap::new();
        for m in &mir.methods {
            // Record methods only for now (sum-variant methods are out of scope).
            if m.variant.is_none() {
                by_method.insert((m.type_symbol.as_str(), m.method.as_str()), m);
            }
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
            in_progress: HashSet::new(),
        }
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
        self.in_progress.insert(sym.clone());

        let mut local_types: Vec<Option<Type>> = vec![None; body.locals.len()];
        for (i, p) in body.params.iter().enumerate() {
            local_types[p.index()] = Some(type_args[i].clone());
        }
        for (local, ty) in capture_seed {
            local_types[local.index()] = Some(ty.clone());
        }
        // A `let x: T = ...` binding fixed its local's type during lowering; seed it
        // so monomorphization preserves an annotation the initializer alone cannot
        // express (e.g. `let x: int32? = null`).
        for (i, decl) in body.locals.iter().enumerate() {
            if let Some(t) = decl.ty.as_known() {
                local_types[i] = Some(t.clone());
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

        // Closure parameter sources: a direct in-body call, or being passed to a
        // higher-order function (probed from the callee). Array pushes give the
        // element type of an empty `[]` literal.
        let indirect_args = collect_indirect_args(body);
        let closure_passes = collect_closure_passes(body);
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

        self.in_progress.remove(&sym);
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
    fn type_stmt(
        &mut self,
        stmt: &MirStmt,
        cur_sym: &str,
        module: &[String],
        indirect_args: &HashMap<LocalId, Vec<Operand>>,
        closure_passes: &HashMap<LocalId, (String, Vec<Operand>, usize)>,
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
                        indirect_args,
                        closure_passes,
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
        // A genuine record method takes priority.
        if let Type::Record(n) = &arg_types[0]
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
        if self.in_progress.contains(&target) {
            return Err(format!(
                "mutual recursion (`{cur_sym}` <-> `{target}`) is unsupported on the typed backend"
            ));
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
        if self.in_progress.contains(&target) {
            return Err(format!(
                "mutual recursion (`{cur_sym}` <-> `{target}`) is unsupported on the typed backend"
            ));
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
        // Mixed numeric operands yield their common type (int width/signedness, and
        // int-with-float), except that an integer literal adapts to a variable's
        // int type (one operand a variable, the other a literal).
        if let (Some(ta), Some(tb)) = (&ta, &tb) {
            let (na, nb) = (unwrap_nullable(ta), unwrap_nullable(tb));
            // A literal adapts to the variable's type only when it fits: a
            // magnitude-typed int64 literal (e.g. INT64_MAX) mixed with an int32
            // variable takes the common (wider) type instead of truncating.
            let lit_kind = if a_local { nb } else { na };
            let var_kind = if a_local { na } else { nb };
            let lit_fits = match (lit_kind, var_kind) {
                (Type::Int(lk), Type::Int(vk)) => lk.bits() <= vk.bits(),
                _ => true,
            };
            let int_literal_adapt = matches!((na, nb), (Type::Int(_), Type::Int(_)))
                && (a_local != b_local)
                && lit_fits;
            if !int_literal_adapt && let Some(common) = prepoly_hir::common_numeric_type(na, nb) {
                return Ok(Some(common));
            }
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
                // A field initialized to `null` carries the bare `Nullable(Never)`;
                // recover the field's declared nullable type so `next: Node?` stays
                // `Node?` (not `Never?`) -- the null value coerces to it. Essential
                // for self-referential records (the field links back to the type).
                Some(Type::Nullable(inner))
                    if matches!(*inner, Type::Never)
                        && matches!(fdecl.resolved_ty, Some(Type::Nullable(_))) =>
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
    fn closure_annotated_params(&self, id: ClosureId) -> Option<Vec<Type>> {
        let clo = self.by_closure.get(&id)?;
        clo.params
            .iter()
            .map(|p| clo.body.locals[p.index()].ty.as_known().cloned())
            .collect()
    }

    /// Type a closure local: its captures come from the creation site and its
    /// parameter types from how it is used -- either an in-body call (direct-call
    /// closures), when it is passed to a higher-order function (the callee's use of
    /// that parameter, recovered by probing), or, for an escaping closure, its own
    /// parameter annotations. Also instantiates the closure body. `None` while any
    /// operand type is still unresolved.
    #[allow(clippy::too_many_arguments)]
    fn closure_local_type(
        &mut self,
        id: ClosureId,
        captures: &[Operand],
        local: LocalId,
        indirect_args: &HashMap<LocalId, Vec<Operand>>,
        closure_passes: &HashMap<LocalId, (String, Vec<Operand>, usize)>,
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
                None => return Ok(None),
            }
        } else if let Some(annotated) = self.closure_annotated_params(id) {
            // An escaping closure (returned): type it from its own parameter
            // annotations rather than a call/pass site.
            annotated
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
        // closure (`arr.map(f)`), its body lives under the class-qualified symbol,
        // not the bare name; recover it from the receiver argument's class.
        let func = match self.by_fn.get(base) {
            Some(f) => *f,
            None => {
                let recv_class = pass_args
                    .first()
                    .and_then(|a| self.operand_type(a, caller_local_types).ok().flatten())
                    .and_then(|t| t.primitive_class());
                let sym = recv_class.and_then(|class| {
                    self.program
                        .primitive_methods
                        .get(&(class.to_string(), base.to_string()))
                });
                match sym.and_then(|s| self.by_fn.get(s.as_str())) {
                    Some(f) => *f,
                    None => return Ok(None),
                }
            }
        };
        let body = &func.body;
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
        if self.in_progress.contains(&sym) {
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
                let (ta, tb) = (ty(a), ty(b));
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
    let TypeKind::Record { methods, .. } = &info.kind else {
        return None;
    };
    methods
        .get(method)?
        .signature
        .ret_ty
        .clone()
        .filter(is_supported)
}

/// The default concrete type of a constant literal (integers default to int32,
/// floats to float64). Errors on non-scalar constants.
fn const_type(lit: &prepoly_mir::Literal) -> Result<Type, String> {
    use prepoly_mir::Literal;
    match lit {
        // An integer literal defaults by magnitude: int32 when it fits, int64
        // otherwise (a 64-bit constant like INT64_MAX must not truncate).
        Literal::Int(v) => Ok(Type::Int(int_literal_kind(*v))),
        Literal::Float(_) => Ok(Type::Float(FloatKind::F64)),
        Literal::Bool(_) => Ok(Type::Bool),
        Literal::Void => Ok(Type::Void),
        Literal::Str(_) => Ok(Type::Str),
        // The null literal: a nullable whose element type is unconstrained here
        // (it unifies with the contextual `T?` it is coerced to).
        Literal::Null => Ok(Type::Nullable(Box::new(Type::Never))),
    }
}

/// Whether a type is in the typed back end's scope: scalars, and records whose
/// fields are all supported (a fully-resolved field-type substitution).
fn is_supported(ty: &Type) -> bool {
    is_supported_rec(ty, &mut HashSet::new())
}

/// `is_supported` with a guard against self-referential record types (e.g.
/// `type Node = { next: Node? }`): a nominal already on the visiting path is assumed
/// supported, so the check terminates. A recursive field is a heap pointer, so the
/// layout is finite even though the type definition is cyclic.
/// Fill a record's field-type substitution from its HIR declaration when it is a
/// bare reference (empty substitution -- a sum variant field's declared type once
/// bound, or a nested declared field). The resolved record is self-describing, so
/// `is_supported` and field-access inference treat it like a constructed value
/// without relaxing the support check for genuinely-unresolved types. Recurses into
/// field and wrapper types; a record already being resolved (a cycle such as
/// `Node { next: Node? }`) is left bare and handled by `is_supported_rec`'s visiting
/// guard. A sum carries no value substitution (its layout comes from the HIR), so it
/// is already self-describing and left as is.
fn resolve_nominal(program: &Program, ty: &Type) -> Type {
    fn go(program: &Program, ty: &Type, stack: &mut HashSet<i32>) -> Type {
        match ty {
            Type::Record(n) if n.substitution.is_empty() && !n.is_name("File") => {
                let Some(info) = program.type_by_id(n.id) else {
                    return ty.clone();
                };
                let TypeKind::Record { fields, .. } = &info.kind else {
                    return ty.clone();
                };
                if !stack.insert(n.id) {
                    return ty.clone(); // already resolving this type: a cycle
                }
                let mut subst = Substitution::empty();
                for f in fields {
                    if let Some(t) = &f.resolved_ty {
                        subst.insert(f.name.clone(), go(program, t, stack));
                    }
                }
                stack.remove(&n.id);
                Type::Record(NominalType::with_substitution(n.id, n.name.clone(), subst))
            }
            Type::Nullable(inner) => Type::Nullable(Box::new(go(program, inner, stack))),
            Type::Slice(inner) => Type::Slice(Box::new(go(program, inner, stack))),
            Type::Array(inner, k) => Type::Array(Box::new(go(program, inner, stack)), *k),
            _ => ty.clone(),
        }
    }
    go(program, ty, &mut HashSet::new())
}

/// Whether a sum variant's field can be laid out by the typed back end. An
/// unannotated field with no inferred type (`None`/`Unknown`) is allowed as long
/// as it is never accessed: it occupies an opaque, pointer-sized slot. Any other
/// field type must be concretely supported once its nominal references are resolved
/// (a record/sum field is a heap pointer whose own layout is monomorphized
/// independently).
fn variant_field_layoutable(program: &Program, ty: &Option<Type>) -> bool {
    match ty {
        None | Some(Type::Unknown(_)) => true,
        Some(t) => is_supported(&resolve_nominal(program, t)),
    }
}

fn is_supported_rec(ty: &Type, visiting: &mut HashSet<i32>) -> bool {
    match ty {
        Type::Bool | Type::Int(_) | Type::Float(_) | Type::Void | Type::Str => true,
        // `Never` only types values on a statically-unreachable path -- e.g. the
        // truthy arm of `if x` for a bare `null` (`never?`), where narrowing
        // yields `never`. The arm is type-checked (so payloads still infer) but
        // the back end skips emitting it, so an opaque placeholder slot suffices.
        Type::Never => true,
        // `File` is a builtin opaque handle (a runtime file descriptor object), not
        // a user record with fields, so it is supported despite an empty field set.
        Type::Record(n) if n.is_name("File") => true,
        Type::Record(n) => {
            if !visiting.insert(n.id) {
                return true; // already on the path: a self-reference, finite layout
            }
            // A bare reference (empty substitution -- a field's declared nominal
            // type, or a sum variant binding) is a supported heap pointer; its own
            // field concreteness is validated when the record is monomorphized as a
            // value. A substituted (constructed/generic) record additionally
            // requires every field type to be supported. This mirrors how a `Sum`
            // is trusted as a pointer below.
            let ok = !n.substitution.is_empty()
                && n.substitution
                    .iter()
                    .all(|(_, t)| is_supported_rec(t, visiting));
            visiting.remove(&n.id);
            ok
        }
        // A bare sum reference (empty substitution) is a supported heap pointer
        // whose per-variant field concreteness is checked at construction
        // (`variant_type`). A substituted sum -- a constructed `Result<T, E>` --
        // additionally requires its payload types to be supported, so an open `T!`
        // error payload (an unresolved `Unknown`) is rejected here. That makes a
        // `-> T!` signature's annotation unsupported, so `instantiate_fn` drops it
        // and the engine infers the concrete `Result` from the body instead.
        Type::Sum(n) => {
            if !visiting.insert(n.id) {
                return true; // already on the path: a self-reference, finite layout
            }
            let ok = n.substitution.is_empty()
                || n.substitution
                    .iter()
                    .all(|(_, t)| is_supported_rec(t, visiting));
            visiting.remove(&n.id);
            ok
        }
        Type::Slice(elem) | Type::Array(elem, _) => is_supported_rec(elem, visiting),
        // A tuple is a fixed heterogeneous aggregate; supported when every element is.
        Type::Tuple(elems) => elems.iter().all(|t| is_supported_rec(t, visiting)),
        // A closure value (a typed environment + function pointer).
        Type::Fun(params, ret) => {
            params.iter().all(|p| is_supported_rec(p, visiting)) && is_supported_rec(ret, visiting)
        }
        // A nullable value (a heap cell pointer, null = null pointer). `Never` is
        // the element type of the bare `null` literal until it is coerced.
        Type::Nullable(inner) => {
            matches!(**inner, Type::Never) || is_supported_rec(inner, visiting)
        }
        _ => false,
    }
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

/// The blocks reachable from the entry once statically-known `if` conditions are
/// folded: a `never?` condition (a bare `null`, always null) is taken as false
/// and a non-nullable / non-bool condition (always truthy) as true, so the dead
/// arm is never visited. The typed back end uses this to skip emitting an arm
/// that cannot run -- and the unwrapped `never` values it would otherwise
/// contain (e.g. `a * 2` where `a` is a bare `null`) -- while monomorphization
/// still types both arms so a fallible callable's `Result` payloads infer from
/// whichever arm supplies each.
pub fn reachable_blocks(body: &MirBody, local_types: &[Type], ret: &Type) -> Vec<bool> {
    let mut reached = vec![false; body.blocks.len()];
    let mut stack = vec![body.entry];
    while let Some(id) = stack.pop() {
        if std::mem::replace(&mut reached[id.index()], true) {
            continue;
        }
        match &body.block(id).term {
            Terminator::Goto(b) => stack.push(*b),
            Terminator::CondBranch { cond, then, els } => {
                match cond_static_truthiness(body, local_types, ret, cond, *then) {
                    Some(true) => stack.push(*then),
                    Some(false) => stack.push(*els),
                    None => {
                        stack.push(*then);
                        stack.push(*els);
                    }
                }
            }
            Terminator::Return(_) | Terminator::Unreachable => {}
        }
    }
    reached
}

/// The effective static truthiness of an `if` condition, used to fold a branch.
/// Beyond the operand's own static truthiness, a *structural* `if` folds to false
/// when its then-branch cannot type for this concrete value: its reachable return
/// is a clear primitive-kind mismatch against the function's return type (a
/// structural field that is absent -- already `never?` -- or present at the wrong
/// type). The front end prunes the same dead arm; here the back end skips emitting
/// it so a generic function applied to a non-fitting structure degrades gracefully
/// (the guarded use is dead) rather than miscompiling.
pub fn cond_static_truthiness(
    body: &MirBody,
    local_types: &[Type],
    ret: &Type,
    cond: &Operand,
    then: BlockId,
) -> Option<bool> {
    if then_return_conflicts(body, local_types, ret, then) {
        return Some(false);
    }
    operand_type_of(cond, local_types).static_truthiness()
}

/// Whether the then-branch reached unconditionally from `then` ends in a `return`
/// whose value's primitive kind clearly differs from `ret` (no coercion bridges
/// `string` vs `int`, etc.). A nested branch in the then-arm is not folded.
fn then_return_conflicts(body: &MirBody, local_types: &[Type], ret: &Type, then: BlockId) -> bool {
    // In a fallible callable a bare `return v` is the `Ok` payload, so compare the
    // returned value against the Ok payload type, not the whole `Result`.
    let target = match ret {
        Type::Sum(n) if n.id == RESULT_TYPE_ID => {
            n.result_payloads().map(|(ok, _)| ok).unwrap_or(ret)
        }
        _ => ret,
    };
    let mut id = then;
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(id.index()) {
            return false;
        }
        match &body.block(id).term {
            Terminator::Return(op) => {
                let op_ty = operand_type_of(op, local_types);
                // A returned `Result` flows whole; only a bare value is the Ok
                // payload, so only it is compared against the Ok type.
                if matches!(&op_ty, Type::Sum(n) if n.id == RESULT_TYPE_ID) {
                    return false;
                }
                return primitive_kind_conflict(&op_ty, target);
            }
            Terminator::Goto(b) => id = *b,
            _ => return false,
        }
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

/// Whether `a` and `b` are concrete primitives of different kinds (string/bool/
/// int/float), a mismatch no numeric conversion bridges. Non-primitive types are
/// treated as non-conflicting (conservative -- the fold only targets clear cases).
fn primitive_kind_conflict(a: &Type, b: &Type) -> bool {
    fn kind(t: &Type) -> Option<u8> {
        match t {
            Type::Str => Some(0),
            Type::Bool => Some(1),
            Type::Int(_) => Some(2),
            Type::Float(_) => Some(3),
            _ => None,
        }
    }
    matches!((kind(a), kind(b)), (Some(x), Some(y)) if x != y)
}

/// Check that a binary operator's operands have compatible, in-scope types.
fn check_bin(op: BinOp, a: &Type, b: &Type) -> Result<(), String> {
    // `x == null` / `x != null` (or comparing nullables) is a null/identity test.
    if matches!(op, BinOp::Eq | BinOp::Ne)
        && (matches!(a, Type::Nullable(_)) || matches!(b, Type::Nullable(_)))
    {
        return Ok(());
    }
    // A nullable operand in an arithmetic/comparison context is narrowed to its
    // element type (valid programs guard for null first); the back end unwraps it.
    let a = unwrap_nullable(a);
    let b = unwrap_nullable(b);
    // `never` is the bottom type: it only reaches here on a statically-dead path
    // (a bare `null` narrowed in an always-false `if` arm), which the back end
    // never emits, so any operator over it is vacuously well-typed.
    if matches!(a, Type::Never) || matches!(b, Type::Never) {
        return Ok(());
    }
    let same = a == b;
    let integer = |t: &Type| matches!(t, Type::Int(_));
    let both_int = integer(a) && integer(b);
    match op {
        // `+` is numeric addition or string concatenation. Two integers may
        // differ in width (a literal adapts to the other's type; the back end
        // coerces both to the operand type).
        // Numeric operands of differing types implicitly convert to their common
        // type (mixed width, signedness, and int-with-float); `+` also concatenates
        // two strings.
        BinOp::Add => {
            if prepoly_hir::common_numeric_type(a, b).is_some() || (same && matches!(a, Type::Str))
            {
                Ok(())
            } else {
                Err(format!(
                    "`Add` needs two numeric/string operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        BinOp::Sub | BinOp::Mul | BinOp::Div => {
            if prepoly_hir::common_numeric_type(a, b).is_some() {
                Ok(())
            } else {
                Err(format!(
                    "`{op:?}` needs two numeric operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        // Remainder is integer-only but the widths may differ (coerced to the
        // common int); the bitwise/shift operators need two equal integers.
        BinOp::Rem => {
            if both_int {
                Ok(())
            } else {
                Err(format!(
                    "`Rem` needs two integer operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
            if same && integer(a) {
                Ok(())
            } else {
                Err(format!(
                    "`{op:?}` needs two equal integer operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        // A numeric comparison converts mixed operands to a common type; equality
        // also applies to two bools or two strings.
        BinOp::Eq | BinOp::Ne => {
            if prepoly_hir::common_numeric_type(a, b).is_some()
                || (same && matches!(a, Type::Bool | Type::Str))
            {
                Ok(())
            } else {
                Err(format!(
                    "`{op:?}` needs two comparable operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
            if prepoly_hir::common_numeric_type(a, b).is_some() {
                Ok(())
            } else {
                Err(format!(
                    "`{op:?}` needs two comparable numeric operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        BinOp::And | BinOp::Or => Err(format!("`{op:?}` is unsupported on the typed backend")),
    }
}

/// Shared operand-type rule used by both the typer and the typed dispatch to
/// pick a binary op's operand type: for two integers of different widths, the
/// wider (so a narrower operand is coerced up); otherwise a `Local` operand's
/// type, preferring a non-constant.
pub fn binary_operand_type(a: &Operand, b: &Operand, local_types: &[Type]) -> Type {
    let ra = operand_type_of(a, local_types);
    let rb = operand_type_of(b, local_types);
    // A comparison against the null literal keeps the nullable type (the back end
    // compares pointers); other nullables narrow to their element type.
    let null_lit = |t: &Type| matches!(t, Type::Nullable(inner) if matches!(**inner, Type::Never));
    if null_lit(&ra) {
        return rb;
    }
    if null_lit(&rb) {
        return ra;
    }
    let ta = unwrap_nullable(&ra).clone();
    let tb = unwrap_nullable(&rb).clone();
    let a_local = matches!(a, Operand::Local(_));
    let b_local = matches!(b, Operand::Local(_));
    // An integer literal adapts to a variable's int type (e.g. `byte - 32` stays
    // uint8) rather than forcing a common type.
    if let (Type::Int(_), Type::Int(_)) = (&ta, &tb) {
        match (a_local, b_local) {
            (true, false) => return ta,
            (false, true) => return tb,
            _ => {}
        }
    }
    // Otherwise mixed numeric operands implicitly convert to their common type
    // (wider width, signedness, and int-with-float).
    if let Some(common) = prepoly_hir::common_numeric_type(&ta, &tb) {
        return common;
    }
    if a_local {
        ta
    } else if b_local {
        tb
    } else {
        ta
    }
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
                    _ => {}
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

/// Scan a body for `arr.push(elem)` calls, mapping each array local (resolved
/// through `Use` aliases) to a pushed element operand. Used to infer the element
/// Join two return-operand types of an unannotated non-fallible callable. The
/// front end has already checked the returns are mutually consistent, so this only
/// reconciles the nullable/never lattice: a `return null` path (`never?`) combined
/// with a value-returning path yields that value's nullable type, and an
/// unreachable `Never` arm is absorbed by the other. Without this join the inferred
/// return type would be whichever return block the fixpoint typed first, so a `get`
/// returning `value` or `null` could freeze to the bare `value` type and then have
/// its `null` path rejected as "returns a null value where `T` is required".
fn merge_return_types(a: &Type, b: &Type) -> Type {
    fn nullable_of(t: Type) -> Type {
        match t {
            Type::Nullable(_) => t,
            other => Type::Nullable(Box::new(other)),
        }
    }
    match (a, b) {
        _ if a == b => a.clone(),
        // `Never` types only a statically-unreachable path; the other arm wins.
        (Type::Never, _) => b.clone(),
        (_, Type::Never) => a.clone(),
        (Type::Nullable(x), Type::Nullable(y)) => {
            Type::Nullable(Box::new(merge_return_types(x, y)))
        }
        // One nullable and one bare value (commonly `never?` from `null` vs a real
        // value): the result is nullable over the joined element type.
        (Type::Nullable(x), y) => nullable_of(merge_return_types(x, y)),
        (x, Type::Nullable(y)) => nullable_of(merge_return_types(x, y)),
        // Two distinct non-null types should not occur in a checked program; keep
        // the first so inference stays deterministic rather than panicking.
        _ => a.clone(),
    }
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
