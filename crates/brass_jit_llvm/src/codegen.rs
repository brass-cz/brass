//! LLVM IR generation: [`LlvmCodegen`] implements `brass_engine::Codegen`
//! over monomorphized MIR and emits typed, fully unboxed code. Each instance
//! becomes an LLVM function typed by its concrete parameter and return types
//! (a closure instance takes its environment pointer first); control flow is
//! native LLVM, and heap operations are calls into the runtime.
//!
//! This module holds the generator's state and the emission utilities its
//! parts share. The parts:
//!
//! - `lowering`: the `brass_engine::Codegen` implementation, one method per
//!   MIR operation;
//! - `aggregate`: heap object layouts (records, tuples, sums, closures,
//!   nullable cells, arrays) and field/element access;
//! - `memory`: per-type cycle-collector tracers, destructors and deep copies;
//! - `render`: per-type `to_string` renderers for records and sums;
//! - `equality`: per-type structural `==`;
//! - `session`: module finalization, the ORC session, and lazy function
//!   groups.

use fxhash::FxHashMap as HashMap;
use fxhash::FxHashSet as HashSet;
use std::cell::RefCell;
use std::rc::Rc;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicTypeEnum, FunctionType};
use inkwell::values::BasicValueEnum;
use inkwell::values::{FloatValue, FunctionValue, GlobalValue, IntValue, PointerValue};
use inkwell::{FloatPredicate, IntPredicate};

use brass_engine::Codegen as EngineCodegen;
use brass_hir::{FloatKind, IntKind, NominalType, Program, Type};
use brass_mir::LocalId;
use brass_parser::ast::*;

use crate::jit::orc::{OrcContext, OrcJit};
use crate::layout::Abi;
use crate::monomorph::*;

mod aggregate;
mod closure_target;
mod equality;
mod lowering;
mod memory;
mod render;
mod session;

/// A typed stack slot for one MIR local on the `brass_engine::Codegen` path:
/// its alloca pointer and the concrete LLVM type to load/store. A `void` local
/// has no slot (its value is never observed).
#[derive(Clone, Copy)]
struct MirSlot<'ctx> {
    ptr: PointerValue<'ctx>,
    ty: BasicTypeEnum<'ctx>,
}

/// Peel the front-end wrappers that do not change a value's runtime shape
/// (mutability, reference-ness, const-ness) to reach the underlying type a
/// deep copy dispatches on. A nullable is deliberately *not* peeled: at runtime
/// it is a heap cell `{ header16 | value@16 }` around the value (null = null
/// pointer), so a deep copy must rebuild the cell rather than reinterpret the
/// cell pointer as the inner value.
fn unwrap_copy_wrappers(ty: &Type) -> &Type {
    match ty {
        Type::Mut(inner) | Type::Ref(inner) | Type::ConstOf(inner) => unwrap_copy_wrappers(inner),
        _ => ty,
    }
}

/// Whether `from` and `to` are records/sums of different declarations (or
/// hold them at the same position of an array, slice, or nullable shape), so
/// their values have different layouts. Instantiations of one declaration and
/// passing-mode wrappers share a layout; a structural record's layout is its
/// field-name set.
fn nominal_layout_differs(from: &Type, to: &Type) -> bool {
    fn declaration_differs(a: &NominalType, b: &NominalType) -> bool {
        if a.id != b.id || (a.id < 0 && a.name != b.name) {
            return true;
        }
        a.id == brass_hir::STRUCTURAL_RECORD_ID
            && !a
                .substitution
                .iter()
                .map(|(field, _)| field)
                .eq(b.substitution.iter().map(|(field, _)| field))
    }
    match (unwrap_copy_wrappers(from), unwrap_copy_wrappers(to)) {
        (Type::Record(a), Type::Record(b)) | (Type::Sum(a), Type::Sum(b)) => {
            declaration_differs(a, b)
        }
        (Type::Record(_), Type::Sum(_)) | (Type::Sum(_), Type::Record(_)) => true,
        (Type::Slice(a), Type::Slice(b))
        | (Type::Array(a, _), Type::Array(b, _))
        | (Type::Nullable(a), Type::Nullable(b)) => nominal_layout_differs(a, b),
        _ => false,
    }
}

/// Whether a value of `from` is, unchanged, a valid value of `to`: the two
/// types share one runtime representation -- the same scalar width, or heap
/// values whose contents are laid out alike (element, payload and closure
/// signature representations included). `never` and unresolved types carry no
/// value and match anything.
fn same_representation(from: &Type, to: &Type) -> bool {
    match (unwrap_copy_wrappers(from), unwrap_copy_wrappers(to)) {
        (Type::Never | Type::Unknown(_), _) | (_, Type::Never | Type::Unknown(_)) => true,
        (Type::Bool, Type::Bool) | (Type::Str, Type::Str) | (Type::Void, Type::Void) => true,
        (Type::Int(a), Type::Int(b)) => a.bits() == b.bits(),
        (Type::Float(a), Type::Float(b)) => a == b,
        (Type::Record(_), Type::Record(_)) | (Type::Sum(_), Type::Sum(_)) => {
            !nominal_layout_differs(from, to)
        }
        (Type::Slice(a) | Type::Array(a, _), Type::Slice(b) | Type::Array(b, _))
        | (Type::Nullable(a), Type::Nullable(b)) => same_representation(a, b),
        (Type::Tuple(a), Type::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(x, y)| same_representation(x, y))
        }
        (Type::Fun(pa, ra), Type::Fun(pb, rb)) => {
            pa.len() == pb.len()
                && pa.iter().zip(pb).all(|(x, y)| same_representation(x, y))
                && same_representation(ra, rb)
        }
        _ => false,
    }
}

/// The memo key (and LLVM name) of the per-type helper of family `kind`
/// (`drop`, `tostr`, ...). Built from [`brass_hir::type_key`], which encodes a
/// nominal by its id and substitution and every type constructor
/// unambiguously; a display rendering names a nominal by its bare name and
/// does not parenthesize function types, so types with different layouts can
/// render alike.
fn helper_key(kind: &str, ty: &Type) -> String {
    mangle_fn(&format!("{kind}_{}", brass_hir::type_key(ty)))
}

/// [`helper_key`] for a closure helper keyed by its capture types.
fn capture_helper_key(kind: &str, capture_types: &[Type]) -> String {
    let captures = capture_types
        .iter()
        .map(brass_hir::type_key)
        .collect::<Vec<_>>()
        .join("_");
    mangle_fn(&format!("{kind}_{captures}"))
}

fn is_managed_heap(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Str
            | Type::Record(..)
            | Type::Sum(..)
            | Type::Slice(..)
            | Type::Array(..)
            | Type::Fun(..)
            | Type::Tuple(..)
    )
}

/// Whether a value of `ty` is a heap reference the cycle collector must follow: a
/// managed object, or a nullable cell (itself a heap object holding a value). This
/// is broader than `is_managed_heap` because a cycle is typically bootstrapped
/// through a nullable field (`next: Node?`).
///
/// This is also the *release* predicate for a destructor's contained
/// fields/elements/captures, and must stay extensionally equal to the engine's
/// `rc_managed`: every store the engine retains (which includes nullable cells)
/// must be released on drop, or the cell -- and whatever it owns -- leaks.
fn is_traced(ty: &Type) -> bool {
    is_managed_heap(ty) || matches!(ty, Type::Nullable(_))
}

/// Whether [`LlvmCodegen::to_string`] returns a caller-owned temporary for this
/// exact type. String identities are borrowed and opaque fallbacks are interned.
fn rendered_string_is_owned(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Bool
            | Type::Int(_)
            | Type::Float(_)
            | Type::Nullable(_)
            | Type::Slice(_)
            | Type::Array(..)
            | Type::Tuple(_)
            | Type::Record(_)
            | Type::Sum(_)
    )
}

/// The per-program and per-body state of the `brass_engine::Codegen`
/// implementation, populated as [`LlvmCodegen`] emits each monomorphized
/// instance.
#[derive(Default)]
struct MirState<'ctx> {
    /// Typed storage per MIR `LocalId`; `None` for a `void` local.
    locals: Vec<Option<MirSlot<'ctx>>>,
    /// The LLVM block for each MIR `BlockId` of the current body.
    blocks: Vec<BasicBlock<'ctx>>,
    /// Typed module-level globals, declared in `begin_program`.
    globals: HashMap<String, GlobalValue<'ctx>>,
    /// Init instance symbols, run (in order) before `main`.
    init_symbols: Vec<String>,
    /// Immutable heap-typed module globals (never reassigned outside their
    /// initializer): auto-frozen after init so the module namespace is shareable
    /// across threads.
    frozen_globals: Vec<String>,
    /// The LLVM signature of every monomorphized instance, keyed by mangled
    /// name and shared by all of a lazy run's function modules (one context
    /// serves them all). Present only in lazy per-function codegen, where
    /// [`LlvmCodegen::instance_fn`] declares referenced instances on demand
    /// instead of `begin_program` declaring all of them into every module.
    lazy_signatures: Option<std::rc::Rc<HashMap<String, FunctionType<'ctx>>>>,
    /// Session-owned pending modules and native code. Materializers never borrow
    /// this compiler, including during a runtime resolver's nested ORC lookup.
    orc: Option<OrcJit>,
    /// Defined public symbols and whether their bodies have lazy implementation
    /// names. Declarations alone never reserve a definition across batches.
    defined: HashMap<String, bool>,
    /// Helpers reserved by earlier batches, including units still pending in ORC.
    helpers: Rc<HashSet<String>>,
    lazy_has_main: bool,
    /// Instance symbols whose modules must be materialized before execution:
    /// code a spawned worker thread may enter. Workers cannot run the Rust
    /// materializer (it lives on the main thread), so their whole statically
    /// reachable set is compiled up front; everything else stays lazy.
    lazy_precompile: Vec<String>,
}

/// The LLVM code generator: holds the LLVM context, module, and builder plus the
/// per-program tables, and implements the backend-agnostic
/// `brass_engine::Codegen` trait to emit typed, fully unboxed code.
pub struct LlvmCodegen<'ctx, 'p> {
    ctx: &'ctx Context,
    orc_context: Option<&'ctx OrcContext>,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    abi: Abi<'ctx>,
    program: &'p Program,
    fns: FnCache<'ctx>,
    cur_fn: Option<FunctionValue<'ctx>>,
    /// Per-type recursive destructors (`__drop_*`), memoized by mangled type name.
    /// Emitting one before its body lets self-referential types recurse; the map is
    /// cleared per module. Lazy groups declare helpers owned by their batch.
    ///
    /// This map and the four below MUST key by [`helper_key`] (an injective
    /// type encoding), never a display rendering: two distinct types may render
    /// identically -- same-named types declared in different modules, or
    /// instantiations differing only in hidden `_` members -- and a shared key
    /// hands one type's glue to the other.
    destructors: fxhash::FxHashMap<String, FunctionValue<'ctx>>,
    /// Per-type recursive `to_string` renderers (`pp_fn_tostr_*`) for records and
    /// sums, memoized by mangled type name. Emitting one before its body lets a
    /// self-referential type recurse through a call; cleared per module like
    /// destructors.
    to_string_fns: fxhash::FxHashMap<String, FunctionValue<'ctx>>,
    /// Per-type structural equality helpers (`bool(*Header, *Header)`, see
    /// the `equality` submodule). They are registered before their bodies are
    /// emitted so nested or recursive fields call shared helpers instead of
    /// expanding code generation recursively; cleared per module like the
    /// other type glue.
    equality_fns: fxhash::FxHashMap<String, FunctionValue<'ctx>>,
    /// Per-type deep-copy functions (`fn(*Header) -> *Header`): a fresh, independent
    /// copy of an aggregate value (recursing into managed fields/elements), used to
    /// pass a non-reference argument by value. Memoized to terminate on recursive
    /// types and cleared per module.
    deep_copy_fns: fxhash::FxHashMap<String, FunctionValue<'ctx>>,
    /// Per-type cycle-collector trace functions: visit a value's
    /// managed children. Memoized like destructors, cleared per module.
    tracers: fxhash::FxHashMap<String, Option<FunctionValue<'ctx>>>,
    /// Missing-instance diagnostic functions keyed by their exact LLVM closure ABI.
    missing_closure_targets: fxhash::FxHashMap<String, FunctionValue<'ctx>>,
    /// Groups delegate helper emission to this batch-local generator. It has no
    /// delegate of its own, so recursive helpers use its ordinary local memos.
    helpers: Option<Rc<RefCell<LlvmCodegen<'ctx, 'p>>>>,
    /// Some means this module exports helpers; names from earlier batches must
    /// only be declared. None preserves private glue for whole-module codegen.
    previous_helpers: Option<Rc<HashSet<String>>>,
    /// Whether to emit region write barriers (set in `begin_program` when the
    /// program uses `with`), so a sequential program pays no barrier cost.
    region_barriers: bool,
    /// State for the MIR-driven `brass_engine::Codegen` path.
    mir: MirState<'ctx>,
}

impl<'ctx, 'p> LlvmCodegen<'ctx, 'p> {
    /// A code generator emitting into a fresh module of `ctx`. It is driven
    /// through the `brass_engine::Codegen` trait (for example by
    /// `brass_engine::Engine`) to compile and run a monomorphized program;
    /// the JIT's own run paths start from [`Self::new_orc_backend`].
    pub fn new_backend(ctx: &'ctx Context, program: &'p Program) -> Self {
        LlvmCodegen {
            ctx,
            orc_context: None,
            module: ctx.create_module("brass"),
            builder: ctx.create_builder(),
            abi: Abi::new(ctx),
            program,
            fns: FnCache::default(),
            cur_fn: None,
            destructors: fxhash::FxHashMap::default(),
            to_string_fns: fxhash::FxHashMap::default(),
            equality_fns: fxhash::FxHashMap::default(),
            deep_copy_fns: fxhash::FxHashMap::default(),
            tracers: fxhash::FxHashMap::default(),
            missing_closure_targets: fxhash::FxHashMap::default(),
            helpers: None,
            previous_helpers: None,
            region_barriers: false,
            mir: MirState::default(),
        }
    }

    /// Emit directly in the future ORC session's context. The context wrapper
    /// must outlive this backend; finalization shares its ownership with ORC.
    /// Use `new_backend` when the caller needs an independent LLVM context.
    pub fn new_orc_backend(context: &'ctx OrcContext, program: &'p Program) -> Self {
        let mut backend = Self::new_backend(context.context(), program);
        backend.orc_context = Some(context);
        backend
    }

    /// Declare a batch helper locally with exactly its definition's name and ABI.
    /// No FunctionValue from another module is used as a call operand.
    fn declare_helper(&self, helper: FunctionValue<'ctx>) -> FunctionValue<'ctx> {
        let name = helper.get_name().to_str().expect("helper name is UTF-8");
        self.module.get_function(name).unwrap_or_else(|| {
            self.module
                .add_function(name, helper.get_type(), Some(Linkage::External))
        })
    }

    /// Reserve a helper before emitting its body, allowing recursive references.
    /// The boolean says whether this module owns the definition or just imports it.
    fn helper_function(&self, name: &str, ty: FunctionType<'ctx>) -> (FunctionValue<'ctx>, bool) {
        let linkage = if self.previous_helpers.is_some() {
            Linkage::External
        } else {
            Linkage::Private
        };
        let function = self.module.add_function(name, ty, Some(linkage));
        let define = !self
            .previous_helpers
            .as_ref()
            .is_some_and(|names| names.contains(name));
        (function, define)
    }

    /// An `i64` constant.
    fn i64c(&self, v: i64) -> IntValue<'ctx> {
        self.abi.i64t().const_int(v as u64, true)
    }

    /// Zero-extend a possibly-narrow integer value (e.g. an `i1` bool or an `i32`)
    /// to `i64` so it can be passed to an `i64`-typed runtime parameter. A value
    /// already `i64` is returned unchanged.
    fn int_arg_i64(&self, v: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        let iv = v.into_int_value();
        if iv.get_type().get_bit_width() >= 64 {
            iv
        } else {
            self.builder
                .build_int_z_extend(iv, self.abi.i64t(), "i64arg")
                .unwrap()
        }
    }

    /// Sign-extend a possibly-narrow signed integer (e.g. an `int32` index literal)
    /// to `i64` for an `i64`-typed runtime parameter. A value already `i64` is
    /// returned unchanged.
    fn sext_to_i64(&self, v: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        let iv = v.into_int_value();
        if iv.get_type().get_bit_width() >= 64 {
            iv
        } else {
            self.builder
                .build_int_s_extend(iv, self.abi.i64t(), "sx64")
                .unwrap()
        }
    }

    /// A global string constant; returns its pointer and byte length.
    ///
    /// The constant holds every byte of `s` -- a string carries its length,
    /// so an embedded NUL (`"a\0b"`) is an ordinary byte, not a terminator
    /// -- followed by one NUL for the consumers that read a C string.
    fn global_str(&self, s: &str) -> (PointerValue<'ctx>, u64) {
        let bytes = self.ctx.const_string(s.as_bytes(), true);
        let global = self.module.add_global(bytes.get_type(), None, "str");
        global.set_initializer(&bytes);
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_address(inkwell::values::UnnamedAddress::Global);
        (global.as_pointer_value(), s.len() as u64)
    }

    /// Emit a runtime panic with a static message.
    fn gen_panic(&self, msg: &str) {
        let (ptr, len) = self.global_str(msg);
        let ty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into(), self.abi.i64t().into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_panic", ty);
        self.builder
            .build_call(f, &[ptr.into(), self.i64c(len as i64).into()], "")
            .unwrap();
    }

    /// Branch to a panic block emitting `msg` when `bad` is true, then continue
    /// in a fresh block. `pp_panic` does not return, so the panic block ends in
    /// `unreachable`. Used to insert runtime checks (division by zero, array
    /// bounds) ahead of an operation that is otherwise undefined.
    fn trap_if(&mut self, bad: IntValue<'ctx>, msg: &str) {
        let func = self.cur_fn.unwrap();
        let cont = self.ctx.append_basic_block(func, "ok");
        let trap = self.ctx.append_basic_block(func, "trap");
        self.builder
            .build_conditional_branch(bad, trap, cont)
            .unwrap();
        self.builder.position_at_end(trap);
        self.gen_panic(msg);
        self.builder.build_unreachable().unwrap();
        self.builder.position_at_end(cont);
    }

    /// Stop the program with `internal error: <msg>` when this point is
    /// reached at run time, then continue emitting into a fresh block that
    /// nothing branches to. Marks a combination of types and operations the
    /// front end never produces for a checked program: the program fails with
    /// a clear error at the offending operation instead of computing with a
    /// value of the wrong shape, and IR emission of the (dead) remainder goes on
    /// so an unreached path costs nothing.
    fn internal_error(&self, msg: &str) {
        let func = self.cur_fn.unwrap();
        self.gen_panic(&format!("internal error: {msg}"));
        self.builder.build_unreachable().unwrap();
        let after = self.ctx.append_basic_block(func, "after_internal_error");
        self.builder.position_at_end(after);
    }

    /// [`internal_error`] for an operation that produces a value: the result is
    /// a zero of `ty`'s representation, which keeps the IR well typed and is
    /// never observed (the trap runs first).
    fn internal_error_value(&self, msg: &str, ty: &Type) -> BasicValueEnum<'ctx> {
        self.internal_error(msg);
        self.zero_of(self.abi.typed_basic(ty))
    }

    /// The all-zero constant of an LLVM value representation (`0`, `0.0`, or a
    /// null pointer).
    fn zero_of(&self, llty: BasicTypeEnum<'ctx>) -> BasicValueEnum<'ctx> {
        match llty {
            BasicTypeEnum::IntType(t) => t.const_zero().into(),
            BasicTypeEnum::FloatType(t) => t.const_zero().into(),
            other => other.const_zero(),
        }
    }

    /// Trap before an array index `idx` that is out of `0..len`. The index is
    /// widened to i64 and compared unsigned, so a negative index (a huge unsigned
    /// value) is rejected as well. Mirrors the array length stored at offset 16.
    fn bounds_check(&mut self, arr: BasicValueEnum<'ctx>, idx: IntValue<'ctx>) {
        let i64t = self.abi.i64t();
        let idx64 = if idx.get_type().get_bit_width() < 64 {
            self.builder.build_int_z_extend(idx, i64t, "idx64").unwrap()
        } else {
            idx
        };
        let len = self.array_len(arr).into_int_value();
        let oob = self
            .builder
            .build_int_compare(inkwell::IntPredicate::UGE, idx64, len, "oob")
            .unwrap();
        self.trap_if(oob, brass_utils::builtin_errors::ARRAY_INDEX_OUT_OF_BOUNDS);
    }

    /// Allocate a typed slot in the current function's entry block.
    fn typed_alloca(&self, ty: BasicTypeEnum<'ctx>, name: &str) -> PointerValue<'ctx> {
        let f = self.cur_fn.unwrap();
        let entry = f.get_first_basic_block().unwrap();
        let tmp = self.ctx.create_builder();
        match entry.get_first_instruction() {
            Some(i) => tmp.position_before(&i),
            None => tmp.position_at_end(entry),
        }
        tmp.build_alloca(ty, name).unwrap()
    }

    /// Call a `void(ptr, i64)` runtime group-lock entry (`pp_lock_span` /
    /// `pp_unlock_span`) on a stack span holding `objs`. The span buffer is an
    /// entry-block alloca (not a positional one), so a group wrap inside a loop
    /// reuses one slot instead of growing the stack every iteration.
    fn cown_span_call(&mut self, entry: &str, objs: &[BasicValueEnum<'ctx>]) {
        let ptr_ty = self.abi.ptr();
        let arr_ty = ptr_ty.array_type(objs.len() as u32);
        let slot = self.typed_alloca(arr_ty.into(), "cown_span");
        let i32t = self.ctx.i32_type();
        for (i, o) in objs.iter().enumerate() {
            let gep = unsafe {
                self.builder
                    .build_in_bounds_gep(
                        arr_ty,
                        slot,
                        &[i32t.const_zero(), i32t.const_int(i as u64, false)],
                        "cown_slot",
                    )
                    .unwrap()
            };
            self.builder.build_store(gep, *o).unwrap();
        }
        let ty = self
            .ctx
            .void_type()
            .fn_type(&[ptr_ty.into(), self.abi.i64t().into()], false);
        let f = self.abi.runtime_fn(&self.module, entry, ty);
        let n = self.abi.i64t().const_int(objs.len() as u64, false);
        self.builder
            .build_call(f, &[slot.into(), n.into()], "")
            .unwrap();
    }

    /// The unit/void placeholder value (an `i1 0`); never observed.
    fn typed_unit(&self) -> BasicValueEnum<'ctx> {
        self.ctx.bool_type().const_zero().into()
    }

    fn typed_load_local(&self, id: LocalId) -> BasicValueEnum<'ctx> {
        match self.mir.locals.get(id.index()).and_then(|s| *s) {
            Some(slot) => self.builder.build_load(slot.ty, slot.ptr, "l").unwrap(),
            None => self.typed_unit(),
        }
    }

    /// Store `v` into a local's slot. A `void` local has no slot and its
    /// (unit) value is dropped; a value whose representation differs from the
    /// slot's stops the program with an internal error instead of writing a
    /// value of another width.
    fn typed_store_local(&self, id: LocalId, v: BasicValueEnum<'ctx>) {
        if let Some(slot) = self.mir.locals.get(id.index()).and_then(|s| *s) {
            if v.get_type() != slot.ty {
                return self.internal_error(&format!(
                    "a value of the wrong representation was stored into local {}",
                    id.index()
                ));
            }
            self.builder.build_store(slot.ptr, v).unwrap();
        }
    }

    /// Call a function and return its basic result value.
    fn call_basic(
        &self,
        f: FunctionValue<'ctx>,
        args: &[inkwell::values::BasicMetadataValueEnum<'ctx>],
    ) -> BasicValueEnum<'ctx> {
        self.builder
            .build_call(f, args, "cv")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }

    /// The `(int64 value, is_float flag, f64 value, integer signedness)` values a
    /// `*.from(x)` conversion passes to the runtime.
    fn conv_from_args(
        &mut self,
        arg: BasicValueEnum<'ctx>,
        arg_ty: &Type,
    ) -> (
        IntValue<'ctx>,
        IntValue<'ctx>,
        FloatValue<'ctx>,
        IntValue<'ctx>,
    ) {
        match arg_ty {
            Type::Int(kind) => {
                let xi = self
                    .coerce(arg, arg_ty, &Type::Int(IntKind::I64))
                    .into_int_value();
                (
                    xi,
                    self.i64c(0),
                    self.ctx.f64_type().const_float(0.0),
                    self.i64c(i64::from(kind.is_signed())),
                )
            }
            Type::Float(_) => {
                let xf = self
                    .coerce(arg, arg_ty, &Type::Float(FloatKind::F64))
                    .into_float_value();
                (self.i64c(0), self.i64c(1), xf, self.i64c(1))
            }
            _ => (
                self.i64c(0),
                self.i64c(0),
                self.ctx.f64_type().const_float(0.0),
                self.i64c(1),
            ),
        }
    }

    /// Call a runtime primitive `void name(ptr)` for its side effect.
    fn call_rt_void(&self, name: &str, arg: BasicValueEnum<'ctx>) {
        let ty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        let f = self.abi.runtime_fn(&self.module, name, ty);
        self.builder.build_call(f, &[arg.into()], "").unwrap();
    }

    /// Call a runtime function returning a pointer (a typed heap handle).
    fn call_rt_ptr(&self, name: &str, args: &[BasicValueEnum<'ctx>]) -> BasicValueEnum<'ctx> {
        let ptys: Vec<inkwell::types::BasicMetadataTypeEnum> =
            args.iter().map(|_| self.abi.ptr().into()).collect();
        let ty = self.abi.ptr().fn_type(&ptys, false);
        let f = self.abi.runtime_fn(&self.module, name, ty);
        let av: Vec<inkwell::values::BasicMetadataValueEnum> =
            args.iter().map(|a| (*a).into()).collect();
        self.builder
            .build_call(f, &av, "rtp")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }

    /// Call a runtime to-string converter (mixed scalar args) returning a string
    /// pointer; the parameter types are taken from the argument values.
    fn call_to_str(&self, name: &str, args: &[BasicValueEnum<'ctx>]) -> BasicValueEnum<'ctx> {
        let ptys: Vec<inkwell::types::BasicMetadataTypeEnum> =
            args.iter().map(|a| a.get_type().into()).collect();
        let ty = self.abi.ptr().fn_type(&ptys, false);
        let f = self.abi.runtime_fn(&self.module, name, ty);
        let av: Vec<inkwell::values::BasicMetadataValueEnum> =
            args.iter().map(|a| (*a).into()).collect();
        self.builder
            .build_call(f, &av, "tos")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }

    /// String binary operators: `+` concatenates, `==`/`!=` compare bytes.
    fn str_bin_op(
        &self,
        op: BinOp,
        a: BasicValueEnum<'ctx>,
        b: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        match op {
            BinOp::Add => self.call_rt_ptr("pp_str_concat", &[a, b]),
            BinOp::Eq | BinOp::Ne => {
                let ty = self
                    .ctx
                    .bool_type()
                    .fn_type(&[self.abi.ptr().into(), self.abi.ptr().into()], false);
                let f = self.abi.runtime_fn(&self.module, "pp_str_eq", ty);
                let eq = self
                    .builder
                    .build_call(f, &[a.into(), b.into()], "seq")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_int_value();
                if matches!(op, BinOp::Ne) {
                    self.builder.build_not(eq, "sne").unwrap().into()
                } else {
                    eq.into()
                }
            }
            _ => self.internal_error_value(&format!("`{op:?}` on two strings"), &Type::Str),
        }
    }
}

/// Whether `ty` is a signed integer type (arithmetic shift / signed div/cmp).
fn ty_is_signed(ty: &Type) -> bool {
    matches!(ty, Type::Int(k) if k.is_signed())
}

/// The LLVM integer comparison predicate for a comparison operator.
fn int_predicate(op: BinOp, signed: bool) -> IntPredicate {
    match (op, signed) {
        (BinOp::Eq, _) => IntPredicate::EQ,
        (BinOp::Ne, _) => IntPredicate::NE,
        (BinOp::Lt, true) => IntPredicate::SLT,
        (BinOp::Lt, false) => IntPredicate::ULT,
        (BinOp::Gt, true) => IntPredicate::SGT,
        (BinOp::Gt, false) => IntPredicate::UGT,
        (BinOp::Le, true) => IntPredicate::SLE,
        (BinOp::Le, false) => IntPredicate::ULE,
        (BinOp::Ge, true) => IntPredicate::SGE,
        (BinOp::Ge, false) => IntPredicate::UGE,
        _ => unreachable!("non-comparison op"),
    }
}

/// The LLVM float comparison predicate for a comparison operator.
fn float_predicate(op: BinOp) -> FloatPredicate {
    match op {
        BinOp::Eq => FloatPredicate::OEQ,
        // `!=` is *unordered* not-equal so `NaN != NaN` is true, matching IEEE 754
        // (and Rust/the interpreter); ordered ONE would make it false.
        BinOp::Ne => FloatPredicate::UNE,
        BinOp::Lt => FloatPredicate::OLT,
        BinOp::Gt => FloatPredicate::OGT,
        BinOp::Le => FloatPredicate::OLE,
        BinOp::Ge => FloatPredicate::OGE,
        _ => unreachable!("non-comparison op"),
    }
}

/// The runtime tag value for an integer kind (matches `rt::TAG_INT_*`), passed
/// to the typed conversion runtime functions.
fn int_runtime_tag(k: IntKind) -> i64 {
    match k {
        IntKind::I8 => 8,
        IntKind::I16 => 9,
        IntKind::I32 => 10,
        IntKind::I64 => 11,
        IntKind::U8 => 12,
        IntKind::U16 => 13,
        IntKind::U32 => 14,
        IntKind::U64 => 15,
    }
}

/// Whether an operator is a comparison (shared with the typed bin-op emission).
pub(crate) fn codegen_is_int_cmp(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge
    )
}

#[cfg(test)]
mod representation_tests {
    use super::*;

    #[test]
    fn same_representation_compares_element_and_signature_layouts() {
        use brass_hir::{FloatKind, IntKind};
        let i32t = Type::Int(IntKind::I32);
        let f64t = Type::Float(FloatKind::F64);
        let slice = |t: &Type| Type::Slice(Box::new(t.clone()));
        let fun = |p: &Type, r: &Type| Type::Fun(vec![p.clone()], Box::new(r.clone()));
        assert!(same_representation(&slice(&i32t), &slice(&i32t)));
        assert!(same_representation(
            &Type::Array(Box::new(i32t.clone()), 3),
            &slice(&i32t)
        ));
        assert!(!same_representation(&slice(&i32t), &slice(&f64t)));
        assert!(!same_representation(
            &Type::Tuple(vec![i32t.clone(), Type::Str]),
            &Type::Tuple(vec![f64t.clone(), Type::Str])
        ));
        assert!(!same_representation(&fun(&i32t, &i32t), &fun(&f64t, &i32t)));
        assert!(!same_representation(
            &Type::Nullable(Box::new(i32t.clone())),
            &Type::Nullable(Box::new(Type::Int(IntKind::I64)))
        ));
        assert!(same_representation(
            &Type::Nullable(Box::new(Type::Never)),
            &Type::Nullable(Box::new(Type::Str))
        ));
        assert!(!same_representation(&Type::Str, &i32t));
    }
}
