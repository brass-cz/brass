//! LLVM IR generation. Each Prepoly function/method/closure becomes an LLVM
//! function with the uniform ABI `Value(env, args, argc)`. Control flow is
//! native LLVM; values flow as the `Value` struct; most operations are calls
//! into the runtime. Captured locals are boxed in heap cells so
//! closures observe each other's writes.

use std::collections::HashMap;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::BasicTypeEnum;
use inkwell::values::BasicValueEnum;
use inkwell::values::{FloatValue, FunctionValue, GlobalValue, IntValue, PointerValue};
use inkwell::{FloatPredicate, IntPredicate, OptimizationLevel};

use prepoly_engine::{Codegen as EngineCodegen, MonoFunction, MonoProgram, closure_symbol};
use prepoly_hir::{FloatKind, IntKind, NominalType, Program, Type, TypeKind};
use prepoly_mir::{BlockId, ClosureId, LocalId};
use prepoly_parser::ast::*;

use crate::layout::Abi;
use crate::monomorph::*;

/// A typed stack slot for one MIR local on the `prepoly_engine::Codegen` path:
/// its alloca pointer and the concrete LLVM type to load/store. A `void` local
/// has no slot (its value is never observed).
#[derive(Clone, Copy)]
struct MirSlot<'ctx> {
    ptr: PointerValue<'ctx>,
    ty: BasicTypeEnum<'ctx>,
}

/// Whether a type is a reference-counted heap object (mirrors the engine's
/// `rc_managed`): a destructor releases such a contained field/element. Releasing a
/// closure field frees its block (its captures are released by their own owners).
/// Peel the front-end wrappers that do not change a value's runtime shape
/// (mutability, reference-ness, const-ness, and a narrowing nullable cell) to
/// reach the underlying type a deep copy dispatches on.
fn unwrap_copy_wrappers(ty: &Type) -> &Type {
    match ty {
        Type::Mut(inner) | Type::Ref(inner) | Type::ConstOf(inner) | Type::Nullable(inner) => {
            unwrap_copy_wrappers(inner)
        }
        _ => ty,
    }
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
fn is_traced(ty: &Type) -> bool {
    is_managed_heap(ty) || matches!(ty, Type::Nullable(_))
}

/// State used only by the typed MIR-driven backend path (the
/// `prepoly_engine::Codegen` implementation), kept apart from the AST-walking
/// `compile` state so the two coexist during the migration. Populated as
/// [`LlvmCodegen`] emits each monomorphized instance.
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
    /// The execution engine, created at finalize and reused to run code.
    engine: Option<inkwell::execution_engine::ExecutionEngine<'ctx>>,
    /// Modules compiled at runtime (deferred monomorphization). Kept alive here
    /// because the execution engine references them after `add_module`.
    runtime_modules: Vec<Module<'ctx>>,
}

/// The LLVM code generator: holds the LLVM context, module, and builder plus the
/// per-program tables, and implements the backend-agnostic
/// `prepoly_engine::Codegen` trait to emit typed, fully unboxed code.
pub struct LlvmCodegen<'ctx, 'p> {
    ctx: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    abi: Abi<'ctx>,
    program: &'p Program,
    fns: FnCache<'ctx>,
    cur_fn: Option<FunctionValue<'ctx>>,
    /// Per-type recursive destructors (`__drop_*`), memoized by mangled type name.
    /// Emitting one before its body lets self-referential types recurse; the map is
    /// cleared per module (a destructor can only be called within its own module).
    destructors: std::collections::HashMap<String, FunctionValue<'ctx>>,
    /// Per-type recursive `to_string` renderers (`pp_fn_tostr_*`) for records and
    /// sums, memoized by mangled type name. Emitting one before its body lets a
    /// self-referential type recurse through a call; cleared per module like
    /// destructors (the function is local to the module that defines it).
    to_string_fns: std::collections::HashMap<String, FunctionValue<'ctx>>,
    /// Per-type deep-copy functions (`fn(*Header) -> *Header`): a fresh, independent
    /// copy of an aggregate value (recursing into managed fields/elements), used to
    /// pass a non-reference argument by value. Memoized to terminate on recursive
    /// types and cleared per module.
    deep_copy_fns: std::collections::HashMap<String, FunctionValue<'ctx>>,
    /// Per-type cycle-collector trace functions: visit a value's
    /// managed children. Memoized like destructors, cleared per module.
    tracers: std::collections::HashMap<String, Option<FunctionValue<'ctx>>>,
    /// Whether to emit region write barriers (set in `begin_program` when the
    /// program uses `with`), so a sequential program pays no barrier cost.
    region_barriers: bool,
    /// State for the MIR-driven `prepoly_engine::Codegen` path.
    mir: MirState<'ctx>,
}

impl<'ctx, 'p> LlvmCodegen<'ctx, 'p> {
    /// Construct a code generator for the MIR-driven backend path. The resulting
    /// [`LlvmCodegen`] is handed to `prepoly_engine::Engine`, which drives it
    /// through the `Codegen` trait to compile and run a monomorphized program.
    pub fn new_backend(ctx: &'ctx Context, program: &'p Program) -> Self {
        LlvmCodegen {
            ctx,
            module: ctx.create_module("prepoly"),
            builder: ctx.create_builder(),
            abi: Abi::new(ctx),
            program,
            fns: FnCache::default(),
            cur_fn: None,
            destructors: std::collections::HashMap::new(),
            to_string_fns: std::collections::HashMap::new(),
            deep_copy_fns: std::collections::HashMap::new(),
            tracers: std::collections::HashMap::new(),
            region_barriers: false,
            mir: MirState::default(),
        }
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

    /// Mark every small defined function `alwaysinline`. "Small" is
    /// approximated by basic-block count: a handful of blocks is a leaf-ish helper
    /// (accessors, tiny arithmetic wrappers like `std/math`'s `pow`) that is cheaper
    /// to inline than to call. Functions keep their external definition (so direct
    /// and runtime-dispatched calls still resolve); only call sites are inlined.
    fn mark_small_functions_alwaysinline(&self) {
        const SMALL_BLOCKS: u32 = 4;
        let kind = inkwell::attributes::Attribute::get_named_enum_kind_id("alwaysinline");
        if kind == 0 {
            return;
        }
        let attr = self.ctx.create_enum_attribute(kind, 0);
        let mut f = self.module.get_first_function();
        while let Some(func) = f {
            let blocks = func.count_basic_blocks();
            // A declaration (no body) has 0 blocks; skip it and anything large.
            if blocks > 0 && blocks <= SMALL_BLOCKS {
                func.add_attribute(inkwell::attributes::AttributeLoc::Function, attr);
            }
            f = func.get_next_function();
        }
    }

    /// Emit `__pp_freeze_globals`: a `void()` function that loads each immutable
    /// heap global and deep-freezes it. `execute` calls it
    /// once after module init so the namespace is frozen before `main` runs. No-op
    /// (function still emitted, empty) when there are no immutable heap globals.
    fn emit_freeze_globals_fn(&mut self) {
        let fty = self.ctx.void_type().fn_type(&[], false);
        let func = self.module.add_function(FREEZE_GLOBALS_FN, fty, None);
        let entry = self.ctx.append_basic_block(func, "entry");
        self.builder.position_at_end(entry);
        let freeze_ty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        let freeze = self
            .abi
            .runtime_fn(&self.module, "pp_freeze_deep", freeze_ty);
        let names: Vec<String> = self.mir.frozen_globals.clone();
        for name in names {
            if let Some(g) = self.mir.globals.get(&name) {
                // The global slot holds the heap pointer; load it and freeze it.
                let ptr = self
                    .builder
                    .build_load(self.abi.ptr(), g.as_pointer_value(), "gv")
                    .unwrap();
                self.builder.build_call(freeze, &[ptr.into()], "").unwrap();
            }
        }
        self.builder.build_return(None).unwrap();
    }

    /// Run the always-inliner over the module so the `alwaysinline`
    /// marks above take effect before JIT codegen. Best-effort: optimization is not
    /// required for correctness, so a pass-setup failure is non-fatal.
    fn run_optimization_passes(&self) {
        use inkwell::passes::PassBuilderOptions;
        use inkwell::targets::{CodeModel, RelocMode, Target, TargetMachine};

        let triple = TargetMachine::get_default_triple();
        let Ok(target) = Target::from_triple(&triple) else {
            return;
        };
        let Some(machine) = target.create_target_machine(
            &triple,
            "generic",
            "",
            OptimizationLevel::Default,
            RelocMode::Default,
            CodeModel::Default,
        ) else {
            return;
        };
        let _ = self
            .module
            .run_passes("always-inline", &machine, PassBuilderOptions::create());
    }

    /// A global string constant; returns its pointer and byte length.
    fn global_str(&self, s: &str) -> (PointerValue<'ctx>, u64) {
        let g = self.builder.build_global_string_ptr(s, "str").unwrap();
        (g.as_pointer_value(), s.len() as u64)
    }

    /// Get or emit the per-type destructor `__drop_*` for an aggregate (record or
    /// array/slice): decrement its reference count and, at zero, release the heap
    /// contents it owns (a record's string/record fields recursively; an array's
    /// element buffer) then free the block. Emitted once per type into the current
    /// module and memoized before its body so a self-referential type can call
    /// itself. The decrement is non-atomic: these are `local`-owned (codegen never
    /// freezes them). Used by [`Codegen::release_obj`].
    /// Per-type cycle-collector trace function: `void trace(obj,
    /// visit)` calls `visit` on each managed child of `obj` (record/nullable/array/
    /// sum). `None` for a type with no traced children (a leaf -- never registered).
    /// Unlike the destructor it does not touch reference counts; the collector does.
    fn get_or_emit_tracer(&mut self, ty: &Type) -> Option<FunctionValue<'ctx>> {
        let key = mangle_fn(&format!("trace_{}", ty.display()));
        if let Some(t) = self.tracers.get(&key) {
            return *t;
        }

        // Fixed-offset pointer children (record fields, or a nullable cell's value).
        let mut child_offsets: Vec<u64> = Vec::new();
        // An array/slice element type, when its elements are traced.
        let mut array_elem: Option<Type> = None;
        // A sum's per-variant (tag, payload child offsets), selected by tag at run time.
        let mut sum_variants: Vec<(i32, Vec<u64>)> = Vec::new();
        match ty {
            Type::Record(n) => {
                if let Some(info) = self.program.type_by_id(n.id)
                    && let TypeKind::Record { fields, .. } = &info.kind
                {
                    let mut offset = 16u64;
                    for fdecl in fields {
                        if let Some(fdty) = n.substitution.get(&fdecl.name) {
                            let (size, align) = type_size_align(fdty);
                            offset = align_up(offset, align);
                            if is_traced(fdty) {
                                child_offsets.push(offset);
                            }
                            offset += size;
                        }
                    }
                }
            }
            Type::Nullable(inner) if is_traced(inner) => child_offsets.push(16),
            Type::Slice(e) | Type::Array(e, _) if is_traced(e) => {
                array_elem = Some(e.as_ref().clone())
            }
            Type::Tuple(elems) => {
                let mut offset = 16u64;
                for ety in elems {
                    let (size, align) = type_size_align(ety);
                    offset = align_up(offset, align);
                    if is_traced(ety) {
                        child_offsets.push(offset);
                    }
                    offset += size;
                }
            }
            Type::Sum(n) => {
                let names: Vec<String> = match self.program.type_by_id(n.id).map(|i| &i.kind) {
                    Some(TypeKind::Sum { variants }) => {
                        variants.iter().map(|v| v.name.clone()).collect()
                    }
                    _ => Vec::new(),
                };
                for name in names {
                    if let Some((tag, fields)) = self.variant_layout(n, &name) {
                        let offs: Vec<u64> = fields
                            .into_iter()
                            .filter(|(_, fty, _)| is_traced(fty))
                            .map(|(_, _, off)| off)
                            .collect();
                        if !offs.is_empty() {
                            sum_variants.push((tag, offs));
                        }
                    }
                }
            }
            _ => {}
        }
        if child_offsets.is_empty() && array_elem.is_none() && sum_variants.is_empty() {
            self.tracers.insert(key, None);
            return None;
        }

        let fty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into(), self.abi.ptr().into()], false);
        let f = self.module.add_function(&key, fty, None);
        self.tracers.insert(key, Some(f));

        let saved = self.builder.get_insert_block();
        let entry = self.ctx.append_basic_block(f, "entry");
        let body = self.ctx.append_basic_block(f, "body");
        let done = self.ctx.append_basic_block(f, "done");
        self.builder.position_at_end(entry);
        let obj = f.get_nth_param(0).unwrap().into_pointer_value();
        let visit = f.get_nth_param(1).unwrap().into_pointer_value();
        let visit_ty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        let ptrt = self.abi.ptr();
        let isnull = self.builder.build_is_null(obj, "isnull").unwrap();
        self.builder
            .build_conditional_branch(isnull, done, body)
            .unwrap();
        self.builder.position_at_end(body);

        // Each managed child is a pointer; load it and hand it to the visitor.
        for off in &child_offsets {
            let c = self
                .builder
                .build_load(ptrt, self.field_ptr(obj, *off), "child")
                .unwrap();
            self.builder
                .build_indirect_call(visit_ty, visit, &[c.into()], "v")
                .unwrap();
        }
        if let Some(elem) = array_elem {
            let i64t = self.abi.i64t();
            let elem_llty = self.abi.typed_basic(&elem);
            let len = self
                .builder
                .build_load(i64t, self.field_ptr(obj, 16), "len")
                .unwrap()
                .into_int_value();
            let idx = self.builder.build_alloca(i64t, "i").unwrap();
            self.builder.build_store(idx, i64t.const_zero()).unwrap();
            let lh = self.ctx.append_basic_block(f, "tloop");
            let lb = self.ctx.append_basic_block(f, "telem");
            self.builder.build_unconditional_branch(lh).unwrap();
            self.builder.position_at_end(lh);
            let i = self
                .builder
                .build_load(i64t, idx, "i")
                .unwrap()
                .into_int_value();
            let more = self
                .builder
                .build_int_compare(inkwell::IntPredicate::ULT, i, len, "more")
                .unwrap();
            self.builder
                .build_conditional_branch(more, lb, done)
                .unwrap();
            self.builder.position_at_end(lb);
            let ep = self.elem_ptr(obj, elem_llty, i);
            let c = self.builder.build_load(elem_llty, ep, "el").unwrap();
            self.builder
                .build_indirect_call(visit_ty, visit, &[c.into()], "v")
                .unwrap();
            let inc = self
                .builder
                .build_int_add(i, i64t.const_int(1, false), "inc")
                .unwrap();
            self.builder.build_store(idx, inc).unwrap();
            self.builder.build_unconditional_branch(lh).unwrap();
        } else if !sum_variants.is_empty() {
            let i32t = self.ctx.i32_type();
            let tag = self
                .builder
                .build_load(i32t, self.field_ptr(obj, 16), "tag")
                .unwrap()
                .into_int_value();
            let cases: Vec<_> = sum_variants
                .iter()
                .map(|(t, offs)| {
                    let bb = self.ctx.append_basic_block(f, "var");
                    (i32t.const_int(*t as u64, false), bb, offs.clone())
                })
                .collect();
            let switch_cases: Vec<_> = cases.iter().map(|(v, bb, _)| (*v, *bb)).collect();
            self.builder.build_switch(tag, done, &switch_cases).unwrap();
            for (_, bb, offs) in &cases {
                self.builder.position_at_end(*bb);
                for off in offs {
                    let c = self
                        .builder
                        .build_load(ptrt, self.field_ptr(obj, *off), "pchild")
                        .unwrap();
                    self.builder
                        .build_indirect_call(visit_ty, visit, &[c.into()], "v")
                        .unwrap();
                }
                self.builder.build_unconditional_branch(done).unwrap();
            }
        } else {
            self.builder.build_unconditional_branch(done).unwrap();
        }
        self.builder.position_at_end(done);
        self.builder.build_return(None).unwrap();
        if let Some(s) = saved {
            self.builder.position_at_end(s);
        }
        Some(f)
    }

    /// Register a freshly constructed `obj` with the cycle collector when `ty` is
    /// cycle-capable (has a tracer), so a reference cycle through it can later be
    /// reclaimed. A no-op for leaf types (no registration cost).
    fn register_for_gc(&mut self, obj: BasicValueEnum<'ctx>, ty: &Type) {
        let Some(tracer) = self.get_or_emit_tracer(ty) else {
            return;
        };
        let i64t = self.abi.i64t();
        let tracefn = self
            .builder
            .build_ptr_to_int(tracer.as_global_value().as_pointer_value(), i64t, "tracefn")
            .unwrap();
        let reg_ty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into(), i64t.into()], false);
        let reg = self.abi.runtime_fn(&self.module, "pp_gc_register", reg_ty);
        self.builder
            .build_call(reg, &[obj.into(), tracefn.into()], "")
            .unwrap();
    }

    fn get_or_emit_destructor(&mut self, ty: &Type) -> FunctionValue<'ctx> {
        let key = mangle_fn(&format!("drop_{}", ty.display()));
        if let Some(f) = self.destructors.get(&key) {
            return *f;
        }
        let fty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        let f = self.module.add_function(&key, fty, None);
        self.destructors.insert(key, f);

        // Collect each heap field's (type, byte offset, llvm type) before emitting,
        // so the program/abi borrows end before the recursive release calls. Field
        // offsets mirror `record_layout`.
        let mut heap_fields: Vec<(Type, u64, BasicTypeEnum<'ctx>)> = Vec::new();
        if let Type::Record(n) = ty
            && let Some(info) = self.program.type_by_id(n.id)
            && let TypeKind::Record { fields, .. } = &info.kind
        {
            let mut offset = 16u64;
            for fdecl in fields {
                if let Some(fdty) = n.substitution.get(&fdecl.name) {
                    let (size, align) = type_size_align(fdty);
                    offset = align_up(offset, align);
                    // Release managed fields and nullable cells (the cell is a
                    // heap object; its destructor frees it and any managed
                    // value it holds).
                    if is_traced(fdty) {
                        heap_fields.push((fdty.clone(), offset, self.abi.typed_basic(fdty)));
                    }
                    offset += size;
                }
            }
        }

        // A nullable cell `{ header16 | value@16 }`: release its value (when that
        // value is itself a heap reference) before the cell is freed.
        if let Type::Nullable(inner) = ty
            && is_traced(inner)
        {
            heap_fields.push((inner.as_ref().clone(), 16, self.abi.typed_basic(inner)));
        }

        // A sum's destructor releases the active variant's heap fields (selected by
        // the runtime tag). Collect each variant's (tag, [(field type, llvm type,
        // offset)]) for the fields that are managed.
        type VariantDrop<'c> = (i32, Vec<(Type, BasicTypeEnum<'c>, u64)>);
        let mut sum_variants: Vec<VariantDrop<'ctx>> = Vec::new();
        if let Type::Sum(n) = ty {
            let names: Vec<String> = match self.program.type_by_id(n.id).map(|i| &i.kind) {
                Some(TypeKind::Sum { variants }) => {
                    variants.iter().map(|v| v.name.clone()).collect()
                }
                _ => Vec::new(),
            };
            for name in names {
                if let Some((tag, fields)) = self.variant_layout(n, &name) {
                    let heap: Vec<(Type, BasicTypeEnum<'ctx>, u64)> = fields
                        .into_iter()
                        .filter(|(_, fty, _)| is_managed_heap(fty))
                        .map(|(_, fty, off)| {
                            let ll = self.abi.typed_basic(&fty);
                            (fty, ll, off)
                        })
                        .collect();
                    if !heap.is_empty() {
                        sum_variants.push((tag, heap));
                    }
                }
            }
        }

        let saved = self.builder.get_insert_block();
        let entry = self.ctx.append_basic_block(f, "entry");
        let live = self.ctx.append_basic_block(f, "live");
        let drop_bb = self.ctx.append_basic_block(f, "drop");
        let done_bb = self.ctx.append_basic_block(f, "done");
        self.builder.position_at_end(entry);
        let obj = f.get_nth_param(0).unwrap().into_pointer_value();
        // A managed local may be null (unassigned on this path); releasing null is
        // a no-op, matching `pp_release`.
        let is_null = self.builder.build_is_null(obj, "isnull").unwrap();
        self.builder
            .build_conditional_branch(is_null, done_bb, live)
            .unwrap();
        self.builder.position_at_end(live);
        let i64t = self.abi.i64t();
        let rc1 = self.atomic_rc_dec(obj);
        let dead = self
            .builder
            .build_int_compare(inkwell::IntPredicate::SLE, rc1, i64t.const_zero(), "dead")
            .unwrap();
        self.builder
            .build_conditional_branch(dead, drop_bb, done_bb)
            .unwrap();

        self.builder.position_at_end(drop_bb);
        for (fdty, offset, llty) in heap_fields {
            let fp = self.field_ptr(obj, offset);
            let fv = self.builder.build_load(llty, fp, "fld").unwrap();
            self.emit_release(fv, &fdty);
        }
        let free_ty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        let free = self.abi.runtime_fn(&self.module, "pp_obj_free", free_ty);
        // An array/slice owns a separately-allocated element buffer (ptr at offset
        // 32). Release each heap element (loop over `len`), then free the buffer,
        // then the header.
        let array_elem = match ty {
            Type::Slice(e) => Some(e.as_ref().clone()),
            Type::Array(e, _) => Some(e.as_ref().clone()),
            _ => None,
        };
        if let Some(elem) = array_elem {
            let data = self
                .builder
                .build_load(self.abi.ptr(), self.field_ptr(obj, 32), "data")
                .unwrap()
                .into_pointer_value();
            if is_managed_heap(&elem) {
                let len = self
                    .builder
                    .build_load(i64t, self.field_ptr(obj, 16), "len")
                    .unwrap()
                    .into_int_value();
                let elem_llty = self.abi.typed_basic(&elem);
                let idx = self.builder.build_alloca(i64t, "i").unwrap();
                self.builder.build_store(idx, i64t.const_zero()).unwrap();
                let lh = self.ctx.append_basic_block(f, "drop_loop");
                let lb = self.ctx.append_basic_block(f, "drop_elem");
                let lx = self.ctx.append_basic_block(f, "drop_buf");
                self.builder.build_unconditional_branch(lh).unwrap();
                self.builder.position_at_end(lh);
                let i = self
                    .builder
                    .build_load(i64t, idx, "i")
                    .unwrap()
                    .into_int_value();
                let more = self
                    .builder
                    .build_int_compare(inkwell::IntPredicate::ULT, i, len, "more")
                    .unwrap();
                self.builder.build_conditional_branch(more, lb, lx).unwrap();
                self.builder.position_at_end(lb);
                let ep = unsafe {
                    self.builder
                        .build_in_bounds_gep(elem_llty, data, &[i], "ep")
                        .unwrap()
                };
                let e = self.builder.build_load(elem_llty, ep, "e").unwrap();
                self.emit_release(e, &elem);
                let inc = self
                    .builder
                    .build_int_add(i, i64t.const_int(1, false), "inc")
                    .unwrap();
                self.builder.build_store(idx, inc).unwrap();
                self.builder.build_unconditional_branch(lh).unwrap();
                self.builder.position_at_end(lx);
            }
            self.builder.build_call(free, &[data.into()], "").unwrap();
        }
        // A sum: release the active variant's heap fields, selected by the runtime
        // tag, before freeing the block. Variants with no managed fields fall to the
        // switch's default (straight to free).
        if !sum_variants.is_empty() {
            let i32t = self.ctx.i32_type();
            let tag = self
                .builder
                .build_load(i32t, self.field_ptr(obj, 16), "tag")
                .unwrap()
                .into_int_value();
            let after = self.ctx.append_basic_block(f, "sum_done");
            let mut cases: Vec<(IntValue<'ctx>, inkwell::basic_block::BasicBlock<'ctx>)> =
                Vec::new();
            let mut bodies: Vec<(
                inkwell::basic_block::BasicBlock<'ctx>,
                Vec<SumFieldLayout<'ctx>>,
            )> = Vec::new();
            for (tagv, fields) in sum_variants {
                let vb = self.ctx.append_basic_block(f, "variant");
                cases.push((i32t.const_int(tagv as u64, true), vb));
                bodies.push((vb, fields));
            }
            self.builder.build_switch(tag, after, &cases).unwrap();
            for (vb, fields) in bodies {
                self.builder.position_at_end(vb);
                for (fty, llty, offset) in fields {
                    let fp = self.field_ptr(obj, offset);
                    let fv = self.builder.build_load(llty, fp, "vf").unwrap();
                    self.emit_release(fv, &fty);
                }
                self.builder.build_unconditional_branch(after).unwrap();
            }
            self.builder.position_at_end(after);
        }
        self.builder.build_call(free, &[obj.into()], "").unwrap();
        self.builder.build_unconditional_branch(done_bb).unwrap();

        self.builder.position_at_end(done_bb);
        self.builder.build_return(None).unwrap();

        if let Some(b) = saved {
            self.builder.position_at_end(b);
        }
        f
    }

    /// Emit (memoized by capture signature) a closure destructor `__clodrop_*`:
    /// null-guard, decrement the refcount, and at zero release each managed capture
    /// before freeing the environment block. Stored at offset 24 of the closure so
    /// it can be invoked knowing only the `Fun` type (which hides capture types).
    fn emit_closure_dtor(&mut self, capture_types: &[Type]) -> FunctionValue<'ctx> {
        let (offsets, _) = closure_layout(capture_types);
        let key = mangle_fn(&format!(
            "clodrop_{}",
            capture_types
                .iter()
                .map(|t| t.display())
                .collect::<Vec<_>>()
                .join(",")
        ));
        if let Some(f) = self.destructors.get(&key) {
            return *f;
        }
        let fty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        let f = self.module.add_function(&key, fty, None);
        self.destructors.insert(key, f);

        // Collect managed captures (type, llvm type, offset) before emitting.
        let managed: Vec<(Type, BasicTypeEnum<'ctx>, u64)> = capture_types
            .iter()
            .zip(offsets)
            .filter(|(t, _)| is_managed_heap(t))
            .map(|(t, off)| (t.clone(), self.abi.typed_basic(t), off))
            .collect();

        let saved = self.builder.get_insert_block();
        let entry = self.ctx.append_basic_block(f, "entry");
        let live = self.ctx.append_basic_block(f, "live");
        let drop_bb = self.ctx.append_basic_block(f, "drop");
        let done_bb = self.ctx.append_basic_block(f, "done");
        self.builder.position_at_end(entry);
        let obj = f.get_nth_param(0).unwrap().into_pointer_value();
        let is_null = self.builder.build_is_null(obj, "isnull").unwrap();
        self.builder
            .build_conditional_branch(is_null, done_bb, live)
            .unwrap();
        self.builder.position_at_end(live);
        let i64t = self.abi.i64t();
        let rc1 = self.atomic_rc_dec(obj);
        let dead = self
            .builder
            .build_int_compare(inkwell::IntPredicate::SLE, rc1, i64t.const_zero(), "dead")
            .unwrap();
        self.builder
            .build_conditional_branch(dead, drop_bb, done_bb)
            .unwrap();
        self.builder.position_at_end(drop_bb);
        for (cty, llty, off) in managed {
            let cp = self.field_ptr(obj, off);
            let cv = self.builder.build_load(llty, cp, "cap").unwrap();
            self.emit_release(cv, &cty);
        }
        let free_ty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        let free = self.abi.runtime_fn(&self.module, "pp_obj_free", free_ty);
        self.builder.build_call(free, &[obj.into()], "").unwrap();
        self.builder.build_unconditional_branch(done_bb).unwrap();
        self.builder.position_at_end(done_bb);
        self.builder.build_return(None).unwrap();
        if let Some(b) = saved {
            self.builder.position_at_end(b);
        }
        f
    }

    /// Atomically decrement the reference count at `obj` (offset 0) and return the
    /// new count. The decrement is always atomic because an object shared across
    /// `spawn` threads is released from more than one thread, so a plain
    /// load/sub/store would lose a decrement (a leak) or both observe the object
    /// dead (a double free). A thread-exclusive object is only ever decremented on
    /// its own thread, where the atomic op is still correct -- a small end-of-life
    /// cost; its hot retain/release path stays non-atomic via `rc_atomic`.
    fn atomic_rc_dec(&self, obj: PointerValue<'ctx>) -> IntValue<'ctx> {
        let i64t = self.abi.i64t();
        let old = self
            .builder
            .build_atomicrmw(
                inkwell::AtomicRMWBinOp::Sub,
                obj,
                i64t.const_int(1, false),
                inkwell::AtomicOrdering::SequentiallyConsistent,
            )
            .unwrap();
        self.builder
            .build_int_sub(old, i64t.const_int(1, false), "rc1")
            .unwrap()
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
    /// `unreachable`. Used to insert runtime safety checks (division by zero,
    /// array bounds) ahead of an operation that is otherwise undefined.
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
        self.trap_if(oob, "array index out of bounds");
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

    fn typed_store_local(&self, id: LocalId, v: BasicValueEnum<'ctx>) {
        if let Some(slot) = self.mir.locals.get(id.index()).and_then(|s| *s) {
            self.builder.build_store(slot.ptr, v).unwrap();
        }
    }

    /// The JIT machine address of a compiled instance by its instance symbol
    /// (after [`EngineCodegen::finalize`]), for embedding and tests that call a
    /// non-entry instance directly.
    pub fn address_of(&self, instance_symbol: &str) -> Option<usize> {
        self.mir
            .engine
            .as_ref()?
            .get_function_address(&mangle_fn(instance_symbol))
            .ok()
    }

    /// Run a compiled zero-argument instance returning `i32` (for tests/embedding
    /// after [`EngineCodegen::finalize`]). Sibling helpers exist for other return
    /// types.
    pub fn run_entry_i32(&self, name: &str) -> Option<i32> {
        let addr = self
            .mir
            .engine
            .as_ref()?
            .get_function_address(&mangle_fn(name))
            .ok()?;
        let f: unsafe extern "C" fn() -> i32 = unsafe { std::mem::transmute(addr) };
        Some(unsafe { f() })
    }

    pub fn run_entry_i64(&self, name: &str) -> Option<i64> {
        let addr = self
            .mir
            .engine
            .as_ref()?
            .get_function_address(&mangle_fn(name))
            .ok()?;
        let f: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(addr) };
        Some(unsafe { f() })
    }

    pub fn run_entry_f64(&self, name: &str) -> Option<f64> {
        let addr = self
            .mir
            .engine
            .as_ref()?
            .get_function_address(&mangle_fn(name))
            .ok()?;
        let f: unsafe extern "C" fn() -> f64 = unsafe { std::mem::transmute(addr) };
        Some(unsafe { f() })
    }

    /// The printed LLVM type of a compiled instance's function (e.g.
    /// `"i32 (i32)"`), for verifying the typed/unboxed signature in tests.
    pub fn instance_fn_type_string(&self, name: &str) -> Option<String> {
        let f = self.module.get_function(&mangle_fn(name))?;
        Some(f.get_type().print_to_string().to_string())
    }
}

/// Whether an integer kind is signed (arithmetic shift / signed div/cmp).
fn ty_is_signed(ty: &Type) -> bool {
    matches!(ty, Type::Int(k) if int_signed(*k))
}

/// Whether an integer kind is signed.
fn int_signed(k: IntKind) -> bool {
    matches!(k, IntKind::I8 | IntKind::I16 | IntKind::I32 | IntKind::I64)
}

/// The generated function that auto-freezes immutable heap globals after module
/// init; called by `execute` between init and `main`.
const FREEZE_GLOBALS_FN: &str = "__pp_freeze_globals";

/// The module globals that are immutable (never reassigned outside their
/// initializer) and heap-pointer-typed -- the ones auto-frozen after init. A global written by any non-initializer instance is
/// mutable and left thread-local (the auto-cown candidates).
fn immutable_heap_globals(program: &MonoProgram) -> Vec<String> {
    use std::collections::HashSet;
    let inits: HashSet<&str> = program.init_symbols.iter().map(|s| s.as_str()).collect();
    let mut mutated: HashSet<&str> = HashSet::new();
    for f in &program.functions {
        if inits.contains(f.symbol.as_str()) {
            continue;
        }
        for block in &f.body.blocks {
            for stmt in &block.stmts {
                if let prepoly_mir::MirStmt::SetGlobal(name, _) = stmt {
                    mutated.insert(name.as_str());
                }
            }
        }
    }
    program
        .globals
        .iter()
        .filter(|(name, ty)| is_heap_pointer_type(ty) && !mutated.contains(name.as_str()))
        .map(|(name, _)| name.clone())
        .collect()
}

/// Whether a global of this type is stored as a single heap pointer (so its slot
/// holds a `*Header` the freeze can read). Excludes inline fixed arrays (`T[n]`)
/// and the closure struct, whose global slots are not a lone pointer.
fn is_heap_pointer_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Str | Type::Record(..) | Type::Sum(..) | Type::Slice(..) | Type::Nullable(..)
    )
}

/// The module-level global symbol for a program global of the given name.
fn mangle_global(n: &str) -> String {
    format!(
        "pp_g_{}",
        n.chars()
            .map(|c| if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            })
            .collect::<String>()
    )
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
        BinOp::Ne => FloatPredicate::ONE,
        BinOp::Lt => FloatPredicate::OLT,
        BinOp::Gt => FloatPredicate::OGT,
        BinOp::Le => FloatPredicate::OLE,
        BinOp::Ge => FloatPredicate::OGE,
        _ => unreachable!("non-comparison op"),
    }
}

/// Size and alignment (bytes) of a typed value in a record layout. Heap
/// references (records) are pointer-sized.
fn type_size_align(ty: &Type) -> (u64, u64) {
    match ty {
        Type::Bool => (1, 1),
        Type::Int(IntKind::I8 | IntKind::U8) => (1, 1),
        Type::Int(IntKind::I16 | IntKind::U16) => (2, 2),
        Type::Int(IntKind::I32 | IntKind::U32) => (4, 4),
        Type::Int(IntKind::I64 | IntKind::U64) => (8, 8),
        Type::Float(FloatKind::F32) => (4, 4),
        Type::Float(FloatKind::F64) => (8, 8),
        _ => (8, 8),
    }
}

fn align_up(offset: u64, align: u64) -> u64 {
    (offset + align - 1) & !(align - 1)
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

/// Bit width of an integer kind.
fn int_bits_of(k: IntKind) -> u32 {
    match k {
        IntKind::I8 | IntKind::U8 => 8,
        IntKind::I16 | IntKind::U16 => 16,
        IntKind::I32 | IntKind::U32 => 32,
        IntKind::I64 | IntKind::U64 => 64,
    }
}

/// The byte offsets and total size of a closure environment: a function pointer at
/// offset 16, a capture-releasing destructor pointer at offset 24, then the
/// captured values packed (and aligned) from offset 32. The destructor slot is at
/// a fixed offset so a closure can be reclaimed knowing only its `Fun` type (which
/// hides the capture types). The same layout is used when building a closure and
/// when a closure instance reads its captures.
fn closure_layout(capture_types: &[Type]) -> (Vec<u64>, u64) {
    let mut offset = 32u64;
    let mut offsets = Vec::with_capacity(capture_types.len());
    for t in capture_types {
        let (size, align) = type_size_align(t);
        offset = align_up(offset, align);
        offsets.push(offset);
        offset += size;
    }
    (offsets, align_up(offset.max(32), 8))
}

/// The element type of an array/slice type, or `void` if not a sequence.
fn elem_of(ty: &Type) -> Type {
    match ty {
        Type::Slice(e) | Type::Array(e, _) => (**e).clone(),
        _ => Type::Void,
    }
}

/// One record field's placement: its name, LLVM type, and byte offset.
type RecordFieldLayout<'ctx> = (String, BasicTypeEnum<'ctx>, u64);
/// One sum-variant field's placement: its name, type, and byte offset.
type VariantFieldLayout = (String, Type, u64);
/// A lowered sum-variant field during code generation: source type, LLVM type,
/// and byte offset.
type SumFieldLayout<'ctx> = (Type, BasicTypeEnum<'ctx>, u64);

impl<'ctx, 'p> LlvmCodegen<'ctx, 'p> {
    /// The byte layout of a record instance: `(field name, LLVM type, byte
    /// offset)` for each declared field (laid out in order after the 16-byte
    /// header, naturally aligned) plus the total object size.
    /// A tuple's `(llvm element type, byte offset)` layout and total object size:
    /// the 16-byte header followed by each element at its naturally-aligned offset,
    /// positionally (mirrors a record's field layout but keyed by position).
    fn tuple_layout(&self, elem_types: &[Type]) -> (Vec<(BasicTypeEnum<'ctx>, u64)>, u64) {
        let mut offset = 16u64;
        let mut out = Vec::with_capacity(elem_types.len());
        for ety in elem_types {
            let (size, align) = type_size_align(ety);
            offset = align_up(offset, align);
            out.push((self.abi.typed_basic(ety), offset));
            offset += size;
        }
        (out, align_up(offset.max(16), 8))
    }

    fn record_layout(&self, record_ty: &Type) -> Option<(Vec<RecordFieldLayout<'ctx>>, u64)> {
        let Type::Record(n) = record_ty else {
            return None;
        };
        // Field names, types, and offsets come from `record_fields`. The object
        // size is the end of the last field, aligned.
        let mut end = 16u64; // header size
        let out: Vec<RecordFieldLayout<'ctx>> = self
            .record_fields(n)?
            .into_iter()
            .map(|(name, fty, offset)| {
                let (size, _) = type_size_align(&fty);
                end = offset + size;
                (name, self.abi.typed_basic(&fty), offset)
            })
            .collect();
        Some((out, align_up(end.max(16), 8)))
    }

    /// A record's `(field name, concrete type, byte offset)` list, or `None` for a
    /// non-record type. For a constructed value the substitution is authoritative:
    /// fields are taken in declaration order with their substituted types (correct
    /// even when two modules share a type name), and a declared field absent from
    /// the substitution makes the whole layout unavailable. For a bare nominal
    /// reference (empty substitution -- a sum variant binding or a nested declared
    /// field type) the HIR declaration's field names and declared types are used,
    /// so the nominal still lays out and renders.
    fn record_fields(&self, n: &NominalType) -> Option<Vec<(String, Type, u64)>> {
        let pairs: Vec<(String, Type)> = if n.substitution.is_empty() {
            let info = self.program.type_by_id(n.id)?;
            let TypeKind::Record { fields, .. } = &info.kind else {
                return None;
            };
            fields
                .iter()
                .filter_map(|f| f.resolved_ty.clone().map(|t| (f.name.clone(), t)))
                .collect()
        } else {
            // Declaration order (a structural record built at the deserialize
            // boundary has no declaration; use the substitution's field-name order).
            let names: Vec<String> = match self.program.type_by_id(n.id) {
                Some(info) => match &info.kind {
                    TypeKind::Record { fields, .. } => {
                        fields.iter().map(|f| f.name.clone()).collect()
                    }
                    _ => return None,
                },
                None => n
                    .substitution
                    .iter()
                    .map(|(name, _)| name.to_string())
                    .collect(),
            };
            names
                .into_iter()
                .map(|name| n.substitution.get(&name).cloned().map(|t| (name, t)))
                .collect::<Option<Vec<_>>>()?
        };
        let mut offset = 16u64; // header size
        let mut out = Vec::with_capacity(pairs.len());
        for (name, ty) in pairs {
            let (size, align) = type_size_align(&ty);
            offset = align_up(offset, align);
            out.push((name, ty, offset));
            offset += size;
        }
        Some(out)
    }

    /// A pointer to byte `offset` within a heap object.
    fn field_ptr(&self, base: PointerValue<'ctx>, offset: u64) -> PointerValue<'ctx> {
        unsafe {
            self.builder
                .build_in_bounds_gep(self.ctx.i8_type(), base, &[self.i64c(offset as i64)], "fp")
                .unwrap()
        }
    }

    /// A pointer to element `idx` of an array (data starts at byte offset 24,
    /// elements packed by their LLVM type's stride).
    /// A pointer to element `idx` of a growable array: the element buffer is a
    /// separate allocation held in the data slot at byte offset 32.
    fn elem_ptr(
        &self,
        base: PointerValue<'ctx>,
        elem_llty: BasicTypeEnum<'ctx>,
        idx: IntValue<'ctx>,
    ) -> PointerValue<'ctx> {
        let data = self
            .builder
            .build_load(self.abi.ptr(), self.field_ptr(base, 32), "data")
            .unwrap()
            .into_pointer_value();
        unsafe {
            self.builder
                .build_in_bounds_gep(elem_llty, data, &[idx], "ep")
                .unwrap()
        }
    }

    /// Wrap a value into a nullable's heap cell `{ header16 | value@16 }`,
    /// returning the (non-null) pointer.
    fn nullable_wrap(&mut self, v: BasicValueEnum<'ctx>, inner: &Type) -> BasicValueEnum<'ctx> {
        let (size, _) = type_size_align(inner);
        let cell = align_up(16 + size, 8);
        let alloc_ty = self.abi.ptr().fn_type(&[self.abi.i64t().into()], false);
        let alloc = self
            .abi
            .runtime_fn(&self.module, "pp_typed_alloc", alloc_ty);
        let base = self
            .builder
            .build_call(alloc, &[self.i64c(cell as i64).into()], "opt")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value();
        let p = self.field_ptr(base, 16);
        self.builder.build_store(p, v).unwrap();
        // The cell now holds a reference to its value; retain it (the cell's
        // destructor releases it) so the value lives as long as the cell. This also
        // makes a `next: Node?` self-cycle a real cycle (the node's count stays above
        // zero), which the cycle collector -- not reference counting -- reclaims.
        if is_traced(inner) {
            self.retain(v);
        }
        // A nullable cell wrapping a heap reference can be a cycle link (e.g. a
        // `next: Node?` field), so register it with the cycle collector.
        self.register_for_gc(base.into(), &Type::Nullable(Box::new(inner.clone())));
        base.into()
    }

    /// Read the value out of a non-null nullable cell (narrowing).
    fn nullable_unwrap(&self, v: BasicValueEnum<'ctx>, to: &Type) -> BasicValueEnum<'ctx> {
        let llty = self.abi.typed_basic(to);
        let p = self.field_ptr(v.into_pointer_value(), 16);
        self.builder.build_load(llty, p, "nv").unwrap()
    }

    /// The concrete type of a sum variant's field: a `Result`-style generic sum
    /// carries its payloads in the nominal substitution (keyed `Variant.field`),
    /// overriding the HIR's (possibly generic) declared type.
    fn variant_field_type(
        &self,
        n: &NominalType,
        variant: &str,
        fld: &str,
        hir: &Option<Type>,
    ) -> Option<Type> {
        n.substitution
            .get(&format!("{variant}.{fld}"))
            .cloned()
            .or_else(|| hir.clone())
    }

    /// Lay out one sum variant's fields after the `{ header(16) | tag(@16) }`
    /// prefix (payload starts at offset 24): `(tag, [(name, type, offset)])`.
    fn variant_layout(
        &self,
        n: &NominalType,
        variant: &str,
    ) -> Option<(i32, Vec<VariantFieldLayout>)> {
        let info = self.program.type_by_id(n.id)?;
        let TypeKind::Sum { variants } = &info.kind else {
            return None;
        };
        let v = variants.iter().find(|v| v.name == variant)?;
        let mut offset = 24u64; // header(16) + i32 tag(@16) + pad
        let mut out = Vec::with_capacity(v.fields.len());
        for fld in &v.fields {
            let fty = self.variant_field_type(n, &v.name, &fld.name, &fld.resolved_ty)?;
            let (size, align) = type_size_align(&fty);
            offset = align_up(offset, align);
            out.push((fld.name.clone(), fty, offset));
            offset += size;
        }
        Some((v.tag, out))
    }

    /// Total size of a sum object: the header+tag prefix plus the largest
    /// variant payload.
    fn sum_total_size(&self, n: &NominalType) -> u64 {
        let Some(info) = self.program.type_by_id(n.id) else {
            return 24;
        };
        let TypeKind::Sum { variants } = &info.kind else {
            return 24;
        };
        let mut max = 24u64;
        for v in variants {
            let mut offset = 24u64;
            for fld in &v.fields {
                let fty = self
                    .variant_field_type(n, &v.name, &fld.name, &fld.resolved_ty)
                    .unwrap_or(Type::Void);
                let (size, align) = type_size_align(&fty);
                offset = align_up(offset, align) + size;
            }
            max = max.max(offset);
        }
        align_up(max, 8)
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

    /// The `(int64 value, is_float flag, f64 value)` triple a `*.from(x)`
    /// conversion passes to the runtime, from an int or float argument.
    fn conv_from_args(
        &mut self,
        arg: BasicValueEnum<'ctx>,
        arg_ty: &Type,
    ) -> (IntValue<'ctx>, IntValue<'ctx>, FloatValue<'ctx>) {
        match arg_ty {
            Type::Int(_) => {
                let xi = self
                    .coerce(arg, arg_ty, &Type::Int(IntKind::I64))
                    .into_int_value();
                (xi, self.i64c(0), self.ctx.f64_type().const_float(0.0))
            }
            Type::Float(_) => {
                let xf = self
                    .coerce(arg, arg_ty, &Type::Float(FloatKind::F64))
                    .into_float_value();
                (self.i64c(0), self.i64c(1), xf)
            }
            _ => (
                self.i64c(0),
                self.i64c(0),
                self.ctx.f64_type().const_float(0.0),
            ),
        }
    }

    /// Call a runtime function returning a pointer (a typed heap handle).
    /// Call a runtime primitive `void name(ptr)` for its side effect.
    fn call_rt_void(&self, name: &str, arg: BasicValueEnum<'ctx>) {
        let ty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        let f = self.abi.runtime_fn(&self.module, name, ty);
        self.builder.build_call(f, &[arg.into()], "").unwrap();
    }

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
            _ => self.typed_unit(),
        }
    }

    /// The type and byte offset of field `field` in whichever variant defines it.
    /// Read a field from a sum value. A variant-qualified field (`Variant.field`,
    /// from a variant pattern binding) reads that variant's slot directly. A bare
    /// field common to several variants may sit at a different byte
    /// offset in each variant (when preceded by different-sized fields), so its load
    /// is dispatched on the runtime tag; when the offset is the same in every variant
    /// (the common case) it loads directly.
    fn load_sum_field(
        &mut self,
        base: BasicValueEnum<'ctx>,
        n: &NominalType,
        field: &str,
    ) -> BasicValueEnum<'ctx> {
        let (want_variant, fname) = match field.split_once('.') {
            Some((v, f)) => (Some(v), f),
            None => (None, field),
        };
        let names: Vec<String> = match self.program.type_by_id(n.id).map(|i| &i.kind) {
            Some(TypeKind::Sum { variants }) => variants.iter().map(|v| v.name.clone()).collect(),
            _ => return self.typed_unit(),
        };
        // (tag, type, offset) of `field` in each (matching) variant that declares it.
        let mut entries: Vec<(i32, Type, u64)> = Vec::new();
        for name in &names {
            if want_variant.is_some_and(|w| w != name) {
                continue;
            }
            if let Some((tag, layout)) = self.variant_layout(n, name)
                && let Some((_, fty, offset)) =
                    layout.into_iter().find(|(name, _, _)| name == fname)
            {
                entries.push((tag, fty, offset));
            }
        }
        let Some((_, fty0, off0)) = entries.first().cloned() else {
            return self.typed_unit();
        };
        let llty = self.abi.typed_basic(&fty0);
        let basep = base.into_pointer_value();
        // Fast path: a single (qualified) variant, or the same offset everywhere.
        if entries.iter().all(|(_, _, off)| *off == off0) {
            let fp = self.field_ptr(basep, off0);
            return self.builder.build_load(llty, fp, "f").unwrap();
        }
        // Tag-dispatched load: switch on the i32 tag @16, load at each variant's slot.
        let f = self.cur_fn.unwrap();
        let i32t = self.ctx.i32_type();
        let slot = self.builder.build_alloca(llty, "sumfld").unwrap();
        let tag = self
            .builder
            .build_load(i32t, self.field_ptr(basep, 16), "tag")
            .unwrap()
            .into_int_value();
        let merge = self.ctx.append_basic_block(f, "sumfld_merge");
        let default = self.ctx.append_basic_block(f, "sumfld_default");
        let mut switch_cases = Vec::with_capacity(entries.len());
        let mut blocks = Vec::with_capacity(entries.len());
        for (tag_v, _, _) in &entries {
            let bb = self.ctx.append_basic_block(f, "sumfld_case");
            switch_cases.push((i32t.const_int(*tag_v as u64, true), bb));
            blocks.push(bb);
        }
        self.builder
            .build_switch(tag, default, &switch_cases)
            .unwrap();
        for ((_, _, offset), bb) in entries.iter().zip(blocks) {
            self.builder.position_at_end(bb);
            let v = self
                .builder
                .build_load(llty, self.field_ptr(basep, *offset), "f")
                .unwrap();
            self.builder.build_store(slot, v).unwrap();
            self.builder.build_unconditional_branch(merge).unwrap();
        }
        // Unreachable for a well-formed value; fall back to the first variant's slot.
        self.builder.position_at_end(default);
        let v0 = self
            .builder
            .build_load(llty, self.field_ptr(basep, off0), "f")
            .unwrap();
        self.builder.build_store(slot, v0).unwrap();
        self.builder.build_unconditional_branch(merge).unwrap();
        self.builder.position_at_end(merge);
        self.builder.build_load(llty, slot, "sumfld_v").unwrap()
    }

    /// A memoized per-type deep-copy function `fn(*Header) -> *Header`. An
    /// aggregate (record, sum, tuple, array) is rebuilt with each managed field or
    /// element deep-copied (recursing through this same memoized table, so a
    /// self-referential type terminates); a string/closure is shared with its count
    /// raised. Used to pass a non-reference argument by value.
    fn get_or_emit_deep_copy(&mut self, ty: &Type) -> FunctionValue<'ctx> {
        let key = mangle_fn(&format!("dcopy_{}", ty.display()));
        if let Some(f) = self.deep_copy_fns.get(&key) {
            return *f;
        }
        let ptrt = self.abi.ptr();
        let fty = ptrt.fn_type(&[ptrt.into()], false);
        let f = self.module.add_function(&key, fty, None);
        self.deep_copy_fns.insert(key, f);

        let saved_block = self.builder.get_insert_block();
        let saved_fn = self.cur_fn;
        self.cur_fn = Some(f);
        let entry = self.ctx.append_basic_block(f, "entry");
        self.builder.position_at_end(entry);
        let obj = f.get_nth_param(0).unwrap().into_pointer_value();

        let result = match ty {
            Type::Record(n) => {
                let fields = self.record_field_types(n);
                let copied: Vec<(String, BasicValueEnum<'ctx>)> = fields
                    .iter()
                    .map(|(name, fty, offset)| {
                        let llty = self.abi.typed_basic(fty);
                        let fv = self
                            .builder
                            .build_load(llty, self.field_ptr(obj, *offset), "f")
                            .unwrap();
                        (name.clone(), self.deep_copy(fv, fty))
                    })
                    .collect();
                let refs: Vec<(&str, BasicValueEnum<'ctx>)> =
                    copied.iter().map(|(n, v)| (n.as_str(), *v)).collect();
                self.make_record(ty, &refs)
            }
            Type::Tuple(elems) => {
                let copied: Vec<BasicValueEnum<'ctx>> = elems
                    .iter()
                    .enumerate()
                    .map(|(i, ety)| {
                        let ev = self.tuple_field(obj.into(), elems, i);
                        self.deep_copy(ev, ety)
                    })
                    .collect();
                self.make_tuple(elems, &copied)
            }
            Type::Sum(n) => self.deep_copy_sum(f, ty, n, obj),
            Type::Slice(_) | Type::Array(..) => {
                let elem = prepoly_engine::element_type(ty);
                let (esize, _) = type_size_align(&elem);
                // A managed element is copied through its own deep-copy function
                // (recursing for nesting); a scalar element is copied byte-wise.
                let copy_fn = if prepoly_engine::rc_managed(&elem) {
                    let ef = self.get_or_emit_deep_copy(&elem);
                    self.builder
                        .build_ptr_to_int(
                            ef.as_global_value().as_pointer_value(),
                            self.abi.i64t(),
                            "copyfn",
                        )
                        .unwrap()
                } else {
                    self.i64c(0)
                };
                let dty = ptrt.fn_type(
                    &[ptrt.into(), self.abi.i64t().into(), self.abi.i64t().into()],
                    false,
                );
                let df = self.abi.runtime_fn(&self.module, "pp_arr_deep_copy", dty);
                self.builder
                    .build_call(
                        df,
                        &[obj.into(), self.i64c(esize as i64).into(), copy_fn.into()],
                        "arrdcopy",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
            }
            // A string/closure (or any other managed value) is immutable or never
            // mutated through this copy, so it is shared with its count raised.
            _ => {
                self.retain(obj.into());
                obj.into()
            }
        };
        self.builder.build_return(Some(&result)).unwrap();

        self.cur_fn = saved_fn;
        if let Some(b) = saved_block {
            self.builder.position_at_end(b);
        }
        f
    }

    /// The sum arm of [`get_or_emit_deep_copy`]: switch on the discriminant tag and
    /// rebuild the active variant with each of its fields deep-copied.
    fn deep_copy_sum(
        &mut self,
        f: FunctionValue<'ctx>,
        sum_ty: &Type,
        n: &NominalType,
        obj: PointerValue<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let ptrt = self.abi.ptr();
        let slot = self.builder.build_alloca(ptrt, "sumcopy").unwrap();
        let i32t = self.ctx.i32_type();
        let tag = self
            .builder
            .build_load(i32t, self.field_ptr(obj, 16), "tag")
            .unwrap()
            .into_int_value();
        let variants = self.sum_variant_fields(n);
        let merge = self.ctx.append_basic_block(f, "dcopy_merge");
        let default = self.ctx.append_basic_block(f, "dcopy_unknown");
        let blocks: Vec<_> = variants
            .iter()
            .map(|_| self.ctx.append_basic_block(f, "dcopy_variant"))
            .collect();
        let cases: Vec<_> = variants
            .iter()
            .zip(&blocks)
            .map(|((tag_v, _, _), bb)| (i32t.const_int(*tag_v as u64, true), *bb))
            .collect();
        self.builder.build_switch(tag, default, &cases).unwrap();
        for ((_, vname, vfields), bb) in variants.iter().zip(&blocks) {
            self.builder.position_at_end(*bb);
            let copied: Vec<(String, BasicValueEnum<'ctx>)> = vfields
                .iter()
                .map(|(fname, fty, offset)| {
                    let llty = self.abi.typed_basic(fty);
                    let fv = self
                        .builder
                        .build_load(llty, self.field_ptr(obj, *offset), "vf")
                        .unwrap();
                    (fname.clone(), self.deep_copy(fv, fty))
                })
                .collect();
            let refs: Vec<(&str, BasicValueEnum<'ctx>)> =
                copied.iter().map(|(n, v)| (n.as_str(), *v)).collect();
            let v = self.make_variant(sum_ty, vname, &refs);
            self.builder.build_store(slot, v).unwrap();
            self.builder.build_unconditional_branch(merge).unwrap();
        }
        // An unknown tag should be unreachable for a well-typed value; share it.
        self.builder.position_at_end(default);
        self.retain(obj.into());
        self.builder.build_store(slot, obj).unwrap();
        self.builder.build_unconditional_branch(merge).unwrap();

        self.builder.position_at_end(merge);
        self.builder.build_load(ptrt, slot, "sumcopy_v").unwrap()
    }

    /// A memoized per-type `to_string` renderer for a record or sum. A record
    /// renders as `T {\n    field: <value>,\n}` and a sum as
    /// `T.Variant {\n    field: <value>,\n}` (a field-less variant as bare
    /// `T.Variant`), with each field rendered by [`to_string`] so nested
    /// records/sums/scalars format recursively. Registered before its body is
    /// emitted so a self-referential type (e.g. a field of its own type) recurses
    /// through the call rather than re-entering code generation.
    fn get_or_emit_to_string(&mut self, ty: &Type) -> FunctionValue<'ctx> {
        let key = mangle_fn(&format!("tostr_{}", ty.display()));
        if let Some(f) = self.to_string_fns.get(&key) {
            return *f;
        }
        let fty = self.abi.ptr().fn_type(&[self.abi.ptr().into()], false);
        let f = self.module.add_function(&key, fty, None);
        self.to_string_fns.insert(key, f);

        // Gather the shape up front so the `program` borrow ends before the
        // recursive field renderings below (which borrow `self` mutably).
        let record = match ty {
            // A structural record (anonymous structure / `T.from` result) renders
            // under the `anonymous` label rather than its internal `<structural>`.
            Type::Record(n) => {
                let header = if n.name == prepoly_hir::STRUCTURAL_RECORD_NAME {
                    "anonymous".to_string()
                } else {
                    n.name.clone()
                };
                Some((header, self.record_field_types(n)))
            }
            _ => None,
        };
        let sum = match ty {
            Type::Sum(n) => Some((n.name.clone(), self.sum_variant_fields(n))),
            _ => None,
        };

        let saved_block = self.builder.get_insert_block();
        let saved_fn = self.cur_fn;
        self.cur_fn = Some(f);
        let entry = self.ctx.append_basic_block(f, "entry");
        self.builder.position_at_end(entry);
        let obj = f.get_nth_param(0).unwrap().into_pointer_value();

        let result = if let Some((name, fields)) = record {
            self.render_named_fields(obj, &name, &fields)
        } else if let Some((name, variants)) = sum {
            self.render_sum(f, obj, &name, &variants)
        } else {
            self.const_str(&ty.display())
        };
        self.builder.build_return(Some(&result)).unwrap();

        self.cur_fn = saved_fn;
        if let Some(b) = saved_block {
            self.builder.position_at_end(b);
        }
        f
    }

    /// `(field name, concrete type, byte offset)` for each record field (for
    /// rendering), or empty when the type has no record layout. See [`record_fields`].
    fn record_field_types(&self, n: &NominalType) -> Vec<(String, Type, u64)> {
        self.record_fields(n).unwrap_or_default()
    }

    /// `(tag, variant name, [(field name, type, offset)])` for each variant of a
    /// sum, sharing [`variant_layout`]'s payload offsets.
    fn sum_variant_fields(&self, n: &NominalType) -> Vec<(i32, String, Vec<VariantFieldLayout>)> {
        let names: Vec<String> = match self.program.type_by_id(n.id).map(|i| &i.kind) {
            Some(TypeKind::Sum { variants }) => variants.iter().map(|v| v.name.clone()).collect(),
            _ => Vec::new(),
        };
        let mut out = Vec::with_capacity(names.len());
        for name in names {
            if let Some((tag, fields)) = self.variant_layout(n, &name) {
                out.push((tag, name, fields));
            }
        }
        out
    }

    /// Concatenate two runtime strings into a fresh one.
    fn str_concat2(
        &self,
        a: BasicValueEnum<'ctx>,
        b: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_str_concat", &[a, b])
    }

    /// Indent `s` one level (four spaces after each newline). Applied to a field's
    /// rendered value so a nested record/sum prints one level deeper per depth.
    fn str_indent(&self, s: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_str_indent", &[s])
    }

    /// Build `<header> {\n    f: <v>,\n}` for the fields of the object at `obj`
    /// (or `<header> {}` with no fields). `header` is `T` for a record or
    /// `T.Variant` for a sum variant; each field value is rendered by `to_string`.
    fn render_named_fields(
        &mut self,
        obj: PointerValue<'ctx>,
        header: &str,
        fields: &[(String, Type, u64)],
    ) -> BasicValueEnum<'ctx> {
        if fields.is_empty() {
            return self.const_str(&format!("{header} {{}}"));
        }
        let mut acc = self.const_str(&format!("{header} {{\n"));
        for (fname, fty, offset) in fields {
            let prefix = self.const_str(&format!("    {fname}: "));
            acc = self.str_concat2(acc, prefix);
            let llty = self.abi.typed_basic(fty);
            let fp = self.field_ptr(obj, *offset);
            let fv = self.builder.build_load(llty, fp, "fld").unwrap();
            // Indent the field's rendering one level so a nested record/sum (which
            // is itself multi-line) sits under its label with deeper indentation.
            let fs = self.to_string(fv, fty);
            let fs = self.str_indent(fs);
            acc = self.str_concat2(acc, fs);
            let comma = self.const_str(",\n");
            acc = self.str_concat2(acc, comma);
        }
        let close = self.const_str("}");
        self.str_concat2(acc, close)
    }

    /// Render a sum value: read the runtime tag (i32 @16) and, for the active
    /// variant, build `T.Variant { ... }` (bare `T.Variant` when field-less). An
    /// unrecognized tag (not expected for a well-formed value) renders the type
    /// name alone.
    fn render_sum(
        &mut self,
        f: FunctionValue<'ctx>,
        obj: PointerValue<'ctx>,
        name: &str,
        variants: &[(i32, String, Vec<VariantFieldLayout>)],
    ) -> BasicValueEnum<'ctx> {
        let ptrt = self.abi.ptr();
        let slot = self.builder.build_alloca(ptrt, "sumstr").unwrap();
        let i32t = self.ctx.i32_type();
        let tag = self
            .builder
            .build_load(i32t, self.field_ptr(obj, 16), "tag")
            .unwrap()
            .into_int_value();
        let merge = self.ctx.append_basic_block(f, "tostr_merge");
        let default = self.ctx.append_basic_block(f, "tostr_unknown");
        let mut blocks = Vec::with_capacity(variants.len());
        let mut cases = Vec::with_capacity(variants.len());
        for (tag_v, _, _) in variants {
            let bb = self.ctx.append_basic_block(f, "tostr_variant");
            cases.push((i32t.const_int(*tag_v as u64, true), bb));
            blocks.push(bb);
        }
        self.builder.build_switch(tag, default, &cases).unwrap();
        for ((_, vname, vfields), bb) in variants.iter().zip(blocks) {
            self.builder.position_at_end(bb);
            let header = format!("{name}.{vname}");
            let s = if vfields.is_empty() {
                self.const_str(&header)
            } else {
                self.render_named_fields(obj, &header, vfields)
            };
            self.builder.build_store(slot, s).unwrap();
            self.builder.build_unconditional_branch(merge).unwrap();
        }
        self.builder.position_at_end(default);
        let unknown = self.const_str(name);
        self.builder.build_store(slot, unknown).unwrap();
        self.builder.build_unconditional_branch(merge).unwrap();

        self.builder.position_at_end(merge);
        self.builder.build_load(ptrt, slot, "sumstr_v").unwrap()
    }
}

impl<'ctx, 'p> prepoly_engine::RuntimeJit for LlvmCodegen<'ctx, 'p> {
    /// Compile one monomorphized instance into the live execution engine and
    /// return its callable address (deferred monomorphization).
    ///
    /// The instance is emitted into a *fresh* module where every other instance
    /// and global is an external declaration -- the engine resolves those against
    /// the already-compiled code -- and only this instance gets a body. The module
    /// is kept alive (the engine references it after `add_module`) and added to the
    /// running engine. This is the LLVM-specific half of the runtime backend; the
    /// cache/orchestration lives backend-agnostically in `prepoly_engine`.
    fn compile_instance(
        &mut self,
        program: &MonoProgram,
        f: &MonoFunction,
    ) -> Result<usize, String> {
        if self.mir.engine.is_none() {
            return Err("compile_instance called before finalize".to_string());
        }
        // Swap in a fresh module + codegen tables so the instance is emitted in
        // isolation, then restore the persistent state. `begin_program` declares
        // every instance (and global) into the fresh module; `codegen_function`
        // defines just this instance's body, leaving the rest external.
        let fresh = self.ctx.create_module("prepoly_rt");
        let saved_module = std::mem::replace(&mut self.module, fresh);
        let saved_fns = std::mem::take(&mut self.fns);
        let saved_globals = std::mem::take(&mut self.mir.globals);
        let saved_inits = std::mem::take(&mut self.mir.init_symbols);
        // Destructors are per-module (a `__drop_*` can only be called within the
        // module that defines it); give the fresh module its own memo. The
        // per-type `to_string` renderers are module-local for the same reason.
        let saved_destructors = std::mem::take(&mut self.destructors);
        let saved_to_string_fns = std::mem::take(&mut self.to_string_fns);
        let saved_deep_copy_fns = std::mem::take(&mut self.deep_copy_fns);

        self.begin_program(program);
        self.codegen_function(program, f);
        let verified = self
            .module
            .verify()
            .map_err(|e| format!("runtime instance verification failed:\n{}", e.to_string()));

        let filled = std::mem::replace(&mut self.module, saved_module);
        self.fns = saved_fns;
        self.mir.globals = saved_globals;
        self.mir.init_symbols = saved_inits;
        self.destructors = saved_destructors;
        self.to_string_fns = saved_to_string_fns;
        self.deep_copy_fns = saved_deep_copy_fns;
        verified?;

        // Keep the module alive and hand it to the live engine.
        self.mir.runtime_modules.push(filled);
        let module_ref = self.mir.runtime_modules.last().unwrap();
        let engine = self.mir.engine.as_ref().unwrap();
        engine
            .add_module(module_ref)
            .map_err(|_| "failed to add runtime module to engine".to_string())?;
        crate::jit::engine::map_runtime_symbols(engine, module_ref);
        let addr = engine
            .get_function_address(&mangle_fn(&f.symbol))
            .map_err(|e| format!("runtime instance address unavailable: {e}"))?;
        Ok(addr as usize)
    }
}

impl<'ctx, 'p> EngineCodegen for LlvmCodegen<'ctx, 'p> {
    type Value = BasicValueEnum<'ctx>;

    fn begin_program(&mut self, program: &MonoProgram) {
        // Emit region write barriers only when the program uses `with`; a
        // sequential program then pays no barrier cost.
        self.region_barriers = prepoly_engine::program_uses_with(program);
        // Declare one typed LLVM function per instance, named by its instance
        // symbol, so calls/recursion resolve before bodies are emitted.
        for f in &program.functions {
            // A closure instance takes a leading environment pointer (even when
            // it captures nothing).
            let fty = if f.is_closure {
                self.abi.typed_closure_fn_type(&f.type_args, &f.ret)
            } else {
                self.abi.typed_fn_type(&f.type_args, &f.ret)
            };
            let name = mangle_fn(&f.symbol);
            let func = self.module.add_function(&name, fty, None);
            self.fns.map.insert(name, func);
        }
        // Declare each typed global, zero-initialized; init instances fill them.
        for (name, ty) in &program.globals {
            let llty = self.abi.typed_basic(ty);
            let g = self.module.add_global(llty, None, &mangle_global(name));
            g.set_initializer(&llty.const_zero());
            self.mir.globals.insert(name.clone(), g);
        }
        self.mir.init_symbols = program.init_symbols.clone();
        self.mir.frozen_globals = immutable_heap_globals(program);
    }

    fn finalize(&mut self) -> Result<(), String> {
        // Generate the auto-freeze entry over the module's immutable heap globals, called between init and `main` in `execute`.
        self.emit_freeze_globals_fn();
        self.module
            .verify()
            .map_err(|e| format!("LLVM module verification failed:\n{}", e.to_string()))?;
        // Mark small functions `alwaysinline` and run the optimizer.
        self.mark_small_functions_alwaysinline();
        self.run_optimization_passes();
        // O2-equivalent backend codegen: `Default` is LLVM's `-O2`,
        // not the previous `Aggressive` (~`-O3`).
        let engine = self
            .module
            .create_jit_execution_engine(OptimizationLevel::Default)
            .map_err(|e| format!("failed to create JIT engine: {e}"))?;
        // Map any runtime primitives the module references (none for the pure
        // scalar subset, but keeps the path correct as it grows).
        crate::jit::engine::map_runtime_symbols(&engine, &self.module);
        self.mir.engine = Some(engine);
        Ok(())
    }

    fn execute(&mut self) -> Result<(), String> {
        let inits = self.mir.init_symbols.clone();
        let frozen = self.mir.frozen_globals.clone();
        let engine = self
            .mir
            .engine
            .as_ref()
            .ok_or("execute called before finalize")?;
        let call = |sym: &str| {
            if let Ok(addr) = engine.get_function_address(&mangle_fn(sym)) {
                let f: unsafe extern "C" fn() = unsafe { std::mem::transmute(addr) };
                unsafe { f() };
            }
        };
        // Module initializers run (in order), populating the globals.
        for sym in &inits {
            call(sym);
        }
        // Module init is complete: auto-freeze the namespace's immutable heap
        // globals so they are deeply immutable and safely
        // shareable across threads before `main` (which may `spawn`) runs. The
        // freeze is a generated function (`emit_freeze_globals_fn`) that reads each
        // global and deep-freezes it.
        if !frozen.is_empty()
            && let Ok(addr) = engine.get_function_address(FREEZE_GLOBALS_FN)
        {
            let f: unsafe extern "C" fn() = unsafe { std::mem::transmute(addr) };
            unsafe { f() };
        }
        call("main");
        // Wait for threads `spawn`ed during the run so their work completes and
        // output is deterministic before the program ends.
        prepoly_runtime::conc::pp_join_all();
        // Reclaim reference cycles that plain reference counting could not free, so a long-running program does not leak them.
        prepoly_runtime::gc::pp_gc_collect();
        Ok(())
    }

    fn begin_body(&mut self, func: &MonoFunction) {
        let f = self.fns.map[&mangle_fn(&func.symbol)];
        let body = func.body;
        self.cur_fn = Some(f);

        let setup = self.ctx.append_basic_block(f, "setup");
        let blocks: Vec<BasicBlock<'ctx>> = (0..body.blocks.len())
            .map(|i| self.ctx.append_basic_block(f, &format!("bb{i}")))
            .collect();
        self.builder.position_at_end(setup);

        // For a closure instance, captured locals live in the environment object
        // (LLVM param 0) rather than in stack slots; map each to its byte offset.
        let is_closure = func.is_closure;
        let capture_offsets: HashMap<usize, u64> = if is_closure {
            let ctys: Vec<Type> = func
                .captures
                .iter()
                .map(|c| func.local_types[c.index()].clone())
                .collect();
            let (offsets, _) = closure_layout(&ctys);
            func.captures
                .iter()
                .zip(offsets)
                .map(|(c, o)| (c.index(), o))
                .collect()
        } else {
            HashMap::new()
        };
        let env = is_closure.then(|| f.get_nth_param(0).unwrap().into_pointer_value());

        // Typed storage per local: an env field pointer for captures, a stack
        // slot otherwise (none for void locals, which have no value).
        let mut locals: Vec<Option<MirSlot<'ctx>>> = Vec::with_capacity(body.locals.len());
        for (idx, ty) in func.local_types.iter().enumerate() {
            if matches!(ty, Type::Void) {
                locals.push(None);
                continue;
            }
            let llty = self.abi.typed_basic(ty);
            let ptr = match capture_offsets.get(&idx) {
                Some(off) => self.field_ptr(env.unwrap(), *off),
                None => {
                    let a = self.typed_alloca(llty, "l");
                    // Null-initialize object (pointer) slots so reference counting
                    // can release a local unconditionally at return: an
                    // unassigned-on-this-path local reads as null, and release of
                    // null is a no-op. Parameters are overwritten just below.
                    if llty.is_pointer_type() {
                        self.builder.build_store(a, llty.const_zero()).unwrap();
                    }
                    a
                }
            };
            locals.push(Some(MirSlot { ptr, ty: llty }));
        }
        self.mir.locals = locals;

        // Bind incoming typed parameters; a closure's params follow the env.
        let base = if is_closure { 1 } else { 0 };
        for (i, plocal) in body.params.iter().enumerate() {
            let v = f.get_nth_param((i + base) as u32).unwrap();
            self.typed_store_local(*plocal, v);
        }

        self.builder
            .build_unconditional_branch(blocks[body.entry.index()])
            .unwrap();
        self.mir.blocks = blocks;
    }

    fn end_body(&mut self) {
        self.mir.locals.clear();
        self.mir.blocks.clear();
    }

    fn begin_block(&mut self, id: BlockId) {
        self.builder.position_at_end(self.mir.blocks[id.index()]);
    }

    fn load_local(&mut self, id: LocalId) -> BasicValueEnum<'ctx> {
        self.typed_load_local(id)
    }
    fn store_local(&mut self, id: LocalId, v: BasicValueEnum<'ctx>) {
        self.typed_store_local(id, v);
    }

    fn const_int(&mut self, v: i64, ty: &Type) -> BasicValueEnum<'ctx> {
        match self.abi.typed_basic(ty) {
            BasicTypeEnum::IntType(it) => it.const_int(v as u64, ty_is_signed(ty)).into(),
            _ => self.typed_unit(),
        }
    }
    fn const_float(&mut self, v: f64, ty: &Type) -> BasicValueEnum<'ctx> {
        match self.abi.typed_basic(ty) {
            BasicTypeEnum::FloatType(ft) => ft.const_float(v).into(),
            _ => self.typed_unit(),
        }
    }
    fn const_bool(&mut self, v: bool) -> BasicValueEnum<'ctx> {
        self.ctx.bool_type().const_int(v as u64, false).into()
    }
    fn const_str(&mut self, s: &str) -> BasicValueEnum<'ctx> {
        let (ptr, len) = self.global_str(s);
        let ty = self
            .abi
            .ptr()
            .fn_type(&[self.abi.ptr().into(), self.abi.i64t().into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_str_const", ty);
        self.builder
            .build_call(f, &[ptr.into(), self.i64c(len as i64).into()], "str")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }
    fn const_null(&mut self) -> BasicValueEnum<'ctx> {
        self.abi.ptr().const_null().into()
    }
    fn truthy(&mut self, v: BasicValueEnum<'ctx>, ty: &Type) -> BasicValueEnum<'ctx> {
        // Truthiness is derived from the condition's type: a bool is its own
        // value, a nullable is a non-null test, and any other (non-nullable)
        // type is unconditionally true. The operand `v` is still evaluated for
        // its side effects before being discarded in the always-true case.
        match ty {
            Type::Bool => v,
            Type::Nullable(_) => self
                .builder
                .build_is_not_null(v.into_pointer_value(), "nn")
                .unwrap()
                .into(),
            _ => self.const_bool(true),
        }
    }
    fn unit(&mut self) -> BasicValueEnum<'ctx> {
        self.typed_unit()
    }

    fn coerce(&mut self, v: BasicValueEnum<'ctx>, from: &Type, to: &Type) -> BasicValueEnum<'ctx> {
        match (from, to) {
            (Type::Int(fk), Type::Int(tk)) => {
                let (fb, tb) = (int_bits_of(*fk), int_bits_of(*tk));
                if fb == tb {
                    return v;
                }
                let BasicTypeEnum::IntType(target) = self.abi.typed_basic(to) else {
                    return v;
                };
                let iv = v.into_int_value();
                if tb > fb {
                    if int_signed(*fk) {
                        self.builder
                            .build_int_s_extend(iv, target, "sx")
                            .unwrap()
                            .into()
                    } else {
                        self.builder
                            .build_int_z_extend(iv, target, "zx")
                            .unwrap()
                            .into()
                    }
                } else {
                    self.builder
                        .build_int_truncate(iv, target, "tr")
                        .unwrap()
                        .into()
                }
            }
            (Type::Float(FloatKind::F32), Type::Float(FloatKind::F64)) => self
                .builder
                .build_float_ext(v.into_float_value(), self.ctx.f64_type(), "fx")
                .unwrap()
                .into(),
            (Type::Float(FloatKind::F64), Type::Float(FloatKind::F32)) => self
                .builder
                .build_float_trunc(v.into_float_value(), self.ctx.f32_type(), "ft")
                .unwrap()
                .into(),
            // An integer implicitly converts to a float (e.g. `int * float`):
            // signed/unsigned int-to-float per the int's signedness.
            (Type::Int(k), Type::Float(fk)) => {
                let target = match fk {
                    FloatKind::F32 => self.ctx.f32_type(),
                    FloatKind::F64 => self.ctx.f64_type(),
                };
                let iv = v.into_int_value();
                if int_signed(*k) {
                    self.builder
                        .build_signed_int_to_float(iv, target, "sitofp")
                        .unwrap()
                        .into()
                } else {
                    self.builder
                        .build_unsigned_int_to_float(iv, target, "uitofp")
                        .unwrap()
                        .into()
                }
            }
            // Nullables share the pointer repr (null = null pointer); coercion
            // between two nullables is identity, value -> nullable wraps it in a
            // heap cell, and nullable -> value unwraps (narrowing).
            (Type::Nullable(_), Type::Nullable(_)) => v,
            (_, Type::Nullable(inner)) => self.nullable_wrap(v, inner),
            (Type::Nullable(_), _) => self.nullable_unwrap(v, to),
            _ => v,
        }
    }

    fn string_len(&mut self, s: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        let ty = self.abi.i64t().fn_type(&[self.abi.ptr().into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_str_len", ty);
        self.builder
            .build_call(f, &[s.into()], "slen")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }

    fn string_slice(
        &mut self,
        s: BasicValueEnum<'ctx>,
        start: BasicValueEnum<'ctx>,
        end: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let ty = self.abi.ptr().fn_type(
            &[
                self.abi.ptr().into(),
                self.abi.i64t().into(),
                self.abi.i64t().into(),
            ],
            false,
        );
        let f = self.abi.runtime_fn(&self.module, "pp_str_slice", ty);
        self.builder
            .build_call(f, &[s.into(), start.into(), end.into()], "slice")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }

    fn string_to_bytes(&mut self, s: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_str_to_bytes", &[s])
    }

    fn string_find(
        &mut self,
        s: BasicValueEnum<'ctx>,
        sub: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_str_find", &[s, sub])
    }

    fn string_concat(
        &mut self,
        a: BasicValueEnum<'ctx>,
        b: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_str_concat", &[a, b])
    }

    fn string_cmp(
        &mut self,
        a: BasicValueEnum<'ctx>,
        b: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        // pp_str_cmp returns an i32 (-1/0/1), so it needs a typed call signature
        // rather than the pointer-returning helper.
        let ty = self
            .ctx
            .i32_type()
            .fn_type(&[self.abi.ptr().into(), self.abi.ptr().into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_str_cmp", ty);
        self.call_basic(f, &[a.into(), b.into()])
    }

    fn string_char_at(
        &mut self,
        s: BasicValueEnum<'ctx>,
        i: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let ty = self
            .abi
            .ptr()
            .fn_type(&[self.abi.ptr().into(), self.abi.i64t().into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_str_char_at", ty);
        self.call_basic(f, &[s.into(), i.into()])
    }

    fn string_from_bytes(&mut self, bytes: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_str_from_bytes", &[bytes])
    }
    fn file_open(
        &mut self,
        path: BasicValueEnum<'ctx>,
        mode: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_file_open", &[path, mode])
    }
    fn file_std(&mut self, which: u8) -> BasicValueEnum<'ctx> {
        let name = match which {
            0 => "pp_file_stdin",
            1 => "pp_file_stdout",
            _ => "pp_file_stderr",
        };
        self.call_rt_ptr(name, &[])
    }
    fn file_read(
        &mut self,
        file: BasicValueEnum<'ctx>,
        n: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        // The runtime takes an i64 count, but `n` may arrive as a narrower int
        // literal (e.g. `read(1)`); widen it so every `pp_file_read` call site
        // agrees on the (ptr, i64) signature.
        let i64t = self.abi.i64t();
        let iv = n.into_int_value();
        let n64 = if iv.get_type().get_bit_width() < 64 {
            self.builder.build_int_s_extend(iv, i64t, "n64").unwrap()
        } else {
            iv
        };
        let ty = self
            .abi
            .ptr()
            .fn_type(&[self.abi.ptr().into(), i64t.into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_file_read", ty);
        self.builder
            .build_call(f, &[file.into(), n64.into()], "frd")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }
    fn file_write(
        &mut self,
        file: BasicValueEnum<'ctx>,
        bytes: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_file_write", &[file, bytes])
    }
    fn file_size(&mut self, file: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_file_size", &[file])
    }
    fn file_seek(
        &mut self,
        file: BasicValueEnum<'ctx>,
        pos: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_file_seek", &[file, pos])
    }
    fn file_close(&mut self, file: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_file_close", &[file])
    }

    fn convert(
        &mut self,
        target: &Type,
        method: &str,
        arg_ty: &Type,
        arg: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let parse = method == "parse";
        match target {
            Type::Int(k) => {
                let tag = self.i64c(int_runtime_tag(*k));
                if parse {
                    // arg is a typed string pointer.
                    let ty = self
                        .abi
                        .ptr()
                        .fn_type(&[self.abi.ptr().into(), self.abi.i64t().into()], false);
                    let f = self.abi.runtime_fn(&self.module, "pp_conv_int_parse", ty);
                    self.call_basic(f, &[arg.into(), tag.into()])
                } else {
                    let (xi, is_float, xf) = self.conv_from_args(arg, arg_ty);
                    let ty = self.abi.ptr().fn_type(
                        &[
                            self.abi.i64t().into(),
                            self.abi.i64t().into(),
                            self.ctx.f64_type().into(),
                            self.abi.i64t().into(),
                        ],
                        false,
                    );
                    let f = self.abi.runtime_fn(&self.module, "pp_conv_int_from", ty);
                    self.call_basic(f, &[xi.into(), is_float.into(), xf.into(), tag.into()])
                }
            }
            Type::Float(k) => {
                let tag = self.i64c(if matches!(k, FloatKind::F32) { 16 } else { 17 });
                if parse {
                    let ty = self
                        .abi
                        .ptr()
                        .fn_type(&[self.abi.ptr().into(), self.abi.i64t().into()], false);
                    let f = self.abi.runtime_fn(&self.module, "pp_conv_float_parse", ty);
                    self.call_basic(f, &[arg.into(), tag.into()])
                } else {
                    let (xi, is_float, xf) = self.conv_from_args(arg, arg_ty);
                    let ty = self.ctx.f64_type().fn_type(
                        &[
                            self.abi.i64t().into(),
                            self.abi.i64t().into(),
                            self.ctx.f64_type().into(),
                            self.abi.i64t().into(),
                        ],
                        false,
                    );
                    let f = self.abi.runtime_fn(&self.module, "pp_conv_float_from", ty);
                    let wide =
                        self.call_basic(f, &[xi.into(), is_float.into(), xf.into(), tag.into()]);
                    // `pp_conv_float_from` returns an f64; a `float32` target must
                    // truncate it to f32 before it is stored into the 4-byte slot.
                    // The value is already f32-rounded in the runtime, so the
                    // truncation is exact -- without it the f64 bit pattern is read
                    // as f32 and every float32 reads as garbage.
                    if matches!(k, FloatKind::F32) {
                        self.builder
                            .build_float_trunc(
                                wide.into_float_value(),
                                self.ctx.f32_type(),
                                "f32from",
                            )
                            .unwrap()
                            .into()
                    } else {
                        wide
                    }
                }
            }
            _ => self.typed_unit(),
        }
    }

    fn to_string(&mut self, v: BasicValueEnum<'ctx>, ty: &Type) -> BasicValueEnum<'ctx> {
        match ty {
            // Rendering a string is the identity; whether the result needs a
            // reference-count bump depends on whether it is bound (handled by the
            // engine when the rvalue's result is stored), so the leaf stays pure.
            Type::Str => v,
            Type::Bool => {
                let ext = self
                    .builder
                    .build_int_z_extend(v.into_int_value(), self.abi.i64t(), "z")
                    .unwrap();
                self.call_to_str("pp_bool_to_str", &[ext.into()])
            }
            Type::Int(k) => {
                let iv = v.into_int_value();
                let wide = if int_signed(*k) {
                    self.builder.build_int_s_extend(iv, self.abi.i64t(), "sx")
                } else {
                    self.builder.build_int_z_extend(iv, self.abi.i64t(), "zx")
                }
                .unwrap();
                let signed = self.i64c(int_signed(*k) as i64);
                self.call_to_str("pp_int_to_str", &[wide.into(), signed.into()])
            }
            Type::Float(_) => {
                let fv = v.into_float_value();
                let wide = self
                    .builder
                    .build_float_ext(fv, self.ctx.f64_type(), "fx")
                    .unwrap();
                self.call_to_str("pp_float_to_str", &[wide.into()])
            }
            // A nullable renders its value when present, else "null" -- a branch
            // since the result is one string or the other (matches `display`).
            Type::Nullable(inner) => {
                let f = self.cur_fn.unwrap();
                let then_bb = self.ctx.append_basic_block(f, "nn_some");
                let else_bb = self.ctx.append_basic_block(f, "nn_none");
                let merge_bb = self.ctx.append_basic_block(f, "nn_join");
                let nn = self
                    .builder
                    .build_is_not_null(v.into_pointer_value(), "nn")
                    .unwrap();
                self.builder
                    .build_conditional_branch(nn, then_bb, else_bb)
                    .unwrap();

                self.builder.position_at_end(then_bb);
                let inner_val = self.nullable_unwrap(v, inner);
                let s_some = self.to_string(inner_val, inner);
                // `to_string` of a string is the identity -- an alias to the cell's
                // owned string -- so the non-null branch must retain it to return an
                // owned reference like the `null` branch and every other inner type
                // (whose `to_string` is freshly allocated). Without this, releasing
                // the result (e.g. an interpolation temporary) drops the cell's
                // string a second time and corrupts the heap.
                if matches!(inner.as_ref(), Type::Str) {
                    self.retain(s_some);
                }
                let some_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge_bb).unwrap();

                self.builder.position_at_end(else_bb);
                let s_none = self.const_str("null");
                self.builder.build_unconditional_branch(merge_bb).unwrap();

                self.builder.position_at_end(merge_bb);
                let phi = self.builder.build_phi(self.abi.ptr(), "nstr").unwrap();
                phi.add_incoming(&[(&s_some, some_end), (&s_none, else_bb)]);
                phi.as_basic_value()
            }
            // An array renders as `[e0, e1, ...]`: build the string by looping over
            // the elements, rendering each (recursively) and joining with ", ".
            Type::Slice(elem) | Type::Array(elem, _) => {
                let arr = v.into_pointer_value();
                let i64t = self.abi.i64t();
                let ptrt = self.abi.ptr();
                let elem_llty = self.abi.typed_basic(elem);
                let elem_ty = elem.as_ref().clone();
                let concat_ty = ptrt.fn_type(&[ptrt.into(), ptrt.into()], false);
                let concat = self
                    .abi
                    .runtime_fn(&self.module, "pp_str_concat", concat_ty);
                let result = self.builder.build_alloca(ptrt, "arrstr").unwrap();
                let open = self.const_str("[");
                self.builder.build_store(result, open).unwrap();
                let len = self
                    .builder
                    .build_load(i64t, self.field_ptr(arr, 16), "len")
                    .unwrap()
                    .into_int_value();
                let idx = self.builder.build_alloca(i64t, "i").unwrap();
                self.builder.build_store(idx, i64t.const_zero()).unwrap();
                let f = self.cur_fn.unwrap();
                let head = self.ctx.append_basic_block(f, "ats_head");
                let sep = self.ctx.append_basic_block(f, "ats_sep");
                let elembb = self.ctx.append_basic_block(f, "ats_elem");
                let exit = self.ctx.append_basic_block(f, "ats_exit");
                self.builder.build_unconditional_branch(head).unwrap();
                self.builder.position_at_end(head);
                let i = self
                    .builder
                    .build_load(i64t, idx, "i")
                    .unwrap()
                    .into_int_value();
                let more = self
                    .builder
                    .build_int_compare(inkwell::IntPredicate::ULT, i, len, "more")
                    .unwrap();
                self.builder
                    .build_conditional_branch(more, sep, exit)
                    .unwrap();
                // Prepend ", " before every element except the first.
                self.builder.position_at_end(sep);
                let nz = self
                    .builder
                    .build_int_compare(inkwell::IntPredicate::NE, i, i64t.const_zero(), "nz")
                    .unwrap();
                let do_sep = self.ctx.append_basic_block(f, "ats_dosep");
                self.builder
                    .build_conditional_branch(nz, do_sep, elembb)
                    .unwrap();
                self.builder.position_at_end(do_sep);
                let cur = self.builder.build_load(ptrt, result, "cur").unwrap();
                let comma = self.const_str(", ");
                let ws = self
                    .builder
                    .build_call(concat, &[cur.into(), comma.into()], "ws")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                self.builder.build_store(result, ws).unwrap();
                self.builder.build_unconditional_branch(elembb).unwrap();
                self.builder.position_at_end(elembb);
                let ep = self.elem_ptr(arr, elem_llty, i);
                let ev = self.builder.build_load(elem_llty, ep, "ev").unwrap();
                let es = self.to_string(ev, &elem_ty);
                let cur2 = self.builder.build_load(ptrt, result, "cur2").unwrap();
                let ap = self
                    .builder
                    .build_call(concat, &[cur2.into(), es.into()], "ap")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                self.builder.build_store(result, ap).unwrap();
                let inc = self
                    .builder
                    .build_int_add(i, i64t.const_int(1, false), "inc")
                    .unwrap();
                self.builder.build_store(idx, inc).unwrap();
                self.builder.build_unconditional_branch(head).unwrap();
                self.builder.position_at_end(exit);
                let cur3 = self.builder.build_load(ptrt, result, "cur3").unwrap();
                let close = self.const_str("]");
                self.builder
                    .build_call(concat, &[cur3.into(), close.into()], "fin")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
            }
            // A tuple renders as `[e0, e1, ...]`. Its length and element types are
            // statically known, so the rendering is unrolled: each element is loaded
            // at its layout offset, rendered with its own type, and joined.
            Type::Tuple(elems) => {
                let ptrt = self.abi.ptr();
                let concat_ty = ptrt.fn_type(&[ptrt.into(), ptrt.into()], false);
                let concat = self
                    .abi
                    .runtime_fn(&self.module, "pp_str_concat", concat_ty);
                let (layout, _) = self.tuple_layout(elems);
                let tup = v.into_pointer_value();
                let mut cur = self.const_str("[");
                for (i, ety) in elems.iter().enumerate() {
                    if i > 0 {
                        let comma = self.const_str(", ");
                        cur = self
                            .builder
                            .build_call(concat, &[cur.into(), comma.into()], "ws")
                            .unwrap()
                            .try_as_basic_value()
                            .unwrap_basic();
                    }
                    let (llty, offset) = layout[i];
                    let fp = self.field_ptr(tup, offset);
                    let ev = self.builder.build_load(llty, fp, "te").unwrap();
                    let es = self.to_string(ev, ety);
                    cur = self
                        .builder
                        .build_call(concat, &[cur.into(), es.into()], "ap")
                        .unwrap()
                        .try_as_basic_value()
                        .unwrap_basic();
                }
                let close = self.const_str("]");
                self.builder
                    .build_call(concat, &[cur.into(), close.into()], "cl")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
            }
            // A record/sum renders through a memoized per-type formatter so a
            // self-referential type recurses by call rather than inlining forever.
            Type::Record(_) | Type::Sum(_) => {
                let f = self.get_or_emit_to_string(ty);
                self.call_basic(f, &[v.into()])
            }
            // A field whose type has no rendering (a closure, or an opaque/unknown
            // slot from an unannotated unaccessed field) renders as a placeholder.
            // `to_string` always yields a string, so this must not be a unit value
            // (it is concatenated/indented into the surrounding rendering).
            _ => self.const_str("<opaque>"),
        }
    }

    fn bin_op(
        &mut self,
        op: BinOp,
        a: BasicValueEnum<'ctx>,
        b: BasicValueEnum<'ctx>,
        operand_ty: &Type,
    ) -> BasicValueEnum<'ctx> {
        // Integer division/remainder by zero is undefined in LLVM (it lowers to a
        // raw sdiv/udiv), so trap on a zero divisor before emitting it. Float
        // division by zero is defined (inf/nan), so it is left alone.
        if matches!(operand_ty, Type::Int(_)) && matches!(op, BinOp::Div | BinOp::Rem) {
            let y = b.into_int_value();
            let is_zero = self
                .builder
                .build_int_compare(
                    inkwell::IntPredicate::EQ,
                    y,
                    y.get_type().const_zero(),
                    "dz",
                )
                .unwrap();
            self.trap_if(is_zero, "division by zero");
        }
        let b_ = &self.builder;
        match operand_ty {
            Type::Int(_) => {
                let (x, y) = (a.into_int_value(), b.into_int_value());
                let signed = ty_is_signed(operand_ty);
                if codegen_is_int_cmp(op) {
                    return b_
                        .build_int_compare(int_predicate(op, signed), x, y, "cmp")
                        .unwrap()
                        .into();
                }
                let r = match op {
                    BinOp::Add => b_.build_int_add(x, y, "add").unwrap(),
                    BinOp::Sub => b_.build_int_sub(x, y, "sub").unwrap(),
                    BinOp::Mul => b_.build_int_mul(x, y, "mul").unwrap(),
                    BinOp::Div if signed => b_.build_int_signed_div(x, y, "div").unwrap(),
                    BinOp::Div => b_.build_int_unsigned_div(x, y, "div").unwrap(),
                    BinOp::Rem if signed => b_.build_int_signed_rem(x, y, "rem").unwrap(),
                    BinOp::Rem => b_.build_int_unsigned_rem(x, y, "rem").unwrap(),
                    BinOp::BitAnd => b_.build_and(x, y, "and").unwrap(),
                    BinOp::BitOr => b_.build_or(x, y, "or").unwrap(),
                    BinOp::BitXor => b_.build_xor(x, y, "xor").unwrap(),
                    BinOp::Shl => b_.build_left_shift(x, y, "shl").unwrap(),
                    BinOp::Shr => b_.build_right_shift(x, y, signed, "shr").unwrap(),
                    _ => return self.typed_unit(),
                };
                r.into()
            }
            Type::Float(_) => {
                let (x, y) = (a.into_float_value(), b.into_float_value());
                if codegen_is_int_cmp(op) {
                    return b_
                        .build_float_compare(float_predicate(op), x, y, "fcmp")
                        .unwrap()
                        .into();
                }
                let r = match op {
                    BinOp::Add => b_.build_float_add(x, y, "fadd").unwrap(),
                    BinOp::Sub => b_.build_float_sub(x, y, "fsub").unwrap(),
                    BinOp::Mul => b_.build_float_mul(x, y, "fmul").unwrap(),
                    BinOp::Div => b_.build_float_div(x, y, "fdiv").unwrap(),
                    _ => return self.typed_unit(),
                };
                r.into()
            }
            // Bool: only equality comparisons are in scope.
            Type::Bool => {
                let (x, y) = (a.into_int_value(), b.into_int_value());
                b_.build_int_compare(int_predicate(op, false), x, y, "bcmp")
                    .unwrap()
                    .into()
            }
            // String: `+` is concatenation, `==`/`!=` are byte equality.
            Type::Str => self.str_bin_op(op, a, b),
            // Nullable `==`/`!=`: a pointer (presence/identity) comparison.
            Type::Nullable(_) => {
                let pa = self
                    .builder
                    .build_ptr_to_int(a.into_pointer_value(), self.abi.i64t(), "pa")
                    .unwrap();
                let pb = self
                    .builder
                    .build_ptr_to_int(b.into_pointer_value(), self.abi.i64t(), "pb")
                    .unwrap();
                self.builder
                    .build_int_compare(int_predicate(op, false), pa, pb, "ncmp")
                    .unwrap()
                    .into()
            }
            _ => self.typed_unit(),
        }
    }

    fn un_op(
        &mut self,
        op: UnaryOp,
        a: BasicValueEnum<'ctx>,
        operand_ty: &Type,
    ) -> BasicValueEnum<'ctx> {
        match op {
            UnaryOp::Neg => match operand_ty {
                Type::Float(_) => self
                    .builder
                    .build_float_neg(a.into_float_value(), "fneg")
                    .unwrap()
                    .into(),
                _ => self
                    .builder
                    .build_int_neg(a.into_int_value(), "neg")
                    .unwrap()
                    .into(),
            },
            // `!x` on a nullable tests for null; on a bool/int it is bit/logical
            // negation.
            UnaryOp::Not | UnaryOp::BitNot => match operand_ty {
                Type::Nullable(_) => self
                    .builder
                    .build_is_null(a.into_pointer_value(), "isnull")
                    .unwrap()
                    .into(),
                _ => self
                    .builder
                    .build_not(a.into_int_value(), "not")
                    .unwrap()
                    .into(),
            },
        }
    }

    fn call(
        &mut self,
        symbol: &str,
        args: &[BasicValueEnum<'ctx>],
        ret: &Type,
    ) -> BasicValueEnum<'ctx> {
        let f = self.fns.map[&mangle_fn(symbol)];
        let meta: Vec<inkwell::values::BasicMetadataValueEnum> =
            args.iter().map(|a| (*a).into()).collect();
        let cs = self.builder.build_call(f, &meta, "call").unwrap();
        if matches!(ret, Type::Void) {
            self.typed_unit()
        } else {
            cs.try_as_basic_value().unwrap_basic()
        }
    }

    fn make_record(
        &mut self,
        record_ty: &Type,
        fields: &[(&str, BasicValueEnum<'ctx>)],
    ) -> BasicValueEnum<'ctx> {
        let Some((layout, size)) = self.record_layout(record_ty) else {
            return self.typed_unit();
        };
        // Allocate a typed heap object (header + the field layout).
        let alloc_ty = self.abi.ptr().fn_type(&[self.abi.i64t().into()], false);
        let alloc = self
            .abi
            .runtime_fn(&self.module, "pp_typed_alloc", alloc_ty);
        let base = self
            .builder
            .build_call(alloc, &[self.i64c(size as i64).into()], "rec")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value();
        // Store each field at its byte offset.
        for (name, _llty, offset) in &layout {
            if let Some((_, v)) = fields.iter().find(|f| f.0 == name.as_str()) {
                let fp = self.field_ptr(base, *offset);
                self.builder.build_store(fp, *v).unwrap();
            }
        }
        self.register_for_gc(base.into(), record_ty);
        base.into()
    }

    fn make_tuple(
        &mut self,
        elem_types: &[Type],
        elems: &[BasicValueEnum<'ctx>],
    ) -> BasicValueEnum<'ctx> {
        let (layout, size) = self.tuple_layout(elem_types);
        let alloc_ty = self.abi.ptr().fn_type(&[self.abi.i64t().into()], false);
        let alloc = self
            .abi
            .runtime_fn(&self.module, "pp_typed_alloc", alloc_ty);
        let base = self
            .builder
            .build_call(alloc, &[self.i64c(size as i64).into()], "tup")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value();
        for ((_, offset), v) in layout.iter().zip(elems) {
            let fp = self.field_ptr(base, *offset);
            self.builder.build_store(fp, *v).unwrap();
        }
        self.register_for_gc(base.into(), &Type::Tuple(elem_types.to_vec()));
        base.into()
    }

    fn tuple_field(
        &mut self,
        tup: BasicValueEnum<'ctx>,
        elem_types: &[Type],
        index: usize,
    ) -> BasicValueEnum<'ctx> {
        let (layout, _) = self.tuple_layout(elem_types);
        let Some((llty, offset)) = layout.get(index).copied() else {
            return self.typed_unit();
        };
        let fp = self.field_ptr(tup.into_pointer_value(), offset);
        self.builder.build_load(llty, fp, "te").unwrap()
    }

    fn load_field(
        &mut self,
        base: BasicValueEnum<'ctx>,
        base_ty: &Type,
        field: &str,
    ) -> BasicValueEnum<'ctx> {
        match base_ty {
            Type::Record(_) => {
                let Some((layout, _)) = self.record_layout(base_ty) else {
                    return self.const_null();
                };
                // A field the record's layout does not have yields null (an absent
                // structural field; the type checker typed it nullable).
                let Some((_, llty, offset)) = layout.iter().find(|f| f.0 == field) else {
                    return self.const_null();
                };
                let fp = self.field_ptr(base.into_pointer_value(), *offset);
                self.builder.build_load(*llty, fp, "f").unwrap()
            }
            Type::Sum(n) => self.load_sum_field(base, n, field),
            _ => self.const_null(),
        }
    }

    fn make_variant(
        &mut self,
        sum_ty: &Type,
        variant: &str,
        fields: &[(&str, BasicValueEnum<'ctx>)],
    ) -> BasicValueEnum<'ctx> {
        let Type::Sum(n) = sum_ty else {
            return self.typed_unit();
        };
        let Some((tag, layout)) = self.variant_layout(n, variant) else {
            return self.typed_unit();
        };
        let size = self.sum_total_size(n);
        let alloc_ty = self.abi.ptr().fn_type(&[self.abi.i64t().into()], false);
        let alloc = self
            .abi
            .runtime_fn(&self.module, "pp_typed_alloc", alloc_ty);
        let base = self
            .builder
            .build_call(alloc, &[self.i64c(size as i64).into()], "sum")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value();
        // Discriminant tag at offset 16.
        let tagp = self.field_ptr(base, 16);
        let tagv = self.ctx.i32_type().const_int(tag as u64, true);
        self.builder.build_store(tagp, tagv).unwrap();
        // Variant fields in the payload.
        for (name, _ty, offset) in &layout {
            if let Some((_, v)) = fields.iter().find(|f| f.0 == name.as_str()) {
                let fp = self.field_ptr(base, *offset);
                self.builder.build_store(fp, *v).unwrap();
            }
        }
        base.into()
    }

    fn pattern_matches(
        &mut self,
        subj: BasicValueEnum<'ctx>,
        subj_ty: &Type,
        variant: &str,
    ) -> BasicValueEnum<'ctx> {
        match subj_ty {
            Type::Sum(n) => {
                let Some((tag, _)) = self.variant_layout(n, variant) else {
                    return self.ctx.bool_type().const_zero().into();
                };
                let tagp = self.field_ptr(subj.into_pointer_value(), 16);
                let loaded = self
                    .builder
                    .build_load(self.ctx.i32_type(), tagp, "tag")
                    .unwrap()
                    .into_int_value();
                let want = self.ctx.i32_type().const_int(tag as u64, true);
                self.builder
                    .build_int_compare(IntPredicate::EQ, loaded, want, "vmatch")
                    .unwrap()
                    .into()
            }
            // A record (or any non-sum) always matches its sole shape.
            _ => self.ctx.bool_type().const_int(1, false).into(),
        }
    }

    fn emit_panic(&mut self, msg: &str) {
        self.gen_panic(msg);
    }
    fn runtime_panic(&mut self, msg: BasicValueEnum<'ctx>) {
        self.call_rt_void("pp_panic_obj", msg);
    }

    fn float_builtin(&mut self, name: &str, args: &[BasicValueEnum<'ctx>]) -> BasicValueEnum<'ctx> {
        let intrinsic = match name {
            "_float_sqrt" => "llvm.sqrt.f64",
            "_float_floor" => "llvm.floor.f64",
            "_float_ceil" => "llvm.ceil.f64",
            "_float_pow" => "llvm.pow.f64",
            _ => return self.typed_unit(),
        };
        let f64t = self.ctx.f64_type();
        let ptys: Vec<inkwell::types::BasicMetadataTypeEnum> =
            args.iter().map(|_| f64t.into()).collect();
        let ty = f64t.fn_type(&ptys, false);
        let f = self.abi.runtime_fn(&self.module, intrinsic, ty);
        let av: Vec<inkwell::values::BasicMetadataValueEnum> =
            args.iter().map(|a| (*a).into()).collect();
        self.builder
            .build_call(f, &av, "fi")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }

    fn emit_print(&mut self, s: BasicValueEnum<'ctx>, newline: bool) {
        let name = if newline {
            "pp_println_str"
        } else {
            "pp_print_str"
        };
        self.call_rt_void(name, s);
    }

    fn spawn(&mut self, closure: BasicValueEnum<'ctx>) {
        self.call_rt_void("pp_spawn", closure);
    }

    fn freeze(&mut self, value: BasicValueEnum<'ctx>) {
        self.call_rt_void("pp_freeze_deep", value);
    }

    fn make_cown(&mut self, value: BasicValueEnum<'ctx>) {
        self.call_rt_void("pp_make_cown", value);
    }

    fn thread_join_all(&mut self) {
        let ty = self.ctx.void_type().fn_type(&[], false);
        let f = self.abi.runtime_fn(&self.module, "pp_join_all", ty);
        self.builder.build_call(f, &[], "").unwrap();
    }

    fn retain(&mut self, value: BasicValueEnum<'ctx>) {
        self.call_rt_void("pp_retain", value);
    }

    fn release(&mut self, value: BasicValueEnum<'ctx>) {
        self.call_rt_void("pp_release", value);
    }

    fn release_obj(&mut self, value: BasicValueEnum<'ctx>, ty: &Type) {
        let f = self.get_or_emit_destructor(ty);
        self.builder.build_call(f, &[value.into()], "").unwrap();
    }

    fn release_closure(&mut self, value: BasicValueEnum<'ctx>) {
        // Load and invoke the closure's destructor (offset 24); null-guard first,
        // since reading the slot from a null closure would fault.
        let env = value.into_pointer_value();
        let func = self.cur_fn.unwrap();
        let call_bb = self.ctx.append_basic_block(func, "clo_drop");
        let done_bb = self.ctx.append_basic_block(func, "clo_done");
        let is_null = self.builder.build_is_null(env, "clonull").unwrap();
        self.builder
            .build_conditional_branch(is_null, done_bb, call_bb)
            .unwrap();
        self.builder.position_at_end(call_bb);
        let dp = self.field_ptr(env, 24);
        let dtor = self
            .builder
            .build_load(self.abi.ptr(), dp, "dtor")
            .unwrap()
            .into_pointer_value();
        let fn_ty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        self.builder
            .build_indirect_call(fn_ty, dtor, &[env.into()], "")
            .unwrap();
        self.builder.build_unconditional_branch(done_bb).unwrap();
        self.builder.position_at_end(done_bb);
    }

    fn cown_lock(&mut self, obj: BasicValueEnum<'ctx>) {
        self.call_rt_void("pp_lock", obj);
    }

    fn cown_unlock(&mut self, obj: BasicValueEnum<'ctx>) {
        self.call_rt_void("pp_unlock", obj);
    }

    fn cown_lock_all(&mut self, arr: BasicValueEnum<'ctx>) {
        self.call_rt_void("pp_lock_all", arr);
    }

    fn cown_unlock_all(&mut self, arr: BasicValueEnum<'ctx>) {
        self.call_rt_void("pp_unlock_all", arr);
    }

    fn region_open(&mut self, bridge: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        let i64t = self.abi.i64t();
        let ty = i64t.fn_type(&[self.abi.ptr().into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_region_open", ty);
        self.builder
            .build_call(f, &[bridge.into()], "rid")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }

    fn region_close(&mut self, region_id: BasicValueEnum<'ctx>) {
        let i8t = self.ctx.i8_type();
        let ty = i8t.fn_type(&[self.abi.i64t().into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_region_close", ty);
        let closed = self
            .builder
            .build_call(f, &[region_id.into()], "closed")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_int_value();
        let ok = self
            .builder
            .build_int_compare(inkwell::IntPredicate::NE, closed, i8t.const_zero(), "ok")
            .unwrap();
        let func = self.cur_fn.unwrap();
        let cont = self.ctx.append_basic_block(func, "region_ok");
        let leak = self.ctx.append_basic_block(func, "region_leak");
        self.builder
            .build_conditional_branch(ok, cont, leak)
            .unwrap();
        self.builder.position_at_end(leak);
        self.gen_panic("region not closed: a reference escaped a `with` scope");
        self.builder.build_unreachable().unwrap();
        self.builder.position_at_end(cont);
    }

    fn region_write(&mut self, container: BasicValueEnum<'ctx>, value: BasicValueEnum<'ctx>) {
        let ty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into(), self.abi.ptr().into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_region_write", ty);
        self.builder
            .build_call(f, &[container.into(), value.into()], "")
            .unwrap();
    }

    fn emit_region_barrier(&self) -> bool {
        self.region_barriers
    }

    fn store_global(&mut self, name: &str, _ty: &Type, v: BasicValueEnum<'ctx>) {
        if let Some(g) = self.mir.globals.get(name) {
            self.builder.build_store(g.as_pointer_value(), v).unwrap();
        }
    }

    fn load_global(&mut self, name: &str, ty: &Type) -> BasicValueEnum<'ctx> {
        match self.mir.globals.get(name) {
            Some(g) => {
                let llty = self.abi.typed_basic(ty);
                self.builder
                    .build_load(llty, g.as_pointer_value(), "g")
                    .unwrap()
            }
            None => self.typed_unit(),
        }
    }

    fn make_array(
        &mut self,
        elem_ty: &Type,
        elems: &[BasicValueEnum<'ctx>],
    ) -> BasicValueEnum<'ctx> {
        // Growable layout: pp_arr_new allocates the object and an element buffer;
        // the literal's elements are stored into the buffer.
        let (esize, _) = type_size_align(elem_ty);
        let llty = self.abi.typed_basic(elem_ty);
        let len = elems.len() as u64;
        let new_ty = self
            .abi
            .ptr()
            .fn_type(&[self.abi.i64t().into(), self.abi.i64t().into()], false);
        let new = self.abi.runtime_fn(&self.module, "pp_arr_new", new_ty);
        let base = self
            .builder
            .build_call(
                new,
                &[self.i64c(esize as i64).into(), self.i64c(len as i64).into()],
                "arr",
            )
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value();
        for (i, v) in elems.iter().enumerate() {
            let ep = self.elem_ptr(base, llty, self.i64c(i as i64));
            self.builder.build_store(ep, *v).unwrap();
        }
        base.into()
    }

    fn push(&mut self, arr: BasicValueEnum<'ctx>, elem_ty: &Type, v: BasicValueEnum<'ctx>) {
        let (esize, _) = type_size_align(elem_ty);
        let llty = self.abi.typed_basic(elem_ty);
        // Stash the element in a stack slot so the runtime can copy its bytes.
        let tmp = self.typed_alloca(llty, "pushtmp");
        self.builder.build_store(tmp, v).unwrap();
        let ty = self.ctx.void_type().fn_type(
            &[
                self.abi.ptr().into(),
                self.abi.ptr().into(),
                self.abi.i64t().into(),
            ],
            false,
        );
        let f = self.abi.runtime_fn(&self.module, "pp_arr_push", ty);
        self.builder
            .build_call(
                f,
                &[arr.into(), tmp.into(), self.i64c(esize as i64).into()],
                "",
            )
            .unwrap();
    }

    fn insert(
        &mut self,
        arr: BasicValueEnum<'ctx>,
        elem_ty: &Type,
        idx: BasicValueEnum<'ctx>,
        v: BasicValueEnum<'ctx>,
    ) {
        let (esize, _) = type_size_align(elem_ty);
        let llty = self.abi.typed_basic(elem_ty);
        // Stash the element in a stack slot so the runtime can copy its bytes.
        let tmp = self.typed_alloca(llty, "instmp");
        self.builder.build_store(tmp, v).unwrap();
        let idx64 = self.sext_to_i64(idx);
        let ty = self.ctx.void_type().fn_type(
            &[
                self.abi.ptr().into(),
                self.abi.i64t().into(),
                self.abi.ptr().into(),
                self.abi.i64t().into(),
            ],
            false,
        );
        let f = self.abi.runtime_fn(&self.module, "pp_arr_insert", ty);
        self.builder
            .build_call(
                f,
                &[
                    arr.into(),
                    idx64.into(),
                    tmp.into(),
                    self.i64c(esize as i64).into(),
                ],
                "",
            )
            .unwrap();
    }

    fn remove(
        &mut self,
        arr: BasicValueEnum<'ctx>,
        elem_ty: &Type,
        idx: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let (esize, _) = type_size_align(elem_ty);
        let llty = self.abi.typed_basic(elem_ty);
        let idx64 = self.sext_to_i64(idx);
        // The runtime returns the removed element's bytes zero-extended in an i64;
        // store them and reload at the element type to reinterpret.
        let ity = self.ctx.i64_type().fn_type(
            &[
                self.abi.ptr().into(),
                self.abi.i64t().into(),
                self.abi.i64t().into(),
            ],
            false,
        );
        let f = self.abi.runtime_fn(&self.module, "pp_arr_remove", ity);
        let bits = self
            .builder
            .build_call(
                f,
                &[arr.into(), idx64.into(), self.i64c(esize as i64).into()],
                "rm",
            )
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic();
        let slot = self.typed_alloca(self.ctx.i64_type().into(), "rmtmp");
        self.builder.build_store(slot, bits).unwrap();
        self.builder.build_load(llty, slot, "rmv").unwrap()
    }

    fn pop(&mut self, arr: BasicValueEnum<'ctx>, elem_ty: &Type) -> BasicValueEnum<'ctx> {
        let (esize, _) = type_size_align(elem_ty);
        // The runtime returns the nullable cell pointer directly (null = empty),
        // which is exactly the `elem_ty?` representation -- no wrapping needed.
        let ty = self
            .abi
            .ptr()
            .fn_type(&[self.abi.ptr().into(), self.abi.i64t().into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_arr_pop", ty);
        self.builder
            .build_call(f, &[arr.into(), self.i64c(esize as i64).into()], "pop")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }

    fn deep_copy(&mut self, value: BasicValueEnum<'ctx>, ty: &Type) -> BasicValueEnum<'ctx> {
        let inner = unwrap_copy_wrappers(ty).clone();
        // A managed value (aggregate, string, or closure) is copied by its memoized
        // per-type deep-copy function -- an aggregate gets a fresh, independent value
        // with managed fields/elements copied recursively, a string/closure is shared
        // with its count raised. A scalar is returned unchanged.
        if prepoly_engine::rc_managed(&inner) && value.is_pointer_value() {
            let f = self.get_or_emit_deep_copy(&inner);
            self.builder
                .build_call(f, &[value.into()], "dcopy")
                .unwrap()
                .try_as_basic_value()
                .unwrap_basic()
        } else {
            value
        }
    }

    fn int_widen(
        &mut self,
        x: BasicValueEnum<'ctx>,
        from_bits: BasicValueEnum<'ctx>,
        to_bits: BasicValueEnum<'ctx>,
        signed: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let s = self.int_arg_i64(signed);
        let ty = self.ctx.i64_type().fn_type(
            &[
                self.abi.i64t().into(),
                self.abi.i64t().into(),
                self.abi.i64t().into(),
                self.abi.i64t().into(),
            ],
            false,
        );
        let f = self.abi.runtime_fn(&self.module, "pp_int_widen", ty);
        self.builder
            .build_call(
                f,
                &[x.into(), from_bits.into(), to_bits.into(), s.into()],
                "wd",
            )
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }

    fn int_narrow(
        &mut self,
        x: BasicValueEnum<'ctx>,
        from_bits: BasicValueEnum<'ctx>,
        to_bits: BasicValueEnum<'ctx>,
        signed: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let s = self.int_arg_i64(signed);
        let ty = self.abi.ptr().fn_type(
            &[
                self.abi.i64t().into(),
                self.abi.i64t().into(),
                self.abi.i64t().into(),
                self.abi.i64t().into(),
            ],
            false,
        );
        let f = self.abi.runtime_fn(&self.module, "pp_int_narrow", ty);
        self.builder
            .build_call(
                f,
                &[x.into(), from_bits.into(), to_bits.into(), s.into()],
                "nr",
            )
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }

    fn load_index(
        &mut self,
        arr: BasicValueEnum<'ctx>,
        arr_ty: &Type,
        idx: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let elem_ty = elem_of(arr_ty);
        let llty = self.abi.typed_basic(&elem_ty);
        self.bounds_check(arr, idx.into_int_value());
        let ep = self.elem_ptr(arr.into_pointer_value(), llty, idx.into_int_value());
        self.builder.build_load(llty, ep, "e").unwrap()
    }

    fn store_index(
        &mut self,
        arr: BasicValueEnum<'ctx>,
        arr_ty: &Type,
        idx: BasicValueEnum<'ctx>,
        v: BasicValueEnum<'ctx>,
    ) {
        let llty = self.abi.typed_basic(&elem_of(arr_ty));
        self.bounds_check(arr, idx.into_int_value());
        let ep = self.elem_ptr(arr.into_pointer_value(), llty, idx.into_int_value());
        self.builder.build_store(ep, v).unwrap();
    }

    fn array_len(&mut self, arr: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        let lenp = self.field_ptr(arr.into_pointer_value(), 16);
        self.builder
            .build_load(self.abi.i64t(), lenp, "alen")
            .unwrap()
    }

    fn make_closure(
        &mut self,
        fun_ty: &Type,
        id: ClosureId,
        captures: &[(Type, BasicValueEnum<'ctx>)],
    ) -> BasicValueEnum<'ctx> {
        let Type::Fun(params, _) = fun_ty else {
            return self.typed_unit();
        };
        let capture_types: Vec<Type> = captures.iter().map(|(t, _)| t.clone()).collect();
        let (offsets, size) = closure_layout(&capture_types);
        // Allocate the environment object and store the instance function pointer
        // (offset 16) and the captured values (packed from offset 24).
        let alloc_ty = self.abi.ptr().fn_type(&[self.abi.i64t().into()], false);
        let alloc = self
            .abi
            .runtime_fn(&self.module, "pp_typed_alloc", alloc_ty);
        let base = self
            .builder
            .build_call(alloc, &[self.i64c(size as i64).into()], "clo")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value();
        let sym = closure_symbol(id, &capture_types, params);
        if let Some(func) = self.fns.map.get(&mangle_fn(&sym)) {
            let fp = func.as_global_value().as_pointer_value();
            let fpp = self.field_ptr(base, 16);
            self.builder.build_store(fpp, fp).unwrap();
        }
        // Store this closure's capture-releasing destructor (offset 24): emitted
        // here, where the capture types are known, and called when the closure is
        // released (the `Fun` type alone could not recover the capture layout).
        let dtor = self.emit_closure_dtor(&capture_types);
        let dp = self.field_ptr(base, 24);
        self.builder
            .build_store(dp, dtor.as_global_value().as_pointer_value())
            .unwrap();
        for ((_, v), off) in captures.iter().zip(offsets) {
            let cp = self.field_ptr(base, off);
            self.builder.build_store(cp, *v).unwrap();
        }
        base.into()
    }

    fn call_indirect(
        &mut self,
        callee: BasicValueEnum<'ctx>,
        callee_ty: &Type,
        args: &[BasicValueEnum<'ctx>],
    ) -> BasicValueEnum<'ctx> {
        let Type::Fun(params, ret) = callee_ty else {
            return self.typed_unit();
        };
        let env = callee.into_pointer_value();
        let fp = self
            .builder
            .build_load(self.abi.ptr(), self.field_ptr(env, 16), "fp")
            .unwrap()
            .into_pointer_value();
        let fn_ty = self.abi.typed_closure_fn_type(params, ret);
        // The environment is passed as the leading argument.
        let mut argv: Vec<inkwell::values::BasicMetadataValueEnum> = vec![env.into()];
        argv.extend(
            args.iter()
                .map(|a| -> inkwell::values::BasicMetadataValueEnum { (*a).into() }),
        );
        let cs = self
            .builder
            .build_indirect_call(fn_ty, fp, &argv, "ci")
            .unwrap();
        if matches!(ret.as_ref(), Type::Void) {
            self.typed_unit()
        } else {
            cs.try_as_basic_value().unwrap_basic()
        }
    }

    fn deferred_dispatch(
        &mut self,
        consumer: &str,
        type_name: &str,
        value: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        // Resolve the consumer's storage symbol from its source name (the symbol
        // the runtime service instantiates).
        let symbol = self
            .program
            .functions
            .values()
            .find(|fi| fi.signature.name == consumer)
            .map(|fi| fi.symbol.clone())
            .unwrap_or_else(|| consumer.to_string());
        let (sym_ptr, sym_len) = self.global_str(&symbol);
        let (ty_ptr, ty_len) = self.global_str(type_name);

        // addr = pp_resolve(name_ptr, name_len, type_ptr, type_len): the consumer
        // compiled for the runtime type (cached after first use), or 0 if it fails.
        let i64t = self.abi.i64t();
        let ptr = self.abi.ptr();
        let resolve_ty = i64t.fn_type(&[ptr.into(), i64t.into(), ptr.into(), i64t.into()], false);
        let resolve = self.abi.runtime_fn(&self.module, "pp_resolve", resolve_ty);
        let addr = self
            .builder
            .build_call(
                resolve,
                &[
                    sym_ptr.into(),
                    self.i64c(sym_len as i64).into(),
                    ty_ptr.into(),
                    self.i64c(ty_len as i64).into(),
                ],
                "addr",
            )
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_int_value();

        // Indirect-call the resolved consumer `(ptr) -> i32` on the value.
        let fp = self
            .builder
            .build_int_to_ptr(addr, self.abi.ptr(), "fp")
            .unwrap();
        let fn_ty = self.ctx.i32_type().fn_type(&[self.abi.ptr().into()], false);
        self.builder
            .build_indirect_call(fn_ty, fp, &[value.into()], "dd")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }

    fn store_field(
        &mut self,
        base: BasicValueEnum<'ctx>,
        base_ty: &Type,
        field: &str,
        v: BasicValueEnum<'ctx>,
    ) {
        let Some((layout, _)) = self.record_layout(base_ty) else {
            return;
        };
        let Some((_, _llty, offset)) = layout.iter().find(|f| f.0 == field) else {
            return;
        };
        let fp = self.field_ptr(base.into_pointer_value(), *offset);
        self.builder.build_store(fp, v).unwrap();
    }

    fn emit_return(&mut self, v: Option<BasicValueEnum<'ctx>>) {
        match v {
            Some(val) => {
                self.builder.build_return(Some(&val)).unwrap();
            }
            None => {
                self.builder.build_return(None).unwrap();
            }
        }
    }
    fn emit_goto(&mut self, target: BlockId) {
        self.builder
            .build_unconditional_branch(self.mir.blocks[target.index()])
            .unwrap();
    }
    fn emit_cond_branch(&mut self, cond: BasicValueEnum<'ctx>, then: BlockId, els: BlockId) {
        self.builder
            .build_conditional_branch(
                cond.into_int_value(),
                self.mir.blocks[then.index()],
                self.mir.blocks[els.index()],
            )
            .unwrap();
    }
    fn emit_unreachable(&mut self) {
        self.builder.build_unreachable().unwrap();
    }
}

/// Whether an operator is a comparison (shared with the typed bin-op emission).
pub(crate) fn codegen_is_int_cmp(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge
    )
}
