//! The `brass_engine::Codegen` implementation: one method per MIR operation,
//! each emitting its typed IR at the builder's position. Shared emission
//! utilities live in the parent module, layouts in `aggregate`, and per-type
//! helpers in `memory`, `render` and `equality`.

use fxhash::FxHashMap as HashMap;

use inkwell::IntPredicate;
use inkwell::basic_block::BasicBlock;
use inkwell::module::Linkage;
use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValue, BasicValueEnum};

use brass_engine::{Codegen as EngineCodegen, MonoFunction, MonoProgram, closure_symbol};
use brass_hir::{FloatKind, Type};
use brass_mir::{BlockId, ClosureId, LocalId};
use brass_parser::ast::{BinOp, UnaryOp};

use crate::jit::orc::OptTier;
use crate::monomorph::mangle_fn;

use super::aggregate::{closure_layout, elem_of, type_size_align};
use super::session::immutable_heap_globals;
use super::{
    LlvmCodegen, MirSlot, codegen_is_int_cmp, float_predicate, int_predicate, int_runtime_tag,
    nominal_layout_differs, rendered_string_is_owned, same_representation, ty_is_signed,
    unwrap_copy_wrappers,
};

impl<'ctx, 'p> EngineCodegen for LlvmCodegen<'ctx, 'p> {
    type Value = BasicValueEnum<'ctx>;

    fn begin_program(&mut self, program: &MonoProgram) {
        // Emit region write barriers only when the program uses `with`; a
        // sequential program then pays no barrier cost.
        self.region_barriers = brass_engine::program_uses_with(program);
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
        self.declare_globals(program, true);
        self.mir.init_symbols = program.init_symbols.clone();
        self.mir.frozen_globals = immutable_heap_globals(program);
        self.mir.lazy_has_main = program.lookup("main").is_some();
    }

    fn finalize(&mut self) -> Result<(), String> {
        self.emit_freeze_globals_fn();
        self.module
            .verify()
            .map_err(|e| format!("LLVM module verification failed:\n{e}"))?;
        self.mark_small_functions_alwaysinline();
        self.run_optimization_passes();
        // Whole-module callers retain their established IR pipeline and O2
        // instruction selection, independently of the lazy BRASS_OPT setting.
        self.create_orc(OptTier::O2)?;
        for f in self
            .module
            .get_functions()
            .filter(|f| f.count_basic_blocks() != 0)
        {
            self.mir
                .defined
                .insert(f.get_name().to_string_lossy().into_owned(), false);
        }
        let jit = self.mir.orc.as_ref().expect("ORC session created");
        jit.add_optimized_module(jit.copy_module(&self.module)?)
    }

    fn execute(&mut self) -> Result<(), String> {
        self.execute_lazy_orc()
    }

    fn begin_body(&mut self, func: &MonoFunction) {
        let f = self
            .instance_fn(&func.symbol)
            .expect("body of an undeclared instance");
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
            HashMap::default()
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
            // A constant evaluated for a `void` destination is discarded.
            _ if matches!(ty, Type::Void) => self.typed_unit(),
            _ => self.internal_error_value(
                &format!("an integer constant was typed `{}`", ty.display()),
                ty,
            ),
        }
    }
    fn const_float(&mut self, v: f64, ty: &Type) -> BasicValueEnum<'ctx> {
        match self.abi.typed_basic(ty) {
            BasicTypeEnum::FloatType(ft) => ft.const_float(v).into(),
            _ if matches!(ty, Type::Void) => self.typed_unit(),
            _ => self.internal_error_value(
                &format!("a float constant was typed `{}`", ty.display()),
                ty,
            ),
        }
    }
    fn const_bool(&mut self, v: bool) -> BasicValueEnum<'ctx> {
        self.ctx.bool_type().const_int(v as u64, false).into()
    }
    fn const_str(&mut self, s: &str) -> BasicValueEnum<'ctx> {
        // Interned, not freshly allocated: a literal evaluated in a loop's
        // non-owning position (comparison, argument, interpolation) has no
        // release site, so a per-evaluation allocation would grow without
        // bound.
        let (ptr, len) = self.global_str(s);
        let ty = self
            .abi
            .ptr()
            .fn_type(&[self.abi.ptr().into(), self.abi.i64t().into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_str_intern", ty);
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
        // A function value keeps its target when its representation is shared.
        // The creation and invocation signatures must therefore agree exactly.
        if cfg!(debug_assertions)
            && let (Type::Fun(from_params, from_ret), Type::Fun(to_params, to_ret)) = (from, to)
            && same_representation(from, to)
        {
            debug_assert_eq!(
                self.abi.typed_closure_fn_type(from_params, from_ret),
                self.abi.typed_closure_fn_type(to_params, to_ret),
                "closure coercion ABI: {} -> {}",
                from.display(),
                to.display()
            );
        }
        // A record/sum of another declaration has another layout, and no arm
        // below converts between declarations: an accepted flow of that shape
        // is a front-end defect, so the program stops here with an internal
        // error instead of reading the value at the wrong layout.
        if nominal_layout_differs(from, to) {
            let always = self.ctx.bool_type().const_int(1, false);
            self.trap_if(
                always,
                &format!(
                    "internal error: a `{}` value reached a `{}` slot",
                    from.display(),
                    to.display()
                ),
            );
        }
        match (from, to) {
            (Type::Int(fk), Type::Int(tk)) => {
                let (fb, tb) = (fk.bits(), tk.bits());
                if fb == tb {
                    return v;
                }
                let BasicTypeEnum::IntType(target) = self.abi.typed_basic(to) else {
                    return v;
                };
                let iv = v.into_int_value();
                if tb > fb {
                    if fk.is_signed() {
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
                    // Implicit integer conversions only widen: the checker
                    // and monomorphization type every operator, join and
                    // flow by value-preserving rules. A narrower slot is a
                    // front-end defect; stop with an internal error instead
                    // of dropping the high bits.
                    let always = self.ctx.bool_type().const_int(1, false);
                    self.trap_if(
                        always,
                        &format!(
                            "internal error: a `{}` value reached a narrower `{}` slot",
                            from.display(),
                            to.display()
                        ),
                    );
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
                if k.is_signed() {
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
            // heap cell, and nullable -> value unwraps (narrowing). A numeric
            // value converts to the cell's element type before wrapping
            // (`int32 -> int64?` stores an int64 cell).
            (Type::Nullable(_), Type::Nullable(_)) if same_representation(from, to) => v,
            (f, Type::Nullable(inner)) if !matches!(f, Type::Nullable(_)) => {
                let v = self.coerce(v, f, inner);
                self.nullable_wrap(v, inner)
            }
            (Type::Nullable(_), t) if !matches!(t, Type::Nullable(_)) => {
                self.nullable_unwrap(v, to)
            }
            // Every other pair passes the value through unchanged, which is
            // only right when both types share one representation; a value
            // discarded into `void` is never read.
            _ if matches!(to, Type::Void) || same_representation(from, to) => v,
            _ => self.internal_error_value(
                &format!(
                    "a `{}` value reached a `{}` slot",
                    from.display(),
                    to.display()
                ),
                to,
            ),
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
    fn argv(&mut self) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_argv", &[])
    }

    fn flush(&mut self) {
        let fty = self.ctx.void_type().fn_type(&[], false);
        let f = self.abi.runtime_fn(&self.module, "pp_flush", fty);
        self.builder.build_call(f, &[], "").unwrap();
    }
    fn stdin_read(&mut self, n: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        // `pp_stdin_read(i64) -> ptr`: the count is an integer; widen a
        // narrower literal so every call site declares one signature.
        let i64t = self.abi.i64t();
        let n = match n {
            BasicValueEnum::IntValue(iv) if iv.get_type().get_bit_width() < 64 => self
                .builder
                .build_int_s_extend(iv, i64t, "n64")
                .unwrap()
                .into(),
            other => other,
        };
        let ty = self.abi.ptr().fn_type(&[i64t.into()], false);
        let f = self.abi.runtime_fn(&self.module, "pp_stdin_read", ty);
        self.builder
            .build_call(f, &[n.into()], "stdin")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }
    fn plugin_call(
        &mut self,
        rt_name: &'static str,
        strings: [BasicValueEnum<'ctx>; 3],
        args: &[(BasicValueEnum<'ctx>, Type)],
        ret: &Type,
    ) -> BasicValueEnum<'ctx> {
        let i64t = self.abi.i64t();
        // Pack the payload into 8-byte stack slots the runtime decodes per the
        // signature string: integers widen to i64 (bools zero-extend), floats
        // store their bits, heap objects their address.
        // An entry-block alloca: a positional one inside a loop would grow the
        // stack once per iteration.
        let arr_ty = i64t.array_type(args.len() as u32);
        let slots = self.typed_alloca(arr_ty.into(), "plugin_args");
        for (i, (v, t)) in args.iter().enumerate() {
            let slot = unsafe {
                self.builder
                    .build_in_bounds_gep(i64t, slots, &[self.i64c(i as i64)], "pslot")
                    .unwrap()
            };
            match v {
                BasicValueEnum::IntValue(iv) => {
                    let wide = if iv.get_type().get_bit_width() < 64 {
                        if matches!(t, Type::Bool) {
                            self.builder.build_int_z_extend(*iv, i64t, "pb").unwrap()
                        } else {
                            self.builder.build_int_s_extend(*iv, i64t, "pn").unwrap()
                        }
                    } else {
                        *iv
                    };
                    self.builder.build_store(slot, wide).unwrap();
                }
                // An f64 occupies the slot's 8 bytes verbatim; the runtime
                // reinterprets per the signature.
                BasicValueEnum::FloatValue(fv) => {
                    self.builder.build_store(slot, *fv).unwrap();
                }
                BasicValueEnum::PointerValue(pv) => {
                    let addr = self.builder.build_ptr_to_int(*pv, i64t, "pp").unwrap();
                    self.builder.build_store(slot, addr).unwrap();
                }
                other => panic!("unsupported plugin argument value {other:?}"),
            }
        }
        // pp_plugin_call_{int,float,obj}(logical_id, name, sig, argv, argc).
        let ptys: Vec<inkwell::types::BasicMetadataTypeEnum> = vec![
            self.abi.ptr().into(),
            self.abi.ptr().into(),
            self.abi.ptr().into(),
            self.abi.ptr().into(),
            i64t.into(),
        ];
        let fn_ty = match rt_name {
            "pp_plugin_call_int" => i64t.fn_type(&ptys, false),
            "pp_plugin_call_float" => self.ctx.f64_type().fn_type(&ptys, false),
            _ => self.abi.ptr().fn_type(&ptys, false),
        };
        let f = self.abi.runtime_fn(&self.module, rt_name, fn_ty);
        let argc = self.i64c(args.len() as i64);
        let raw = self
            .builder
            .build_call(
                f,
                &[
                    strings[0].into(),
                    strings[1].into(),
                    strings[2].into(),
                    slots.into(),
                    argc.into(),
                ],
                "plugin",
            )
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic();
        // Shape the raw scalar to the builtin's typed result.
        match ret {
            Type::Void => self.unit(),
            Type::Bool => self
                .builder
                .build_int_compare(
                    inkwell::IntPredicate::NE,
                    raw.into_int_value(),
                    i64t.const_zero(),
                    "pbool",
                )
                .unwrap()
                .into(),
            _ => raw,
        }
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
                    let (xi, is_float, xf, source_signed) = self.conv_from_args(arg, arg_ty);
                    let ty = self.abi.ptr().fn_type(
                        &[
                            self.abi.i64t().into(),
                            self.abi.i64t().into(),
                            self.ctx.f64_type().into(),
                            self.abi.i64t().into(),
                            self.abi.i64t().into(),
                        ],
                        false,
                    );
                    let f = self.abi.runtime_fn(&self.module, "pp_conv_int_from", ty);
                    self.call_basic(
                        f,
                        &[
                            xi.into(),
                            is_float.into(),
                            xf.into(),
                            source_signed.into(),
                            tag.into(),
                        ],
                    )
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
                    let (xi, is_float, xf, source_signed) = self.conv_from_args(arg, arg_ty);
                    let ty = self.ctx.f64_type().fn_type(
                        &[
                            self.abi.i64t().into(),
                            self.abi.i64t().into(),
                            self.ctx.f64_type().into(),
                            self.abi.i64t().into(),
                            self.abi.i64t().into(),
                        ],
                        false,
                    );
                    let f = self.abi.runtime_fn(&self.module, "pp_conv_float_from", ty);
                    let wide = self.call_basic(
                        f,
                        &[
                            xi.into(),
                            is_float.into(),
                            xf.into(),
                            source_signed.into(),
                            tag.into(),
                        ],
                    );
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
            _ => self.internal_error_value(
                &format!("conversion to non-numeric `{}`", target.display()),
                target,
            ),
        }
    }

    fn display_nullable(
        &mut self,
        v: BasicValueEnum<'ctx>,
        inner: &Type,
        symbol: &str,
        ret: &Type,
    ) -> BasicValueEnum<'ctx> {
        let f = self.cur_fn.unwrap();
        let some_bb = self.ctx.append_basic_block(f, "nd_some");
        let none_bb = self.ctx.append_basic_block(f, "nd_none");
        let join_bb = self.ctx.append_basic_block(f, "nd_join");
        let present = self
            .builder
            .build_is_not_null(v.into_pointer_value(), "nd_present")
            .unwrap();
        self.builder
            .build_conditional_branch(present, some_bb, none_bb)
            .unwrap();
        self.builder.position_at_end(some_bb);
        let inner_val = self.nullable_unwrap(v, inner);
        let rendered = self.call(symbol, &[inner_val], ret);
        let some_end = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(join_bb).unwrap();
        self.builder.position_at_end(none_bb);
        let null_text = self.const_str("null");
        self.builder.build_unconditional_branch(join_bb).unwrap();
        self.builder.position_at_end(join_bb);
        let phi = self.builder.build_phi(self.abi.ptr(), "nd_str").unwrap();
        phi.add_incoming(&[(&rendered, some_end), (&null_text, none_bb)]);
        phi.as_basic_value()
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
                let wide = if k.bits() == 64 {
                    iv
                } else if k.is_signed() {
                    self.builder
                        .build_int_s_extend(iv, self.abi.i64t(), "sx")
                        .unwrap()
                } else {
                    self.builder
                        .build_int_z_extend(iv, self.abi.i64t(), "zx")
                        .unwrap()
                };
                let signed = self.i64c(k.is_signed() as i64);
                self.call_to_str("pp_int_to_str", &[wide.into(), signed.into()])
            }
            Type::Float(k) => {
                let fv = v.into_float_value();
                let wide = if k.bits() == 64 {
                    fv
                } else {
                    self.builder
                        .build_float_ext(fv, self.ctx.f64_type(), "fx")
                        .unwrap()
                };
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
                // owned string -- so the non-null branch retains it to return an
                // owned reference like the `null` branch and every other inner type
                // (whose `to_string` is freshly allocated): the caller releases the
                // result (e.g. an interpolation temporary) on either branch.
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
                let empty = self.const_str("");
                let initial = self
                    .builder
                    .build_call(concat, &[open.into(), empty.into()], "initial")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                self.builder.build_store(result, initial).unwrap();
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
                self.release(cur);
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
                self.release(cur2);
                if rendered_string_is_owned(&elem_ty) {
                    self.release(es);
                }
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
                let finished = self
                    .builder
                    .build_call(concat, &[cur3.into(), close.into()], "fin")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                self.release(cur3);
                finished
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
                let open = self.const_str("[");
                let empty = self.const_str("");
                let mut cur = self
                    .builder
                    .build_call(concat, &[open.into(), empty.into()], "initial")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                for (i, ety) in elems.iter().enumerate() {
                    if i > 0 {
                        let comma = self.const_str(", ");
                        let next = self
                            .builder
                            .build_call(concat, &[cur.into(), comma.into()], "ws")
                            .unwrap()
                            .try_as_basic_value()
                            .unwrap_basic();
                        self.release(cur);
                        cur = next;
                    }
                    let (llty, offset) = layout[i];
                    let fp = self.field_ptr(tup, offset);
                    let ev = self.builder.build_load(llty, fp, "te").unwrap();
                    let es = self.to_string(ev, ety);
                    let next = self
                        .builder
                        .build_call(concat, &[cur.into(), es.into()], "ap")
                        .unwrap()
                        .try_as_basic_value()
                        .unwrap_basic();
                    self.release(cur);
                    if rendered_string_is_owned(ety) {
                        self.release(es);
                    }
                    cur = next;
                }
                let close = self.const_str("]");
                let result = self
                    .builder
                    .build_call(concat, &[cur.into(), close.into()], "cl")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                self.release(cur);
                result
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
                    // Signed division/remainder wrap on overflow like the
                    // interpreter (`wrapping_div`/`wrapping_rem`): raw sdiv/srem
                    // is UB for `MIN / -1`, so the overflowing pair's divisor is
                    // replaced by 1, yielding exactly the wrapped results (MIN
                    // and 0). Division by zero already trapped above.
                    BinOp::Div | BinOp::Rem if signed => {
                        let w = x.get_type();
                        let min = w.const_int(1u64 << (w.get_bit_width() - 1), false);
                        let is_min = b_
                            .build_int_compare(inkwell::IntPredicate::EQ, x, min, "ovx")
                            .unwrap();
                        let is_m1 = b_
                            .build_int_compare(
                                inkwell::IntPredicate::EQ,
                                y,
                                w.const_all_ones(),
                                "ovy",
                            )
                            .unwrap();
                        let ov = b_.build_and(is_min, is_m1, "ov").unwrap();
                        let safe_y = b_
                            .build_select(ov, w.const_int(1, false), y, "safey")
                            .unwrap()
                            .into_int_value();
                        if matches!(op, BinOp::Div) {
                            b_.build_int_signed_div(x, safe_y, "div").unwrap()
                        } else {
                            b_.build_int_signed_rem(x, safe_y, "rem").unwrap()
                        }
                    }
                    BinOp::Div => b_.build_int_unsigned_div(x, y, "div").unwrap(),
                    BinOp::Rem => b_.build_int_unsigned_rem(x, y, "rem").unwrap(),
                    BinOp::BitAnd => b_.build_and(x, y, "and").unwrap(),
                    BinOp::BitOr => b_.build_or(x, y, "or").unwrap(),
                    BinOp::BitXor => b_.build_xor(x, y, "xor").unwrap(),
                    // Shifts follow the interpreter exactly: it computes every
                    // shift at 64 bits with Rust's wrapping semantics (amount
                    // masked to 0..63), then truncates to the operand width. A
                    // raw LLVM shift is poison for amounts >= the bit width, and
                    // masking to width-1 would still diverge for narrow types
                    // (`1i32 << 40` is 0 under the interpreter, not 256).
                    BinOp::Shl | BinOp::Shr => {
                        let i64t = self.abi.i64t();
                        let w = x.get_type().get_bit_width();
                        let xe = match (w < 64, signed) {
                            (false, _) => x,
                            (true, true) => b_.build_int_s_extend(x, i64t, "xe").unwrap(),
                            (true, false) => b_.build_int_z_extend(x, i64t, "xe").unwrap(),
                        };
                        // Only the low 6 bits of the amount matter; any extension
                        // preserves them.
                        let ye = if y.get_type().get_bit_width() < 64 {
                            b_.build_int_z_extend(y, i64t, "ye").unwrap()
                        } else {
                            y
                        };
                        let amt = b_.build_and(ye, i64t.const_int(63, false), "amt").unwrap();
                        let shifted = if matches!(op, BinOp::Shl) {
                            b_.build_left_shift(xe, amt, "shl").unwrap()
                        } else {
                            b_.build_right_shift(xe, amt, signed, "shr").unwrap()
                        };
                        if w < 64 {
                            b_.build_int_truncate(shifted, x.get_type(), "sht").unwrap()
                        } else {
                            shifted
                        }
                    }
                    _ => {
                        return self
                            .internal_error_value(&format!("`{op:?}` on integers"), operand_ty);
                    }
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
                    _ => {
                        return self
                            .internal_error_value(&format!("`{op:?}` on floats"), operand_ty);
                    }
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
            // Every other `==`/`!=` follows the shared structural definition
            // (`brass_engine::equality_kind`). The heap kinds answer the
            // identity and null cases inline, so `x == null` stays a pointer
            // test -- also when the operand is typed at a non-nullable
            // record/sum (`n != null` for an unannotated parameter `n`
            // instantiated at `Node`).
            Type::Nullable(_)
            | Type::Record(_)
            | Type::Sum(..)
            | Type::Slice(..)
            | Type::Array(..)
            | Type::Fun(..)
            | Type::Tuple(..)
                if matches!(op, BinOp::Eq | BinOp::Ne) =>
            {
                let mut equal = self.equality_value(a, b, operand_ty);
                if matches!(op, BinOp::Ne) {
                    equal = self.builder.build_not(equal, "ne").unwrap();
                }
                equal.into()
            }
            _ => {
                let result_ty = if brass_engine::is_comparison(op) {
                    Type::Bool
                } else {
                    operand_ty.clone()
                };
                self.internal_error_value(
                    &format!("`{op:?}` on `{}`", operand_ty.display()),
                    &result_ty,
                )
            }
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
        let f = self
            .instance_fn(symbol)
            .unwrap_or_else(|| panic!("call to undeclared instance `{symbol}`"));
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
            return self.internal_error_value(
                &format!(
                    "record `{}` has no layout to construct",
                    record_ty.display()
                ),
                record_ty,
            );
        };
        // Every field the construction supplies has a slot, and every slot is
        // supplied: a mismatch would drop a value or leave a slot unset.
        let supplied_unknown = fields
            .iter()
            .find(|(name, _)| !layout.iter().any(|f| f.0 == *name));
        let missing = layout
            .iter()
            .find(|f| !fields.iter().any(|(name, _)| f.0 == *name));
        if let Some((name, _)) = supplied_unknown {
            return self.internal_error_value(
                &format!("record `{}` has no field `{name}`", record_ty.display()),
                record_ty,
            );
        }
        if let Some((name, _, _)) = missing {
            return self.internal_error_value(
                &format!(
                    "record `{}` was constructed without field `{name}`",
                    record_ty.display()
                ),
                record_ty,
            );
        }
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
            return self.internal_error_value(
                &format!("tuple position {index} is out of range"),
                &Type::Void,
            );
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
                    return self.internal_error_value(
                        &format!("record `{}` has no layout to read", base_ty.display()),
                        &Type::Void,
                    );
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
            other => self.internal_error_value(
                &format!("field `{field}` read from `{}`", other.display()),
                &Type::Void,
            ),
        }
    }

    fn make_variant(
        &mut self,
        sum_ty: &Type,
        variant: &str,
        fields: &[(&str, BasicValueEnum<'ctx>)],
    ) -> BasicValueEnum<'ctx> {
        let Type::Sum(n) = sum_ty else {
            return self.internal_error_value(
                &format!("variant `{variant}` built as `{}`", sum_ty.display()),
                sum_ty,
            );
        };
        let Some((tag, layout)) = self.variant_layout(n, variant) else {
            return self.internal_error_value(
                &format!("sum `{}` has no layout for variant `{variant}`", n.name),
                sum_ty,
            );
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
        self.register_for_gc(base.into(), sum_ty);
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
            _ => {
                return self.internal_error_value(
                    &format!("unknown float builtin `{name}`"),
                    &Type::Float(FloatKind::F64),
                );
            }
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

    fn share_escaping(&mut self, value: BasicValueEnum<'ctx>, ty: &Type) {
        // A nullable is a cell: promote the cell, then its content when that is
        // itself a heap object (an absent cell unwraps to null, which the
        // runtime ignores).
        self.make_cown(value);
        if let Type::Nullable(inner) = ty
            && brass_engine::rc_managed(inner)
        {
            let content = self.nullable_unwrap(value, inner);
            self.make_cown(content);
        }
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
        // Load and invoke the closure's destructor (offset 24); a null closure
        // value (an unset slot) has no destructor, so it is skipped.
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

    fn cown_lock_many(&mut self, objs: &[BasicValueEnum<'ctx>]) {
        self.cown_span_call("pp_lock_span", objs);
    }

    fn cown_unlock_many(&mut self, objs: &[BasicValueEnum<'ctx>]) {
        self.cown_span_call("pp_unlock_span", objs);
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

    fn region_store(
        &mut self,
        container: BasicValueEnum<'ctx>,
        old: BasicValueEnum<'ctx>,
        value: BasicValueEnum<'ctx>,
        managed_cells: bool,
    ) {
        let ty = self.ctx.void_type().fn_type(
            &[
                self.abi.ptr().into(),
                self.abi.ptr().into(),
                self.abi.ptr().into(),
                self.abi.i64t().into(),
            ],
            false,
        );
        let f = self.abi.runtime_fn(&self.module, "pp_region_store", ty);
        let cells = self.i64c(managed_cells as i64);
        self.builder
            .build_call(
                f,
                &[container.into(), old.into(), value.into(), cells.into()],
                "",
            )
            .unwrap();
    }

    fn emit_region_barrier(&self) -> bool {
        self.region_barriers
    }

    fn store_global(&mut self, name: &str, ty: &Type, v: BasicValueEnum<'ctx>) {
        let Some(g) = self.mir.globals.get(name).copied() else {
            return self.internal_error(&format!("module global `{name}` is not declared"));
        };
        if v.get_type() != self.abi.typed_basic(ty) {
            return self.internal_error(&format!(
                "a value of the wrong representation was stored into module global `{name}`"
            ));
        }
        self.builder.build_store(g.as_pointer_value(), v).unwrap();
    }

    fn load_global(&mut self, name: &str, ty: &Type) -> BasicValueEnum<'ctx> {
        match self.mir.globals.get(name) {
            Some(g) => {
                let llty = self.abi.typed_basic(ty);
                self.builder
                    .build_load(llty, g.as_pointer_value(), "g")
                    .unwrap()
            }
            None => {
                self.internal_error_value(&format!("module global `{name}` is not declared"), ty)
            }
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
        self.register_for_gc(base.into(), &Type::Slice(Box::new(elem_ty.clone())));
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
        // An out-of-range index traps like the interpreter (which halts with this
        // message); the runtime's `pp_arr_remove` would silently return 0 bytes,
        // letting the program continue on a garbage element. The unsigned compare
        // rejects a negative index as well.
        let len = self.array_len(arr).into_int_value();
        let oob = self
            .builder
            .build_int_compare(inkwell::IntPredicate::UGE, idx64, len, "oob")
            .unwrap();
        self.trap_if(oob, "array remove index out of bounds");
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
        if brass_engine::rc_managed(&inner) && value.is_pointer_value() {
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
        target: Option<&str>,
        captures: &[(Type, BasicValueEnum<'ctx>)],
    ) -> BasicValueEnum<'ctx> {
        let Type::Fun(params, ret) = fun_ty else {
            return self
                .internal_error_value(&format!("closure built as `{}`", fun_ty.display()), fun_ty);
        };
        let capture_types: Vec<Type> = captures.iter().map(|(t, _)| t.clone()).collect();
        let (offsets, size) = closure_layout(&capture_types);
        // Allocate the environment object and store the instance function pointer
        // (offset 16) and the captured values (packed from offset 32).
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
        let sym = target
            .map(str::to_owned)
            .unwrap_or_else(|| closure_symbol(id, &capture_types, params));
        // Every closure stores a callable target with its exact ABI. Missing
        // instances diagnose only when called, after argument evaluation.
        let func = self.closure_target(&sym, params, ret);
        let fp = func.as_global_value().as_pointer_value();
        let fpp = self.field_ptr(base, 16);
        self.builder.build_store(fpp, fp).unwrap();
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
        if let Some(tracer) = self.get_or_emit_closure_tracer(&capture_types) {
            self.register_with_tracer(base.into(), tracer);
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
            return self.internal_error_value(
                &format!("indirect call through `{}`", callee_ty.display()),
                &Type::Void,
            );
        };
        let env = callee.into_pointer_value();
        let fp = self
            .builder
            .build_load(self.abi.ptr(), self.field_ptr(env, 16), "fp")
            .unwrap()
            .into_pointer_value();
        // Constructors store a registered instance or a diagnostic helper,
        // both with this exact closure ABI.
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

    fn deferred_call(
        &mut self,
        symbol: &str,
        args: &[BasicValueEnum<'ctx>],
        params: &[Type],
        ret: &Type,
    ) -> BasicValueEnum<'ctx> {
        // The lazy JIT's runtime-resolved call through the `pp_resolve`
        // trampoline, keyed by the INSTANCE SYMBOL alone: the resolver holds
        // the recorded (base, type args) contract for every deferred site, so
        // no type encoding crosses into the runtime. The indirect call is
        // typed with the site's recorded signature, which is the instance's
        // own ABI -- instances are keyed by caller argument types.
        //
        // The resolved address is cached in a module-private slot per
        // instance symbol: resolution is idempotent (the resolver compiles
        // the instance once and answers with the same address forever), so
        // every call after the first is a load plus an indirect call instead
        // of a string-keyed `pp_resolve` round trip -- the difference between
        // a hot cross-function loop running at eager speed or 50x slower.
        // Threads racing the first call each resolve and store the same
        // address (monotonic atomics; a failed resolution stores 0, which
        // the next call simply retries).
        let i64t = self.abi.i64t();
        let ptr = self.abi.ptr();
        let slot_name = format!("pp_addr_{}", mangle_fn(symbol));
        let slot = self.module.get_global(&slot_name).unwrap_or_else(|| {
            let g = self.module.add_global(i64t, None, &slot_name);
            g.set_linkage(Linkage::Private);
            g.set_initializer(&i64t.const_zero());
            g
        });
        let slot_ptr = slot.as_pointer_value();
        let func = self.cur_fn.unwrap();
        let cached = self
            .builder
            .build_load(i64t, slot_ptr, "dc_cached")
            .unwrap()
            .into_int_value();
        let cached_inst = cached.as_instruction_value().unwrap();
        cached_inst.set_alignment(8).unwrap();
        cached_inst
            .set_atomic_ordering(inkwell::AtomicOrdering::Monotonic)
            .unwrap();
        let hit_bb = self.builder.get_insert_block().unwrap();
        let miss_bb = self.ctx.append_basic_block(func, "dc_resolve");
        let ready_bb = self.ctx.append_basic_block(func, "dc_ready");
        let unresolved = self
            .builder
            .build_int_compare(
                inkwell::IntPredicate::EQ,
                cached,
                i64t.const_zero(),
                "dc_miss",
            )
            .unwrap();
        self.builder
            .build_conditional_branch(unresolved, miss_bb, ready_bb)
            .unwrap();
        self.builder.position_at_end(miss_bb);
        let (sym_ptr, sym_len) = self.global_str(symbol);
        let resolve_ty = i64t.fn_type(&[ptr.into(), i64t.into()], false);
        let resolve = self.abi.runtime_fn(&self.module, "pp_resolve", resolve_ty);
        let resolved = self
            .builder
            .build_call(
                resolve,
                &[sym_ptr.into(), self.i64c(sym_len as i64).into()],
                "addr",
            )
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_int_value();
        let store = self.builder.build_store(slot_ptr, resolved).unwrap();
        store.set_alignment(8).unwrap();
        store
            .set_atomic_ordering(inkwell::AtomicOrdering::Monotonic)
            .unwrap();
        self.builder.build_unconditional_branch(ready_bb).unwrap();
        self.builder.position_at_end(ready_bb);
        let addr_phi = self.builder.build_phi(i64t, "dc_addr").unwrap();
        addr_phi.add_incoming(&[(&cached, hit_bb), (&resolved, miss_bb)]);
        let addr = addr_phi.as_basic_value().into_int_value();
        // 0 means the resolver could not supply the instance (its check
        // failed, or resolution ran on a thread that cannot compile); the
        // resolver reports the real diagnostic itself, this trap only keeps
        // the failure defined.
        let failed = self
            .builder
            .build_int_compare(
                inkwell::IntPredicate::EQ,
                addr,
                self.abi.i64t().const_zero(),
                "noaddr",
            )
            .unwrap();
        self.trap_if(failed, "deferred function was not compiled");
        let fp = self
            .builder
            .build_int_to_ptr(addr, self.abi.ptr(), "fp")
            .unwrap();
        let fn_ty = self.abi.typed_fn_type(params, ret);
        let meta: Vec<inkwell::values::BasicMetadataValueEnum> =
            args.iter().map(|a| (*a).into()).collect();
        let cs = self
            .builder
            .build_indirect_call(fn_ty, fp, &meta, "dc")
            .unwrap();
        if matches!(ret, Type::Void) {
            self.typed_unit()
        } else {
            cs.try_as_basic_value().unwrap_basic()
        }
    }

    fn store_field(
        &mut self,
        base: BasicValueEnum<'ctx>,
        base_ty: &Type,
        field: &str,
        v: BasicValueEnum<'ctx>,
    ) {
        if let Type::Sum(n) = base_ty {
            return self.store_sum_field(base, n, field, v);
        }
        let slot = self
            .record_layout(base_ty)
            .and_then(|(layout, _)| layout.into_iter().find(|f| f.0 == field));
        let Some((_, llty, offset)) = slot else {
            return self.internal_error(&format!(
                "`{}` has no field `{field}` to write",
                base_ty.display()
            ));
        };
        if v.get_type() != llty {
            return self.internal_error(&format!(
                "a value of the wrong representation was written to field `{field}` of `{}`",
                base_ty.display()
            ));
        }
        let fp = self.field_ptr(base.into_pointer_value(), offset);
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
