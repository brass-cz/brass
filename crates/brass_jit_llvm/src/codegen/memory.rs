//! Per-type memory glue: the cycle collector's trace functions and object
//! registration, reference-count destructors for aggregates and closure
//! environments, and deep copies for by-value passing. Each helper is
//! memoized per concrete type (a closure's per capture signature) and
//! registered before its body is emitted, so a self-referential type recurses
//! through a call.

use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};

use brass_engine::Codegen as EngineCodegen;
use brass_hir::{NominalType, Type, TypeKind};

use super::aggregate::{SumFieldLayout, align_up, closure_layout, type_size_align};
use super::{LlvmCodegen, capture_helper_key, helper_key, is_traced};

impl<'ctx, 'p> LlvmCodegen<'ctx, 'p> {
    /// Get or emit the per-type cycle-collector trace function `void trace(obj,
    /// visit)`: it calls `visit` on each traced child of `obj` -- the traced
    /// fields of a record or tuple, a nullable cell's traced value, an array's
    /// traced elements, or the active sum variant's traced payload fields -- and
    /// does nothing for a null `obj`. `None` for a type with no traced children
    /// (a leaf, never registered with the collector). Memoized per type. Unlike
    /// the destructor it does not touch reference counts; the collector does.
    fn get_or_emit_tracer(&mut self, ty: &Type) -> Option<FunctionValue<'ctx>> {
        if let Some(helpers) = &self.helpers {
            let helper = helpers.borrow_mut().get_or_emit_tracer(ty);
            return helper.map(|helper| self.declare_helper(helper));
        }
        let key = helper_key("trace", ty);
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
        let (f, define) = self.helper_function(&key, fty);
        self.tracers.insert(key, Some(f));
        if !define {
            return Some(f);
        }

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
    pub(super) fn register_for_gc(&mut self, obj: BasicValueEnum<'ctx>, ty: &Type) {
        let Some(tracer) = self.get_or_emit_tracer(ty) else {
            return;
        };
        self.register_with_tracer(obj, tracer);
    }

    /// Register an object whose trace layout is selected by its construction
    /// site rather than by its erased public type.
    pub(super) fn register_with_tracer(
        &self,
        obj: BasicValueEnum<'ctx>,
        tracer: FunctionValue<'ctx>,
    ) {
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

    /// Emit the trace function for one concrete closure environment layout.
    pub(super) fn get_or_emit_closure_tracer(
        &mut self,
        capture_types: &[Type],
    ) -> Option<FunctionValue<'ctx>> {
        if let Some(helpers) = &self.helpers {
            let helper = helpers
                .borrow_mut()
                .get_or_emit_closure_tracer(capture_types);
            return helper.map(|helper| self.declare_helper(helper));
        }
        let (offsets, _) = closure_layout(capture_types);
        let children: Vec<u64> = capture_types
            .iter()
            .zip(offsets)
            .filter_map(|(ty, offset)| is_traced(ty).then_some(offset))
            .collect();
        if children.is_empty() {
            return None;
        }
        let key = capture_helper_key("trace_closure", capture_types);
        if let Some(tracer) = self.tracers.get(&key) {
            return *tracer;
        }

        let ptrt = self.abi.ptr();
        let fty = self
            .ctx
            .void_type()
            .fn_type(&[ptrt.into(), ptrt.into()], false);
        let (tracer, define) = self.helper_function(&key, fty);
        self.tracers.insert(key, Some(tracer));
        if !define {
            return Some(tracer);
        }
        let saved = self.builder.get_insert_block();
        let entry = self.ctx.append_basic_block(tracer, "entry");
        self.builder.position_at_end(entry);
        let obj = tracer.get_nth_param(0).unwrap().into_pointer_value();
        let visit = tracer.get_nth_param(1).unwrap().into_pointer_value();
        let visit_ty = self.ctx.void_type().fn_type(&[ptrt.into()], false);
        for offset in children {
            let child = self
                .builder
                .build_load(ptrt, self.field_ptr(obj, offset), "capture")
                .unwrap();
            self.builder
                .build_indirect_call(visit_ty, visit, &[child.into()], "")
                .unwrap();
        }
        self.builder.build_return(None).unwrap();
        if let Some(block) = saved {
            self.builder.position_at_end(block);
        }
        Some(tracer)
    }

    /// Get or emit the per-type destructor for a heap value (record, tuple, sum,
    /// array/slice, or nullable cell): a no-op on null; otherwise decrement its
    /// reference count and, at zero, release what it owns -- a record's or
    /// tuple's traced fields, a nullable cell's traced value, the active sum
    /// variant's traced payload fields, or an array's traced elements and then
    /// its element buffer -- before freeing the block. Memoized per type and
    /// registered before its body is emitted, so a self-referential type calls
    /// itself. The decrement is atomic (see [`Self::atomic_rc_dec`]). Used by
    /// [`EngineCodegen::release_obj`].
    pub(super) fn get_or_emit_destructor(&mut self, ty: &Type) -> FunctionValue<'ctx> {
        if let Some(helpers) = &self.helpers {
            let helper = helpers.borrow_mut().get_or_emit_destructor(ty);
            return self.declare_helper(helper);
        }
        let key = helper_key("drop", ty);
        if let Some(f) = self.destructors.get(&key) {
            return *f;
        }
        let fty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        let (f, define) = self.helper_function(&key, fty);
        self.destructors.insert(key, f);
        if !define {
            return f;
        }
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

        // Tuples use the same packed heap layout as construction: release every
        // managed element at its computed aligned offset.
        if let Type::Tuple(elems) = ty {
            let (layout, _) = self.tuple_layout(elems);
            heap_fields.extend(
                elems
                    .iter()
                    .zip(layout)
                    .filter(|(elem, _)| is_traced(elem))
                    .map(|(elem, (llty, offset))| (elem.clone(), offset, llty)),
            );
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
                        // `is_traced`, not `is_managed_heap`: a nullable payload
                        // field is a retained heap cell and must be released too.
                        .filter(|(_, fty, _)| is_traced(fty))
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
        // Field/capture releases may append their own control flow to the
        // CURRENT function (`release_closure` null-guards through `cur_fn`), so
        // the destructor must be the current function while its body is emitted
        // -- otherwise those blocks land in whatever function triggered the
        // emission and the module fails verification.
        let saved_fn = self.cur_fn;
        self.cur_fn = Some(f);
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
            // `is_traced`, not `is_managed_heap`: a `T?[]` element is a retained
            // nullable heap cell and is released like any managed element.
            if is_traced(&elem) {
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

        self.cur_fn = saved_fn;
        if let Some(b) = saved {
            self.builder.position_at_end(b);
        }
        f
    }

    /// Emit (memoized by capture signature) a closure destructor `__clodrop_*`:
    /// null-guard, decrement the refcount, and at zero release each managed capture
    /// before freeing the environment block. Stored at offset 24 of the closure so
    /// it can be invoked knowing only the `Fun` type (which hides capture types).
    pub(super) fn emit_closure_dtor(&mut self, capture_types: &[Type]) -> FunctionValue<'ctx> {
        if let Some(helpers) = &self.helpers {
            let helper = helpers.borrow_mut().emit_closure_dtor(capture_types);
            return self.declare_helper(helper);
        }
        let (offsets, _) = closure_layout(capture_types);
        let key = capture_helper_key("clodrop", capture_types);
        if let Some(f) = self.destructors.get(&key) {
            return *f;
        }
        let fty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        let (f, define) = self.helper_function(&key, fty);
        self.destructors.insert(key, f);
        if !define {
            return f;
        }

        // Collect managed captures (type, llvm type, offset) before emitting.
        // `is_traced`, not `is_managed_heap`: a captured nullable is a retained
        // heap cell the environment owns, so it must be released as well.
        let managed: Vec<(Type, BasicTypeEnum<'ctx>, u64)> = capture_types
            .iter()
            .zip(offsets)
            .filter(|(t, _)| is_traced(t))
            .map(|(t, off)| (t.clone(), self.abi.typed_basic(t), off))
            .collect();

        let saved = self.builder.get_insert_block();
        // Field/capture releases may append their own control flow to the
        // CURRENT function (`release_closure` null-guards through `cur_fn`), so
        // the destructor must be the current function while its body is emitted
        // -- otherwise those blocks land in whatever function triggered the
        // emission and the module fails verification.
        let saved_fn = self.cur_fn;
        self.cur_fn = Some(f);
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
        self.cur_fn = saved_fn;
        if let Some(b) = saved {
            self.builder.position_at_end(b);
        }
        f
    }

    /// Atomically decrement the reference count at `obj` (offset 0) and return the
    /// new count. The decrement is always atomic because an object shared across
    /// `spawn` threads is released from more than one thread, and each release
    /// must see the count the previous one left so that exactly one of them
    /// reclaims the object. A thread-exclusive object is only ever decremented on
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

    /// A memoized per-type deep-copy function `fn(*Header) -> *Header`. An
    /// aggregate (record, sum, tuple, array) is rebuilt with each managed field or
    /// element deep-copied (recursing through this same memoized table, so a
    /// self-referential type terminates); a string/closure is shared with its count
    /// raised. Used to pass a non-reference argument by value.
    pub(super) fn get_or_emit_deep_copy(&mut self, ty: &Type) -> FunctionValue<'ctx> {
        if let Some(helpers) = &self.helpers {
            let helper = helpers.borrow_mut().get_or_emit_deep_copy(ty);
            return self.declare_helper(helper);
        }
        let key = helper_key("dcopy", ty);
        if let Some(f) = self.deep_copy_fns.get(&key) {
            return *f;
        }
        let ptrt = self.abi.ptr();
        let fty = ptrt.fn_type(&[ptrt.into()], false);
        let (f, define) = self.helper_function(&key, fty);
        self.deep_copy_fns.insert(key, f);
        if !define {
            return f;
        }

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
            // A nullable cell: null copies to null; a present cell is rebuilt
            // around a deep copy of its value, so a `T?` field / `T?[]` element
            // copy shares no mutable storage with the original (sharing the cell
            // would let the copy see later reassignments through it).
            Type::Nullable(inner) => {
                let slot = self.builder.build_alloca(ptrt, "ncopy").unwrap();
                self.builder.build_store(slot, ptrt.const_null()).unwrap();
                let live = self.ctx.append_basic_block(f, "nn");
                let done = self.ctx.append_basic_block(f, "nn_done");
                let is_null = self.builder.build_is_null(obj, "isnull").unwrap();
                self.builder
                    .build_conditional_branch(is_null, done, live)
                    .unwrap();
                self.builder.position_at_end(live);
                let llty = self.abi.typed_basic(inner);
                let v = self
                    .builder
                    .build_load(llty, self.field_ptr(obj, 16), "nv")
                    .unwrap();
                let copied = self.deep_copy(v, inner);
                // The fresh cell takes over the copy's reference (nothing else
                // drops it), so no retain -- the cell's destructor releases it.
                let cell = self.nullable_cell_owning(copied, inner);
                self.builder.build_store(slot, cell).unwrap();
                self.builder.build_unconditional_branch(done).unwrap();
                self.builder.position_at_end(done);
                self.builder.build_load(ptrt, slot, "ncopy").unwrap()
            }
            Type::Slice(_) | Type::Array(..) => {
                let elem = brass_engine::element_type(ty);
                let (esize, _) = type_size_align(&elem);
                // A managed element is copied through its own deep-copy function
                // (recursing for nesting); a scalar element is copied byte-wise.
                let copy_fn = if brass_engine::rc_managed(&elem) {
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
                let copied = self
                    .builder
                    .build_call(
                        df,
                        &[obj.into(), self.i64c(esize as i64).into(), copy_fn.into()],
                        "arrdcopy",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                self.register_for_gc(copied, ty);
                copied
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
}
