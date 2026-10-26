//! `==` on the LLVM back end: the shared structural definition of
//! [`brass_engine::equality_kind`] emitted as IR.
//!
//! Scalars and strings compare inline. Every heap-represented kind (nullable
//! cell, record, sum, array, tuple) compares through one memoized helper per
//! concrete type, `bool(ptr, ptr)`, registered before its body is emitted so a
//! recursive type's comparison recurses through a call. Each helper first
//! answers equal for two handles to one object and unequal when exactly one
//! side is null, then compares the contents, stopping at the first difference.

use inkwell::IntPredicate;
use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};

use brass_engine::EqualityKind;
use brass_hir::Type;
use brass_parser::ast::BinOp;

use super::aggregate::elem_of;
use super::{LlvmCodegen, helper_key};

impl<'ctx, 'p> LlvmCodegen<'ctx, 'p> {
    /// The `==` result of two values of the concrete type `ty`.
    pub(super) fn equality_value(
        &mut self,
        a: BasicValueEnum<'ctx>,
        b: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> IntValue<'ctx> {
        let ty = brass_engine::strip_wrappers(ty);
        match brass_engine::equality_kind(ty) {
            EqualityKind::Scalar => {
                if a.get_type() != b.get_type() || !a.is_int_value() {
                    return self.mismatched_equality(ty);
                }
                self.builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        a.into_int_value(),
                        b.into_int_value(),
                        "eq",
                    )
                    .unwrap()
            }
            EqualityKind::Float => {
                if a.get_type() != b.get_type() || !a.is_float_value() {
                    return self.mismatched_equality(ty);
                }
                self.builder
                    .build_float_compare(
                        inkwell::FloatPredicate::OEQ,
                        a.into_float_value(),
                        b.into_float_value(),
                        "eq",
                    )
                    .unwrap()
            }
            EqualityKind::Str => self.str_bin_op(BinOp::Eq, a, b).into_int_value(),
            EqualityKind::Unit => self.ctx.bool_type().const_int(1, false),
            EqualityKind::Identity => {
                if !a.is_pointer_value() || !b.is_pointer_value() {
                    return self.mismatched_equality(ty);
                }
                self.pointers_equal(a.into_pointer_value(), b.into_pointer_value())
            }
            EqualityKind::Nullable
            | EqualityKind::Record
            | EqualityKind::Sum
            | EqualityKind::Sequence
            | EqualityKind::Tuple => {
                if !a.is_pointer_value() || !b.is_pointer_value() {
                    return self.mismatched_equality(ty);
                }
                let (pa, pb) = (a.into_pointer_value(), b.into_pointer_value());
                self.heap_equality(pa, pb, ty)
            }
        }
    }

    /// `==` of two heap handles of type `ty`, with the identity and null
    /// answers inline so the common `x == null` / same-object comparisons do
    /// not call the helper.
    fn heap_equality(
        &mut self,
        a: PointerValue<'ctx>,
        b: PointerValue<'ctx>,
        ty: &Type,
    ) -> IntValue<'ctx> {
        let func = self.cur_fn.unwrap();
        let bool_t = self.ctx.bool_type();
        let start = self.builder.get_insert_block().unwrap();
        let check_null = self.ctx.append_basic_block(func, "eq_check_null");
        let deep = self.ctx.append_basic_block(func, "eq_deep");
        let done = self.ctx.append_basic_block(func, "eq_done");
        let identical = self.pointers_equal(a, b);
        self.builder
            .build_conditional_branch(identical, done, check_null)
            .unwrap();
        self.builder.position_at_end(check_null);
        let either_null = self.either_null(a, b);
        self.builder
            .build_conditional_branch(either_null, done, deep)
            .unwrap();
        self.builder.position_at_end(deep);
        let helper = self.get_or_emit_equality(ty);
        let contents = self
            .call_basic(helper, &[a.into(), b.into()])
            .into_int_value();
        let deep_end = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(done).unwrap();
        self.builder.position_at_end(done);
        let phi = self.builder.build_phi(bool_t, "eq").unwrap();
        phi.add_incoming(&[
            (&bool_t.const_int(1, false), start),
            (&bool_t.const_zero(), check_null),
            (&contents, deep_end),
        ]);
        phi.as_basic_value().into_int_value()
    }

    /// The memoized content comparison helper `bool(ptr, ptr)` of one heap
    /// type: equal for the same object, unequal when exactly one side is null,
    /// otherwise the per-kind comparison of the contents.
    fn get_or_emit_equality(&mut self, ty: &Type) -> FunctionValue<'ctx> {
        if let Some(helpers) = &self.helpers {
            let helper = helpers.borrow_mut().get_or_emit_equality(ty);
            return self.declare_helper(helper);
        }
        let key = helper_key("eq", ty);
        if let Some(f) = self.equality_fns.get(&key) {
            return *f;
        }
        let ptr = self.abi.ptr();
        let fty = self
            .ctx
            .bool_type()
            .fn_type(&[ptr.into(), ptr.into()], false);
        let (f, define) = self.helper_function(&key, fty);
        self.equality_fns.insert(key, f);
        if !define {
            return f;
        }

        let saved_block = self.builder.get_insert_block();
        let saved_fn = self.cur_fn;
        self.cur_fn = Some(f);
        let entry = self.ctx.append_basic_block(f, "entry");
        let same = self.ctx.append_basic_block(f, "same");
        let check_null = self.ctx.append_basic_block(f, "check_null");
        let differ = self.ctx.append_basic_block(f, "differ");
        let compare = self.ctx.append_basic_block(f, "compare");
        self.builder.position_at_end(entry);
        let a = f.get_nth_param(0).unwrap().into_pointer_value();
        let b = f.get_nth_param(1).unwrap().into_pointer_value();
        let identical = self.pointers_equal(a, b);
        self.builder
            .build_conditional_branch(identical, same, check_null)
            .unwrap();
        self.builder.position_at_end(same);
        self.builder
            .build_return(Some(&self.ctx.bool_type().const_int(1, false)))
            .unwrap();
        self.builder.position_at_end(check_null);
        let either_null = self.either_null(a, b);
        self.builder
            .build_conditional_branch(either_null, differ, compare)
            .unwrap();
        self.builder.position_at_end(differ);
        self.builder
            .build_return(Some(&self.ctx.bool_type().const_zero()))
            .unwrap();
        self.builder.position_at_end(compare);
        self.emit_contents_equality(a, b, ty, differ);
        self.builder
            .build_return(Some(&self.ctx.bool_type().const_int(1, false)))
            .unwrap();

        self.cur_fn = saved_fn;
        if let Some(block) = saved_block {
            self.builder.position_at_end(block);
        }
        f
    }

    /// Emit the comparison of two distinct non-null objects of type `ty` at
    /// the current position: every difference branches to `differ`, and the
    /// emission ends positioned where the contents are known to be equal.
    fn emit_contents_equality(
        &mut self,
        a: PointerValue<'ctx>,
        b: PointerValue<'ctx>,
        ty: &Type,
        differ: inkwell::basic_block::BasicBlock<'ctx>,
    ) {
        match ty {
            // A present cell holds its value at offset 16.
            Type::Nullable(inner) => {
                let llty = self.abi.typed_basic(inner);
                let av = self.load_at(a, 16, llty, "na");
                let bv = self.load_at(b, 16, llty, "nb");
                self.require_equal(av, bv, inner, differ);
            }
            Type::Record(n) => {
                let Some(fields) = self.record_fields(n) else {
                    self.internal_error(&format!("record `{}` has no layout to compare", n.name));
                    return;
                };
                for (_, fty, offset) in fields {
                    let llty = self.abi.typed_basic(&fty);
                    let av = self.load_at(a, offset, llty, "af");
                    let bv = self.load_at(b, offset, llty, "bf");
                    self.require_equal(av, bv, &fty, differ);
                }
            }
            Type::Sum(n) => self.emit_sum_equality(a, b, n, differ),
            Type::Slice(_) | Type::Array(..) => self.emit_sequence_equality(a, b, ty, differ),
            Type::Tuple(elem_types) => {
                let (layout, _) = self.tuple_layout(elem_types);
                for ((llty, offset), ety) in layout.into_iter().zip(elem_types) {
                    let av = self.load_at(a, offset, llty, "ta");
                    let bv = self.load_at(b, offset, llty, "tb");
                    self.require_equal(av, bv, ety, differ);
                }
            }
            other => {
                self.internal_error(&format!("no structural equality for `{}`", other.display()))
            }
        }
    }

    /// Sum contents: the tags first, then the active variant's payload fields.
    /// A variant whose payload has no resolvable layout (an opaque,
    /// never-accessed field) compares by tag alone, as on the interpreter.
    fn emit_sum_equality(
        &mut self,
        a: PointerValue<'ctx>,
        b: PointerValue<'ctx>,
        n: &brass_hir::NominalType,
        differ: inkwell::basic_block::BasicBlock<'ctx>,
    ) {
        let func = self.cur_fn.unwrap();
        let i32t = self.ctx.i32_type();
        let tag_a = self.load_at(a, 16, i32t.into(), "tag_a").into_int_value();
        let tag_b = self.load_at(b, 16, i32t.into(), "tag_b").into_int_value();
        let same_tag = self
            .builder
            .build_int_compare(IntPredicate::EQ, tag_a, tag_b, "same_tag")
            .unwrap();
        let by_variant = self.ctx.append_basic_block(func, "eq_variant");
        self.builder
            .build_conditional_branch(same_tag, by_variant, differ)
            .unwrap();
        self.builder.position_at_end(by_variant);
        let variants = self.sum_variant_fields(n);
        let equal = self.ctx.append_basic_block(func, "eq_variant_equal");
        let mut cases = Vec::with_capacity(variants.len());
        for (tag, _, fields) in variants {
            let case = self.ctx.append_basic_block(func, "eq_variant_case");
            cases.push((i32t.const_int(tag as u64, true), case));
            let resume = self.builder.get_insert_block().unwrap();
            self.builder.position_at_end(case);
            for (_, fty, offset) in fields {
                let llty = self.abi.typed_basic(&fty);
                let av = self.load_at(a, offset, llty, "va");
                let bv = self.load_at(b, offset, llty, "vb");
                self.require_equal(av, bv, &fty, differ);
            }
            self.builder.build_unconditional_branch(equal).unwrap();
            self.builder.position_at_end(resume);
        }
        self.builder.build_switch(tag_a, equal, &cases).unwrap();
        self.builder.position_at_end(equal);
    }

    /// Array contents: the lengths, then each element in order.
    fn emit_sequence_equality(
        &mut self,
        a: PointerValue<'ctx>,
        b: PointerValue<'ctx>,
        ty: &Type,
        differ: inkwell::basic_block::BasicBlock<'ctx>,
    ) {
        let func = self.cur_fn.unwrap();
        let i64t = self.abi.i64t();
        let elem_ty = elem_of(ty);
        let elem_llty = self.abi.typed_basic(&elem_ty);
        let len_a = self.load_at(a, 16, i64t.into(), "len_a").into_int_value();
        let len_b = self.load_at(b, 16, i64t.into(), "len_b").into_int_value();
        let same_len = self
            .builder
            .build_int_compare(IntPredicate::EQ, len_a, len_b, "same_len")
            .unwrap();
        let pre = self.builder.get_insert_block().unwrap();
        let head = self.ctx.append_basic_block(func, "eq_elem_head");
        let body = self.ctx.append_basic_block(func, "eq_elem_body");
        let done = self.ctx.append_basic_block(func, "eq_elem_done");
        self.builder
            .build_conditional_branch(same_len, head, differ)
            .unwrap();
        self.builder.position_at_end(head);
        let index = self.builder.build_phi(i64t, "i").unwrap();
        index.add_incoming(&[(&i64t.const_zero(), pre)]);
        let i = index.as_basic_value().into_int_value();
        let more = self
            .builder
            .build_int_compare(IntPredicate::ULT, i, len_a, "more")
            .unwrap();
        self.builder
            .build_conditional_branch(more, body, done)
            .unwrap();
        self.builder.position_at_end(body);
        let ea = self.elem_ptr(a, elem_llty, i);
        let eb = self.elem_ptr(b, elem_llty, i);
        let av = self.builder.build_load(elem_llty, ea, "ea").unwrap();
        let bv = self.builder.build_load(elem_llty, eb, "eb").unwrap();
        self.require_equal(av, bv, &elem_ty, differ);
        let next = self
            .builder
            .build_int_add(i, i64t.const_int(1, false), "next")
            .unwrap();
        let latch = self.builder.get_insert_block().unwrap();
        index.add_incoming(&[(&next, latch)]);
        self.builder.build_unconditional_branch(head).unwrap();
        self.builder.position_at_end(done);
    }

    /// Compare two values of `ty` and branch to `differ` when they are not
    /// equal; emission continues in the block where they are.
    fn require_equal(
        &mut self,
        a: BasicValueEnum<'ctx>,
        b: BasicValueEnum<'ctx>,
        ty: &Type,
        differ: inkwell::basic_block::BasicBlock<'ctx>,
    ) {
        let equal = self.equality_value(a, b, ty);
        let func = self.cur_fn.unwrap();
        let next = self.ctx.append_basic_block(func, "eq_next");
        self.builder
            .build_conditional_branch(equal, next, differ)
            .unwrap();
        self.builder.position_at_end(next);
    }

    /// Load a value of representation `llty` at byte `offset` of an object.
    fn load_at(
        &self,
        base: PointerValue<'ctx>,
        offset: u64,
        llty: BasicTypeEnum<'ctx>,
        name: &str,
    ) -> BasicValueEnum<'ctx> {
        self.builder
            .build_load(llty, self.field_ptr(base, offset), name)
            .unwrap()
    }

    /// Whether two handles are the same object (or both null).
    fn pointers_equal(&self, a: PointerValue<'ctx>, b: PointerValue<'ctx>) -> IntValue<'ctx> {
        let i64t = self.abi.i64t();
        let pa = self.builder.build_ptr_to_int(a, i64t, "pa").unwrap();
        let pb = self.builder.build_ptr_to_int(b, i64t, "pb").unwrap();
        self.builder
            .build_int_compare(IntPredicate::EQ, pa, pb, "same")
            .unwrap()
    }

    /// Whether at least one of two handles is null.
    fn either_null(&self, a: PointerValue<'ctx>, b: PointerValue<'ctx>) -> IntValue<'ctx> {
        self.builder
            .build_or(
                self.builder.build_is_null(a, "anull").unwrap(),
                self.builder.build_is_null(b, "bnull").unwrap(),
                "either_null",
            )
            .unwrap()
    }

    /// The operands of a comparison do not have `ty`'s representation, which
    /// the front end never produces: stop with an internal error.
    fn mismatched_equality(&mut self, ty: &Type) -> IntValue<'ctx> {
        self.internal_error_value(
            &format!(
                "`==` operands do not have the representation of `{}`",
                ty.display()
            ),
            &Type::Bool,
        )
        .into_int_value()
    }
}
