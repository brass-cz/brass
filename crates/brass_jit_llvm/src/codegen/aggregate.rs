//! Heap object layouts and field access: the byte placement of record,
//! tuple, sum-variant and closure-environment contents after the object
//! header, nullable cells, and the loads/stores that address them.

use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValueEnum, IntValue, PointerValue};

use brass_engine::Codegen as EngineCodegen;
use brass_hir::{FloatKind, IntKind, NominalType, Type, TypeKind};

use super::{LlvmCodegen, is_traced};

/// Size and alignment (bytes) of a typed value in an object layout (record,
/// tuple, variant payload, closure environment, array element). Every heap
/// reference (string, record, sum, array, nullable cell, closure) is
/// pointer-sized.
pub(super) fn type_size_align(ty: &Type) -> (u64, u64) {
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

pub(super) fn align_up(offset: u64, align: u64) -> u64 {
    (offset + align - 1) & !(align - 1)
}

/// The byte offsets and total size of a closure environment: a function pointer at
/// offset 16, a capture-releasing destructor pointer at offset 24, then the
/// captured values packed (and aligned) from offset 32. The destructor slot is at
/// a fixed offset so a closure can be reclaimed knowing only its `Fun` type (which
/// hides the capture types). The same layout is used when building a closure and
/// when a closure instance reads its captures.
pub(super) fn closure_layout(capture_types: &[Type]) -> (Vec<u64>, u64) {
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
pub(super) fn elem_of(ty: &Type) -> Type {
    match ty {
        Type::Slice(e) | Type::Array(e, _) => (**e).clone(),
        _ => Type::Void,
    }
}

/// One record field's placement: its name, LLVM type, and byte offset.
type RecordFieldLayout<'ctx> = (String, BasicTypeEnum<'ctx>, u64);
/// One sum-variant field's placement: its name, type, and byte offset.
pub(super) type VariantFieldLayout = (String, Type, u64);
/// A lowered sum-variant field during code generation: source type, LLVM type,
/// and byte offset.
pub(super) type SumFieldLayout<'ctx> = (Type, BasicTypeEnum<'ctx>, u64);

impl<'ctx, 'p> LlvmCodegen<'ctx, 'p> {
    /// A tuple's `(LLVM element type, byte offset)` per element and its total
    /// object size: the 16-byte header followed by each element at its naturally
    /// aligned offset, in position order (a record's field layout keyed by
    /// position), the size rounded up to a multiple of 8.
    pub(super) fn tuple_layout(
        &self,
        elem_types: &[Type],
    ) -> (Vec<(BasicTypeEnum<'ctx>, u64)>, u64) {
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

    /// The byte layout of a record instance: `(field name, LLVM type, byte
    /// offset)` for each field of [`Self::record_fields`] (in order after the
    /// 16-byte header, naturally aligned) plus the total object size, rounded up
    /// to a multiple of 8. `None` for a non-record type or an unavailable layout.
    pub(super) fn record_layout(
        &self,
        record_ty: &Type,
    ) -> Option<(Vec<RecordFieldLayout<'ctx>>, u64)> {
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
    /// non-record type or an unavailable layout. The field decision -- which
    /// fields, in what order, at what types -- comes from
    /// [`brass_engine::render_record_fields`], the shared authority both back
    /// ends' renderers resolve fields through, so a record renders identically
    /// here and on the REPL interpreter. This adds the byte placement: fields
    /// laid out in list order after the 16-byte header, naturally aligned.
    pub(super) fn record_fields(&self, n: &NominalType) -> Option<Vec<(String, Type, u64)>> {
        let pairs = brass_engine::render_record_fields(self.program, n)?;
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
    pub(super) fn field_ptr(&self, base: PointerValue<'ctx>, offset: u64) -> PointerValue<'ctx> {
        unsafe {
            self.builder
                .build_in_bounds_gep(self.ctx.i8_type(), base, &[self.i64c(offset as i64)], "fp")
                .unwrap()
        }
    }

    /// A pointer to element `idx` of a growable array: the element buffer is a
    /// separate allocation held in the data slot at byte offset 32, its elements
    /// packed by their LLVM type's stride. The index is not bounds-checked.
    pub(super) fn elem_ptr(
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
    pub(super) fn nullable_wrap(
        &mut self,
        v: BasicValueEnum<'ctx>,
        inner: &Type,
    ) -> BasicValueEnum<'ctx> {
        let base = self.nullable_cell_owning(v, inner);
        // The cell now holds a reference to its value; retain it (the cell's
        // destructor releases it) so the value lives as long as the cell. This also
        // makes a `next: Node?` self-cycle a real cycle (the node's count stays above
        // zero), which the cycle collector -- not reference counting -- reclaims.
        if is_traced(inner) {
            self.retain(v);
        }
        base
    }

    /// Allocate a nullable cell around `v` *without* retaining it: the cell takes
    /// over the caller's reference (used where `v` is a fresh value nothing else
    /// drops, e.g. a deep copy). [`nullable_wrap`] adds the retain for the aliased
    /// case.
    pub(super) fn nullable_cell_owning(
        &mut self,
        v: BasicValueEnum<'ctx>,
        inner: &Type,
    ) -> BasicValueEnum<'ctx> {
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
        // A nullable cell wrapping a heap reference can be a cycle link (e.g. a
        // `next: Node?` field), so register it with the cycle collector.
        self.register_for_gc(base.into(), &Type::Nullable(Box::new(inner.clone())));
        base.into()
    }

    /// Read the value out of a nullable cell (narrowing). The cell is null-checked
    /// first and a null cell yields the target type's zero value (a null pointer
    /// for a managed target, 0 for a scalar): the source-level null test that
    /// guards a narrowed use is not visible to this coercion, so the unwrap is
    /// kept defined on every path.
    pub(super) fn nullable_unwrap(
        &mut self,
        v: BasicValueEnum<'ctx>,
        to: &Type,
    ) -> BasicValueEnum<'ctx> {
        let llty = self.abi.typed_basic(to);
        let f = self.cur_fn.unwrap();
        let cell = v.into_pointer_value();
        let entry = self.builder.get_insert_block().unwrap();
        let load_bb = self.ctx.append_basic_block(f, "nv_load");
        let done_bb = self.ctx.append_basic_block(f, "nv_done");
        let is_null = self.builder.build_is_null(cell, "nv_isnull").unwrap();
        self.builder
            .build_conditional_branch(is_null, done_bb, load_bb)
            .unwrap();
        self.builder.position_at_end(load_bb);
        let p = self.field_ptr(cell, 16);
        let loaded = self.builder.build_load(llty, p, "nv").unwrap();
        self.builder.build_unconditional_branch(done_bb).unwrap();
        self.builder.position_at_end(done_bb);
        let phi = self.builder.build_phi(llty, "nv_phi").unwrap();
        // `typed_basic` only produces int/float/pointer representations.
        let zero: BasicValueEnum<'ctx> = match llty {
            BasicTypeEnum::IntType(t) => t.const_zero().into(),
            BasicTypeEnum::FloatType(t) => t.const_zero().into(),
            _ => llty.into_pointer_type().const_null().into(),
        };
        phi.add_incoming(&[(&zero, entry), (&loaded, load_bb)]);
        phi.as_basic_value()
    }

    /// The concrete type of a sum variant's field: a `Result`-style generic sum
    /// carries its payloads in the nominal substitution (keyed `Variant.field`),
    /// overriding the HIR's (possibly generic) declared type. Used for sizing
    /// ([`sum_total_size`] counts an unresolvable field as an opaque `void` slot);
    /// the per-variant layout itself resolves fields through
    /// [`brass_engine::render_variant_fields`] in [`variant_layout`].
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
    /// The field decision comes from [`brass_engine::render_variant_fields`],
    /// the shared authority both back ends' renderers resolve fields through;
    /// this adds the byte placement.
    pub(super) fn variant_layout(
        &self,
        n: &NominalType,
        variant: &str,
    ) -> Option<(i32, Vec<VariantFieldLayout>)> {
        let (tag, pairs) = brass_engine::render_variant_fields(self.program, n, variant)?;
        let mut offset = 24u64; // header(16) + i32 tag(@16) + pad
        let mut out = Vec::with_capacity(pairs.len());
        for (name, fty) in pairs {
            let (size, align) = type_size_align(&fty);
            offset = align_up(offset, align);
            out.push((name, fty, offset));
            offset += size;
        }
        Some((tag, out))
    }

    /// Total size of a sum object: the header+tag prefix plus the largest
    /// variant payload.
    pub(super) fn sum_total_size(&self, n: &NominalType) -> u64 {
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

    /// The `(tag, type, byte offset)` of sum field `field` in each variant that
    /// declares it: a variant-qualified field (`Variant.field`, from a variant
    /// pattern binding) yields that variant's slot only, a bare field common to
    /// several variants one slot per variant (the offsets can differ when the
    /// field is preceded by different-sized fields).
    fn sum_field_slots(&self, n: &NominalType, field: &str) -> Vec<(i32, Type, u64)> {
        let (want_variant, fname) = match field.split_once('.') {
            Some((v, f)) => (Some(v), f),
            None => (None, field),
        };
        let names: Vec<String> = match self.program.type_by_id(n.id).map(|i| &i.kind) {
            Some(TypeKind::Sum { variants }) => variants.iter().map(|v| v.name.clone()).collect(),
            _ => return Vec::new(),
        };
        names
            .iter()
            .filter(|name| want_variant.is_none_or(|w| w == name.as_str()))
            .filter_map(|name| {
                let (tag, layout) = self.variant_layout(n, name)?;
                layout
                    .into_iter()
                    .find(|(slot, _, _)| slot == fname)
                    .map(|(_, fty, offset)| (tag, fty, offset))
            })
            .collect()
    }

    /// Read a field from a sum value through its [`sum_field_slots`]: a direct
    /// load when every variant holds the field at the same offset (the common
    /// case), otherwise a load dispatched on the runtime tag.
    pub(super) fn load_sum_field(
        &mut self,
        base: BasicValueEnum<'ctx>,
        n: &NominalType,
        field: &str,
    ) -> BasicValueEnum<'ctx> {
        let entries = self.sum_field_slots(n, field);
        let Some((_, fty0, off0)) = entries.first().cloned() else {
            return self.internal_error_value(
                &format!("sum `{}` has no field `{field}` to read", n.name),
                &Type::Void,
            );
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

    /// Write a field of a sum value through its [`sum_field_slots`]: a field
    /// common to every variant is stored at the active variant's slot -- a
    /// direct store when the offset is the same in every variant, otherwise a
    /// store dispatched on the runtime tag.
    pub(super) fn store_sum_field(
        &mut self,
        base: BasicValueEnum<'ctx>,
        n: &NominalType,
        field: &str,
        v: BasicValueEnum<'ctx>,
    ) {
        let entries = self.sum_field_slots(n, field);
        let Some((_, fty0, off0)) = entries.first().cloned() else {
            return self
                .internal_error(&format!("sum `{}` has no field `{field}` to write", n.name));
        };
        if v.get_type() != self.abi.typed_basic(&fty0) {
            return self.internal_error(&format!(
                "a value of the wrong representation was written to field `{field}` of `{}`",
                n.name
            ));
        }
        let basep = base.into_pointer_value();
        if entries.iter().all(|(_, _, off)| *off == off0) {
            let fp = self.field_ptr(basep, off0);
            self.builder.build_store(fp, v).unwrap();
            return;
        }
        let f = self.cur_fn.unwrap();
        let i32t = self.ctx.i32_type();
        let tag = self
            .builder
            .build_load(i32t, self.field_ptr(basep, 16), "tag")
            .unwrap()
            .into_int_value();
        let merge = self.ctx.append_basic_block(f, "sumst_merge");
        let mut switch_cases = Vec::with_capacity(entries.len());
        for (tag_v, _, offset) in &entries {
            let bb = self.ctx.append_basic_block(f, "sumst_case");
            switch_cases.push((i32t.const_int(*tag_v as u64, true), bb));
            let saved = self.builder.get_insert_block().unwrap();
            self.builder.position_at_end(bb);
            self.builder
                .build_store(self.field_ptr(basep, *offset), v)
                .unwrap();
            self.builder.build_unconditional_branch(merge).unwrap();
            self.builder.position_at_end(saved);
        }
        // Every variant declares a common field, so the default is unreachable
        // for a well-formed value.
        let default = self.ctx.append_basic_block(f, "sumst_default");
        self.builder
            .build_switch(tag, default, &switch_cases)
            .unwrap();
        self.builder.position_at_end(default);
        self.builder.build_unreachable().unwrap();
        self.builder.position_at_end(merge);
    }

    /// `(field name, concrete type, byte offset)` for each record field (for the
    /// renderer and the deep copy), or empty when the type has no record layout.
    /// See [`record_fields`].
    pub(super) fn record_field_types(&self, n: &NominalType) -> Vec<(String, Type, u64)> {
        self.record_fields(n).unwrap_or_default()
    }

    /// `(tag, variant name, [(field name, type, offset)])` for each variant of a
    /// sum, sharing [`variant_layout`]'s payload offsets.
    pub(super) fn sum_variant_fields(
        &self,
        n: &NominalType,
    ) -> Vec<(i32, String, Vec<VariantFieldLayout>)> {
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
}
