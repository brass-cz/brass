//! Per-type `to_string` renderers for records and sums: `T { field: .. }`
//! and `T.Variant { .. }` built from each field's own rendering, memoized
//! per concrete type so a self-referential type recurses through a call.

use inkwell::values::{BasicValueEnum, FunctionValue, PointerValue};

use brass_engine::Codegen as EngineCodegen;
use brass_hir::Type;

use super::aggregate::VariantFieldLayout;
use super::{LlvmCodegen, helper_key, rendered_string_is_owned};

impl<'ctx, 'p> LlvmCodegen<'ctx, 'p> {
    /// A memoized per-type `to_string` renderer for a record or sum. A record
    /// renders as `T {\n    field: <value>,\n}` and a sum as
    /// `T.Variant {\n    field: <value>,\n}` (a field-less variant as bare
    /// `T.Variant`), with each field rendered by [`to_string`] so nested
    /// records/sums/scalars format recursively. Registered before its body is
    /// emitted so a self-referential type (e.g. a field of its own type) recurses
    /// through the call rather than re-entering code generation.
    pub(super) fn get_or_emit_to_string(&mut self, ty: &Type) -> FunctionValue<'ctx> {
        if let Some(helpers) = &self.helpers {
            let helper = helpers.borrow_mut().get_or_emit_to_string(ty);
            return self.declare_helper(helper);
        }
        let key = helper_key("tostr", ty);
        if let Some(f) = self.to_string_fns.get(&key) {
            return *f;
        }
        let fty = self.abi.ptr().fn_type(&[self.abi.ptr().into()], false);
        let (f, define) = self.helper_function(&key, fty);
        self.to_string_fns.insert(key, f);
        if !define {
            return f;
        }

        // Gather the shape up front so the `program` borrow ends before the
        // recursive field renderings below (which borrow `self` mutably).
        let record = match ty {
            // A structural record (anonymous structure / `T.from` result) renders
            // under the `anonymous` label rather than its internal `<structural>`.
            Type::Record(n) => {
                let header = if n.id == brass_hir::STRUCTURAL_RECORD_ID {
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

    /// The quoted, escaped debug form of the string `s` (a new string), the way
    /// a string field renders inside a record or variant.
    fn str_debug(&self, s: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        self.call_rt_ptr("pp_str_debug", &[s])
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
        let mut acc_owned = false;
        for (fname, fty, offset) in fields {
            // A string-typed field value renders in its quoted, escaped debug
            // form, so the struct output distinguishes the string "1" from the
            // number 1 (and shows empty strings at all). A nullable string
            // quotes only when the value is present (`null` stays bare).
            let is_str = matches!(fty, Type::Str);
            let is_opt_str = matches!(fty, Type::Nullable(inner) if matches!(**inner, Type::Str));
            let prefix = self.const_str(&format!("    {fname}: "));
            let next = self.str_concat2(acc, prefix);
            if acc_owned {
                self.release(acc);
            }
            acc = next;
            acc_owned = true;
            let llty = self.abi.typed_basic(fty);
            let fp = self.field_ptr(obj, *offset);
            let fv = self.builder.build_load(llty, fp, "fld").unwrap();
            // Indent the field's rendering one level so a nested record/sum
            // (which is itself multi-line) sits under its label with deeper
            // indentation; a string renders on one line in its debug form.
            let (mut fs, rendered) = if is_str {
                (self.str_debug(fv), None)
            } else {
                let rendered = self.to_string(fv, fty);
                (self.str_indent(rendered), Some(rendered))
            };
            if is_opt_str {
                let f = self.cur_fn.unwrap();
                let ptrt = self.abi.ptr();
                let slot = self.builder.build_alloca(ptrt, "optstr").unwrap();
                self.builder.build_store(slot, fs).unwrap();
                let quote_bb = self.ctx.append_basic_block(f, "fld_quote");
                let done_bb = self.ctx.append_basic_block(f, "fld_done");
                let is_null = self
                    .builder
                    .build_is_null(fv.into_pointer_value(), "fldnull")
                    .unwrap();
                self.builder
                    .build_conditional_branch(is_null, done_bb, quote_bb)
                    .unwrap();
                self.builder.position_at_end(quote_bb);
                let present = rendered.expect("a nullable string field is rendered first");
                let quoted = self.str_debug(present);
                self.release(fs);
                self.builder.build_store(slot, quoted).unwrap();
                self.builder.build_unconditional_branch(done_bb).unwrap();
                self.builder.position_at_end(done_bb);
                fs = self.builder.build_load(ptrt, slot, "optstr_v").unwrap();
            }
            if let Some(rendered) = rendered
                && rendered_string_is_owned(fty)
            {
                self.release(rendered);
            }
            let next = self.str_concat2(acc, fs);
            self.release(acc);
            self.release(fs);
            acc = next;
            let comma = self.const_str(",\n");
            let next = self.str_concat2(acc, comma);
            self.release(acc);
            acc = next;
        }
        let close = self.const_str("}");
        let result = self.str_concat2(acc, close);
        self.release(acc);
        result
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
