//! Per-type `to_string` renderers for records and sums: `T { field: .. }`
//! and `T.Variant { .. }` built from each field's own rendering, memoized
//! per concrete type so a self-referential type recurses through a call.

use inkwell::values::{BasicValueEnum, FunctionValue, PointerValue};

use brass_engine::Codegen as EngineCodegen;
use brass_hir::Type;

use super::aggregate::VariantFieldLayout;
use super::{LlvmCodegen, helper_key};

impl<'ctx, 'p> LlvmCodegen<'ctx, 'p> {
    /// Effective debug returns an owned string, including quoted string leaves.
    /// The shared resolver selects nominal methods; builtin children recurse here.
    pub(super) fn effective_debug(
        &mut self,
        v: BasicValueEnum<'ctx>,
        ty: &Type,
    ) -> BasicValueEnum<'ctx> {
        if let Type::Nullable(inner) = ty {
            let f = self.cur_fn.unwrap();
            let some = self.ctx.append_basic_block(f, "debug_some");
            let none = self.ctx.append_basic_block(f, "debug_none");
            let join = self.ctx.append_basic_block(f, "debug_join");
            let present = self
                .builder
                .build_is_not_null(v.into_pointer_value(), "present")
                .unwrap();
            self.builder
                .build_conditional_branch(present, some, none)
                .unwrap();
            self.builder.position_at_end(some);
            let value = self.nullable_unwrap(v, inner);
            let text = self.effective_debug(value, inner);
            let end = self.builder.get_insert_block().unwrap();
            self.builder.build_unconditional_branch(join).unwrap();
            self.builder.position_at_end(none);
            let null = self.const_str("null");
            self.builder.build_unconditional_branch(join).unwrap();
            self.builder.position_at_end(join);
            let phi = self
                .builder
                .build_phi(self.abi.ptr(), "debug_text")
                .unwrap();
            phi.add_incoming(&[(&text, end), (&null, none)]);
            return phi.as_basic_value();
        }
        if let Some(symbol) = brass_engine::render::resolve_renderer(
            self.program,
            ty,
            brass_engine::render::RenderForm::Debug,
        ) {
            return self.call(&symbol, &[v], &Type::Str);
        }
        if matches!(ty, Type::Str) {
            return self.str_debug(v);
        }
        self.to_string(v, ty)
    }

    /// A memoized per-type `to_string` renderer for a record or sum. A record
    /// renders as `T {\n    field: <value>,\n}` and a sum as
    /// `T.Variant {\n    field: <value>,\n}` (a field-less variant as bare
    /// `T.Variant`), with each field rendered through effective debug so nested
    /// records/sums/scalars honor their structural or custom form. Registered before its body is
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
            let rendered = self.effective_debug(fv, fty);
            let fs = self.str_indent(rendered);
            self.release(rendered);
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
