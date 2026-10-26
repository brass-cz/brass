//! Callable closure targets and shared, signature-correct missing-instance diagnostics.

use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::values::FunctionValue;

use brass_hir::Type;

use super::LlvmCodegen;
use crate::monomorph::mangle_fn;

impl<'ctx, 'p> LlvmCodegen<'ctx, 'p> {
    /// Select a registered instance or a diagnostic function with the same closure ABI.
    pub(super) fn closure_target(
        &mut self,
        symbol: &str,
        params: &[Type],
        ret: &Type,
    ) -> FunctionValue<'ctx> {
        if let Some(function) = self.instance_fn(symbol) {
            debug_assert_eq!(
                function.get_type(),
                self.abi.typed_closure_fn_type(params, ret),
                "closure target ABI: {symbol}"
            );
            function
        } else {
            self.missing_closure_target(params, ret)
        }
    }

    /// Emit one non-returning diagnostic per LLVM closure signature, shared by lazy groups.
    fn missing_closure_target(&mut self, params: &[Type], ret: &Type) -> FunctionValue<'ctx> {
        if let Some(helpers) = &self.helpers {
            let function = helpers.borrow_mut().missing_closure_target(params, ret);
            return self.declare_helper(function);
        }
        let signature = self.abi.typed_closure_fn_type(params, ret);
        // LLVM's type spelling includes argument order, widths and return type.
        // Escaping it injectively keeps opaque-pointer ABIs shared without using
        // type display names or context-local addresses in object-cache inputs.
        let key = mangle_fn(&format!(
            "{}missing_closure:{}",
            brass_engine::SYNTH_SIGIL,
            signature.print_to_string()
        ));
        if let Some(function) = self.missing_closure_targets.get(&key) {
            return *function;
        }
        let (function, define) = self.helper_function(&key, signature);
        self.missing_closure_targets.insert(key, function);
        for name in ["cold", "noinline", "noreturn"] {
            let kind = Attribute::get_named_enum_kind_id(name);
            function.add_attribute(
                AttributeLoc::Function,
                self.ctx.create_enum_attribute(kind, 0),
            );
        }
        if define {
            let saved = self.builder.get_insert_block();
            let entry = self.ctx.append_basic_block(function, "entry");
            self.builder.position_at_end(entry);
            self.gen_panic("internal error: call of a closure that has no compiled instance");
            self.builder.build_unreachable().unwrap();
            if let Some(block) = saved {
                self.builder.position_at_end(block);
            } else {
                self.builder.clear_insertion_position();
            }
        }
        function
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use brass_hir::{FloatKind, IntKind, NominalType};
    use inkwell::context::Context;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn diagnostic_helpers_cover_each_abi_and_preserve_the_builder() {
        let (program, _) = brass_hir::lower(&[]);
        let context = Context::create();
        let mut codegen = LlvmCodegen::new_backend(&context, &program);
        let caller =
            codegen
                .module
                .add_function("caller", context.void_type().fn_type(&[], false), None);
        let block = context.append_basic_block(caller, "entry");
        codegen.builder.position_at_end(block);
        let mut types = vec![
            Type::Bool,
            Type::Float(FloatKind::F32),
            Type::Float(FloatKind::F64),
            Type::Str,
        ];
        types.extend(
            [
                IntKind::I8,
                IntKind::U8,
                IntKind::I16,
                IntKind::U16,
                IntKind::I32,
                IntKind::U32,
                IntKind::I64,
                IntKind::U64,
            ]
            .map(Type::Int),
        );
        types.extend([
            Type::Nullable(Box::new(Type::Int(IntKind::I32))),
            Type::Tuple(vec![Type::Bool]),
            Type::Fun(vec![], Box::new(Type::Void)),
            Type::Record(NominalType::new(42, "Record")),
            Type::Sum(NominalType::new(brass_hir::RESULT_TYPE_ID, "Result")),
        ]);
        // Vary both sides of the ABI, including signatures with mixed register classes.
        for ret in types.iter().chain(std::iter::once(&Type::Void)) {
            for params in [vec![], types.clone(), vec![ret.clone()]] {
                let helper = codegen.missing_closure_target(&params, ret);
                assert_eq!(
                    helper.get_type(),
                    codegen.abi.typed_closure_fn_type(&params, ret)
                );
                assert_eq!(helper, codegen.missing_closure_target(&params, ret));
                assert_eq!(codegen.builder.get_insert_block(), Some(block));
                assert_eq!(helper.count_basic_blocks(), 1);
                for name in ["cold", "noinline", "noreturn"] {
                    assert!(
                        helper
                            .get_enum_attribute(
                                AttributeLoc::Function,
                                Attribute::get_named_enum_kind_id(name)
                            )
                            .is_some()
                    );
                }
            }
        }
        codegen.builder.build_return(None).unwrap();
        codegen.mark_small_functions_alwaysinline();
        let alwaysinline = Attribute::get_named_enum_kind_id("alwaysinline");
        assert!(codegen.missing_closure_targets.values().all(|f| {
            f.get_enum_attribute(AttributeLoc::Function, alwaysinline)
                .is_none()
        }));
        codegen.module.verify().unwrap();
        // Nominally different pointer types share the exact same helper ABI.
        let pointer = codegen.missing_closure_target(&[Type::Str], &Type::Str);
        let tuple = Type::Tuple(vec![Type::Bool]);
        assert_eq!(
            pointer,
            codegen.missing_closure_target(std::slice::from_ref(&tuple), &tuple)
        );
        assert_ne!(
            pointer,
            codegen.missing_closure_target(&[Type::Str], &Type::Void)
        );
    }

    #[test]
    fn lazy_groups_and_later_batches_import_one_definition() {
        let (program, _) = brass_hir::lower(&[]);
        let context = Context::create();
        let mut owner = LlvmCodegen::new_backend(&context, &program);
        owner.previous_helpers = Some(Rc::default());
        let owner = Rc::new(RefCell::new(owner));
        let mut first = LlvmCodegen::new_backend(&context, &program);
        first.helpers = Some(owner.clone());
        let imported = first.missing_closure_target(&[Type::Bool], &Type::Void);
        assert_eq!(imported.count_basic_blocks(), 0);
        let name = imported.get_name().to_str().unwrap().to_owned();
        assert_eq!(
            owner
                .borrow()
                .module
                .get_function(&name)
                .unwrap()
                .count_basic_blocks(),
            1
        );
        let mut second = LlvmCodegen::new_backend(&context, &program);
        second.helpers = Some(owner.clone());
        assert_eq!(
            second
                .missing_closure_target(&[Type::Bool], &Type::Void)
                .get_name(),
            imported.get_name()
        );
        assert_eq!(owner.borrow().missing_closure_targets.len(), 1);
        // A later batch reserves the same stable symbol but emits no second body.
        let mut later = LlvmCodegen::new_backend(&context, &program);
        later.previous_helpers = Some(Rc::new([name.clone()].into_iter().collect()));
        let reused = later.missing_closure_target(&[Type::Bool], &Type::Void);
        assert_eq!(reused.get_name().to_str().unwrap(), name);
        assert_eq!(reused.count_basic_blocks(), 0);
        owner.borrow().module.verify().unwrap();
        first.module.verify().unwrap();
        second.module.verify().unwrap();
        later.module.verify().unwrap();
    }

    #[test]
    fn closure_creation_initializes_a_callable_slot_and_calls_have_no_guard() {
        use brass_engine::{Codegen, closure_symbol};
        use brass_mir::ClosureId;
        use inkwell::values::AnyValue;

        // Both a registered instance and a missing instance use the same mixed
        // closure ABI. Only the missing instance needs a diagnostic definition.
        for registered in [false, true] {
            let (program, _) = brass_hir::lower(&[]);
            let context = Context::create();
            let mut codegen = LlvmCodegen::new_backend(&context, &program);
            let params = vec![
                Type::Int(IntKind::I32),
                Type::Float(FloatKind::F64),
                Type::Str,
            ];
            let ret = Type::Int(IntKind::I64);
            let id = ClosureId(42);
            if registered {
                let symbol = mangle_fn(&closure_symbol(id, &[], &params));
                let target = codegen.module.add_function(
                    &symbol,
                    codegen.abi.typed_closure_fn_type(&params, &ret),
                    None,
                );
                codegen.fns.map.insert(symbol, target);
            }
            let caller = codegen.module.add_function(
                "caller",
                context.void_type().fn_type(&[], false),
                None,
            );
            codegen
                .builder
                .position_at_end(context.append_basic_block(caller, "entry"));
            let ty = Type::Fun(params, Box::new(ret));
            let closure = codegen.make_closure(&ty, id, None, &[]);
            codegen.call_indirect(
                closure,
                &ty,
                &[
                    context.i32_type().const_int(7, false).into(),
                    context.f64_type().const_float(2.5).into(),
                    context
                        .ptr_type(inkwell::AddressSpace::default())
                        .const_null()
                        .into(),
                ],
            );
            codegen.builder.build_return(None).unwrap();
            codegen.module.verify().unwrap();
            let ir = caller.print_to_string().to_string();
            let target_name = if registered {
                let Type::Fun(params, _) = &ty else {
                    unreachable!()
                };
                mangle_fn(&closure_symbol(id, &[], params))
            } else {
                codegen
                    .missing_closure_targets
                    .values()
                    .next()
                    .unwrap()
                    .get_name()
                    .to_str()
                    .unwrap()
                    .to_owned()
            };
            assert!(ir.contains(&format!("store ptr @{target_name},")), "{ir}");
            assert!(ir.contains("call i64 %"), "{ir}");
            assert!(!ir.contains("fp_missing"), "{ir}");
            assert_eq!(caller.count_basic_blocks(), 1, "{ir}");
            assert_eq!(
                codegen.missing_closure_targets.len(),
                usize::from(!registered)
            );
        }
    }
}
