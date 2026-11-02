//! Shared return cleanup, followed by each exit's original result construction.

use brass_engine::{Codegen, MonoFunction, return_owned_locals};
use brass_hir::Type;
use brass_mir::LocalId;
use inkwell::IntPredicate;
use inkwell::basic_block::BasicBlock;
use inkwell::values::PhiValue;

use super::LlvmCodegen;

/// Per-function cleanup state. The two phis select the moved-out local and the
/// continuation; local slots retain their values until that continuation returns.
pub(super) struct ReturnCleanup<'ctx> {
    block: BasicBlock<'ctx>,
    excluded: PhiValue<'ctx>,
    destination: PhiValue<'ctx>,
    continuations: Vec<BasicBlock<'ctx>>,
    locals: Vec<(LocalId, Type)>,
    returned: Vec<LocalId>,
}

impl<'ctx> LlvmCodegen<'ctx, '_> {
    /// Route an exit through one cleanup chain. Each path releases exactly the
    /// invocation-owned locals, in local order, except its moved-out operand.
    /// Borrowed-result retention stays before cleanup; operand evaluation,
    /// coercion and Result wrapping stay after it, in the original continuation.
    /// Cleanup IR grows with locals, not with locals times return sites.
    pub(super) fn emit_shared_return_cleanup(
        &mut self,
        f: &MonoFunction,
        returned: Option<LocalId>,
    ) {
        let source = self.builder.get_insert_block().unwrap();
        let function = self.cur_fn.unwrap();
        if self.mir.return_cleanup.is_none() {
            let locals: Vec<_> = return_owned_locals(f)
                .map(|id| (id, f.local_type(id).clone()))
                .collect();
            if locals.is_empty() {
                return;
            }
            let block = self.ctx.append_basic_block(function, "return_cleanup");
            self.builder.position_at_end(block);
            let excluded = self
                .builder
                .build_phi(self.ctx.i32_type(), "returned_local")
                .unwrap();
            let destination = self
                .builder
                .build_phi(self.ctx.i32_type(), "return_site")
                .unwrap();
            self.mir.return_cleanup = Some(ReturnCleanup {
                block,
                excluded,
                destination,
                continuations: Vec::new(),
                locals,
                returned: Vec::new(),
            });
            self.builder.position_at_end(source);
        }
        let cleanup = self.mir.return_cleanup.as_mut().unwrap();
        let continuation = self.ctx.append_basic_block(function, "after_cleanup");
        let index = self
            .ctx
            .i32_type()
            .const_int(cleanup.continuations.len() as u64, false);
        let excluded = self
            .ctx
            .i32_type()
            .const_int(returned.map_or(u32::MAX, |id| id.0) as u64, false);
        cleanup.destination.add_incoming(&[(&index, source)]);
        cleanup.excluded.add_incoming(&[(&excluded, source)]);
        cleanup.continuations.push(continuation);
        if let Some(id) = returned {
            cleanup.returned.push(id);
        }
        self.builder
            .build_unconditional_branch(cleanup.block)
            .unwrap();
        self.builder.position_at_end(continuation);
    }

    /// Complete the shared chain once all exits are known. Only locals actually
    /// returned need a conditional exclusion; all other releases remain straight
    /// line. The dispatch resumes result construction without re-running cleanup.
    pub(super) fn finish_return_cleanup(&mut self) {
        let Some(cleanup) = self.mir.return_cleanup.take() else {
            return;
        };
        let function = self.cur_fn.unwrap();
        self.builder.position_at_end(cleanup.block);
        for (id, ty) in cleanup.locals {
            let next = if cleanup.returned.contains(&id) {
                let release = self.ctx.append_basic_block(function, "return_release");
                let next = self.ctx.append_basic_block(function, "return_next");
                let excluded = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        cleanup.excluded.as_basic_value().into_int_value(),
                        self.ctx.i32_type().const_int(id.0 as u64, false),
                        "is_returned",
                    )
                    .unwrap();
                self.builder
                    .build_conditional_branch(excluded, next, release)
                    .unwrap();
                self.builder.position_at_end(release);
                Some(next)
            } else {
                None
            };
            let value = self.load_local(id);
            self.emit_release(value, &ty);
            if let Some(next) = next {
                self.builder.build_unconditional_branch(next).unwrap();
                self.builder.position_at_end(next);
            }
        }
        let cases: Vec<_> = cleanup
            .continuations
            .iter()
            .enumerate()
            .skip(1)
            .map(|(i, block)| (self.ctx.i32_type().const_int(i as u64, false), *block))
            .collect();
        self.builder
            .build_switch(
                cleanup.destination.as_basic_value().into_int_value(),
                cleanup.continuations[0],
                &cases,
            )
            .unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use brass_engine::monomorphize;
    use brass_hir::{LoadedModule, lower};
    use brass_mir::lower_program;
    use inkwell::context::Context;

    #[test]
    fn cleanup_release_sites_do_not_multiply_with_returns() {
        let mut counts = Vec::new();
        for exits in [2, 12] {
            let mut source =
                String::from("fun work(n: int32) -> int32 {\nlet a = string.from(n)\n");
            for i in 0..exits - 1 {
                source.push_str(&format!("if n == {i} {{ return {i} }}\n"));
            }
            source.push_str("return 99\n}\nfun main() { work(7) }\n");
            let (hir, errors) = lower(&[LoadedModule {
                source: None,
                is_prelude: false,
                path: vec!["main".into()],
                ast: brass_parser::parse(&source).unwrap(),
            }]);
            assert!(errors.is_empty());
            let mir = lower_program(&hir);
            let mono = monomorphize(&mir, &hir).unwrap();
            let ctx = Context::create();
            let mut backend = LlvmCodegen::new_backend(&ctx, &hir);
            backend.begin_program(&mono);
            backend.codegen_program(&mono);
            backend.module.verify().unwrap();
            let ir = backend.module.print_to_string().to_string();
            // Branches still select their original return value, but one cleanup
            // chain owns the releases regardless of how many exits reach it.
            assert_eq!(ir.matches("ret i32").count(), exits, "{ir}");
            counts.push(
                ir.lines()
                    .filter(|line| line.contains("call void @pp_release("))
                    .count(),
            );
        }
        assert!(counts[0] > 0);
        assert_eq!(counts[0], counts[1]);
    }
}
