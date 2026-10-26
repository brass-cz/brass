//! Precompilation of deferred targets before worker execution.

use super::{BodySpans, LazyState, resolve_deferred};
use brass_hir::Program;
use brass_parser::Span;
use fxhash::FxHashMap as HashMap;

/// Compile and prime EVERY recorded deferred target, to a fixpoint: called
/// when a batch containing `spawn` was compiled, before its code runs.
/// Spawned code executes on worker threads, which answer deferred calls only
/// from the cross-thread resolved cache; after this drain, every site any
/// worker could reach is in it. False aborts the run (a target's check or
/// compilation failed -- `resolve_deferred` reported it).
#[allow(clippy::too_many_arguments)] // the execution-side state is one bundle
pub(super) fn drain_targets_for_spawn(
    backend: &mut brass_jit_llvm::LlvmCodegen,
    program: &Program,
    tables: &brass_mir::LowerTables,
    call_locations: &HashMap<Span, (String, u32, u32)>,
    sources: &brass_resolve::SourceMap,
    bodies: &BodySpans,
    globals: &[(String, brass_hir::Type)],
    lowering: &mut brass_mir::SubsetLowering,
    lazy: &mut LazyState,
    targets: &mut HashMap<String, brass_engine::DeferredSig>,
) -> bool {
    loop {
        let mut pending: Vec<String> = targets
            .keys()
            .filter(|symbol| !backend.has_instance(symbol))
            .cloned()
            .collect();
        pending.sort();
        if pending.is_empty() {
            // Targets already defined in another batch still need their shared
            // deferred slots primed. Static bodies can cross batch boundaries,
            // so close the whole registered session before workers start.
            let mut symbols: Vec<_> = targets.keys().collect();
            symbols.sort();
            for symbol in symbols {
                let Some(address) = backend.address_of(symbol) else {
                    return false;
                };
                brass_jit_llvm::prime_resolved(symbol, address);
            }
            return match backend.materialize_all() {
                Ok(()) => true,
                Err(error) => {
                    eprintln!("error: worker materialization failed: {error}");
                    false
                }
            };
        }
        for symbol in pending {
            let addr = resolve_deferred(
                backend,
                &symbol,
                program,
                tables,
                call_locations,
                sources,
                bodies,
                globals,
                lowering,
                lazy,
                targets,
            );
            if addr == 0 {
                return false;
            }
            brass_jit_llvm::prime_resolved(&symbol, addr);
        }
    }
}
