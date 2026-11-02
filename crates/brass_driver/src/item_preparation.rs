//! Item selection and context preparation. Eager/check analyses consume
//! the selected request; streaming completes uncovered facts for its body schedule.

use brass_hir::{LoadedModule, LowerError, Program};
use brass_typeck::reachability::{AnalysisView, CheckSelection, ItemIndex, Reachability};

/// Core-only graphs use the complete context path: their bounded context cost is
/// smaller than constructing a selector. Any disk or plugin module disables this
/// shortcut, including local/package/include imports and explicitly loaded std.
pub(crate) fn has_dependencies(modules: &[LoadedModule]) -> bool {
    modules
        .iter()
        .take(modules.len().saturating_sub(1))
        .any(|module| !module.is_prelude)
}

/// Thread-local HIR and projected selection retained after ownership checking.
/// The driver and checker each own their HIR; its reference-counted bodies never
/// cross a thread boundary. Rewriting invalidates the HIR before it is retained.
pub(crate) struct Prepared {
    /// Final HIR and its declaration diagnostics, in source order.
    pub(crate) lowered: (Program, Vec<LowerError>),
    /// Selection projected onto this exact HIR.
    pub(crate) view: AnalysisView,
}

/// Select before ownership rewriting and retain the lowered graph. Inserted calls
/// require re-lowering and a new closure; unchanged bodies reuse the first graph.
#[cold]
pub(crate) fn front(
    modules: &mut [LoadedModule],
    sources: &brass_resolve::SourceMap,
    errors: &mut Vec<(String, brass_parser::Span)>,
    load_errors: Vec<(String, brass_parser::Span)>,
) -> Result<Box<Prepared>, Vec<String>> {
    let started = std::time::Instant::now();
    let (program, lower_errors) = brass_hir::lower(modules);
    brass_utils::perf_phase("item/pre-hir", started.elapsed());
    let started = std::time::Instant::now();
    #[cfg(jit_backend)]
    let rewritten;
    let mut index = ItemIndex::new(&program);
    let scope = super::item_shadow::project_scope(
        &modules
            .last()
            .expect("entry module")
            .source
            .as_ref()
            .expect("loaded entry provenance")
            .location,
    );
    let selection = Reachability::new(&index, &scope).into_selection();
    let view = AnalysisView::new(&program, selection, Default::default(), Default::default());
    let owners = brass_hir::diagnostics::DiagnosticOwners::new(&program);
    errors.retain(|(_, span)| view.reports(&owners.body_owner(*span)));
    let load_errors: Vec<_> = load_errors
        .into_iter()
        .filter(|(message, span)| {
            !message.starts_with("syntax error:")
                || sources.locate(span.lo).is_none_or(|p| {
                    view.reports(&owners.syntax_owner(*span, p.src, span.lo - p.local))
                })
        })
        .collect();
    if !load_errors.is_empty() {
        return Err(super::render_errors(&load_errors, sources));
    }
    brass_utils::perf_phase("item/pre-selection", started.elapsed());
    #[cfg(jit_backend)]
    {
        let (spawn_errors, warnings, may_rewrite) =
            super::auto_acquire_modules::<true>(modules, Some(&view));
        if spawn_errors.is_empty() {
            for warning in warnings {
                eprintln!("{warning}");
            }
        }
        errors.extend(spawn_errors);
        if may_rewrite {
            let started = std::time::Instant::now();
            rewritten = brass_hir::lower(modules);
            brass_utils::perf_phase("item/rewrite-hir", started.elapsed());
            let started = std::time::Instant::now();
            index.refresh_bodies(&rewritten.0);
            let selection = Reachability::new(&index, &scope).into_selection();
            brass_utils::perf_phase("item/rewrite-selection", started.elapsed());
            let view = AnalysisView::new(
                &rewritten.0,
                selection,
                Default::default(),
                Default::default(),
            );
            return Ok(Box::new(Prepared {
                lowered: rewritten,
                view,
            }));
        }
    }
    Ok(Box::new(Prepared {
        lowered: (program, lower_errors),
        view,
    }))
}

/// Prepare only requested context returns and co-checks. Dirty module/importer
/// invalidation and storage-identity collision fallback remain authoritative.
pub(crate) fn context_seed(
    ctx: &[LoadedModule],
    sources: &brass_resolve::SourceMap,
    selection: &std::sync::Arc<CheckSelection>,
) -> Option<brass_typeck::ContextTables> {
    let started = std::time::Instant::now();
    let (program, errors) = brass_hir::lower_context(ctx);
    let view = AnalysisView::with_selection(
        &program,
        selection.clone(),
        Default::default(),
        Default::default(),
    );
    let analysis = brass_typeck::prepare_context(&program, &view);
    let spans = errors
        .iter()
        .map(|e| e.span)
        .chain(analysis.errors.iter().map(|e| e.span));
    let seed = super::retain_diagnostic_free_context(
        ctx,
        sources,
        &program,
        analysis.context_tables,
        spans,
    );
    if let Some(items) = seed.as_ref().and_then(|seed| seed.items.as_ref()) {
        tracing::debug!(target: "brass::item_preparation", returns = items.coverage.returns.len(), co_checks = items.coverage.co_checks.len(), bodies = items.coverage.bodies.len(), schemes = items.shared.schemes.len(), initializers = items.shared.initializers.len(), "item: context coverage");
    }
    brass_utils::perf_phase("front/context-check", started.elapsed());
    seed
}
