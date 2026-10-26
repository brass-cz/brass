//! Whole-analysis fallback before execution.

use super::CheckerPause;
use crate::source_locations::LocationTables;
use crate::{AnalyzedProgram, analyze, execute, print_diags, report_runtime_error};
use std::path::Path;

/// Fall back to the whole-analysis verdict: reclaim the checker thread and
/// re-run the pipeline EAGERLY, in process. The streaming analysis's payload
/// is never executed or reported from -- its lazy profile types some calls
/// from signatures without recording their instances' channel entries or
/// per-instance diagnostics, so only a genuinely eager analysis is a whole
/// verdict.
#[allow(clippy::too_many_arguments)]
pub(super) fn finish_eagerly(
    rt: &tokio::runtime::Runtime,
    checker: tokio::task::JoinHandle<Result<AnalyzedProgram, Vec<String>>>,
    stop: &std::sync::Arc<std::sync::atomic::AtomicBool>,
    paused: &std::sync::Arc<CheckerPause>,
    mut events: tokio::sync::mpsc::UnboundedReceiver<brass_typeck::stream::CheckEvent>,
    label: &str,
    src: &str,
    root: &Path,
) -> Result<(), u8> {
    // Reclaim the thread: stop it at the next boundary (releasing the held
    // background queue so it can reach one), drain its events, and join.
    stop.store(true, std::sync::atomic::Ordering::Relaxed);
    paused.resume();
    while events.blocking_recv().is_some() {}
    let _ = rt
        .block_on(checker)
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic.into_panic()));
    tracing::debug!(target: "brass::perf", "lazy: rerunning eagerly");
    let checked = match analyze(label, src, root, LocationTables::Execution) {
        Ok(c) => c,
        Err(diags) => return Err(print_diags(diags)),
    };
    execute(&checked.program, &checked.channels()).map_err(|e| {
        report_runtime_error(&e);
        1
    })
}
