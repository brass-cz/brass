//! Opt-in selection observation. Ordinary runs neither lower a second catalog
//! nor enumerate package files. No shadow result enters checking or lowering.

use brass_hir::{LoadedModule, ProjectScope};
use brass_resolve::SourceMap;
use brass_typeck::reachability::{DiagnosticOwners, ItemIndex, Reachability};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Explicit CLI ownership input; it does not alter import resolution.
pub(crate) static PROJECT_ROOT: OnceLock<PathBuf> = OnceLock::new();

/// Inspect a combined graph only when `brass::item_selection=trace` is enabled.
/// Called after qualified-use rewriting and before the ordinary context seed.
#[cold]
pub(crate) fn observe(modules: &[LoadedModule], entry: &Path) {
    let scope = project_scope(entry);
    let (program, _) = brass_hir::lower(modules);
    let index = ItemIndex::new(&program);
    let reach = Reachability::new(&index, &scope);
    let selected = reach.selection();
    tracing::trace!(target: "brass::item_selection", total = index.len(), selected = selected.reasons.len(), bodies = selected.body_roots.len(), types = selected.type_roots.len(), own = selected.own_roots.len(), revision = selected.revision, scope = ?scope, "item: selection");
    for (key, label) in index.items() {
        tracing::trace!(target: "brass::item_selection", label, selected = selected.reasons.contains_key(key), reasons = ?selected.reasons.get(key), id = ?key, "item: member");
    }
    for (key, label, obligation) in index.shared_obligations() {
        if selected
            .reasons
            .get(key)
            .is_some_and(|reasons| reasons.contains(&brass_hir::Reason::SharedInference))
        {
            tracing::trace!(target: "brass::item_selection", label, ?obligation, "item: shared obligation");
        }
    }
    for (key, label, effects) in index.effect_summaries() {
        tracing::trace!(target: "brass::item_selection", label, selected = selected.reasons.contains_key(key), clean = effects.is_clean(), ?effects, "item: effects");
    }
    for (key, label, effects) in index.rootless_effect_summaries() {
        tracing::trace!(target: "brass::item_selection", label, selected = selected.reasons.contains_key(key), clean = effects.is_clean(), ?effects, "item: rootless effects");
    }
    for widening in reach.widenings() {
        tracing::trace!(target: "brass::item_selection", source = ?widening.source, cause = widening.cause, "item: widening");
    }
}

/// Observe the original body diagnostics after checking, without another walk.
#[cold]
pub(crate) fn diagnostics(
    program: &brass_hir::Program,
    errors: &[brass_typeck::TypeError],
    warnings: &[brass_typeck::TypeError],
) {
    let owners = DiagnosticOwners::new(program);
    for (kind, diagnostics) in [("error", errors), ("warning", warnings)] {
        for diagnostic in diagnostics {
            let owner = diagnostic.body_owner(&owners);
            tracing::trace!(target: "brass::item_selection", kind, message = diagnostic.message, span = ?diagnostic.span, ?owner, "item: diagnostic owner");
        }
    }
}

/// Attribute recovered syntax without changing the driver's early error policy.
#[cold]
pub(crate) fn syntax(
    modules: &[LoadedModule],
    sources: &SourceMap,
    errors: &[(String, brass_parser::Span)],
) {
    let (program, _) = brass_hir::lower(modules);
    let owners = DiagnosticOwners::new(&program);
    for (message, span) in errors {
        let owner = sources
            .locate(span.lo)
            .map(|p| owners.syntax_owner(*span, p.src, span.lo - p.local));
        tracing::trace!(target: "brass::item_selection", message, ?span, ?owner, "item: syntax owner");
    }
}

/// Resolve ownership once from explicit CLI, manifest cwd or bare-file input.
pub(crate) fn project_scope(entry: &Path) -> ProjectScope {
    let canonical =
        |path: &Path| std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    let explicit = PROJECT_ROOT.get().map(|root| canonical(root));
    let manifest = std::env::current_dir()
        .ok()
        .filter(|cwd| cwd.join("package.toml").is_file())
        .map(|cwd| canonical(&cwd));
    ProjectScope::new(canonical(entry), explicit, manifest)
}

/// Extend the CLI only when explicit ownership input was requested. Ordinary
/// successful parsing builds exactly the ordinary driver's argument catalog.
/// Program arguments have already been split off and cannot set project scope.
#[cold]
pub(crate) fn parse_project_cli(argv: &[std::ffi::OsString], error: clap::Error) -> super::Cli {
    use clap::{CommandFactory, FromArgMatches};
    if error.kind() != clap::error::ErrorKind::UnknownArgument
        || !argv.iter().any(|arg| {
            arg == "--project-root" || arg.to_string_lossy().starts_with("--project-root=")
        })
    {
        error.exit();
    }
    let mut matches = super::Cli::command()
        .arg(
            clap::Arg::new("project_root")
                .long("project-root")
                .global(true)
                .value_parser(clap::value_parser!(PathBuf))
                .help("Owning package root (does not change import paths)"),
        )
        .try_get_matches_from(argv)
        .unwrap_or_else(|error| error.exit());
    if let Some(root) = matches.remove_one::<PathBuf>("project_root") {
        let _ = PROJECT_ROOT.set(root);
    }
    super::Cli::from_arg_matches_mut(&mut matches).unwrap_or_else(|error| error.exit())
}
