//! Editor selection shares the compiler's authority. Context seeds carry their
//! exact request; source changes and changed requests invalidate reuse together.

use super::world::World;
use brass_hir::{Program, ProjectScope, lower_context};
use brass_typeck::reachability::{
    AnalysisView, CheckSelection, DiagnosticOwners, ItemIndex, Reachability,
};
use std::sync::{Arc, Mutex, OnceLock};

/// In-process preparation facts paired with the exact request that produced them.
struct Seed {
    fingerprint: u64,
    selection: Option<Arc<CheckSelection>>,
    tables: Arc<brass_typeck::ContextTables>,
}

/// Keep only the latest selected seed per buffer, rather than every edit.
#[derive(PartialEq, Eq, Hash)]
enum SeedKey {
    Core(u64),
    Buffer(std::path::PathBuf),
}

static SEEDS: OnceLock<Mutex<fxhash::FxHashMap<SeedKey, Seed>>> = OnceLock::new();

/// Select the whole active buffer and reached imports; the small embedded core
/// alone uses complete context checking, just as the command-line driver does.
pub(super) fn view(program: &Program, world: &World) -> Option<AnalysisView> {
    if !world.has_dependencies() {
        return None;
    }
    let entry = world.main_source.as_ref().expect("open-buffer provenance");
    let scope = ProjectScope::new(entry.location.clone(), None, None);
    let index = ItemIndex::new(program);
    Some(AnalysisView::new(
        program,
        Reachability::new(&index, &scope).into_selection(),
        Default::default(),
        Default::default(),
    ))
}

/// Reuse only a source-identical context with the same selected request. Partial
/// seeds claim only real return/co-check coverage; an erroneous context falls
/// back to the selected entry analysis, never an unfiltered dependency walk.
pub(super) fn context_seed(
    world: &World,
    view: Option<&AnalysisView>,
) -> Option<Arc<brass_typeck::ContextTables>> {
    let fingerprint = super::context_fingerprint(world);
    let request = view.map(|view| view.selection().clone());
    let key = if request.is_some() {
        SeedKey::Buffer(
            world
                .main_source
                .as_ref()
                .expect("open-buffer provenance")
                .location
                .clone(),
        )
    } else {
        SeedKey::Core(fingerprint)
    };
    let seeds = SEEDS.get_or_init(Default::default);
    if let Some(seed) = seeds.lock().ok()?.get(&key)
        && seed.fingerprint == fingerprint
        && seed.selection == request
    {
        return Some(seed.tables.clone());
    }
    let mut context = world.context_modules.clone();
    let qualified = brass_resolve::resolve_qualified_uses(&mut context);
    let (program, errors) = lower_context(&context);
    let projected = request.as_ref().map(|request| {
        AnalysisView::with_selection(
            &program,
            request.clone(),
            Default::default(),
            Default::default(),
        )
    });
    let owners = projected.as_ref().map(|_| DiagnosticOwners::new(&program));
    let reports = |span| {
        projected.as_ref().is_none_or(|view| {
            view.reports(
                &owners
                    .as_ref()
                    .expect("selected ownership")
                    .body_owner(span),
            )
        })
    };
    if qualified.iter().any(|e| reports(e.span)) || errors.iter().any(|e| reports(e.span)) {
        return None;
    }
    let tables = match &projected {
        Some(view) => {
            let analysis = brass_typeck::prepare_context(&program, view);
            if !analysis.errors.is_empty() {
                return None;
            }
            analysis.context_tables
        }
        None => brass_typeck::context_seed(&program)?,
    };
    let tables = Arc::new(tables);
    seeds.lock().ok()?.insert(
        key,
        Seed {
            fingerprint,
            selection: request,
            tables: tables.clone(),
        },
    );
    Some(tables)
}
