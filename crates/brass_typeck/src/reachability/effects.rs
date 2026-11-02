//! Shared footprints are a syntactic may-effect analysis, not inference. The
//! selection visitor resolves call edges. Record declaration walks require
//! exact callees; rootless sum walks close over complete virtual families too.
//! Neither proof uses the currently inhabited set to hide external effects.
//! SCCs are closed bottom-up; recursive cycles start with their direct effects,
//! so a cycle cannot hide a write or manufacture an absence proof from a callee
//! whose body is unavailable. Certificates are built only for requested candidates.

use super::{ItemIndex, edges, inhabited::Inhabited};
use std::collections::BTreeSet;

mod components;

/// Transitive dependencies that can prevent omission of a shared method walk.
/// Empty means a syntactic absence proof; nonempty entries are conservative.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EffectSummary {
    /// Defining module and binding name, including renamed or qualified imports.
    pub global_reads: BTreeSet<(Vec<String>, String)>,
    /// Assignments to global bindings, qualified like reads.
    pub global_writes: BTreeSet<(Vec<String>, String)>,
    /// Potential mutation or constraints on non-private cells, with source labels.
    pub shared_cells: BTreeSet<String>,
    /// Closure environments or unresolved captured names that need a deeper proof.
    pub captures: BTreeSet<String>,
    /// Unresolved/dynamic call sites and unavailable bodies; never assumed pure.
    pub unknown_calls: BTreeSet<String>,
}

impl EffectSummary {
    /// Whether every reachable effect has a static absence proof.
    pub fn is_clean(&self) -> bool {
        self.global_reads.is_empty()
            && self.global_writes.is_empty()
            && self.shared_cells.is_empty()
            && self.captures.is_empty()
            && self.unknown_calls.is_empty()
    }

    fn include(&mut self, other: &Self) {
        self.global_reads.extend(other.global_reads.iter().cloned());
        self.global_writes
            .extend(other.global_writes.iter().cloned());
        self.shared_cells.extend(other.shared_cells.iter().cloned());
        self.captures.extend(other.captures.iter().cloned());
        self.unknown_calls
            .extend(other.unknown_calls.iter().cloned());
    }
}

/// Per-catalog, demand-built certificates. A direct walk is shared by the two
/// effect projections; global preparation has a cheaper read/call projection.
#[derive(Default)]
pub(super) struct Cache {
    direct: Vec<std::cell::OnceCell<edges::Dependencies>>,
    global_direct: Vec<std::cell::OnceCell<edges::Dependencies>>,
    ordinary: Vec<std::cell::OnceCell<EffectSummary>>,
    rootless: Vec<std::cell::OnceCell<EffectSummary>>,
    globals: Vec<std::cell::OnceCell<EffectSummary>>,
    contributors: std::cell::OnceCell<fxhash::FxHashMap<Vec<String>, Vec<usize>>>,
}

impl Cache {
    /// Reserve empty slots, without traversing a callable body.
    pub(super) fn new(count: usize) -> Self {
        Self {
            direct: (0..count).map(|_| Default::default()).collect(),
            global_direct: (0..count).map(|_| Default::default()).collect(),
            ordinary: (0..count).map(|_| Default::default()).collect(),
            rootless: (0..count).map(|_| Default::default()).collect(),
            globals: (0..count).map(|_| Default::default()).collect(),
            contributors: Default::default(),
        }
    }

    /// Reserve unproved slots for appended bodies. The caller invalidates old
    /// dispatch-sensitive proofs before extending; contributors include new slots.
    pub(super) fn extend(&mut self, count: usize) {
        self.direct.resize_with(count, Default::default);
        self.global_direct.resize_with(count, Default::default);
        self.ordinary.resize_with(count, Default::default);
        self.rootless.resize_with(count, Default::default);
        self.globals.resize_with(count, Default::default);
        self.contributors.take();
    }

    fn table(&self, projection: Projection) -> &[std::cell::OnceCell<EffectSummary>] {
        match projection {
            Projection::Ordinary => &self.ordinary,
            Projection::Rootless => &self.rootless,
            Projection::Globals => &self.globals,
        }
    }
}

/// Immutable proof slots for rebinding an append-only catalog. No mutable
/// cells cross threads, and the caller validates all method-name reads first.
pub(super) struct FrozenCache {
    direct: Vec<Option<edges::Dependencies>>,
    global_direct: Vec<Option<edges::Dependencies>>,
    ordinary: Vec<Option<EffectSummary>>,
    rootless: Vec<Option<EffectSummary>>,
    globals: Vec<Option<EffectSummary>>,
}

impl Cache {
    /// Copy established slots into a transportable checkpoint, without HIR bodies.
    pub(super) fn freeze(&self) -> FrozenCache {
        fn freeze<T: Clone>(v: &[std::cell::OnceCell<T>]) -> Vec<Option<T>> {
            v.iter().map(|v| v.get().cloned()).collect()
        }
        FrozenCache {
            direct: freeze(&self.direct),
            global_direct: freeze(&self.global_direct),
            ordinary: freeze(&self.ordinary),
            rootless: freeze(&self.rootless),
            globals: freeze(&self.globals),
        }
    }
}
impl FrozenCache {
    /// Restore validated slots. Global contributors are indexed again to include
    /// newly appended roots, using their established summaries for old bodies.
    pub(super) fn thaw(&self) -> Cache {
        fn thaw<T: Clone>(v: &[Option<T>]) -> Vec<std::cell::OnceCell<T>> {
            v.iter()
                .map(|v| {
                    v.clone()
                        .map_or_else(Default::default, std::cell::OnceCell::from)
                })
                .collect()
        }
        Cache {
            direct: thaw(&self.direct),
            global_direct: thaw(&self.global_direct),
            ordinary: thaw(&self.ordinary),
            rootless: thaw(&self.rootless),
            globals: thaw(&self.globals),
            contributors: Default::default(),
        }
    }
}

/// The ordinary co frame, rootless instance frame, and initializer cells need
/// different projections of the same source call graph.
#[derive(Clone, Copy)]
enum Projection {
    Ordinary,
    Rootless,
    Globals,
}

/// Close a candidate and its transitive callees, preserving SCC absence proofs.
pub(super) fn summary<'a>(
    index: &'a ItemIndex<'_>,
    id: usize,
    rootless: bool,
) -> &'a EffectSummary {
    let projection = if rootless {
        Projection::Rootless
    } else {
        Projection::Ordinary
    };
    ensure(index, &[id], projection);
    index.effects.table(projection)[id]
        .get()
        .expect("closed effect component")
}

/// Initializer cells can be constrained by uncalled bodies. Every callable is
/// therefore a candidate for this narrow read/call projection, even if it never
/// needs the full method certificate. Modules without bindings have no such work.
pub(super) fn global_contributors<'a>(index: &'a ItemIndex<'_>, module: &[String]) -> &'a [usize] {
    if !index.globals.contains_key(module) {
        return &[];
    }
    index
        .effects
        .contributors
        .get_or_init(|| {
            let roots: Vec<_> = index
                .entries
                .iter()
                .enumerate()
                .filter_map(|(id, entry)| {
                    matches!(
                        entry.key,
                        super::ItemKey::Body(super::BodyId::Function(_) | super::BodyId::Method(_))
                    )
                    .then_some(id)
                })
                .collect();
            ensure(index, &roots, Projection::Globals);
            let mut contributors: fxhash::FxHashMap<Vec<String>, Vec<usize>> = Default::default();
            for id in roots {
                let effects = index.effects.globals[id]
                    .get()
                    .expect("global contribution closure");
                for (module, _) in effects.global_reads.iter().chain(&effects.global_writes) {
                    let list = contributors.entry(module.clone()).or_default();
                    if list.last() != Some(&id) {
                        list.push(id);
                    }
                }
            }
            contributors
        })
        .get(module)
        .map_or(&[], Vec::as_slice)
}

fn direct<'a>(
    index: &'a ItemIndex<'_>,
    id: usize,
    projection: Projection,
) -> (&'a EffectSummary, &'a [usize]) {
    let globals = matches!(projection, Projection::Globals);
    let cache = if globals {
        &index.effects.global_direct
    } else {
        &index.effects.direct
    };
    let deps = cache[id].get_or_init(|| {
        let mut deps = edges::dependencies(
            index,
            id,
            &mut Inhabited::default(),
            false,
            true,
            true,
            globals,
        );
        deps.rootless.global_reads = deps.effects.global_reads.clone();
        deps.rootless.global_writes = deps.effects.global_writes.clone();
        deps.rootless.captures = deps.effects.captures.clone();
        deps
    });
    if matches!(projection, Projection::Rootless) {
        (&deps.rootless, &deps.rootless_calls)
    } else {
        (&deps.effects, &deps.calls)
    }
}

fn ensure(index: &ItemIndex<'_>, roots: &[usize], projection: Projection) {
    let table = index.effects.table(projection);
    if roots.iter().all(|&id| table[id].get().is_some()) {
        return;
    }
    let started = super::cost::start();
    let mut positions = vec![usize::MAX; index.entries.len()];
    let mut members = Vec::new();
    for &root in roots {
        if positions[root] == usize::MAX {
            positions[root] = members.len();
            members.push(root);
        }
    }
    let mut graph = Vec::new();
    let mut summaries = Vec::new();
    let mut cursor = 0;
    while cursor < members.len() {
        let id = members[cursor];
        cursor += 1;
        if let Some(cached) = table[id].get() {
            summaries.push(cached.clone());
            graph.push(Vec::new());
            continue;
        }
        let (effects, calls) = direct(index, id, projection);
        summaries.push(effects.clone());
        let mut edges = Vec::new();
        for &callee in calls {
            if positions[callee] == usize::MAX {
                positions[callee] = members.len();
                members.push(callee);
            }
            edges.push(positions[callee]);
        }
        graph.push(edges);
    }
    for component in components::bottom_up(&graph) {
        let mut merged = EffectSummary::default();
        for &member in &component {
            merged.include(&summaries[member]);
            for &callee in &graph[member] {
                merged.include(&summaries[callee]);
            }
        }
        for member in component {
            summaries[member] = merged.clone();
        }
    }
    for (id, summary) in members.into_iter().zip(summaries) {
        if table[id].get().is_none() {
            table[id]
                .set(summary)
                .expect("effect component is published once");
        }
    }
    if let Some(started) = started {
        let elapsed = started.elapsed();
        index.effect_time.set(index.effect_time.get() + elapsed);
        super::cost::elapsed("effects", elapsed);
    }
}
