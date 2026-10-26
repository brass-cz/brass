//! Dependency-indexed resolutions used only at committed publication boundaries.

use std::collections::BTreeSet;
use std::rc::Rc;

use super::instances::TagRef;
use super::*;

#[derive(Clone, PartialEq, Eq, Hash)]
enum Read {
    Typed(usize),
    Tag(TagRef),
    Instance(usize),
    Numeric(usize),
    Sum(Span),
}

/// A resolved sidecar observation and its shared aggregate interpretation.
pub(super) struct Observation {
    /// The observation resolved against the current solution.
    pub(super) expression: brass_hir::TypedExpr,
    /// The completed aggregate type and its seedability, when known.
    pub(super) aggregate: Option<(Type, bool)>,
    dependencies: Vec<u32>,
}

/// The normalized instance identity and every solution variable read to obtain it.
pub(super) struct TagResolution {
    /// The aggregate state's interned key, absent while arguments remain open.
    pub(super) key: Option<u32>,
    dependencies: Vec<u32>,
}

/// Resolved observations with reverse dependencies on the solver's bindings.
#[derive(Default)]
pub(crate) struct Publication {
    typed: HashMap<usize, Rc<Observation>>,
    tags: HashMap<TagRef, Rc<TagResolution>>,
    readers: HashMap<u32, HashSet<Read>>,
    dependencies: HashMap<Read, Vec<u32>>,
}

impl Publication {
    fn forget(&mut self, read: &Read) {
        if let Some(variables) = self.dependencies.remove(read) {
            for variable in variables {
                if let Some(readers) = self.readers.get_mut(&variable) {
                    readers.remove(read);
                    if readers.is_empty() {
                        self.readers.remove(&variable);
                    }
                }
            }
        }
    }

    fn watch(&mut self, read: Read, variables: &[u32]) {
        self.forget(&read);
        for variable in variables {
            self.readers
                .entry(*variable)
                .or_default()
                .insert(read.clone());
        }
        if !variables.is_empty() {
            self.dependencies.insert(read, variables.to_vec());
        }
    }

    /// Invalidate reads affected by bindings or rollbacks since the last boundary.
    /// Settled observations lose cached values but are not republished by this step.
    pub(super) fn invalidate(
        &mut self,
        checker: &Checker,
        counters: &mut stream::ChannelCounters,
    ) -> (
        BTreeSet<usize>,
        BTreeSet<usize>,
        HashSet<Span>,
        BTreeSet<usize>,
    ) {
        let changed = checker.solver.take_publication_changes();
        counters.solution_epoch = changed.epoch;
        let affected: HashSet<_> = changed
            .variables
            .iter()
            .filter_map(|variable| self.readers.get(variable))
            .flat_map(|readers| readers.iter().cloned())
            .collect();
        counters.invalidated_readers = affected.len();
        let mut typed = BTreeSet::new();
        let mut instances = BTreeSet::new();
        let mut sums = HashSet::default();
        let mut numeric = BTreeSet::new();
        for read in affected {
            self.forget(&read);
            match read {
                Read::Numeric(index) => {
                    numeric.insert(index);
                }
                Read::Sum(span) => {
                    sums.insert(span);
                }
                Read::Typed(index) => {
                    self.typed.remove(&index);
                    typed.insert(index);
                }
                Read::Tag(tag) => {
                    self.tags.remove(&tag);
                }
                Read::Instance(index) => {
                    instances.insert(index);
                }
            }
        }
        (typed, instances, sums, numeric)
    }

    /// Resolve one sidecar entry once, sharing its reading across channel folds.
    pub(super) fn observation(
        &mut self,
        checker: &Checker,
        index: usize,
        counters: &mut stream::ChannelCounters,
    ) -> Rc<Observation> {
        if let Some(value) = self.typed.get(&index) {
            counters.typed_cache_hits += 1;
            return Rc::clone(value);
        }
        counters.typed_resolutions += 1;
        let raw = &checker.typed.expressions[index];
        let (ty, dependencies) = checker.solver.resolve_with_dependencies(&raw.ty);
        let expression = brass_hir::TypedExpr {
            kind: raw.kind.clone(),
            span: raw.span,
            ty,
            constness: raw.constness,
        };
        let aggregate =
            stream::aggregate_observation(&expression.kind, &expression.ty, checker.program);
        let value = Rc::new(Observation {
            expression,
            aggregate,
            dependencies,
        });
        self.watch(Read::Typed(index), &value.dependencies);
        self.typed.insert(index, Rc::clone(&value));
        value
    }

    /// Normalize an interned tag once per relevant solution change.
    pub(super) fn tag(
        &mut self,
        checker: &Checker,
        tag: &TagRef,
        aggregate: &mut stream::InstanceAggState,
        counters: &mut stream::ChannelCounters,
    ) -> Rc<TagResolution> {
        if let Some(value) = self.tags.get(tag) {
            counters.tag_cache_hits += 1;
            return Rc::clone(value);
        }
        counters.tag_resolutions += 1;
        let mut dependencies = Vec::new();
        let args: Vec<_> = tag
            .args
            .iter()
            .map(|arg| {
                let (ty, variables) = checker.solver.resolve_with_dependencies(arg);
                dependencies.extend(variables);
                ty
            })
            .collect();
        dependencies.sort_unstable();
        dependencies.dedup();
        let key = brass_hir::InstanceKey::new(checker.program, tag.callable.clone(), &args).map(
            |mut key| {
                key.numeric_layout = tag.numeric_layout.clone();
                aggregate.key_id(&key)
            },
        );
        let value = Rc::new(TagResolution { key, dependencies });
        self.watch(Read::Tag(tag.clone()), &value.dependencies);
        self.tags.insert(tag.clone(), Rc::clone(&value));
        value
    }

    /// Wake a pending instance when either its identity or its observed value changes.
    pub(super) fn wait_instance(
        &mut self,
        index: usize,
        observation: &Observation,
        tag: &TagResolution,
    ) {
        let mut variables = observation.dependencies.clone();
        variables.extend(&tag.dependencies);
        variables.sort_unstable();
        variables.dedup();
        self.watch(Read::Instance(index), &variables);
    }

    /// Wake a numeric call contract when its enclosing instance becomes known.
    pub(super) fn watch_numeric(&mut self, index: usize, tag: &TagResolution) {
        self.watch(Read::Numeric(index), &tag.dependencies);
    }

    /// A completed call contract no longer needs pending dependency tracking.
    pub(super) fn settle_numeric(&mut self, index: usize) {
        self.forget(&Read::Numeric(index));
    }

    /// Track the raw sum-view payload before provisional open slots become void.
    pub(super) fn watch_sum(&mut self, span: Span, variables: &[u32]) {
        self.watch(Read::Sum(span), variables);
    }

    /// Stop watching an instance whose observation has joined the aggregate.
    pub(super) fn settle_instance(&mut self, index: usize) {
        self.forget(&Read::Instance(index));
    }
}
