//! Replayable observations made while elaborating callable bodies.
//!
//! The channel observations of a call-site elaboration go through `record_*`
//! helpers (most of them here), which apply them and journal them in the
//! elaboration's window. A clean elaboration's journal becomes a memo entry
//! over canonical input variables (see `Checker::elaboration_memo`); a later
//! call with the same canonical inputs replays the entry through the same
//! helpers instead of walking the body again, so poisoning and conflict
//! reports behave as in a real elaboration.

use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};

use brass_hir::{Constness, TypedExprKind};
use fxhash::{FxHashMap, FxHasher};

use super::instances::{InstanceTag, KeyedObservation, TagRef};
use super::*;

mod chunks;
mod concrete;
use chunks::Chunks;

/// One open input variable after first-occurrence canonicalization.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct CanonVar {
    pub(super) slot: u32,
    pub(super) kind: InferenceVarKind,
}

/// A callable elaboration key independent of the checker's inference ids.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct ElaborationMemoKey {
    /// Separate ordinary observations from co-check observations and roots.
    pub(super) flavor: MemoFlavor,
    pub(super) callable: String,
    pub(super) receiver: Option<Type>,
    pub(super) args: Vec<Type>,
    pub(super) scheme_inputs: Vec<Option<Type>>,
    pub(super) canon_vars: Vec<CanonVar>,
}

/// The observation contract under which a reusable body walk was performed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum MemoFlavor {
    /// An ordinary call may publish its fully settled instance return.
    Ordinary,
    /// A co-check never publishes an instance return. Rootless walks cannot
    /// consume entries recorded while an enclosing co-method owned effects.
    CoCheck { has_root: bool },
}

/// The key plus the caller variables represented by its canonical slots.
#[derive(Clone)]
pub(super) struct ElaborationMemoContext {
    pub(super) key: ElaborationMemoKey,
    pub(super) inputs: Vec<(CanonVar, Type)>,
}

/// A non-input inference variable retained by a memoized result skeleton.
#[derive(Clone)]
pub(super) struct ElaborationFreshVar {
    pub(super) placeholder: u32,
    pub(super) kind: InferenceVarKind,
}

/// One semantic channel observation made while elaborating a callable body.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) enum ElaborationJournalEntry {
    Typed {
        kind: TypedExprKind,
        span: Span,
        ty: Type,
        constness: Constness,
        /// The instance the observation was made in (see
        /// `Checker::current_instance`); a replay substitutes its argument
        /// types like the observed type's, so a nested elaboration's
        /// observations stay attributed to that nested instance.
        instance: Option<TagRef>,
    },
    PropKind(Span, PropKind),
    NullProp(Span),
    SumView(Span, Type),
    SumViewIdentity(Span),
    LiftKind(Span, bool),
    LiftErr(Span),
    TypeName(Span, String),
    /// An anonymous record literal built as the declared record (symbol).
    LiteralNominal(Span, String),
    TypeOf(Span, Type),
    TypeTest(Span, Type),
    FieldsLoop {
        span: Span,
        fields: Vec<String>,
        instance: Option<TagRef>,
    },
    ViewArg(Span),
    /// A reflective call at `span`: (receiver symbol, method, key), and the
    /// instance it was made in (see the `Typed` entry's `instance`).
    KeyedCall {
        span: Span,
        receiver: String,
        method: String,
        key: Type,
        instance: Option<TagRef>,
    },
    /// The return-origin storage demanded by one enclosing numeric solution.
    NumericCall {
        span: Span,
        ty: Option<brass_hir::NumericLayout>,
        instance: Option<TagRef>,
    },
    InstanceReturn(String, Vec<Type>, Type),
    /// A display-only observation that one application of a Fun-typed value
    /// instantiated an open parameter variable (first, kept as `Type::Unknown`
    /// so memo canonicalization and replay substitution apply) to a concrete
    /// type (second). See `Checker::record_closure_binding`.
    ClosureBinding(Type, Type),
    /// One ordered return relation, attached to the replay's current co-method.
    /// Unlike channel observations, identical links retain their multiplicity.
    CoReturnLink {
        left: Type,
        right: Type,
    },
    /// A dependency on a global's provisional type, replayed as a set insertion.
    CoGlobalRead {
        name: String,
    },
}

/// The reusable result of one clean elaboration (see
/// `Checker::elaboration_memo` for what it retains and how a hit replays it).
#[derive(Clone)]
pub(super) struct ElaborationMemoEntry {
    pub(super) ret: Type,
    pub(super) bindings: Vec<(CanonVar, Type)>,
    pub(super) fresh: Vec<ElaborationFreshVar>,
    pub(super) shapes: Vec<(Type, ShapeConstraint)>,
    journal: Chunks<ElaborationJournalEntry>,
    /// Exact global reads of the walk; absence certifies an empty read set.
    pub(super) global_reads: Option<Rc<co_replay::GlobalReadProvenance>>,
    /// Present only for a co method whose shared state must still match.
    pub(super) method_dependencies: Option<Box<co_replay::MethodMemoDependencies>>,
}

impl ElaborationMemoEntry {
    /// Logical retained observations and co effects, counting shared child
    /// chunks per entry. This is opt-in inventory, not physical heap accounting.
    pub(super) fn observation_counts(&self) -> (usize, usize, usize) {
        (
            self.journal.len(),
            self.journal
                .iter()
                .filter(|e| matches!(e, ElaborationJournalEntry::CoReturnLink { .. }))
                .count(),
            self.journal
                .iter()
                .filter(|e| matches!(e, ElaborationJournalEntry::CoGlobalRead { .. }))
                .count(),
        )
    }
}

/// The window of one elaboration in progress (see
/// `Checker::elaboration_journals`): the observations and shape constraints
/// recorded since it began, its nested elaborations' included.
#[derive(Clone, Default)]
pub(super) struct ElaborationJournalFrame {
    /// A generic closure owns a lexical environment that this journal cannot
    /// replay. Re-elaborate such bodies so returned closures retain their checks.
    pub(super) has_closure_bodies: bool,
    /// The first inference variable id the elaboration could allocate: every
    /// variable below it existed before the body walk began.
    start_var: u32,
    journal: Chunks<ElaborationJournalEntry>,
    shapes: Chunks<(Type, ShapeConstraint)>,
    journal_seen: Option<FxHashMap<u64, Vec<usize>>>,
    /// Qualified reads include nested walks and replayed child entries.
    pub(super) global_reads: co_replay::GlobalReadProvenance,
    /// Whether a nested hit supplied any part of this body window.
    pub(super) memo_replayed: bool,
}

impl ElaborationJournalFrame {
    /// Start an independent inventory journal at the current variable boundary.
    pub(super) fn observation(start_var: u32) -> Self {
        Self {
            start_var,
            ..Self::default()
        }
    }

    /// Preserve observation order, including duplicate co-return links.
    pub(super) fn observe_entry(&mut self, entry: ElaborationJournalEntry) {
        self.push(entry);
    }

    /// Retain a shape dependency for the ordinary memo skeleton eligibility check.
    pub(super) fn observe_shape(&mut self, ty: Type, constraint: ShapeConstraint) {
        self.shapes.push((ty, constraint));
    }

    fn push(&mut self, entry: ElaborationJournalEntry) {
        if matches!(entry, ElaborationJournalEntry::CoReturnLink { .. }) {
            self.journal.push(entry);
            return;
        }
        if let Some(seen) = &mut self.journal_seen {
            let hash = fx_hash(&entry);
            if seen.get(&hash).is_some_and(|indices| {
                indices
                    .iter()
                    .any(|index| *self.journal.flat_at(*index) == entry)
            }) {
                return;
            }
            seen.entry(hash).or_default().push(self.journal.len());
        }
        self.journal.push(entry);
    }

    /// Exact repeated observations are idempotent, so a parent that contains
    /// memo replays keeps only their first occurrence while preserving the
    /// order of distinct writes.
    fn prepare_for_replay(&mut self) {
        if self.journal_seen.is_some() {
            return;
        }
        let mut seen: FxHashMap<u64, Vec<usize>> = FxHashMap::default();
        let mut journal = Vec::with_capacity(self.journal.len());
        for entry in self.journal.iter() {
            if matches!(entry, ElaborationJournalEntry::CoReturnLink { .. }) {
                journal.push(entry.clone());
                continue;
            }
            let hash = fx_hash(&entry);
            if seen
                .get(&hash)
                .is_some_and(|indices| indices.iter().any(|index| journal[*index] == *entry))
            {
                continue;
            }
            seen.entry(hash).or_default().push(journal.len());
            journal.push(entry.clone());
        }
        self.journal = journal.into_iter().collect();
        self.journal_seen = Some(seen);
    }

    fn extend(&mut self, child: &Self) {
        if self.journal_seen.is_some() {
            for entry in child.journal.iter() {
                self.push(entry.clone());
            }
        } else {
            self.journal.append(&child.journal);
        }
        self.shapes.append(&child.shapes);
        self.global_reads.extend(&child.global_reads);
        self.memo_replayed |= child.memo_replayed;
    }
}

struct MemoSkeleton {
    vars: BTreeMap<u32, Type>,
    next_placeholder: u32,
    fresh: Vec<ElaborationFreshVar>,
    /// The elaboration's first variable id (see `ElaborationJournalFrame`).
    start_var: u32,
    /// Set when the recorded types mention a variable that existed before the
    /// elaboration began and is neither an input nor a declaration's own.
    outer: bool,
    /// The template of each instance tag the journal mentions, made once.
    tags: FxHashMap<TagRef, TagRef>,
}

/// The `Checker::typed_seen` bucket of one typed observation.
pub(super) fn typed_hash(kind: &TypedExprKind, span: Span, ty: &Type, constness: Constness) -> u64 {
    fx_hash(&(kind, span, ty, constness))
}

fn fx_hash(value: &impl Hash) -> u64 {
    let mut hasher = FxHasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

fn substitute_shape_constraint(
    constraint: &ShapeConstraint,
    substitution: &BTreeMap<u32, Type>,
) -> ShapeConstraint {
    match constraint {
        ShapeConstraint::Equals(ty) => {
            ShapeConstraint::Equals(brass_hir::substitute_vars(ty, substitution))
        }
        other => other.clone(),
    }
}

fn substitute_journal_entry(
    entry: &ElaborationJournalEntry,
    substitution: &BTreeMap<u32, Type>,
) -> ElaborationJournalEntry {
    match entry {
        ElaborationJournalEntry::Typed {
            kind,
            span,
            ty,
            constness,
            instance,
        } => ElaborationJournalEntry::Typed {
            kind: kind.clone(),
            span: *span,
            ty: brass_hir::substitute_vars(ty, substitution),
            constness: *constness,
            // A replay re-tags through `Checker::replay_tag`.
            instance: instance.clone(),
        },
        ElaborationJournalEntry::SumView(span, ty) => {
            ElaborationJournalEntry::SumView(*span, brass_hir::substitute_vars(ty, substitution))
        }
        ElaborationJournalEntry::TypeOf(span, ty) => {
            ElaborationJournalEntry::TypeOf(*span, brass_hir::substitute_vars(ty, substitution))
        }
        ElaborationJournalEntry::TypeTest(span, ty) => {
            ElaborationJournalEntry::TypeTest(*span, brass_hir::substitute_vars(ty, substitution))
        }
        ElaborationJournalEntry::KeyedCall {
            span,
            receiver,
            method,
            key,
            instance,
        } => ElaborationJournalEntry::KeyedCall {
            span: *span,
            receiver: receiver.clone(),
            method: method.clone(),
            key: brass_hir::substitute_vars(key, substitution),
            instance: instance.clone(),
        },
        ElaborationJournalEntry::CoReturnLink { left, right } => {
            ElaborationJournalEntry::CoReturnLink {
                left: brass_hir::substitute_vars(left, substitution),
                right: brass_hir::substitute_vars(right, substitution),
            }
        }
        ElaborationJournalEntry::ClosureBinding(var, ty) => {
            ElaborationJournalEntry::ClosureBinding(
                brass_hir::substitute_vars(var, substitution),
                brass_hir::substitute_vars(ty, substitution),
            )
        }
        ElaborationJournalEntry::InstanceReturn(symbol, args, ret) => {
            ElaborationJournalEntry::InstanceReturn(
                symbol.clone(),
                args.iter()
                    .map(|arg| brass_hir::substitute_vars(arg, substitution))
                    .collect(),
                brass_hir::substitute_vars(ret, substitution),
            )
        }
        other => other.clone(),
    }
}

impl Checker<'_> {
    fn fresh_memo_var(&mut self, kind: InferenceVarKind) -> Type {
        let id = self.next_unknown;
        self.next_unknown += 1;
        self.solver.record_var(id, kind);
        Type::Unknown(id)
    }

    #[inline]
    pub(super) fn journal_elaboration(&mut self, entry: ElaborationJournalEntry) {
        if self.method_inventory.is_some() {
            self.observe_method_entry(&entry);
        }
        if let Some(frame) = self.elaboration_journals.last_mut() {
            frame.push(entry);
        }
    }

    #[inline]
    pub(super) fn journal_elaboration_shape(&mut self, ty: Type, constraint: ShapeConstraint) {
        if self.method_inventory.is_some() {
            self.observe_method_shape(&ty, &constraint);
        }
        if let Some(frame) = self.elaboration_journals.last_mut() {
            frame.shapes.push((ty, constraint));
        }
    }

    /// Open the window of an elaboration about to walk a callee body.
    pub(super) fn begin_elaboration_journal(&mut self) {
        self.elaboration_journals.push(ElaborationJournalFrame {
            start_var: self.next_unknown,
            ..ElaborationJournalFrame::default()
        });
    }

    /// Whether `id` is one of the variables lowering embedded in the program's
    /// declarations (`Program::next_infer_var`): a field's or method
    /// signature's open type, which every elaboration sees as the same
    /// variable. A memo skeleton keeps these as they are.
    pub(super) fn is_declaration_var(&self, id: u32) -> bool {
        id == brass_hir::INFER_VAR || id < self.program.next_infer_var
    }

    /// Close this callable's window and include its complete subtree in the
    /// enclosing callable's window.
    pub(super) fn finish_elaboration_journal(&mut self) -> ElaborationJournalFrame {
        let frame = self
            .elaboration_journals
            .pop()
            .expect("an elaboration journal frame must be active");
        if let Some(parent) = self.elaboration_journals.last_mut() {
            parent.extend(&frame);
            parent.has_closure_bodies |= frame.has_closure_bodies;
        }
        frame
    }

    /// The memo entry of a finished elaboration, or `None` when replaying it
    /// would not be equivalent to elaborating the body again.
    ///
    /// Replay re-binds the canonical inputs and gives every other variable of
    /// the recorded result, bindings, shapes and observations a FRESH
    /// placeholder (a declaration's own variables aside: every elaboration
    /// sees the same ones, so they are kept). That is only right for a variable
    /// the elaboration itself created. One that existed before it began and is
    /// not an input -- a global's element type (`store.push(x)`), the
    /// provisional return of an enclosing recursive elaboration -- is shared
    /// state, and a fresh copy would detach the replayed call from it, so such
    /// an elaboration is not memoized.
    pub(super) fn build_elaboration_memo_entry(
        &self,
        ret: &Type,
        frame: ElaborationJournalFrame,
        context: &ElaborationMemoContext,
    ) -> Option<ElaborationMemoEntry> {
        let mut skeleton = MemoSkeleton {
            start_var: frame.start_var,
            outer: false,
            vars: context
                .inputs
                .iter()
                .map(|(var, actual)| match actual {
                    Type::Unknown(id) => (*id, Type::Unknown(var.slot)),
                    _ => unreachable!("canonical memo inputs must be inference variables"),
                })
                .collect(),
            next_placeholder: context.inputs.len() as u32,
            fresh: Vec::new(),
            tags: FxHashMap::default(),
        };
        let ret = self.memo_skeleton_type(ret, &mut skeleton);
        let bindings = context
            .inputs
            .iter()
            .map(|(var, actual)| (*var, self.memo_skeleton_type(actual, &mut skeleton)))
            .collect();
        let shapes = frame
            .shapes
            .iter()
            .cloned()
            .map(|(ty, constraint)| {
                (
                    self.memo_skeleton_type(&ty, &mut skeleton),
                    self.memo_skeleton_shape(constraint, &mut skeleton),
                )
            })
            .collect();
        let journal = if frame.journal.iter().all(concrete::unchanged) {
            frame.journal
        } else {
            frame
                .journal
                .iter()
                .cloned()
                .map(|entry| self.memo_skeleton_journal_entry(entry, &mut skeleton))
                .collect()
        };
        if matches!(context.key.flavor, MemoFlavor::CoCheck { .. }) {
            tracing::trace!(target: "brass::perf", callable = context.key.callable,
                reason = if skeleton.outer { "outer_variable" } else { "stored" },
                observations = journal.len(),
                co_links = journal.iter().filter(|e| matches!(e, ElaborationJournalEntry::CoReturnLink { .. })).count(),
                co_reads = journal.iter().filter(|e| matches!(e, ElaborationJournalEntry::CoGlobalRead { .. })).count(),
                observation_bytes = std::mem::size_of::<ElaborationJournalEntry>(),
                "check: co memo storage");
        }
        (!skeleton.outer).then_some(ElaborationMemoEntry {
            ret,
            bindings,
            fresh: skeleton.fresh,
            shapes,
            journal,
            global_reads: frame.global_reads.retained(),
            method_dependencies: None,
        })
    }

    /// Replay through the ordinary memo journal. Closed entries have no
    /// canonical inputs, fresh placeholders or solver bindings to substitute.
    pub(super) fn replay_numeric_closure(&mut self, entry: &ElaborationMemoEntry) -> Type {
        // Every expression here has a final numeric type, except the block
        // ending in return. Binding identifiers cannot be divergent. These
        // concrete observations therefore restore the flow marks as well,
        // even when an enclosing body check has cleared its local flow set.
        for observation in entry.journal.iter() {
            if let ElaborationJournalEntry::Typed { span, ty, .. } = observation {
                if matches!(ty, Type::Never) {
                    self.diverging_exprs.insert(*span);
                } else {
                    self.diverging_exprs.remove(span);
                }
            }
        }
        let context = journal::ElaborationMemoContext {
            key: journal::ElaborationMemoKey {
                flavor: MemoFlavor::Ordinary,
                callable: String::new(),
                receiver: None,
                args: Vec::new(),
                scheme_inputs: Vec::new(),
                canon_vars: Vec::new(),
            },
            inputs: Vec::new(),
        };
        self.replay_elaboration_memo_entry(entry, &context)
    }

    /// Retain only concrete typed observations of a closed arithmetic body.
    /// Their exact types and tags are already final, so replay needs neither
    /// canonical variables nor tag rebasing. The caller keys the enclosing
    /// instance and admits no captured reads, calls, or diagnostic effects.
    pub(super) fn build_numeric_closure_memo(
        &self,
        ret: &Type,
        frame: ElaborationJournalFrame,
    ) -> Option<ElaborationMemoEntry> {
        fn concrete_observation(ty: &Type) -> bool {
            match ty {
                Type::Int(_) | Type::Float(_) | Type::Void | Type::Never => true,
                Type::Fun(args, ret) => {
                    args.iter().all(closure_memo::primitive_numeric)
                        && closure_memo::primitive_numeric(ret)
                }
                _ => false,
            }
        }
        let enclosing = self.current_instance();
        let concrete_tag = |tag: &Option<instances::TagRef>| {
            tag.as_ref().is_none_or(|tag| {
                Some(tag) == enclosing.as_ref()
                    || (matches!(tag.callable, brass_hir::InstanceCallable::Closure { .. })
                        && tag.args.iter().all(closure_memo::primitive_numeric))
            })
        };
        if !closure_memo::primitive_numeric(ret)
            || frame.has_closure_bodies
            || !frame.shapes.is_empty()
            || !frame.journal.iter().all(|entry| match entry {
                ElaborationJournalEntry::Typed { ty, instance, .. } => {
                    concrete_observation(ty) && concrete_tag(instance)
                }
                ElaborationJournalEntry::NumericCall { instance, .. } => concrete_tag(instance),
                _ => false,
            })
        {
            return None;
        }
        Some(ElaborationMemoEntry {
            ret: ret.clone(),
            bindings: Vec::new(),
            fresh: Vec::new(),
            shapes: Vec::new(),
            journal: frame.journal,
            global_reads: frame.global_reads.retained(),
            method_dependencies: None,
        })
    }

    /// Replay `entry` at the call `context` describes and return the call's
    /// result: bind the canonical inputs, give the entry's other variables
    /// fresh ids, register its shapes, and re-record every observation
    /// through its normal `record_*` helper, so poison semantics are those of
    /// a real elaboration.
    pub(super) fn replay_elaboration_memo_entry(
        &mut self,
        entry: &ElaborationMemoEntry,
        context: &ElaborationMemoContext,
    ) -> Type {
        self.replay_global_provenance(entry.global_reads.as_deref());
        if context.inputs.is_empty() && entry.fresh.is_empty() {
            if let Some(frame) = self.elaboration_journals.last_mut() {
                frame.prepare_for_replay();
            }
            for (ty, constraint) in &entry.shapes {
                self.record_shape(ty, constraint.clone());
            }
            for observation in entry.journal.iter() {
                self.replay_elaboration_journal_entry(observation);
            }
            return entry.ret.clone();
        }
        let mut substitution: BTreeMap<u32, Type> = context
            .inputs
            .iter()
            .map(|(var, actual)| (var.slot, actual.clone()))
            .collect();
        for fresh in &entry.fresh {
            substitution.insert(fresh.placeholder, self.fresh_memo_var(fresh.kind));
        }
        for (var, binding) in &entry.bindings {
            let actual = context
                .inputs
                .iter()
                .find_map(|(candidate, actual)| (*candidate == *var).then_some(actual))
                .expect("memo key and binding slots must agree");
            let binding = brass_hir::substitute_vars(binding, &substitution);
            let outcome = self.solver.unify(actual, &binding);
            debug_assert!(outcome.is_ok());
        }
        for (ty, constraint) in &entry.shapes {
            let ty = brass_hir::substitute_vars(ty, &substitution);
            let constraint = substitute_shape_constraint(constraint, &substitution);
            self.record_shape(&ty, constraint);
        }
        if let Some(frame) = self.elaboration_journals.last_mut() {
            frame.prepare_for_replay();
        }
        let mut tags = FxHashMap::default();
        for observation in entry.journal.iter() {
            if matches!(
                observation,
                ElaborationJournalEntry::Typed { .. }
                    | ElaborationJournalEntry::SumView(..)
                    | ElaborationJournalEntry::TypeOf(..)
                    | ElaborationJournalEntry::TypeTest(..)
                    | ElaborationJournalEntry::KeyedCall { .. }
                    | ElaborationJournalEntry::FieldsLoop { .. }
                    | ElaborationJournalEntry::NumericCall { .. }
                    | ElaborationJournalEntry::InstanceReturn(..)
                    | ElaborationJournalEntry::ClosureBinding(..)
                    | ElaborationJournalEntry::CoReturnLink { .. }
            ) {
                let mut observation = substitute_journal_entry(observation, &substitution);
                if let ElaborationJournalEntry::Typed { instance, .. }
                | ElaborationJournalEntry::KeyedCall { instance, .. }
                | ElaborationJournalEntry::FieldsLoop { instance, .. }
                | ElaborationJournalEntry::NumericCall { instance, .. } = &mut observation
                    && let Some(tag) = instance
                {
                    *tag = self.replay_tag(tag, &substitution, &mut tags);
                }
                self.replay_elaboration_journal_entry(&observation);
            } else {
                self.replay_elaboration_journal_entry(observation);
            }
        }
        self.resolve(&brass_hir::substitute_vars(&entry.ret, &substitution))
    }

    fn memo_skeleton_type(&self, ty: &Type, skeleton: &mut MemoSkeleton) -> Type {
        let resolved = self.resolve(ty);
        let mut needs_substitution = false;
        for id in brass_hir::type_vars(&resolved) {
            if skeleton.vars.contains_key(&id) {
                needs_substitution = true;
                continue;
            }
            // The shared `infer` sentinel in a decided type-test pattern is a
            // wildcard, not a solver variable. It must remain byte-identical
            // across replays or equal wildcard patterns would poison the span.
            // A declaration's own variable is the same one every elaboration
            // sees, so it stays too.
            if self.is_declaration_var(id) {
                continue;
            }
            if id < skeleton.start_var {
                skeleton.outer = true;
                continue;
            }
            needs_substitution = true;
            let placeholder = skeleton.next_placeholder;
            skeleton.next_placeholder += 1;
            skeleton.vars.insert(id, Type::Unknown(placeholder));
            skeleton.fresh.push(ElaborationFreshVar {
                placeholder,
                kind: self.solver.kind_of(id).unwrap_or(InferenceVarKind::Source),
            });
        }
        if needs_substitution {
            brass_hir::substitute_vars(&resolved, &skeleton.vars)
        } else {
            resolved
        }
    }

    fn memo_skeleton_shape(
        &self,
        constraint: ShapeConstraint,
        skeleton: &mut MemoSkeleton,
    ) -> ShapeConstraint {
        match constraint {
            ShapeConstraint::Equals(ty) => {
                ShapeConstraint::Equals(self.memo_skeleton_type(&ty, skeleton))
            }
            other => other,
        }
    }

    /// The memo template of instance tag `tag` (made once per skeleton).
    fn memo_skeleton_tag(&self, tag: &TagRef, skeleton: &mut MemoSkeleton) -> TagRef {
        if let Some(done) = skeleton.tags.get(tag) {
            return done.clone();
        }
        let template = TagRef::template(InstanceTag {
            callable: tag.callable.clone(),
            numeric_layout: tag.numeric_layout.clone(),
            args: tag
                .args
                .iter()
                .map(|arg| self.memo_skeleton_type(arg, skeleton))
                .collect(),
        });
        skeleton.tags.insert(tag.clone(), template.clone());
        template
    }

    fn memo_skeleton_journal_entry(
        &self,
        entry: ElaborationJournalEntry,
        skeleton: &mut MemoSkeleton,
    ) -> ElaborationJournalEntry {
        match entry {
            ElaborationJournalEntry::NumericCall { span, ty, instance } => {
                ElaborationJournalEntry::NumericCall {
                    span,
                    ty,
                    instance: instance.map(|tag| self.memo_skeleton_tag(&tag, skeleton)),
                }
            }
            ElaborationJournalEntry::Typed {
                kind,
                span,
                ty,
                constness,
                instance,
            } => ElaborationJournalEntry::Typed {
                kind,
                span,
                ty: self.memo_skeleton_type(&ty, skeleton),
                constness,
                instance: instance.map(|tag| self.memo_skeleton_tag(&tag, skeleton)),
            },
            ElaborationJournalEntry::SumView(span, ty) => {
                ElaborationJournalEntry::SumView(span, self.memo_skeleton_type(&ty, skeleton))
            }
            ElaborationJournalEntry::TypeOf(span, ty) => {
                ElaborationJournalEntry::TypeOf(span, self.memo_skeleton_type(&ty, skeleton))
            }
            ElaborationJournalEntry::TypeTest(span, ty) => {
                ElaborationJournalEntry::TypeTest(span, self.memo_skeleton_type(&ty, skeleton))
            }
            ElaborationJournalEntry::FieldsLoop {
                span,
                fields,
                instance,
            } => ElaborationJournalEntry::FieldsLoop {
                span,
                fields,
                instance: instance.map(|tag| self.memo_skeleton_tag(&tag, skeleton)),
            },
            ElaborationJournalEntry::KeyedCall {
                span,
                receiver,
                method,
                key,
                instance,
            } => ElaborationJournalEntry::KeyedCall {
                span,
                receiver,
                method,
                key: self.memo_skeleton_type(&key, skeleton),
                instance: instance.map(|tag| self.memo_skeleton_tag(&tag, skeleton)),
            },
            ElaborationJournalEntry::InstanceReturn(symbol, args, ret) => {
                ElaborationJournalEntry::InstanceReturn(
                    symbol,
                    args.into_iter()
                        .map(|arg| self.memo_skeleton_type(&arg, skeleton))
                        .collect(),
                    self.memo_skeleton_type(&ret, skeleton),
                )
            }
            ElaborationJournalEntry::ClosureBinding(var, ty) => {
                ElaborationJournalEntry::ClosureBinding(
                    self.memo_skeleton_type(&var, skeleton),
                    self.memo_skeleton_type(&ty, skeleton),
                )
            }
            ElaborationJournalEntry::CoReturnLink { left, right } => {
                ElaborationJournalEntry::CoReturnLink {
                    left: self.memo_skeleton_type(&left, skeleton),
                    right: self.memo_skeleton_type(&right, skeleton),
                }
            }
            other => other,
        }
    }

    fn replay_elaboration_journal_entry(&mut self, entry: &ElaborationJournalEntry) {
        match entry {
            ElaborationJournalEntry::CoReturnLink { left, right } => {
                self.record_co_return_link(left.clone(), right.clone());
            }
            ElaborationJournalEntry::CoGlobalRead { name } => {
                self.record_co_global_read(name);
            }
            ElaborationJournalEntry::Typed {
                kind,
                span,
                ty,
                constness,
                instance,
            } => self.record_typed_in(
                kind.clone(),
                *span,
                ty.clone(),
                *constness,
                instance.clone(),
            ),
            ElaborationJournalEntry::PropKind(span, kind) => self.record_prop_kind(*span, *kind),
            ElaborationJournalEntry::NullProp(span) => self.record_null_prop(*span),
            ElaborationJournalEntry::SumView(span, ty) => {
                self.record_sum_view_type(*span, ty.clone())
            }
            ElaborationJournalEntry::SumViewIdentity(span) => self.record_sum_view_identity(*span),
            ElaborationJournalEntry::LiftKind(span, lifted) => {
                self.record_lift_kind(*span, *lifted)
            }
            ElaborationJournalEntry::LiftErr(span) => self.record_lift_err(*span),
            ElaborationJournalEntry::TypeName(span, name) => {
                self.record_type_name(*span, name.clone())
            }
            ElaborationJournalEntry::LiteralNominal(span, symbol) => {
                self.record_literal_nominal(*span, symbol.clone())
            }
            ElaborationJournalEntry::TypeOf(span, ty) => self.record_typeof_type(*span, ty),
            ElaborationJournalEntry::TypeTest(span, ty) => self.record_type_test(*span, ty),
            ElaborationJournalEntry::FieldsLoop {
                span,
                fields,
                instance,
            } => {
                self.record_fields_loop_in(*span, fields.clone(), instance.clone());
            }
            ElaborationJournalEntry::NumericCall { span, ty, instance } => {
                self.record_numeric_call(*span, ty.clone(), instance.clone());
            }
            ElaborationJournalEntry::ViewArg(span) => self.record_view_arg(*span),
            ElaborationJournalEntry::KeyedCall {
                span,
                receiver,
                method,
                key,
                instance,
            } => self.record_keyed_call_in(
                *span,
                receiver.clone(),
                method.clone(),
                key.clone(),
                instance.clone(),
            ),
            ElaborationJournalEntry::InstanceReturn(symbol, args, ret) => {
                self.record_instance_return(symbol.clone(), args.clone(), ret.clone())
            }
            // The variable side may have been substituted to the current
            // call's own variable (record it) or to a type already concrete
            // here (nothing left to display-resolve).
            ElaborationJournalEntry::ClosureBinding(var, ty) => {
                if let Type::Unknown(id) = self.resolve_head(var) {
                    self.record_closure_binding(id, &ty.clone());
                }
            }
        }
    }

    /// Add a typed observation to the sidecar (once per exact observation),
    /// attributed to the innermost instance being elaborated.
    pub(super) fn record_typed(
        &mut self,
        kind: TypedExprKind,
        span: Span,
        ty: Type,
        constness: Constness,
    ) {
        let instance = self.current_instance();
        self.record_typed_in(kind, span, ty, constness, instance);
    }

    /// [`Checker::record_typed`] attributed to `instance` (the elaboration
    /// that made the observation, which a memo replay names explicitly).
    pub(super) fn record_typed_in(
        &mut self,
        kind: TypedExprKind,
        span: Span,
        ty: Type,
        constness: Constness,
        instance: Option<TagRef>,
    ) {
        // Only an observation that can seed per instance keeps its tag, in
        // the journal too: replays then re-tag just those.
        let instance = instance.filter(|_| self.seeds_per_instance(&kind, &ty));
        self.journal_elaboration(ElaborationJournalEntry::Typed {
            kind: kind.clone(),
            span,
            ty: ty.clone(),
            constness,
            instance: instance.clone(),
        });
        let hash = typed_hash(&kind, span, &ty, constness);
        let recorded = self.typed_seen.get(&hash).and_then(|indices| {
            indices.iter().copied().find(|index| {
                let recorded = &self.typed.expressions[*index];
                recorded.kind == kind
                    && recorded.span == span
                    && recorded.ty == ty
                    && recorded.constness == constness
            })
        });
        let index = match recorded {
            Some(index) => index,
            None => {
                let index = self.typed.expressions.len();
                self.typed.push_kind(kind, span, ty, constness);
                self.typed_seen.entry(hash).or_default().push(index);
                index
            }
        };
        if let Some(tag) = instance {
            self.record_instance_typed(tag, index);
        }
    }

    /// Record what one application of a Fun-typed value instantiated the open
    /// parameter variable `var` to. Display-only: the application's
    /// unification is deliberately local (committing it would defeat
    /// let-polymorphism -- see `apply_callable`), so the solver never learns
    /// it and every sidecar entry mentioning `var` renders as `unknown`. The
    /// language server substitutes these observations into the sidecar when
    /// all applications agree; a second, different observation poisons the
    /// variable back to open.
    pub(super) fn record_closure_binding(&mut self, var: u32, observed: &Type) {
        // Mode wrappers are not part of the bound value's own type, and
        // peeling them keeps a `const` argument from spuriously conflicting
        // with the same type passed mutably.
        let resolved = brass_hir::peel_modes(&self.resolve(observed)).clone();
        if matches!(resolved, Type::Unknown(_)) {
            return;
        }
        self.journal_elaboration(ElaborationJournalEntry::ClosureBinding(
            Type::Unknown(var),
            resolved.clone(),
        ));
        match self.closure_bindings.get(&var) {
            Some(Some(prev)) if *prev != resolved => {
                self.closure_bindings.insert(var, None);
            }
            Some(_) => {}
            None => {
                self.closure_bindings.insert(var, Some(resolved));
            }
        }
    }

    pub(super) fn record_null_prop(&mut self, span: Span) {
        self.journal_elaboration(ElaborationJournalEntry::NullProp(span));
        self.channel_changes
            .get_mut()
            .mark(channel_changes::Channel::NullProp, span);
        self.null_props.insert(span);
    }

    pub(super) fn record_lift_err(&mut self, span: Span) {
        self.journal_elaboration(ElaborationJournalEntry::LiftErr(span));
        self.channel_changes
            .get_mut()
            .mark(channel_changes::Channel::LiftErr, span);
        self.lift_errs.insert(span);
    }

    /// Record the type a `typeof(v).method(..)` static call names, keyed by
    /// the `typeof(v)` span (see [`Inference::type_names`]). One MIR body
    /// serves every instantiation, so two instantiations naming different
    /// types there are an error.
    pub(super) fn record_type_name(&mut self, span: Span, name: String) {
        self.journal_elaboration(ElaborationJournalEntry::TypeName(span, name.clone()));
        self.channel_changes
            .get_mut()
            .mark(channel_changes::Channel::TypeName, span);
        if let Some(prev) = self.type_names.insert(span, name.clone())
            && prev != name
        {
            self.errors.push(TypeError {
                message: format!(
                    "`typeof(..)` resolves to `{prev}` in one instantiation of this generic \
                     function and `{name}` in another; a static call through `typeof` must \
                     name the same type in every instantiation"
                ),
                span,
            });
        }
    }

    /// Record the resolved binding type of the `typeof`-bearing annotation at
    /// `span`, once it is concrete. Two instantiations that disagree poison
    /// the span (see `Checker::typeof_poisoned`).
    pub(super) fn record_typeof_type(&mut self, span: Span, ty: &Type) {
        let concrete = self.resolve(ty);
        if !is_concrete_type(&concrete) || self.typeof_poisoned.contains(&span) {
            return;
        }
        self.journal_elaboration(ElaborationJournalEntry::TypeOf(span, concrete.clone()));
        self.channel_changes
            .get_mut()
            .mark(channel_changes::Channel::TypeOf, span);
        match self.typeof_types.get(&span) {
            Some(prev) if peel_modes(prev) != peel_modes(&concrete) => {
                self.typeof_types.remove(&span);
                self.typeof_poisoned.insert(span);
            }
            _ => {
                self.typeof_types.insert(span, concrete);
            }
        }
    }

    /// Record a call argument requiring a structural view.
    pub(super) fn record_view_arg(&mut self, span: Span) {
        self.journal_elaboration(ElaborationJournalEntry::ViewArg(span));
        self.channel_changes
            .get_mut()
            .mark(channel_changes::Channel::ViewArg, span);
        self.view_args.insert(span);
    }

    /// Record how the `recv.name(..)` call at `span` resolved in this
    /// elaboration: a call of the function value a record FIELD holds
    /// (`field`, the receiver's type-test pattern), or a method call
    /// (`None`). One MIR body serves every instantiation, so a call some
    /// instantiations resolve to a field and others to a method is lowered
    /// as a per-instance branch on the receiver's type (see
    /// `Checker::field_call_map`).
    ///
    /// Not journaled: the observation mentions no inference variable (a
    /// receiver pattern is a bare nominal), so a memo replay of the
    /// elaboration that made it would only repeat it.
    pub(super) fn record_call_kind(&mut self, span: Span, field: Option<Type>) {
        self.channel_changes
            .get_mut()
            .mark(channel_changes::Channel::FieldCall, span);
        let site = self.call_sites.entry(span).or_default();
        match field {
            Some(pattern) => {
                if !site.field_receivers.contains(&pattern) {
                    site.field_receivers.push(pattern);
                }
            }
            None => site.method = true,
        }
    }

    /// Record the reflective call at `span` keyed as (receiver symbol,
    /// method, key), attributed to the innermost instance being elaborated.
    pub(super) fn record_keyed_call(
        &mut self,
        span: Span,
        receiver: String,
        method: String,
        key: Type,
    ) {
        let instance = self.current_instance();
        self.record_keyed_call_in(span, receiver, method, key, instance);
    }

    /// [`Checker::record_keyed_call`] attributed to `instance`. Every
    /// observation is kept (see `Checker::settled_keyed_calls`): a generic
    /// body's instances may key one call differently.
    pub(super) fn record_keyed_call_in(
        &mut self,
        span: Span,
        receiver: String,
        method: String,
        key: Type,
        instance: Option<TagRef>,
    ) {
        self.journal_elaboration(ElaborationJournalEntry::KeyedCall {
            span,
            receiver: receiver.clone(),
            method: method.clone(),
            key: key.clone(),
            instance: instance.clone(),
        });
        self.record_keyed_observation(KeyedObservation {
            instance,
            span,
            receiver: receiver.clone(),
            method: method.clone(),
            key: key.clone(),
        });
        self.channel_changes
            .get_mut()
            .mark(channel_changes::Channel::KeyedCall, span);
        self.keyed_calls.insert(span, (receiver, method, key));
    }

    /// Record the return of the unannotated function instance `symbol` at
    /// `args` (see [`Inference::instance_returns`]). Journaled in any case, so
    /// a replay at concrete inputs records it; kept only once the arguments
    /// and the return are fully known.
    pub(super) fn record_instance_return(&mut self, symbol: String, args: Vec<Type>, ret: Type) {
        let args: Vec<_> = args.iter().map(|arg| self.resolve(arg)).collect();
        let ret = self.resolve(&ret);
        self.journal_elaboration(ElaborationJournalEntry::InstanceReturn(
            symbol.clone(),
            args.clone(),
            ret.clone(),
        ));
        if !args.iter().all(brass_hir::is_fully_known) || !brass_hir::is_fully_known(&ret) {
            return;
        }
        self.channel_changes.get_mut().mark_return(&symbol, &args);
        self.instance_returns.insert((symbol, args), ret);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn concrete_context() -> ElaborationMemoContext {
        ElaborationMemoContext {
            key: ElaborationMemoKey {
                flavor: MemoFlavor::Ordinary,
                callable: "test".to_string(),
                receiver: None,
                args: Vec::new(),
                scheme_inputs: Vec::new(),
                canon_vars: Vec::new(),
            },
            inputs: Vec::new(),
        }
    }

    #[test]
    fn tagged_observations_keep_distinct_skeleton_templates() {
        let program = Program::empty();
        let rows = Rc::new(brass_typesys::RowInfo::analyze(&program));
        let mut recorded = Checker::new(&program, Rc::clone(&rows));
        let callable = brass_hir::InstanceCallable::Function("source".into());
        let args = [Type::Int(IntKind::I32)];
        let tag = recorded.intern_tag(callable.clone(), &args);
        let mut frame = ElaborationJournalFrame::default();
        frame.journal.push(ElaborationJournalEntry::Typed {
            kind: TypedExprKind::TypeOfAnnotation,
            span: Span::new(1, 2),
            ty: Type::Int(IntKind::I32),
            constness: Constness::Unknown,
            instance: Some(tag.clone()),
        });
        let keep = frame.journal.clone();
        let context = concrete_context();
        let memo = recorded
            .build_elaboration_memo_entry(&Type::Bool, frame, &context)
            .unwrap();
        assert!(!std::ptr::eq(
            keep.iter().next().unwrap(),
            memo.journal.iter().next().unwrap()
        ));
        let mut replayed = Checker::new(&program, rows);
        let expected = replayed.intern_tag(callable, &args);
        assert_ne!(tag, expected);
        replayed.replay_elaboration_memo_entry(&memo, &context);
        assert_eq!(replayed.instance_typed.len(), 1);
        let template = &replayed.instance_typed[0].tag;
        assert_ne!(*template, tag);
        assert_ne!(*template, expected);
        assert_eq!(template.callable, expected.callable);
        assert_eq!(template.args, expected.args);
    }

    #[test]
    fn concrete_memo_keeps_child_observation_storage() {
        let program = Program::empty();
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        checker.begin_elaboration_journal();
        checker.begin_elaboration_journal();
        checker.record_typeof_type(Span::new(1, 2), &Type::Int(IntKind::I32));
        let child = checker.finish_elaboration_journal();
        let address = child.journal.iter().next().unwrap() as *const _;
        let memo = checker
            .build_elaboration_memo_entry(&Type::Bool, child, &concrete_context())
            .unwrap();
        let parent = checker.finish_elaboration_journal();
        assert!(std::ptr::eq(address, memo.journal.iter().next().unwrap()));
        assert!(std::ptr::eq(address, parent.journal.iter().next().unwrap()));
    }

    #[test]
    fn resolved_variables_still_use_skeleton_conversion() {
        let program = Program::empty();
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        checker.begin_elaboration_journal();
        let variable = checker.fresh_unknown();
        checker.solver.unify(&variable, &Type::Bool).unwrap();
        let mut frame = checker.finish_elaboration_journal();
        frame
            .journal
            .push(ElaborationJournalEntry::TypeOf(Span::new(1, 2), variable));
        let keep = frame.journal.clone();
        let memo = checker
            .build_elaboration_memo_entry(&Type::Bool, frame, &concrete_context())
            .unwrap();
        assert!(!std::ptr::eq(
            keep.iter().next().unwrap(),
            memo.journal.iter().next().unwrap()
        ));
        assert!(matches!(
            memo.journal.iter().next(),
            Some(ElaborationJournalEntry::TypeOf(_, Type::Bool))
        ));
    }

    #[test]
    fn replay_dedup_keeps_first_occurrences_across_shared_children() {
        let span = Span::new(0, 1);
        let first = ElaborationJournalEntry::PropKind(span, PropKind::Null);
        let conflict = ElaborationJournalEntry::PropKind(span, PropKind::Err);
        let mut child = ElaborationJournalFrame::default();
        child.push(first.clone());
        child.push(conflict.clone());
        child.push(first.clone());
        let mut parent = ElaborationJournalFrame::default();
        parent.push(first.clone());
        parent.extend(&child);
        assert_eq!(parent.journal.len(), 4);
        parent.prepare_for_replay();
        // Deduplication removes identical writes, not the intervening conflict.
        parent.extend(&child);
        assert_eq!(parent.journal.len(), 2);
        assert!(parent.journal.iter().eq([&first, &conflict]));
        // Shapes are ordered separately and are never observation-deduplicated.
        child
            .shapes
            .push((Type::Bool, ShapeConstraint::Equals(Type::Bool)));
        parent.extend(&child);
        parent.extend(&child);
        assert_eq!(parent.shapes.len(), 2);
    }

    #[test]
    fn fields_memo_replays_the_nested_instance_tag() {
        let program = Program::empty();
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        let span = Span::new(3, 4);
        let tag = checker.intern_tag(
            brass_hir::InstanceCallable::Function("child".into()),
            &[Type::Str],
        );
        checker.begin_elaboration_journal();
        checker.record_fields_loop_in(span, vec!["name".into()], Some(tag.clone()));
        let frame = checker.finish_elaboration_journal();
        let context = concrete_context();
        let memo = checker
            .build_elaboration_memo_entry(&Type::Bool, frame, &context)
            .unwrap();
        checker.fields_loops.clear();
        checker.fields_observations.clear();
        checker.enter_instance(
            brass_hir::InstanceCallable::Function("parent".into()),
            &[Type::Bool],
        );
        checker.replay_elaboration_memo_entry(&memo, &context);
        checker.leave_instance();
        // A conflicting reading belongs to child, not the parent active during replay.
        assert!(!checker.record_fields_loop_in(span, vec!["other".into()], Some(tag)));
        assert_eq!(checker.errors.len(), 1);
    }

    #[test]
    fn nested_hit_journal_is_composed_into_its_parent() {
        let program = Program::empty();
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        let child_span = Span::new(2, 3);

        checker.begin_elaboration_journal();
        checker.record_lift_err(child_span);
        let child_frame = checker.finish_elaboration_journal();
        let context = concrete_context();
        let child = checker
            .build_elaboration_memo_entry(&Type::Bool, child_frame, &context)
            .expect("self-contained entry");

        checker.begin_elaboration_journal();
        checker.record_null_prop(Span::new(0, 1));
        checker.replay_elaboration_memo_entry(&child, &context);
        checker.record_view_arg(Span::new(4, 5));
        let parent_frame = checker.finish_elaboration_journal();
        let parent = checker
            .build_elaboration_memo_entry(&Type::Bool, parent_frame, &context)
            .expect("self-contained entry");

        // The skipped child's observation remains between the parent's writes,
        // matching the order of a real nested body walk.
        assert!(matches!(
            parent.journal.iter().collect::<Vec<_>>().as_slice(),
            [
                ElaborationJournalEntry::NullProp(_),
                ElaborationJournalEntry::LiftErr(span),
                ElaborationJournalEntry::ViewArg(_),
            ] if *span == child_span
        ));
        // Shared child chunks still replay through the channel authorities.
        // Activate publication first so this exercises dirty keys, not the
        // initial full-table read.
        let mut replayed =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        let mut publication = stream::FlushState::default();
        delta::flush_delta(&replayed, &mut publication, false);
        replayed.replay_elaboration_memo_entry(&parent, &context);
        let changed = delta::flush_delta(&replayed, &mut publication, false);
        assert_eq!(changed.null_props, vec![Span::new(0, 1)]);
        assert_eq!(changed.lift_errs, vec![child_span]);
        assert_eq!(changed.view_args, vec![Span::new(4, 5)]);
    }

    #[test]
    fn replay_uses_conflict_helpers_and_keeps_typed_entries_idempotent() {
        let program = Program::empty();
        let rows = Rc::new(brass_typesys::RowInfo::analyze(&program));
        let mut recorded = Checker::new(&program, Rc::clone(&rows));
        let span = Span::new(0, 1);

        recorded.begin_elaboration_journal();
        recorded.record_prop_kind(span, PropKind::Null);
        recorded.record_typed(
            TypedExprKind::Int,
            span,
            Type::Int(IntKind::I32),
            Constness::Unknown,
        );
        let frame = recorded.finish_elaboration_journal();
        let context = concrete_context();
        let memo = recorded
            .build_elaboration_memo_entry(&Type::Bool, frame, &context)
            .expect("self-contained entry");

        let mut replayed = Checker::new(&program, rows);
        replayed.record_prop_kind(span, PropKind::Err);
        replayed.replay_elaboration_memo_entry(&memo, &context);
        replayed.replay_elaboration_memo_entry(&memo, &context);

        // A conflicting replay poisons through `record_prop_kind`, while the
        // second identical typed replay contributes no duplicate sidecar node.
        assert!(matches!(replayed.prop_kinds.get(&span), Some(None)));
        assert_eq!(replayed.errors.len(), 1);
        assert_eq!(replayed.typed.expressions.len(), 1);
    }

    #[test]
    fn memo_skeleton_discovers_variables_in_shape_and_journal_payloads() {
        let program = Program::empty();
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        let span = Span::new(0, 1);
        let vars: Vec<Type> = (0..9).map(|_| checker.fresh_unknown()).collect();
        let mut frame = ElaborationJournalFrame::default();
        frame
            .shapes
            .push((vars[0].clone(), ShapeConstraint::Equals(vars[1].clone())));
        frame.journal.extend([
            ElaborationJournalEntry::Typed {
                kind: TypedExprKind::Ident("payload".to_string()),
                span,
                ty: vars[2].clone(),
                constness: Constness::Unknown,
                instance: None,
            },
            ElaborationJournalEntry::SumView(span, vars[3].clone()),
            ElaborationJournalEntry::TypeOf(span, vars[4].clone()),
            ElaborationJournalEntry::TypeTest(span, vars[5].clone()),
            ElaborationJournalEntry::KeyedCall {
                span,
                receiver: "Receiver".to_string(),
                method: "method".to_string(),
                key: vars[6].clone(),
                instance: None,
            },
            ElaborationJournalEntry::InstanceReturn(
                "callee".to_string(),
                vec![vars[7].clone()],
                vars[8].clone(),
            ),
        ]);

        let memo = checker
            .build_elaboration_memo_entry(&Type::Bool, frame, &concrete_context())
            .expect("self-contained entry");

        // Every payload-only variable needs a replay-local placeholder; retaining
        // any checker-local id would couple otherwise independent memo hits.
        assert_eq!(memo.fresh.len(), vars.len());
    }

    #[test]
    fn memo_replay_applies_saved_input_bindings() {
        let program = Program::empty();
        let rows = Rc::new(brass_typesys::RowInfo::analyze(&program));
        let mut recorded = Checker::new(&program, Rc::clone(&rows));
        let input = recorded.fresh_unknown();
        recorded.solver.unify(&input, &Type::Str).unwrap();
        let canon = CanonVar {
            slot: 0,
            kind: InferenceVarKind::Source,
        };
        let context = ElaborationMemoContext {
            key: ElaborationMemoKey {
                flavor: MemoFlavor::Ordinary,
                callable: "input-binding".to_string(),
                receiver: None,
                args: vec![Type::Unknown(canon.slot)],
                scheme_inputs: Vec::new(),
                canon_vars: vec![canon],
            },
            inputs: vec![(canon, input)],
        };
        let memo = recorded
            .build_elaboration_memo_entry(&Type::Void, ElaborationJournalFrame::default(), &context)
            .expect("self-contained entry");

        let mut replayed = Checker::new(&program, rows);
        let replay_input = replayed.fresh_unknown();
        let replay_context = ElaborationMemoContext {
            key: context.key,
            inputs: vec![(canon, replay_input.clone())],
        };
        replayed.replay_elaboration_memo_entry(&memo, &replay_context);

        // The replay is responsible for constraining the new caller variable to
        // the binding learned while the memo entry was recorded.
        assert_eq!(replayed.resolve(&replay_input), Type::Str);
    }
}
