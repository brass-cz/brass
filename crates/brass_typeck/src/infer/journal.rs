//! Replayable observations made while elaborating callable bodies.

use std::hash::{Hash, Hasher};

use brass_hir::{Constness, TypedExprKind};
use fxhash::{FxHashMap, FxHasher};

use super::*;

/// One semantic channel observation made while elaborating a callable body.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) enum ElaborationJournalEntry {
    Typed {
        kind: TypedExprKind,
        span: Span,
        ty: Type,
        constness: Constness,
    },
    PropKind(Span, PropKind),
    NullProp(Span),
    SumView(Span, Type),
    SumViewIdentity(Span),
    LiftKind(Span, bool),
    LiftErr(Span),
    TypeName(Span, String),
    TypeOf(Span, Type),
    TypeTest(Span, Type),
    FieldsLoop(Span, Vec<String>),
    ViewArg(Span),
    KeyedCall(Span, String, String, Type),
    InstanceReturn(String, Vec<Type>, Type),
}

/// The reusable result of one clean elaboration.
#[derive(Clone)]
pub(super) struct ElaborationMemoEntry {
    pub(super) ret: Type,
    journal: Vec<ElaborationJournalEntry>,
}

pub(super) struct ElaborationJournalFrame {
    journal: Vec<ElaborationJournalEntry>,
    journal_seen: Option<FxHashMap<u64, Vec<usize>>>,
    journalable: bool,
}

impl Default for ElaborationJournalFrame {
    fn default() -> Self {
        Self {
            journal: Vec::new(),
            journal_seen: None,
            journalable: true,
        }
    }
}

impl ElaborationJournalFrame {
    fn push(&mut self, entry: ElaborationJournalEntry) {
        if let Some(seen) = &mut self.journal_seen {
            let hash = fx_hash(&entry);
            if seen
                .get(&hash)
                .is_some_and(|indices| indices.iter().any(|index| self.journal[*index] == entry))
            {
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
        for entry in std::mem::take(&mut self.journal) {
            let hash = fx_hash(&entry);
            if seen
                .get(&hash)
                .is_some_and(|indices| indices.iter().any(|index| journal[*index] == entry))
            {
                continue;
            }
            seen.entry(hash).or_default().push(journal.len());
            journal.push(entry);
        }
        self.journal = journal;
        self.journal_seen = Some(seen);
    }

    fn extend(&mut self, child: &Self) {
        for entry in &child.journal {
            self.push(entry.clone());
        }
        self.journalable &= child.journalable;
    }

    pub(super) fn is_journalable(&self) -> bool {
        self.journalable
    }
}

fn fx_hash(value: &impl Hash) -> u64 {
    let mut hasher = FxHasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

impl Checker<'_> {
    pub(super) fn journal_elaboration(&mut self, entry: ElaborationJournalEntry) {
        if let Some(frame) = self.elaboration_journals.last_mut() {
            frame.push(entry);
        }
    }

    pub(super) fn begin_elaboration_journal(&mut self) {
        self.elaboration_journals
            .push(ElaborationJournalFrame::default());
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
        }
        frame
    }

    pub(super) fn build_elaboration_memo_entry(
        &self,
        ret: &Type,
        frame: ElaborationJournalFrame,
    ) -> ElaborationMemoEntry {
        let journal = frame
            .journal
            .into_iter()
            .map(|entry| self.resolve_journal_entry(entry))
            .collect();
        ElaborationMemoEntry {
            ret: self.resolve(ret),
            journal,
        }
    }

    /// Replay must traverse the same helper so poison semantics are those of a
    /// real elaboration.
    pub(super) fn replay_elaboration_memo_entry(&mut self, entry: &ElaborationMemoEntry) -> Type {
        if let Some(frame) = self.elaboration_journals.last_mut() {
            frame.prepare_for_replay();
        }
        for observation in &entry.journal {
            self.replay_elaboration_journal_entry(observation);
        }
        entry.ret.clone()
    }

    fn resolve_journal_entry(&self, entry: ElaborationJournalEntry) -> ElaborationJournalEntry {
        match entry {
            ElaborationJournalEntry::Typed {
                kind,
                span,
                ty,
                constness,
            } => ElaborationJournalEntry::Typed {
                kind,
                span,
                ty: self.resolve(&ty),
                constness,
            },
            ElaborationJournalEntry::SumView(span, ty) => {
                ElaborationJournalEntry::SumView(span, self.resolve(&ty))
            }
            ElaborationJournalEntry::TypeOf(span, ty) => {
                ElaborationJournalEntry::TypeOf(span, self.resolve(&ty))
            }
            ElaborationJournalEntry::TypeTest(span, ty) => {
                ElaborationJournalEntry::TypeTest(span, self.resolve(&ty))
            }
            ElaborationJournalEntry::KeyedCall(span, receiver, method, key) => {
                ElaborationJournalEntry::KeyedCall(span, receiver, method, self.resolve(&key))
            }
            ElaborationJournalEntry::InstanceReturn(symbol, args, ret) => {
                ElaborationJournalEntry::InstanceReturn(
                    symbol,
                    args.into_iter().map(|arg| self.resolve(&arg)).collect(),
                    self.resolve(&ret),
                )
            }
            other => other,
        }
    }

    fn replay_elaboration_journal_entry(&mut self, entry: &ElaborationJournalEntry) {
        match entry {
            ElaborationJournalEntry::Typed {
                kind,
                span,
                ty,
                constness,
            } => self.record_typed(kind.clone(), *span, ty.clone(), *constness),
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
            ElaborationJournalEntry::TypeOf(span, ty) => self.record_typeof_type(*span, ty),
            ElaborationJournalEntry::TypeTest(span, ty) => self.record_type_test(*span, ty),
            ElaborationJournalEntry::FieldsLoop(span, fields) => {
                self.record_fields_loop(*span, fields.clone());
            }
            ElaborationJournalEntry::ViewArg(span) => self.record_view_arg(*span),
            ElaborationJournalEntry::KeyedCall(span, receiver, method, key) => {
                self.record_keyed_call(*span, receiver.clone(), method.clone(), key.clone())
            }
            ElaborationJournalEntry::InstanceReturn(symbol, args, ret) => {
                self.record_instance_return(symbol.clone(), args.clone(), ret.clone())
            }
        }
    }

    pub(super) fn record_typed(
        &mut self,
        kind: TypedExprKind,
        span: Span,
        ty: Type,
        constness: Constness,
    ) {
        self.journal_elaboration(ElaborationJournalEntry::Typed {
            kind: kind.clone(),
            span,
            ty: ty.clone(),
            constness,
        });
        let hash = fx_hash(&(&kind, span, &ty, constness));
        if self.typed_seen.get(&hash).is_some_and(|indices| {
            indices.iter().any(|index| {
                let recorded = &self.typed.expressions[*index];
                recorded.kind == kind
                    && recorded.span == span
                    && recorded.ty == ty
                    && recorded.constness == constness
            })
        }) {
            return;
        }
        let index = self.typed.expressions.len();
        self.typed.push_kind(kind, span, ty, constness);
        self.typed_seen.entry(hash).or_default().push(index);
    }

    pub(super) fn record_null_prop(&mut self, span: Span) {
        self.journal_elaboration(ElaborationJournalEntry::NullProp(span));
        self.null_props.insert(span);
    }

    pub(super) fn record_lift_err(&mut self, span: Span) {
        self.journal_elaboration(ElaborationJournalEntry::LiftErr(span));
        self.lift_errs.insert(span);
    }

    pub(super) fn record_type_name(&mut self, span: Span, name: String) {
        self.journal_elaboration(ElaborationJournalEntry::TypeName(span, name.clone()));
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

    pub(super) fn record_typeof_type(&mut self, span: Span, ty: &Type) {
        let concrete = self.resolve(ty);
        if !is_concrete_type(&concrete) || self.typeof_poisoned.contains(&span) {
            return;
        }
        self.journal_elaboration(ElaborationJournalEntry::TypeOf(span, concrete.clone()));
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

    pub(super) fn record_fields_loop(&mut self, span: Span, fields: Vec<String>) -> bool {
        self.journal_elaboration(ElaborationJournalEntry::FieldsLoop(span, fields.clone()));
        if let Some(prev) = self.fields_loops.get(&span)
            && prev != &fields
        {
            self.errors.push(TypeError {
                message: "`fields(..)` expands different field sets across instantiations \
                          of this generic function (annotate the operand to fix it)"
                    .to_string(),
                span,
            });
            return false;
        }
        self.fields_loops.insert(span, fields);
        true
    }

    pub(super) fn record_view_arg(&mut self, span: Span) {
        self.journal_elaboration(ElaborationJournalEntry::ViewArg(span));
        self.view_args.insert(span);
    }

    pub(super) fn record_keyed_call(
        &mut self,
        span: Span,
        receiver: String,
        method: String,
        key: Type,
    ) {
        self.journal_elaboration(ElaborationJournalEntry::KeyedCall(
            span,
            receiver.clone(),
            method.clone(),
            key.clone(),
        ));
        self.keyed_calls.insert(span, (receiver, method, key));
    }

    pub(super) fn record_instance_return(&mut self, symbol: String, args: Vec<Type>, ret: Type) {
        self.journal_elaboration(ElaborationJournalEntry::InstanceReturn(
            symbol.clone(),
            args.clone(),
            ret.clone(),
        ));
        self.instance_returns.insert((symbol, args), ret);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_hit_journal_is_composed_into_its_parent() {
        let program = Program::empty();
        let mut checker = Checker::new(&program);
        let child_span = Span::new(2, 3);

        checker.begin_elaboration_journal();
        checker.record_lift_err(child_span);
        let child_frame = checker.finish_elaboration_journal();
        let child = checker.build_elaboration_memo_entry(&Type::Bool, child_frame);

        checker.begin_elaboration_journal();
        checker.record_null_prop(Span::new(0, 1));
        checker.replay_elaboration_memo_entry(&child);
        checker.record_view_arg(Span::new(4, 5));
        let parent_frame = checker.finish_elaboration_journal();
        let parent = checker.build_elaboration_memo_entry(&Type::Bool, parent_frame);

        // The skipped child's observation remains between the parent's writes,
        // matching the order of a real nested body walk.
        assert!(matches!(
            parent.journal.as_slice(),
            [
                ElaborationJournalEntry::NullProp(_),
                ElaborationJournalEntry::LiftErr(span),
                ElaborationJournalEntry::ViewArg(_),
            ] if *span == child_span
        ));
    }

    #[test]
    fn replay_uses_conflict_helpers_and_keeps_typed_entries_idempotent() {
        let program = Program::empty();
        let mut recorded = Checker::new(&program);
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
        let memo = recorded.build_elaboration_memo_entry(&Type::Bool, frame);

        let mut replayed = Checker::new(&program);
        replayed.record_prop_kind(span, PropKind::Err);
        replayed.replay_elaboration_memo_entry(&memo);
        replayed.replay_elaboration_memo_entry(&memo);

        // A conflicting replay poisons through `record_prop_kind`, while the
        // second identical typed replay contributes no duplicate sidecar node.
        assert!(matches!(replayed.prop_kinds.get(&span), Some(None)));
        assert_eq!(replayed.errors.len(), 1);
        assert_eq!(replayed.typed.expressions.len(), 1);
    }
}
