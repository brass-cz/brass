//! Instance-qualified observations of compile-time record iteration.

use super::instances::TagRef;
use super::journal::ElaborationJournalEntry;
use super::*;

pub(super) mod recursion;

/// One checked expansion, retaining an open instance tag until publication.
#[derive(Clone, PartialEq, Eq)]
pub(super) struct FieldsObservation {
    instance: Option<TagRef>,
    fields: Vec<String>,
}

impl Checker<'_> {
    /// Record the field names checked by this elaboration of a loop.
    /// Return false after reporting a conflict within its callable instance.
    pub(super) fn record_fields_loop(&mut self, span: Span, fields: Vec<String>) -> bool {
        self.record_fields_loop_in(span, fields, self.current_instance())
    }

    /// Apply a walk or replay under its original enclosing instance identity.
    /// Pattern probes publish nothing; conflicting committed lists return false.
    pub(super) fn record_fields_loop_in(
        &mut self,
        span: Span,
        fields: Vec<String>,
        instance: Option<TagRef>,
    ) -> bool {
        if self.fields_probe_depth > 0 {
            return true;
        }
        self.journal_elaboration(ElaborationJournalEntry::FieldsLoop {
            span,
            fields: fields.clone(),
            instance: instance.clone(),
        });
        let observation = FieldsObservation { instance, fields };
        let key = observation
            .instance
            .as_ref()
            .and_then(|tag| self.instance_key_of(tag));
        let conflict = self
            .fields_observations
            .get(&span)
            .is_some_and(|observations| {
                observations.iter().any(|previous| {
                    let same_instance = previous.instance == observation.instance
                        || key.as_ref().is_some_and(|key| {
                            previous
                                .instance
                                .as_ref()
                                .and_then(|tag| self.instance_key_of(tag))
                                .as_ref()
                                == Some(key)
                        });
                    same_instance && previous.fields != observation.fields
                })
            });
        if conflict {
            self.errors.push(TypeError {
                message: "`fields(..)` expands different field sets within one instantiation of this generic function (annotate the operand to fix it)".to_string(),
                span,
            });
            return false;
        }
        self.fields_loops
            .entry(span)
            .or_insert_with(|| observation.fields.clone());
        let observations = self.fields_observations.entry(span).or_default();
        if !observations.contains(&observation) {
            observations.push(observation);
        }
        self.channel_changes
            .get_mut()
            .mark(channel_changes::Channel::FieldsLoop, span);
        true
    }

    /// Reject observations whose initially open tags settled to one conflicting instance.
    pub(super) fn report_fields_conflicts(&mut self) {
        let mut conflicts = Vec::new();
        for (span, observations) in &self.fields_observations {
            let mut seen = HashMap::default();
            for observation in observations {
                if let Some(key) = observation
                    .instance
                    .as_ref()
                    .and_then(|tag| self.instance_key_of(tag))
                    && let Some(previous) = seen.insert(key, &observation.fields)
                    && previous != &observation.fields
                {
                    conflicts.push(*span);
                    break;
                }
            }
        }
        for span in conflicts {
            self.errors.push(TypeError {
                message: "`fields(..)` expands different field sets within one instantiation of this generic function (annotate the operand to fix it)".to_string(), span,
            });
        }
    }

    /// Publish shared lists unchanged; differing concrete instances get overrides.
    /// Open declaration probes cannot override a concrete call's checked expansion.
    pub(super) fn settled_fields_loops(
        &self,
    ) -> (
        HashMap<Span, Vec<String>>,
        brass_hir::InstanceChannel<Vec<String>>,
    ) {
        let mut shared = self.fields_loops.clone();
        let mut instances = brass_hir::InstanceChannel::default();
        for (span, observations) in &self.fields_observations {
            let mut entries: HashMap<brass_hir::InstanceKey, Option<Vec<String>>> =
                HashMap::default();
            for observation in observations {
                let Some(key) = observation
                    .instance
                    .as_ref()
                    .and_then(|tag| self.instance_key_of(tag))
                else {
                    continue;
                };
                let entry = entries
                    .entry(key)
                    .or_insert_with(|| Some(observation.fields.clone()));
                if entry.as_ref() != Some(&observation.fields) {
                    *entry = None;
                }
            }
            let mut lists: Vec<_> = entries.values().flatten().cloned().collect();
            lists.sort();
            lists.dedup();
            if let Some(first) = lists.first() {
                shared.insert(*span, first.clone());
            }
            if lists.len() > 1 || entries.values().any(Option::is_none) {
                instances.insert(
                    *span,
                    entries
                        .into_iter()
                        .filter_map(|(key, fields)| fields.map(|fields| (key, fields)))
                        .collect(),
                );
            }
        }
        (shared, instances)
    }
}
