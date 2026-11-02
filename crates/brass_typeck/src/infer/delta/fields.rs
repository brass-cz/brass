//! Publish record expansions after the enclosing instance identities settle.

use super::*;

/// Replace delivered lists only when their shared or instance-qualified value changes.
pub(super) fn publish(
    checker: &Checker,
    state: &mut stream::FlushState,
    delta: &mut stream::ChannelDelta,
) {
    let (shared, instances) = checker.settled_fields_loops();
    for (span, fields) in shared {
        if state.fields_loops.get(&span) != Some(&fields) {
            delta.fields_loops.push((span, fields.clone()));
            state.fields_loops.insert(span, fields);
        }
    }
    let removed: Vec<_> = state
        .instance_fields
        .keys()
        .filter(|span| !instances.contains_key(span))
        .copied()
        .collect();
    for span in removed {
        state.instance_fields.remove(&span);
        delta.instance_fields.push((span, Vec::new()));
    }
    for (span, entries) in instances {
        if state.instance_fields.get(&span) != Some(&entries) {
            delta.instance_fields.push((
                span,
                entries
                    .iter()
                    .map(|(key, fields)| (key.clone(), fields.clone()))
                    .collect(),
            ));
            state.instance_fields.insert(span, entries);
        }
    }
}
