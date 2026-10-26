//! Incremental publication of concrete numeric call contracts.

use super::*;

/// Publish newly recorded contracts and records whose instance dependencies resolved.
pub(super) fn publish(
    checker: &Checker,
    state: &mut stream::FlushState,
    delta: &mut stream::ChannelDelta,
    terminal: bool,
    dirty: std::collections::BTreeSet<usize>,
) {
    let mut changed = HashSet::default();
    if terminal {
        state.numeric_seen = 0;
        state.numeric_pending.clear();
        state.numeric_current.clear();
        changed.extend(state.numeric_flushed.keys().cloned());
    }
    let pending: Vec<_> = dirty
        .into_iter()
        .filter(|index| state.numeric_pending.remove(index))
        .collect();
    for index in pending
        .into_iter()
        .chain(state.numeric_seen..checker.numeric_observations.len())
    {
        let observation = &checker.numeric_observations[index];
        let instance = if let Some(tag) = &observation.instance {
            let resolved =
                state
                    .publication
                    .tag(checker, tag, &mut state.instance_agg, &mut state.counters);
            let Some(key) = resolved.key else {
                state.numeric_pending.insert(index);
                state.publication.watch_numeric(index, &resolved);
                continue;
            };
            Some(state.instance_agg.key(key).clone())
        } else {
            None
        };
        state.publication.settle_numeric(index);
        let key = (observation.span, instance);
        state
            .numeric_current
            .insert(key.clone(), observation.ty.clone());
        changed.insert(key);
    }
    state.numeric_seen = checker.numeric_observations.len();
    for key in changed {
        match state.numeric_current.get(&key) {
            Some(ty) if state.numeric_flushed.get(&key) != Some(ty) => {
                state.numeric_flushed.insert(key.clone(), ty.clone());
                delta.numeric_calls.push((key, ty.clone()));
            }
            None if state.numeric_flushed.remove(&key).is_some() => {
                delta.numeric_calls_removed.push(key)
            }
            _ => {}
        }
    }
}
