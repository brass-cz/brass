//! The channel delta a streaming run flushes after each checked body.

use super::*;

mod channels;
mod numeric;
mod reference;
mod verify;

/// Flush the channel entries recorded since the previous flush into a
/// [`stream::ChannelDelta`] (see the field notes there). `terminal` is the
/// flush after `finalize_typed`: the recorded types were re-resolved in
/// place -- which a prefix cursor cannot see -- so the aggregate scans
/// restart from scratch.
pub(super) fn flush_delta(
    checker: &Checker,
    state: &mut stream::FlushState,
    terminal: bool,
) -> stream::ChannelDelta {
    assert!(
        !checker.channel_changes.borrow().forked,
        "publication inside a checker fork"
    );
    assert_eq!(
        checker.speculation_depth, 0,
        "publication inside a speculative probe"
    );
    state.counters = Default::default();
    let started = tracing::enabled!(target: "brass_typeck::channels", tracing::Level::DEBUG)
        .then(std::time::Instant::now);
    let delta = publish(checker, state, terminal);
    if verify::enabled() {
        let reference = state.reference.get_or_insert_with(Default::default);
        let expected = reference::flush_delta(checker, reference, terminal);
        verify::assert_delta(&delta, &expected);
    }
    if let Some(started) = started {
        tracing::debug!(target: "brass_typeck::channels", terminal,
            elapsed_us = started.elapsed().as_micros(),
            typed_pending = state.typed_pending.len(),
            instance_pending = state.instance_pending.len(),
            typed_resolutions = state.counters.typed_resolutions,
            instance_resolutions = state.counters.instance_resolutions,
            tag_resolutions = state.counters.tag_resolutions,
            typed_cache_hits = state.counters.typed_cache_hits,
            tag_cache_hits = state.counters.tag_cache_hits,
            invalidated_readers = state.counters.invalidated_readers,
            solution_epoch = state.counters.solution_epoch,
            dirty_seed_spans = state.counters.dirty_seed_spans,
            instance_maps = state.counters.instance_maps,
            shared_spans = state.expr_flushed.len(),
            instance_spans = state.instance_flushed.len(),
            "channel publication");
    }
    delta
}

fn publish(
    checker: &Checker,
    state: &mut stream::FlushState,
    terminal: bool,
) -> stream::ChannelDelta {
    let mut delta = stream::ChannelDelta::default();
    let mut dirty_seeds = HashSet::default();
    let mut dirty_receivers = HashSet::default();
    if terminal {
        dirty_seeds.extend(state.expr_flushed.keys().copied());
        dirty_seeds.extend(state.instance_flushed.keys().copied());
        dirty_receivers.extend(state.receivers_flushed.keys().copied());
        dirty_receivers.extend(state.receiver_owners_flushed.keys().copied());
    }
    // Aggregate result types: fold the newly recorded typed expressions into
    // the running per-span agreement, then diff the seedable view against
    // what was already delivered. A span can gain a seed (it resolved, or
    // was first seen), change it (superseded value), or lose it (a later
    // instantiation disagreed).
    if terminal {
        state.publication = Default::default();
        state.typed_seen = 0;
        state.typed_pending.clear();
        state.agg = Default::default();
        state.receivers = Default::default();
        state.instance_seen = 0;
        state.instance_pending.clear();
        state.instance_agg = Default::default();
    }
    let (dirty_typed, dirty_instances, dirty_sums, dirty_numeric) =
        state.publication.invalidate(checker, &mut state.counters);
    // Preserve observation order and the pending discipline: only entries the
    // pending scan registered as open are revisited before the terminal rebuild.
    let pending: Vec<_> = dirty_typed
        .into_iter()
        .filter(|index| state.typed_pending.remove(index))
        .collect();
    for index in pending
        .into_iter()
        .chain(state.typed_seen..checker.typed.expressions.len())
    {
        let raw = &checker.typed.expressions[index];
        if !stream::aggregates_from_kind(&raw.kind)
            && !matches!(raw.kind, brass_hir::TypedExprKind::MethodReceiver)
        {
            continue;
        }
        let observation = state
            .publication
            .observation(checker, index, &mut state.counters);
        let e = &observation.expression;
        if stream::seeds_from_kind(&e.kind)
            && !brass_hir::is_fully_known(brass_hir::peel_modes(&e.ty))
        {
            state.typed_pending.insert(index);
        }
        let changed = if stream::instance_numeric(&e.kind)
            && matches!(brass_hir::peel_modes(&e.ty), Type::Int(_) | Type::Float(_))
        {
            state.agg.poison(e.span)
        } else {
            state
                .agg
                .observe_prepared(e.span, observation.aggregate.as_ref())
        };
        if changed {
            dirty_seeds.insert(e.span);
        }
        if state.receivers.observe(e, checker.program) {
            dirty_receivers.insert(e.span);
        }
    }
    state.typed_seen = checker.typed.expressions.len();
    // Per-instance seeds: an observation joins the per-instance agreement once
    // both its instance's argument types and its own type are known (the
    // same pending discipline as the span-keyed scan above), and the spans
    // the span-keyed seeds leave out are published per instance.
    let pending: Vec<_> = dirty_instances
        .into_iter()
        .filter(|index| state.instance_pending.remove(index))
        .collect();
    for index in pending
        .into_iter()
        .chain(state.instance_seen..checker.instance_typed.len())
    {
        state.counters.instance_resolutions += 1;
        let entry = &checker.instance_typed[index];
        let observation =
            state
                .publication
                .observation(checker, entry.index as usize, &mut state.counters);
        let tag = state.publication.tag(
            checker,
            &entry.tag,
            &mut state.instance_agg,
            &mut state.counters,
        );
        let typed = &observation.expression;
        match tag.key {
            Some(key) if brass_hir::is_fully_known(brass_hir::peel_modes(&typed.ty)) => {
                if state.instance_agg.observe_prepared(
                    key,
                    typed.span,
                    observation.aggregate.as_ref(),
                ) {
                    dirty_seeds.insert(typed.span);
                }
                state.publication.settle_instance(index);
            }
            _ => {
                state.instance_pending.insert(index);
                state.publication.wait_instance(index, &observation, &tag);
            }
        }
    }
    state.instance_seen = checker.instance_typed.len();
    numeric::publish(checker, state, &mut delta, terminal, dirty_numeric);
    state.counters.dirty_seed_spans = dirty_seeds.len();
    for span in dirty_seeds {
        match state.agg.seed_at(&span) {
            Some(ty) if state.expr_flushed.get(&span) != Some(ty) => {
                delta.expr_types.push((span, ty.clone()));
                state.expr_flushed.insert(span, ty.clone());
            }
            None if state.expr_flushed.remove(&span).is_some() => {
                delta.expr_types_removed.push(span)
            }
            _ => {}
        }
        // Shared agreement changes can expose instance readings accumulated
        // earlier, even when this boundary observed no new instance value.
        let seeds = state
            .instance_agg
            .seeds_at(&span, state.expr_flushed.contains_key(&span));
        state.counters.instance_maps += usize::from(seeds.is_some());
        match seeds {
            Some(seeds) if state.instance_flushed.get(&span) != Some(&seeds) => {
                delta.instance_seeds.push((
                    span,
                    seeds.iter().map(|(k, t)| (k.clone(), t.clone())).collect(),
                ));
                state.instance_flushed.insert(span, seeds);
            }
            None if state.instance_flushed.remove(&span).is_some() => {
                delta.instance_seeds.push((span, Vec::new()))
            }
            _ => {}
        }
    }
    for span in dirty_receivers {
        match state.receivers.agreed_at(&span) {
            Some(ty) if state.receivers_flushed.get(&span) != Some(ty) => {
                delta.receiver_types.push((span, ty.clone()));
                state.receivers_flushed.insert(span, ty.clone());
            }
            None if state.receivers_flushed.remove(&span).is_some() => {
                delta.receiver_types_removed.push(span)
            }
            _ => {}
        }
        // Ambiguous owner sets retain the last delivered list, matching the
        // append-only owner channel's publication semantics.
        if let Some(owners) = state.receivers.owners_at(&span, checker.program)
            && state.receiver_owners_flushed.get(&span) != Some(&owners)
        {
            delta.receiver_owners.push((span, owners.clone()));
            state.receiver_owners_flushed.insert(span, owners);
        }
    }
    channels::publish(checker, state, &mut delta, terminal, dirty_sums);
    delta
}

#[cfg(test)]
mod tests;
