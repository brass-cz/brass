//! The channel delta a streaming run flushes after each checked body.

use super::super::*;

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
    let mut delta = stream::ChannelDelta::default();
    let numeric = checker.numeric_call_map();
    for (key, ty) in &numeric {
        if state.numeric_flushed.get(key) != Some(ty) {
            delta.numeric_calls.push((key.clone(), ty.clone()));
        }
    }
    for key in state.numeric_flushed.keys() {
        if !numeric.contains_key(key) {
            delta.numeric_calls_removed.push(key.clone());
        }
    }
    state.numeric_flushed = numeric;
    // Aggregate result types: fold the newly recorded typed expressions into
    // the running per-span agreement, then diff the seedable view against
    // what was already delivered. A span can gain a seed (it resolved, or
    // was first seen), change it (superseded value), or lose it (a later
    // instantiation disagreed).
    if terminal {
        state.typed_seen = 0;
        state.typed_pending.clear();
        state.agg = Default::default();
        state.receivers = Default::default();
        state.instance_seen = 0;
        state.instance_pending.clear();
        state.instance_agg = Default::default();
    }
    // An entry was resolved when it was RECORDED, which can be mid-body: a
    // constructor's open slots are pinned by the statements after it
    // (`HashMap.new()` then `set`), or by a LATER body altogether (a global
    // `HashMap.new()` filled by `main`). Resolve against the substitution as it
    // stands NOW -- at a body boundary, with the whole body's pins committed --
    // and keep an entry that is still open pending, to be resolved again at
    // the next flush; otherwise it would stay invisible to the aggregate until
    // the terminal flush, far too late for a consumer that lowers the body's
    // MIR from these deltas.
    let pending = std::mem::take(&mut state.typed_pending);
    for index in pending
        .into_iter()
        .chain(state.typed_seen..checker.typed.expressions.len())
    {
        let mut e = checker.typed.expressions[index].clone();
        e.ty = checker.solver.resolve_reference(&e.ty);
        if stream::seeds_from_kind(&e.kind)
            && !brass_hir::is_fully_known(brass_hir::peel_modes(&e.ty))
        {
            state.typed_pending.insert(index);
        }
        state.agg.observe(&e, checker.program);
        state.receivers.observe(&e, checker.program);
    }
    state.typed_seen = checker.typed.expressions.len();
    let want = state.agg.seedable_map();
    for (span, ty) in &want {
        if state.expr_flushed.get(span) != Some(ty) {
            delta.expr_types.push((*span, ty.clone()));
        }
    }
    for span in state.expr_flushed.keys() {
        if !want.contains_key(span) {
            delta.expr_types_removed.push(*span);
        }
    }
    // Per-instance seeds: an observation joins the per-instance agreement once
    // both its instance's argument types and its own type are known (the
    // same pending discipline as the span-keyed scan above), and the spans
    // the span-keyed seeds leave out are published per instance.
    let pending = std::mem::take(&mut state.instance_pending);
    let mut keys: HashMap<instances::TagRef, Option<u32>> = HashMap::default();
    for index in pending
        .into_iter()
        .chain(state.instance_seen..checker.instance_typed.len())
    {
        let entry = &checker.instance_typed[index];
        let typed = &checker.typed.expressions[entry.index as usize];
        let key = *keys.entry(entry.tag.clone()).or_insert_with(|| {
            let mut key = brass_hir::InstanceKey::new(
                checker.program,
                entry.tag.callable.clone(),
                &entry
                    .tag
                    .args
                    .iter()
                    .map(|ty| checker.solver.resolve_reference(ty))
                    .collect::<Vec<_>>(),
            )?;
            key.numeric_layout = entry.tag.numeric_layout.clone();
            Some(state.instance_agg.key_id(&key))
        });
        let ty = checker.solver.resolve_reference(&typed.ty);
        match key {
            Some(key) if brass_hir::is_fully_known(brass_hir::peel_modes(&ty)) => {
                state
                    .instance_agg
                    .observe(key, &typed.kind, typed.span, &ty, checker.program);
            }
            _ => {
                state.instance_pending.insert(index);
            }
        }
    }
    state.instance_seen = checker.instance_typed.len();
    let instance_want = state.instance_agg.seed_map(&want);
    for (span, seeds) in &instance_want {
        if state.instance_flushed.get(span) != Some(seeds) {
            delta.instance_seeds.push((
                *span,
                seeds.iter().map(|(k, t)| (k.clone(), t.clone())).collect(),
            ));
        }
    }
    for span in state.instance_flushed.keys() {
        if !instance_want.contains_key(span) {
            delta.instance_seeds.push((*span, Vec::new()));
        }
    }
    state.instance_flushed = instance_want;
    state.expr_flushed = want;
    let want = state.receivers.agreed_map();
    for (span, ty) in &want {
        if state.receivers_flushed.get(span) != Some(ty) {
            delta.receiver_types.push((*span, ty.clone()));
        }
    }
    for span in state.receivers_flushed.keys() {
        if !want.contains_key(span) {
            delta.receiver_types_removed.push(*span);
        }
    }
    state.receivers_flushed = want;
    // A call's owner list only grows (an owner once observed stays), so a
    // changed list is re-emitted whole.
    for (span, owners) in state.receivers.owner_map(checker.program) {
        if state.receiver_owners_flushed.get(&span) != Some(&owners) {
            delta.receiver_owners.push((span, owners.clone()));
            state.receiver_owners_flushed.insert(span, owners);
        }
    }
    // Channels whose entries are only ever added (a field call's entry is
    // re-emitted when its receiver list changes).
    for (span, receivers) in checker.field_call_map() {
        if state.field_calls.get(&span) != Some(&receivers) {
            delta.field_calls.push((span, receivers.clone()));
            state.field_calls.insert(span, receivers);
        }
    }
    for s in checker.view_args.difference(&state.view_args) {
        delta.view_args.push(*s);
    }
    state.view_args.extend(delta.view_args.iter().copied());
    for s in checker.lift_errs.difference(&state.lift_errs) {
        delta.lift_errs.push(*s);
    }
    state.lift_errs.extend(delta.lift_errs.iter().copied());
    for s in checker.null_props.difference(&state.null_props) {
        delta.null_props.push(*s);
    }
    state.null_props.extend(delta.null_props.iter().copied());
    for (span, fields) in &checker.fields_loops {
        if state.fields_loops.insert(*span) {
            delta.fields_loops.push((*span, fields.clone()));
        }
    }
    // Last-write-wins maps. `sum_views` values mirror the eager channel
    // copy: resolved against the current substitution, with a still-open
    // `Result` payload defaulted to `void` -- an Err-only flow may leave the
    // Ok slot pinned by nothing, ever, so waiting for it to close would
    // withhold the entry forever. The default is provisional: a later body
    // that does pin the slot changes the resolved value, and the revision is
    // re-emitted for the consumer to re-lower against.
    for (span, t) in &checker.sum_views {
        let mut t = checker.solver.resolve_reference(t);
        if let Type::Sum(n) = &mut t
            && n.is_result_type()
        {
            for key in [
                brass_hir::types::RESULT_OK_VALUE,
                brass_hir::types::RESULT_ERR_ERROR,
            ] {
                if n.substitution.get(key).is_none_or(|t| t.is_unknown()) {
                    n.substitution.insert(key, Type::Void);
                }
            }
        }
        if state.sum_views.get(span) != Some(&t) {
            delta.sum_views.push((*span, t.clone()));
            state.sum_views.insert(*span, t);
        }
    }
    for (span, name) in &checker.type_names {
        if state.type_names.get(span) != Some(name) {
            delta.type_names.push((*span, name.clone()));
            state.type_names.insert(*span, name.clone());
        }
    }
    for (span, t) in &checker.typeof_types {
        if state.typeof_types.get(span) != Some(t) {
            delta.typeof_types.push((*span, t.clone()));
            state.typeof_types.insert(*span, t.clone());
        }
    }
    // A typeof entry disappears when disagreeing instantiations poison it.
    let poisoned: Vec<Span> = state
        .typeof_types
        .keys()
        .filter(|s| !checker.typeof_types.contains_key(*s))
        .copied()
        .collect();
    for span in poisoned {
        state.typeof_types.remove(&span);
        delta.typeof_types_removed.push(span);
    }
    // Type-test patterns follow the typeof discipline: last-write-wins values
    // (a wildcard hole is a legitimate final value, so entries are emitted
    // as-is, never withheld for openness), removals on poisoning.
    for (span, t) in &checker.type_tests {
        if state.type_tests.get(span) != Some(t) {
            delta.type_tests.push((*span, t.clone()));
            state.type_tests.insert(*span, t.clone());
        }
    }
    let poisoned: Vec<Span> = state
        .type_tests
        .keys()
        .filter(|s| !checker.type_tests.contains_key(*s))
        .copied()
        .collect();
    for span in poisoned {
        state.type_tests.remove(&span);
        delta.type_tests_removed.push(span);
    }
    // Clean call-site elaborations can discover contracts for nested
    // unannotated callees before their dedicated body pass. Stream each new
    // instance so runtime resolution can keep the whole call chain deferred.
    for (key, ret) in &checker.instance_returns {
        if state.instance_returns.get(key) != Some(ret) {
            delta
                .instance_returns
                .push((key.0.clone(), key.1.clone(), ret.clone()));
            state.instance_returns.insert(key.clone(), ret.clone());
        }
    }
    for (span, (receiver, method, key)) in &checker.keyed_calls {
        if state.keyed_calls.insert(*span) {
            delta
                .keyed_calls
                .push((*span, receiver.clone(), method.clone(), key.clone()));
        }
    }
    // The errors reported in this window (raw report order; the final
    // analysis sorts and dedups the full set).
    delta.errors = checker.errors[state.errors_seen..].to_vec();
    state.errors_seen = checker.errors.len();
    // Warnings can be rediscovered by call-site and dedicated-body checks, so
    // flush by value instead of by prefix.
    delta.warnings = checker
        .warnings
        .iter()
        .filter(|warning| !state.warnings_flushed.contains(warning))
        .cloned()
        .collect();
    state
        .warnings_flushed
        .extend(delta.warnings.iter().cloned());
    delta
}
