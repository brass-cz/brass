//! Incremental publication of the checker's auxiliary lowering channels.

use super::super::channel_changes::Channel;
use super::*;

/// Reconcile recorded channel writes with the last delivered state.
pub(super) fn publish(
    checker: &Checker,
    state: &mut stream::FlushState,
    delta: &mut stream::ChannelDelta,
    terminal: bool,
    sum_dirty: HashSet<Span>,
) {
    let mut changes = checker.channel_changes.borrow_mut().drain();
    // Initial publication and the terminal boundary read every raw table.
    if terminal || !changes.enabled {
        for (channel, spans) in [
            (
                Channel::FieldCall,
                checker.call_sites.keys().copied().collect::<Vec<_>>(),
            ),
            (
                Channel::ViewArg,
                checker.view_args.iter().copied().collect(),
            ),
            (
                Channel::LiftErr,
                checker.lift_errs.iter().copied().collect(),
            ),
            (
                Channel::NullProp,
                checker.null_props.iter().copied().collect(),
            ),
            (
                Channel::FieldsLoop,
                checker.fields_loops.keys().copied().collect(),
            ),
            (
                Channel::SumView,
                checker.sum_views.keys().copied().collect(),
            ),
            (
                Channel::TypeName,
                checker.type_names.keys().copied().collect(),
            ),
            (
                Channel::TypeOf,
                checker
                    .typeof_types
                    .keys()
                    .chain(state.typeof_types.keys())
                    .copied()
                    .collect(),
            ),
            (
                Channel::TypeTest,
                checker
                    .type_tests
                    .keys()
                    .chain(state.type_tests.keys())
                    .copied()
                    .collect(),
            ),
            (
                Channel::KeyedCall,
                checker.keyed_calls.keys().copied().collect(),
            ),
        ] {
            changes.spans.entry(channel).or_default().extend(spans);
        }
        changes
            .returns
            .extend(checker.instance_returns.keys().cloned());
    }
    for span in changes.take(Channel::FieldCall) {
        if let Some(site) = checker.call_sites.get(&span)
            && !site.field_receivers.is_empty()
        {
            let receivers = site.method.then(|| site.field_receivers.clone());
            if state.field_calls.get(&span) != Some(&receivers) {
                delta.field_calls.push((span, receivers.clone()));
                state.field_calls.insert(span, receivers);
            }
        }
    }
    for (channel, raw, published, entries) in [
        (
            Channel::ViewArg,
            &checker.view_args,
            &mut state.view_args,
            &mut delta.view_args,
        ),
        (
            Channel::LiftErr,
            &checker.lift_errs,
            &mut state.lift_errs,
            &mut delta.lift_errs,
        ),
        (
            Channel::NullProp,
            &checker.null_props,
            &mut state.null_props,
            &mut delta.null_props,
        ),
    ] {
        for span in changes.take(channel) {
            if raw.contains(&span) && published.insert(span) {
                entries.push(span);
            }
        }
    }
    super::fields::publish(checker, state, delta);
    let mut spans = changes.take(Channel::SumView);
    spans.extend(sum_dirty);
    for span in spans {
        if let Some(raw) = checker.sum_views.get(&span) {
            let (mut ty, dependencies) = checker.solver.resolve_with_dependencies(raw);
            state.publication.watch_sum(span, &dependencies);
            if let Type::Sum(n) = &mut ty
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
            if state.sum_views.get(&span) != Some(&ty) {
                delta.sum_views.push((span, ty.clone()));
                state.sum_views.insert(span, ty);
            }
        }
    }
    for span in changes.take(Channel::TypeName) {
        if let Some(name) = checker.type_names.get(&span)
            && state.type_names.get(&span) != Some(name)
        {
            delta.type_names.push((span, name.clone()));
            state.type_names.insert(span, name.clone());
        }
    }
    for (channel, raw, published, entries, removed) in [
        (
            Channel::TypeOf,
            &checker.typeof_types,
            &mut state.typeof_types,
            &mut delta.typeof_types,
            &mut delta.typeof_types_removed,
        ),
        (
            Channel::TypeTest,
            &checker.type_tests,
            &mut state.type_tests,
            &mut delta.type_tests,
            &mut delta.type_tests_removed,
        ),
    ] {
        for span in changes.take(channel) {
            match raw.get(&span) {
                Some(ty) if published.get(&span) != Some(ty) => {
                    entries.push((span, ty.clone()));
                    published.insert(span, ty.clone());
                }
                None if published.remove(&span).is_some() => removed.push(span),
                _ => {}
            }
        }
    }
    for key in std::mem::take(&mut changes.returns) {
        if let Some(ret) = checker.instance_returns.get(&key)
            && state.instance_returns.get(&key) != Some(ret)
        {
            delta
                .instance_returns
                .push((key.0.clone(), key.1.clone(), ret.clone()));
            state.instance_returns.insert(key, ret.clone());
        }
    }
    for span in changes.take(Channel::KeyedCall) {
        if let Some((receiver, method, key)) = checker.keyed_calls.get(&span)
            && state.keyed_calls.insert(span)
        {
            delta
                .keyed_calls
                .push((span, receiver.clone(), method.clone(), key.clone()));
        }
    }
    delta.errors = checker.errors[state.errors_seen..].to_vec();
    state.errors_seen = checker.errors.len();
    // Membership is updated after collecting the window, preserving duplicate
    // warnings within one boundary and their diagnostic report order.
    delta.warnings = checker.warnings[state.warnings_seen..]
        .iter()
        .filter(|warning| {
            !state
                .warning_members
                .contains(&(warning.span, warning.message.clone()))
        })
        .cloned()
        .collect();
    state.warnings_seen = checker.warnings.len();
    state.warning_members.extend(
        delta
            .warnings
            .iter()
            .map(|warning| (warning.span, warning.message.clone())),
    );
}
