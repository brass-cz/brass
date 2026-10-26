//! Boundary-level regression coverage for dependency-indexed publication.

use super::*;
use brass_hir::{InstanceCallable, TypedExprKind};

fn boundary(
    checker: &Checker,
    state: &mut stream::FlushState,
    reference_state: &mut stream::FlushState,
    terminal: bool,
) -> stream::ChannelDelta {
    let actual = flush_delta(checker, state, terminal);
    let expected = reference::flush_delta(checker, reference_state, terminal);
    verify::assert_delta(&actual, &expected);
    actual
}

#[test]
fn pending_observations_follow_aliases_rollbacks_and_only_relevant_bindings() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    let variable = checker.fresh_unknown();
    let alias = checker.fresh_unknown();
    let unrelated = checker.fresh_unknown();
    let span = Span::new(1, 2);
    let tag = checker.intern_tag(
        InstanceCallable::Function("f".into()),
        std::slice::from_ref(&variable),
    );
    checker.record_typed_in(
        TypedExprKind::Array { empty: true },
        span,
        Type::Slice(Box::new(variable.clone())),
        Constness::Unknown,
        Some(tag),
    );
    let mut state = stream::FlushState::default();
    let mut reference = stream::FlushState::default();
    boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(state.counters.typed_resolutions, 1);
    for _ in 0..4 {
        boundary(&checker, &mut state, &mut reference, false);
        assert_eq!(state.counters.typed_resolutions, 0);
        assert_eq!(state.counters.instance_resolutions, 0);
    }
    checker.solver.unify(&unrelated, &Type::Bool).unwrap();
    boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(state.counters.typed_resolutions, 0);
    let snap = checker.solver.snapshot();
    checker.solver.unify(&variable, &alias).unwrap();
    boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(state.counters.typed_resolutions, 1);
    checker.solver.rollback(snap);
    boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(state.counters.typed_resolutions, 1);
    // The removed alias edge must not wake this observation anymore.
    checker.solver.unify(&alias, &Type::Bool).unwrap();
    boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(state.counters.typed_resolutions, 0);
    checker.solver.unify(&variable, &Type::Str).unwrap();
    let delta = boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(
        delta.expr_types,
        vec![(span, Type::Slice(Box::new(Type::Str)))]
    );
    assert_eq!(state.counters.typed_resolutions, 1);
    assert!(state.typed_pending.is_empty());
    assert!(state.instance_pending.is_empty());
    boundary(&checker, &mut state, &mut reference, true);
}

#[test]
fn late_nonpending_closure_keeps_its_terminal_publication_boundary() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    let variable = checker.fresh_unknown();
    let span = Span::new(3, 4);
    checker.record_typed(
        TypedExprKind::Closure,
        span,
        Type::Fun(vec![variable.clone()], Box::new(variable.clone())),
        Constness::Unknown,
    );
    let mut state = stream::FlushState::default();
    let mut reference = stream::FlushState::default();
    boundary(&checker, &mut state, &mut reference, false);
    checker.solver.unify(&variable, &Type::Str).unwrap();
    assert!(
        boundary(&checker, &mut state, &mut reference, false)
            .expr_types
            .is_empty()
    );
    assert_eq!(state.counters.typed_resolutions, 0);
    assert_eq!(
        boundary(&checker, &mut state, &mut reference, true)
            .expr_types
            .len(),
        1
    );
}

#[test]
fn shared_poisoning_exposes_previously_suppressed_instance_seeds() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    let span = Span::new(5, 6);
    let mut state = stream::FlushState::default();
    let mut reference = stream::FlushState::default();
    for ty in [Type::Bool, Type::Str] {
        let tag = checker.intern_tag(
            InstanceCallable::Function("f".into()),
            std::slice::from_ref(&ty),
        );
        checker.record_typed_in(
            TypedExprKind::Array { empty: true },
            span,
            Type::Slice(Box::new(ty)),
            Constness::Unknown,
            Some(tag),
        );
        boundary(&checker, &mut state, &mut reference, false);
    }
    assert!(!state.expr_flushed.contains_key(&span));
    assert_eq!(state.instance_flushed[&span].len(), 2);
    boundary(&checker, &mut state, &mut reference, true);
}

#[test]
fn a_new_instance_reuses_a_recorded_sidecar_entry() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    let span = Span::new(7, 8);
    let mut state = stream::FlushState::default();
    let mut reference = stream::FlushState::default();
    for argument in [Type::Bool, Type::Str] {
        let tag = checker.intern_tag(InstanceCallable::Function("f".into()), &[argument]);
        checker.record_typed_in(
            TypedExprKind::Array { empty: true },
            span,
            Type::Slice(Box::new(Type::Bool)),
            Constness::Unknown,
            Some(tag),
        );
        boundary(&checker, &mut state, &mut reference, false);
    }
    // A replay can add a tag while deduplicating the typed sidecar completely.
    assert_eq!(checker.typed.expressions.len(), 1);
    assert_eq!(checker.instance_typed.len(), 2);
    assert_eq!(state.counters.typed_resolutions, 0);
    let tag = checker.intern_tag(
        InstanceCallable::Function("f".into()),
        &[Type::Int(IntKind::I32)],
    );
    checker.record_typed_in(
        TypedExprKind::Array { empty: true },
        span,
        Type::Slice(Box::new(Type::Str)),
        Constness::Unknown,
        Some(tag),
    );
    boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(state.instance_flushed[&span].len(), 3);
}

#[test]
#[should_panic(expected = "publication inside a speculative probe")]
fn speculative_work_cannot_publish() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    checker.speculation_depth = 1;
    flush_delta(&checker, &mut stream::FlushState::default(), false);
}

#[test]
fn checker_forks_leave_committed_feeds_and_dependency_readers_intact() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    let variable = checker.fresh_unknown();
    let span = Span::new(1, 2);
    checker.record_typed(
        TypedExprKind::Array { empty: true },
        span,
        Type::Slice(Box::new(variable.clone())),
        Constness::Unknown,
    );
    let mut state = stream::FlushState::default();
    let mut reference = stream::FlushState::default();
    boundary(&checker, &mut state, &mut reference, false);
    let snapshot = checker.solver.snapshot();
    checker.solver.unify(&variable, &Type::Bool).unwrap();
    checker.record_type_name(span, "committed".into());
    let mut probe = checker.clone();
    assert!(!probe.channel_changes.borrow().enabled);
    assert!(probe.channel_changes.borrow().spans.is_empty());
    assert!(probe.channel_changes.borrow().returns.is_empty());
    probe.solver.rollback(snapshot);
    probe.solver.unify(&variable, &Type::Str).unwrap();
    probe.record_type_name(span, "speculative".into());
    assert!(probe.channel_changes.borrow().spans.is_empty());
    // Refuse publication before any feed or cursor can be consumed, even if
    // the probe's light inference does not increment speculation_depth.
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            flush_delta(&probe, &mut stream::FlushState::default(), false);
        }))
        .is_err()
    );
    checker.solver.rollback(snapshot);
    checker.solver.unify(&variable, &Type::Str).unwrap();
    let delta = boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(
        delta.expr_types,
        vec![(span, Type::Slice(Box::new(Type::Str)))]
    );
    assert_eq!(delta.type_names, vec![(span, "committed".into())]);
    assert_eq!(state.counters.typed_resolutions, 1);
}

#[test]
fn sum_view_provisional_void_changes_when_a_later_body_binds_its_payload() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    let variable = checker.fresh_unknown();
    let span = Span::new(10, 11);
    let mut nominal = NominalType::new(3, "Result");
    nominal
        .substitution
        .insert(brass_hir::types::RESULT_OK_VALUE, variable.clone());
    nominal
        .substitution
        .insert(brass_hir::types::RESULT_ERR_ERROR, Type::Str);
    checker.record_sum_view_type(span, Type::Sum(nominal));
    let mut state = stream::FlushState::default();
    let mut reference = stream::FlushState::default();
    assert_eq!(
        boundary(&checker, &mut state, &mut reference, false)
            .sum_views
            .len(),
        1
    );
    assert!(
        boundary(&checker, &mut state, &mut reference, false)
            .sum_views
            .is_empty()
    );
    checker.solver.unify(&variable, &Type::Bool).unwrap();
    let delta = boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(delta.sum_views.len(), 1);
    let Type::Sum(nominal) = &delta.sum_views[0].1 else {
        panic!("sum view expected")
    };
    assert_eq!(
        nominal.substitution.get(brass_hir::types::RESULT_OK_VALUE),
        Some(&Type::Bool)
    );
    boundary(&checker, &mut state, &mut reference, true);
}

#[test]
fn poisoned_patterns_and_duplicate_warnings_preserve_boundary_contents() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    let span = Span::new(12, 13);
    let warning = TypeError {
        span,
        message: "duplicate warning".into(),
    };
    checker.record_typeof_type(span, &Type::Bool);
    checker.record_type_test(span, &Type::Bool);
    checker.warnings.extend([warning.clone(), warning.clone()]);
    let mut state = stream::FlushState::default();
    let mut reference = stream::FlushState::default();
    assert_eq!(
        boundary(&checker, &mut state, &mut reference, false)
            .warnings
            .len(),
        2
    );
    checker.record_typeof_type(span, &Type::Str);
    checker.record_type_test(span, &Type::Str);
    checker.warnings.push(warning);
    let delta = boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(delta.typeof_types_removed, vec![span]);
    assert_eq!(delta.type_tests_removed, vec![span]);
    assert!(delta.warnings.is_empty());
    boundary(&checker, &mut state, &mut reference, true);
}

#[test]
fn numeric_slots_and_arguments_publish_resolution_poisoning_and_instances() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    let mut state = stream::FlushState::default();
    let mut reference = stream::FlushState::default();
    for (index, kind) in [
        TypedExprKind::NumericBinding,
        TypedExprKind::NumericArgument,
    ]
    .into_iter()
    .enumerate()
    {
        let span = Span::new(100 + index, 101 + index);
        let open = checker.fresh_unknown();
        let tag = checker.intern_tag(
            InstanceCallable::Function("numeric".into()),
            std::slice::from_ref(&open),
        );
        checker.record_typed_in(
            kind.clone(),
            span,
            open.clone(),
            Constness::Unknown,
            Some(tag),
        );
        boundary(&checker, &mut state, &mut reference, false);
        assert!(!state.expr_flushed.contains_key(&span));
        // The solver feed wakes both the observation and its effective instance key.
        checker
            .solver
            .unify(&open, &Type::Int(IntKind::I32))
            .unwrap();
        boundary(&checker, &mut state, &mut reference, false);
        assert_eq!(state.expr_flushed[&span], Type::Int(IntKind::I32));
        let wide = Type::Int(IntKind::I64);
        let tag = checker.intern_tag(
            InstanceCallable::Function("numeric".into()),
            std::slice::from_ref(&wide),
        );
        checker.record_typed_in(kind, span, wide, Constness::Unknown, Some(tag));
        boundary(&checker, &mut state, &mut reference, false);
        // Different effective instances retain their own layouts after the shared seed is removed.
        assert!(!state.expr_flushed.contains_key(&span));
        assert_eq!(state.instance_flushed[&span].len(), 2);
    }
    boundary(&checker, &mut state, &mut reference, true);
}

#[test]
fn numeric_call_contracts_wake_on_parent_resolution_and_replay_explicit_barriers() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    let open = checker.fresh_unknown();
    let span = Span::new(150, 160);
    let tag = checker.intern_tag(
        InstanceCallable::Function("parent".into()),
        std::slice::from_ref(&open),
    );
    checker.record_numeric_call(
        span,
        Some(vec![(vec![(150, 160)], Type::Int(IntKind::I64))].into()),
        Some(tag.clone()),
    );
    let mut state = stream::FlushState::default();
    let mut reference = stream::FlushState::default();
    assert!(
        boundary(&checker, &mut state, &mut reference, false)
            .numeric_calls
            .is_empty()
    );
    checker
        .solver
        .unify(&open, &Type::Int(IntKind::I32))
        .unwrap();
    let published = boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(published.numeric_calls.len(), 1);
    assert_eq!(
        published.numeric_calls[0].1,
        Some(vec![(vec![(150, 160)], Type::Int(IntKind::I64))].into())
    );
    checker.record_numeric_call(span, None, Some(tag));
    let published = boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(published.numeric_calls.len(), 1);
    assert_eq!(published.numeric_calls[0].1, None);
    assert!(
        boundary(&checker, &mut state, &mut reference, false)
            .numeric_calls
            .is_empty()
    );
    boundary(&checker, &mut state, &mut reference, true);
}

#[test]
fn numeric_layout_flavors_remain_distinct_in_reference_publication() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    let plain = checker.intern_tag(InstanceCallable::Function("seed".into()), &[]);
    let mut flavored = (*plain).clone();
    flavored.numeric_layout = Some(vec![(vec![(150, 160)], Type::Int(IntKind::I64))].into());
    let flavored = instances::TagRef::template(flavored);
    let span = Span::new(170, 171);
    checker.record_typed_in(
        TypedExprKind::NumericBinding,
        span,
        Type::Int(IntKind::I32),
        Constness::Unknown,
        Some(plain),
    );
    checker.record_typed_in(
        TypedExprKind::NumericBinding,
        span,
        Type::Int(IntKind::I64),
        Constness::Unknown,
        Some(flavored),
    );
    let mut state = stream::FlushState::default();
    let mut reference = stream::FlushState::default();
    let delta = boundary(&checker, &mut state, &mut reference, false);
    assert_eq!(delta.instance_seeds[0].1.len(), 2);
    boundary(&checker, &mut state, &mut reference, true);
}

#[test]
fn numeric_arguments_never_seed_an_unseen_instance_from_shared_mir() {
    let program = Program::empty();
    let mut checker = Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
    let span = Span::new(180, 185);
    let mut state = stream::FlushState::default();
    let mut reference = stream::FlushState::default();
    for kind in [IntKind::I32, IntKind::I64] {
        let ty = Type::Int(kind);
        let tag = checker.intern_tag(
            InstanceCallable::Function("forward".into()),
            std::slice::from_ref(&ty),
        );
        checker.record_typed_in(
            TypedExprKind::InstanceNumericArgument,
            span,
            ty,
            Constness::Unknown,
            Some(tag),
        );
        boundary(&checker, &mut state, &mut reference, false);
        // A later demand at a new argument type must reach the checker before
        // a seed from the first checked instance can narrow its argument.
        assert!(!state.expr_flushed.contains_key(&span));
    }
    assert_eq!(state.instance_flushed[&span].len(), 2);
    boundary(&checker, &mut state, &mut reference, true);
}
