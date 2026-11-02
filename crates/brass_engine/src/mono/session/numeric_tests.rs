//! Warm roots own every negotiated storage and closure selection fact.

use super::tests::{program, snapshot};
use super::*;

fn checked_mir(program: &Program) -> MirProgram {
    let analysis = brass_typeck::analyze(program);
    assert!(
        analysis.errors.is_empty(),
        "type errors: {:?}",
        analysis.errors
    );
    let shared = brass_typeck::stream::aggregate_result_types(&analysis.typed, program);
    let seeds = brass_typeck::stream::aggregate_instance_seeds(
        &analysis.instance_typed,
        &analysis.typed,
        program,
    );
    brass_mir::lower_program_with_types(
        program,
        &brass_mir::CheckerChannels {
            selected_bodies: None,
            expr_types: &shared,
            receiver_types: &fxhash::FxHashMap::default(),
            receiver_owners: &fxhash::FxHashMap::default(),
            field_calls: &fxhash::FxHashMap::default(),
            view_args: &analysis.view_args,
            numeric_calls: &analysis.numeric_calls,
            sum_views: &analysis.sum_views,
            call_locations: &fxhash::FxHashMap::default(),
            lift_errs: &fxhash::FxHashSet::default(),
            fields_loops: &analysis.fields_loops,
            instance_fields: &analysis.instance_fields,
            type_names: &analysis.type_names,
            typeof_types: &analysis.typeof_types,
            null_props: &analysis.null_props,
            type_tests: &analysis.type_tests,
            keyed_dispatch: &fxhash::FxHashMap::default(),
            instance_seeds: &seeds,
            instance_dispatch: &fxhash::FxHashMap::default(),
            instance_returns: &analysis.instance_returns,
        },
    )
}

#[test]
fn warm_numeric_roots_preserve_storage_symbols_and_closure_targets() {
    let sources = [
        "fun seed(unused) { let x = 0\nreturn x }\nfun main() { let wide: int64 = 5000000000\nlet a = seed(true)\na = wide\nlet b = seed(true) }\n",
        "fun main() { let f = (unused) -> { let x = 0\nreturn x }\nlet wide: int64 = 5000000000\nlet a = f(1)\na = wide\nlet b = f(1) }\n",
        "fun make() { let x = 0\nreturn (v) -> { if v : int64 { x = 5000000000 }\nreturn x } }\nfun main() { let a = make()\nlet b = make()\nlet wide: int64 = 5000000000\nprintln(a(wide))\nprintln(b(1)) }\n",
    ];
    let mut selected_closures = 0;
    for source in sources {
        let program = program(source);
        let mir = checked_mir(&program);
        assert!(!mir.numeric_calls.is_empty());
        let returns = mir.instance_returns.clone();
        let fresh = monomorphize_entry_with_returns(&mir, &program, true, returns.clone()).unwrap();
        assert!(fresh.main_skip.is_none(), "{:?}", fresh.main_skip);
        selected_closures += fresh
            .functions
            .iter()
            .map(|f| f.closure_targets.len())
            .sum::<usize>();
        let expected = snapshot(Ok(fresh));
        let changes = brass_mir::ChangedInputs::since(0);
        let mut session = MonoSession::default();
        assert_eq!(
            snapshot(session.entry(&mir, &program, true, returns.clone(), &changes)),
            expected
        );
        let id = session.cache.next_id;
        assert_eq!(
            snapshot(session.entry(&mir, &program, true, returns, &changes)),
            expected
        );
        assert_eq!(
            session.cache.next_id, id,
            "unchanged negotiations must replay"
        );
    }
    assert!(
        selected_closures > 0,
        "exercise owned closure selection facts"
    );
}

#[test]
fn changed_removed_and_absent_numeric_selections_invalidate_warm_roots() {
    let program = program(
        "fun seed(unused) { let x = 0\nreturn x }\nfun main() { let wide: int64 = 5000000000\nlet a = seed(true)\na = wide\nlet b = seed(true) }\n",
    );
    let mut mir = checked_mir(&program);
    let selections = mir.numeric_calls.clone();
    assert!(!selections.is_empty());
    let mut session = MonoSession::default();
    let mut previous = String::new();
    for epoch in 0..4 {
        // Body handles stay valid: only the selected storage contracts change.
        // Removing and restoring also tests negative reads of the empty table.
        mir.numeric_calls = if epoch % 2 == 0 {
            selections.clone()
        } else {
            HashMap::default()
        };
        let mut changes = brass_mir::ChangedInputs::since(epoch);
        changes.epoch += 1;
        for key in selections.keys() {
            if epoch % 2 == 0 {
                changes.numeric_calls.change(key.clone());
            } else {
                changes.numeric_calls.remove(key.clone());
            }
        }
        let returns = mir.instance_returns.clone();
        let expected = snapshot(monomorphize_entry_with_returns(
            &mir,
            &program,
            true,
            returns.clone(),
        ));
        assert_ne!(expected, previous);
        let id = session.cache.next_id;
        assert_eq!(
            snapshot(session.entry(&mir, &program, true, returns.clone(), &changes)),
            expected
        );
        assert!(session.cache.next_id > id);
        let warm = brass_mir::ChangedInputs::since(changes.epoch);
        let id = session.cache.next_id;
        assert_eq!(
            snapshot(session.entry(&mir, &program, true, returns, &warm)),
            expected
        );
        assert_eq!(session.cache.next_id, id);
        previous = expected;
    }
}

#[test]
fn root_identity_includes_negotiated_storage_at_identical_arguments() {
    let program = program("fun seed(unused) { let x = 0\nreturn x }\n");
    let key = |kind| {
        let mut instance =
            brass_hir::InstanceKey::function(&program, "seed", &[Type::Bool]).unwrap();
        instance.numeric_layout = Some(std::sync::Arc::new(vec![(vec![(0, 1)], Type::Int(kind))]));
        Root::Function {
            base: "seed".into(),
            args: vec![Type::Bool],
            instance: Some(instance),
        }
    };
    assert_ne!(key(IntKind::I32), key(IntKind::I64));
    assert_eq!(key(IntKind::I64), key(IntKind::I64));
}
