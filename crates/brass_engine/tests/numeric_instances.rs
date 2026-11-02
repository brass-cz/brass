//! Completed numeric storage contracts determine sharing and separation.

use brass_engine::monomorphize;
use brass_hir::LoadedModule;

fn symbols(source: &str, name: &str) -> Vec<String> {
    let ast = brass_parser::parse(source).expect("parse");
    let modules = [LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = brass_hir::lower(&modules);
    assert!(errors.is_empty(), "lower errors: {errors:?}");
    let analysis = brass_typeck::analyze(&program);
    assert!(
        analysis.errors.is_empty(),
        "type errors: {:?}",
        analysis.errors
    );
    let shared = brass_typeck::stream::aggregate_result_types(&analysis.typed, &program);
    let seeds = brass_typeck::stream::aggregate_instance_seeds(
        &analysis.instance_typed,
        &analysis.typed,
        &program,
    );
    let mir = brass_mir::lower_program_with_types(
        &program,
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
    );
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    assert!(mono.main_skip.is_none(), "{:?}", mono.main_skip);
    mono.functions
        .iter()
        .filter(|f| f.symbol.starts_with(&format!("{name}$")))
        .map(|f| f.symbol.clone())
        .collect()
}

#[test]
fn literal_and_typed_inputs_share_identical_completed_bodies() {
    let source = "fun accumulate(init) { let acc = init\nlet wide: int64 = 2\nacc += wide\nreturn acc }\nfun main() { let typed: int64 = 0\nlet a = accumulate(0)\nlet b = accumulate(typed) }\n";
    let instances = symbols(source, "accumulate");
    assert_eq!(instances.len(), 1, "{instances:?}");
}

#[test]
fn identical_arguments_keep_distinct_negotiated_local_storage() {
    let source = "fun seed(unused) { let value = 0\nreturn value }\nfun main() { let wide: int64 = 5000000000\nlet a = seed(true)\na = wide\nlet b = seed(true) }\n";
    let instances = symbols(source, "seed");
    assert_eq!(instances.len(), 2, "{instances:?}");
}

#[test]
fn non_origin_results_share_direct_and_function_value_bodies() {
    // A string result cannot carry a later demand into the local numeric slot.
    let source = "fun label(n) { let total = 0\nlet wide: int64 = 2\ntotal += wide\nreturn \"value\" }\nfun main() { let a = label(true)\nlet value = label\nlet b = value(true) }\n";
    let instances = symbols(source, "label");
    assert_eq!(instances.len(), 1, "{instances:?}");
}

#[test]
fn unchanged_literal_floors_publish_no_contracts_or_value_instances() {
    let source = "fun keep(x) { let y = x\nreturn y }\nfun main() { let total = 0\ntotal += keep(1)\ntotal += keep(2)\ntotal += keep(100) }\n";
    let ast = brass_parser::parse(source).expect("parse");
    let (program, errors) = brass_hir::lower(&[LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty());
    let analysis = brass_typeck::analyze(&program);
    assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
    assert!(analysis.numeric_calls.is_empty());
    assert_eq!(symbols(source, "keep").len(), 1);
}
