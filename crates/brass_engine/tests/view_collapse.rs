//! Monomorphization through view conversion: anonymous arguments to a
//! view-eligible parameter are converted to the callee row's view at the call
//! boundary, so differently-shaped arguments with the same view share ONE
//! compiled instance instead of one per shape (the deserializer-DoS bound).
//!
//! The pipeline mirrors the driver: parse -> HIR -> typeck (producing the
//! view-argument span set) -> MIR lowering with that set -> monomorphize.

use brass_engine::monomorphize;
use brass_hir::LoadedModule;

/// The display example from the design memo: `first_name` is Guarded (its only
/// uses are the truthiness test and the guarded return), `last_name` Required,
/// and both are forced to `string` by the `-> string` returns, so every shape
/// maps to the single view `{ first_name: string?, last_name: string }`.
const DISPLAY: &str = "fun display(obj) -> string {\n\
                       \x20 if obj.first_name {\n    return obj.first_name\n  }\n\
                       \x20 return obj.last_name\n}\n\
                       fun main() {\n\
                       \x20 let a = display({ first_name: \"Ada\", last_name: \"Lovelace\" })\n\
                       \x20 let b = display({ first_name: \"Alan\", last_name: \"Turing\", age: 41 })\n\
                       \x20 let c = display({ last_name: \"Euler\", country: \"CH\" })\n}\n";

#[test]
fn three_shapes_collapse_to_one_display_instance() {
    let ast = brass_parser::parse(DISPLAY).expect("parse");
    let modules = [LoadedModule {
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
    assert_eq!(
        analysis.view_args.len(),
        3,
        "all three anonymous arguments must be view-convertible"
    );
    // Lower with the checker's view-argument spans (no aggregate seeding is
    // needed here) and monomorphize from the zero-parameter roots.
    let mir = brass_mir::lower_program_with_types(
        &program,
        &brass_mir::CheckerChannels {
            expr_types: &fxhash::FxHashMap::default(),
            view_args: &analysis.view_args,
            sum_views: &analysis.sum_views,
            call_locations: &fxhash::FxHashMap::default(),
            lift_errs: &fxhash::FxHashSet::default(),
            fields_loops: &analysis.fields_loops,
            type_names: &analysis.type_names,
            typeof_types: &analysis.typeof_types,
            null_props: &analysis.null_props,
            type_tests: &analysis.type_tests,
        },
    );
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    let display_instances: Vec<&str> = mono
        .functions
        .iter()
        .filter(|f| f.symbol == "display" || f.symbol.starts_with("display$$"))
        .map(|f| f.symbol.as_str())
        .collect();
    assert_eq!(
        display_instances.len(),
        1,
        "the three shapes must share one view-typed instance: {display_instances:?}"
    );
}
