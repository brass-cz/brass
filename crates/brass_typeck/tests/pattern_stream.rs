//! Pattern-cache warming must not suppress inference observations or diagnostics.

use brass_hir::{LoadedModule, Program};
use brass_typeck::stream::{BodyRequest, CheckEvent, Scheduler};

#[derive(Default)]
struct Recorder {
    events: Vec<CheckEvent>,
}

impl Scheduler for Recorder {
    fn drain_requests(&mut self) -> Vec<BodyRequest> {
        Vec::new()
    }
    fn emit(&mut self, event: CheckEvent) {
        self.events.push(event);
    }
}

fn program(source: &str) -> Program {
    let (program, errors) = brass_hir::lower(&[LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast: brass_parser::parse(source).expect("parse"),
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    program
}

#[test]
fn cold_and_warm_pattern_facts_emit_identical_streams() {
    let source = r#"
        type P = { x: int32 }
        type S = | P { x: int32 } | Empty
        type T = | P { x: int32 } | Other
        type Alias = S
        fun first(v) -> int32 {
            if let P { x } = v { return x }
            return -1
        }
        fun qualified(v: Alias?) -> int32 {
            return match v { Alias.P { x } => x, Alias.Empty => 0, null => -1 }
        }
        fun main() {
            let a = first(P { x: 1 })
            let b = first(S.P { x: 2 })
            let c = first(T.P { x: 3 })
            let d = qualified(null)
            let e = first(S.Empty)
        }
    "#;
    for source in [
        source.to_string(),
        format!("{source}\nfun wrong(v: S) {{ match v {{ Alias.Missing => 0 }} }}"),
    ] {
        let cold = program(&source);
        let warm = program(&source);
        let module = vec!["main".into()];
        {
            let scope = warm.pattern_scope(&module);
            for name in ["P", "S", "T", "Alias", "Empty", "Other", "Missing"] {
                scope.braced_head(name);
                scope.type_head(name);
                scope.is_unit_variant(name);
                scope.first_owner(name, true);
            }
        }
        let mut cold_events = Recorder::default();
        let mut warm_events = Recorder::default();
        let cold_analysis = brass_typeck::analyze_streaming(&cold, None, &mut cold_events);
        let warm_analysis = brass_typeck::analyze_streaming(&warm, None, &mut warm_events);
        assert_eq!(
            cold_analysis.errors.is_empty(),
            !source.contains("Alias.Missing")
        );
        // The deterministic scheduler pins event windows as well as the final
        // verdict, including per-instance channels and rejected qualifiers.
        assert_eq!(
            format!("{:?}", cold_events.events),
            format!("{:?}", warm_events.events)
        );
        assert_eq!(cold_analysis.errors, warm_analysis.errors);
        assert_eq!(
            cold_analysis.instance_returns,
            warm_analysis.instance_returns
        );
        assert_eq!(cold_analysis.typeof_types, warm_analysis.typeof_types);
    }
}
