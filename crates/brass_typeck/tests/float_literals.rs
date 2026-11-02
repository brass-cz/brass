//! Float literal adaptation must preserve finiteness while allowing rounding.

use brass_parser::Span;

fn analyze(src: &str) -> brass_typeck::Analysis {
    let ast = brass_parser::parse(src).expect("parse");
    let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    brass_typeck::analyze(&program)
}

#[test]
fn float32_overflow_points_to_the_literal_in_each_context() {
    // Annotations, calls, returns, fields, and nullable destinations must all
    // reject overflow at the number, including a negated literal's magnitude.
    for src in [
        "let f: float32 = 1e39",
        "let f: float32? = 1e39",
        "fun f() { let x: float32 = 1e39 }\nf()",
        "fun f() -> float32 { return -1e39 }\nf()",
        "fun f(x: float32) {}\nf(1e39)",
        "type Box = { x: float32 }\nlet b = Box { x: 1e39 }",
        "fun f() -> float32? { return 1e39 }\nf()",
    ] {
        let analysis = analyze(src);
        let start = src.find("1e39").unwrap();
        let expected = Span::new(start, start + 4);
        assert!(
            analysis.errors.iter().any(|error| {
                error.message == "float literal out of range for float32" && error.span == expected
            }),
            "{src}: {:?}",
            analysis.errors
        );
    }
}

#[test]
fn finite_float32_rounding_and_underflow_are_accepted() {
    // Exact representability is not required, and underflow to zero is valid.
    let analysis = analyze(
        "let rounded: float32 = 0.1\n\
         let tiny: float32 = 1e-50\n\
         let zero = 1e-400\n\
         let largest: float32 = 3.4028234663852886e38\n\
         let wide: float64 = 1e39\n\
         fun f() -> float32 { return -0.1 }\nf()",
    );
    assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
}
