//! Expression source extents and the boundaries of condition and type syntax.
use brass_parser::ast::{Expr, Stmt, TopLevel};
use brass_parser::{parse, parse_with_base};

#[test]
fn parentheses_cover_the_expression_and_its_parents() {
    // Grouping is source metadata: walkers see the same expression children.
    let src = "fun f() {\n(b + c) * d\n(f)(x)\nreturn (z)\n-(q)\n((0xFF))\n}";
    let module = parse_with_base(src, 100).unwrap();
    let TopLevel::Fun(f) = &module.items[0] else {
        panic!()
    };
    for (stmt, expected) in
        f.body
            .stmts
            .iter()
            .zip(["(b + c) * d", "(f)(x)", "return (z)", "-(q)", "((0xFF))"])
    {
        let span = stmt.span();
        assert_eq!(&src[span.lo - 100..span.hi - 100], expected);
    }
    let Stmt::Expr(e) = &f.body.stmts[4] else {
        panic!()
    };
    let span = e.span();
    assert!(span.is_parenthesized());
    assert_eq!(
        &src[span.ungrouped().lo - 100..span.ungrouped().hi - 100],
        "0xFF"
    );
    assert_eq!(span.shifted(1234).source_span(), span);
    assert_eq!(
        span.shifted(1234).ungrouped().source_span(),
        span.ungrouped()
    );
}

#[test]
fn type_tests_have_only_two_head_forms() {
    // Prefixes and operators need an explicit grouped subject; tests are not values.
    for head in [
        "v: string",
        "!(v: string)",
        "(a == b): bool",
        "!((a == b): bool)",
        "(f)(x): int32",
        "v!: int32",
    ] {
        parse(&format!(
            "fun f() {{ if {head} {{}} else if !(v: bool) {{}} }}"
        ))
        .unwrap();
    }
    for head in [
        "(v: string)",
        "!(v: string) && true",
        "true || !(v: string)",
        "!!(v: string)",
    ] {
        assert!(
            parse(&format!("fun f() {{ if {head} {{}} }}")).is_err(),
            "{head}"
        );
    }
    assert!(parse("let x = !(v: string)").is_err());
    for (subject, expected_span, message) in [
        ("!v", "!", "write `!(v: T)` to negate a type test"),
        (
            "a == b",
            "a == b",
            "a type test applies to one operand; parenthesize it: `(a == b): T`",
        ),
        (
            "a && b",
            "a && b",
            "a type test applies to one operand; parenthesize it: `(a && b): T`",
        ),
        (
            "-x",
            "-x",
            "a type test applies to one operand; parenthesize it: `(-x): T`",
        ),
    ] {
        let src = format!("if {subject}: bool {{}}");
        let err = parse(&src).unwrap_err();
        assert_eq!(err.message, message);
        assert_eq!(&src[err.span.lo..err.span.hi], expected_span);
    }
    let module = parse("if !(v: string) {}").unwrap();
    assert!(
        matches!(&module.items[0], TopLevel::Stmt(Stmt::Expr(Expr::If(c, _, _, _))) if matches!(&**c, Expr::TypeTest(_, _, true, _)))
    );
}

#[test]
fn passing_modes_are_whole_parameter_annotations() {
    // All callable parameter positions accept the same three modes.
    for ty in ["ref(P)", "mut(P)", "ref(mut(P))"] {
        for src in [
            format!("fun f(x: {ty}) {{}}"),
            format!("fun P.f(self, x: {ty}) {{}}"),
            format!("let f = (x: {ty}) -> x"),
            format!("type P = {{ f(self, x: {ty}) }}"),
            format!("let f: ({ty}) -> P"),
        ] {
            parse(&src).unwrap();
        }
    }
    // Rejected wrappers report their own complete construct, never the declaration.
    for (ty, offending) in [
        ("ref(ref(P))", "ref(P)"),
        ("mut(mut(P))", "mut(P)"),
        ("mut(ref(P))", "ref(P)"),
        ("ref(mut(mut(P)))", "mut(P)"),
        ("ref(P)[]", "ref(P)"),
        ("mut(P)?", "mut(P)"),
        ("ref(P)!", "ref(P)"),
        ("P { item: ref(P) }", "ref(P)"),
        ("[ref(P)]", "ref(P)"),
        ("ref((ref(P)) -> P)", "ref(P)"),
    ] {
        let src = format!("fun f(x: {ty}) {{}}");
        let err = parse(&src).unwrap_err();
        assert_eq!(&src[err.span.lo..err.span.hi], offending, "{src}");
        assert_eq!(
            err.message,
            format!(
                "`{}(...)` is only allowed as a parameter's type",
                if offending.starts_with("ref") {
                    "ref"
                } else {
                    "mut"
                }
            )
        );
    }
    for src in [
        "fun f() -> ref(P) {}",
        "let x: ref(P)[]",
        "const x: mut(P) = p",
        "type P = { r: ref(P) }",
        "type P = mut(int32)",
        "let f: () -> ref(P)",
    ] {
        let err = parse(src).unwrap_err();
        assert!(
            err.message
                .contains("is only allowed as a parameter's type"),
            "{src}: {err:?}"
        );
        assert!(
            src[err.span.lo..err.span.hi].starts_with("ref(")
                || src[err.span.lo..err.span.hi].starts_with("mut(")
        );
    }
}
