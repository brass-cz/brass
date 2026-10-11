//! Source extents and continuation rules for statement and declaration syntax.
use brass_parser::ast::{Expr, Member, Pattern, Stmt, TopLevel, TypeBody, TypeExpr};
use brass_parser::{Span, parse};

#[test]
fn construct_spans_include_payloads_and_delimiters() {
    // Both sum spellings, signatures, and signed patterns retain full extents.
    let src = "type A = | V { n: int32 }\ntype B = V { n: int32 } | W\ntype C = { m(self, _) }\nfun f(x) { return match x { -5 => 1, -2.5 => 2, _ => 3 } }";
    let module = parse(src).unwrap();
    for item in &module.items[..2] {
        let TopLevel::Type(t) = item else { panic!() };
        let TypeBody::Sum(variants) = &t.body else {
            panic!()
        };
        assert_eq!(
            &src[variants[0].span.lo..variants[0].span.hi],
            "V { n: int32 }"
        );
    }
    let TopLevel::Type(t) = &module.items[2] else {
        panic!()
    };
    let TypeBody::Record(members) = &t.body else {
        panic!()
    };
    let Member::Method(m) = &members[0] else {
        panic!()
    };
    assert_eq!(&src[m.span.lo..m.span.hi], "m(self, _)");
    let TopLevel::Fun(f) = &module.items[3] else {
        panic!()
    };
    let Stmt::Return(Some(Expr::Match(_, arms, _)), _) = &f.body.stmts[0] else {
        panic!()
    };
    for (arm, expected) in arms.iter().zip(["-5", "-2.5"]) {
        let Pattern::Literal(expr, span) = &arm.pattern else {
            panic!()
        };
        assert_eq!(expr.span(), *span);
        assert_eq!(&src[span.lo..span.hi], expected);
    }
}

#[test]
fn declaration_names_keep_independent_spans() {
    // Refinement and anonymous field names retain spans independently of types.
    let src = "type B: A, C, = {}\nlet m: B { field: int32 }\nlet n: anonymous { other: string }";
    let module = parse(src).unwrap();
    let TopLevel::Type(t) = &module.items[0] else {
        panic!()
    };
    assert_eq!(t.name_span, Span::new(5, 6));
    assert_eq!(t.interface_spans, [Span::new(8, 9), Span::new(11, 12)]);
    for (item, expected) in module.items[1..].iter().zip(["field", "other"]) {
        let TopLevel::Stmt(Stmt::Let { ty: Some(ty), .. }) = item else {
            panic!()
        };
        let fields = match ty {
            TypeExpr::Refine(_, fields, _) | TypeExpr::Anonymous(fields, _) => fields,
            _ => panic!(),
        };
        let span = fields[0].2;
        assert_eq!(&src[span.lo..span.hi], expected);
    }
}

#[test]
fn separators_preserve_continuations() {
    // Operators, chains, else, nested brackets, closures, and arm boundaries coexist.
    parse("fun f() {\nlet x = 1 +\n2\nx +=\n3\nlet xs = [\n1,\n2,\n]\nxs\n.len()\nif true {}\nelse {}\nlet c = (_, _) -> {\nreturn 7\n}\nmatch x {\n1 => c(1, 2)\n_ => 0\n}\n}\ntype T = { a: int32\nm(self)\nb: string, }\nlet x: T { a: int32\nb: string }\n").unwrap();
}

#[test]
fn interpolation_cannot_hide_invalid_statements() {
    // Recovered fragment errors propagate, with the enclosing return context.
    let err = parse("let s = \"{if true { return 1 }}\"").unwrap_err();
    assert_eq!(err.message, "`return` outside a function");
    assert_eq!(err.span, Span::new(20, 26));
    parse("fun f() { let s = \"{if true { return 1 }}\" }").unwrap();
}
