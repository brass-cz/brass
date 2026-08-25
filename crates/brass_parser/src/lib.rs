//! Parser for the Brass language: source text -> tokens -> AST.
//!
//! The lexer lives here as [`lexer`]; its core types (`Span`, `Token`) are
//! re-exported at the crate root, so downstream crates name one parser crate
//! for the whole surface syntax.

pub mod ast;
pub mod lexer;
pub mod newline;
mod parser;

pub use lexer::{
    DocComment, LexError, Span, StrPart, Token, TokenKind, is_keyword, keyword_or_ident, lex,
    lex_with_docs, line_col,
};
pub use parser::{ParseError, parse, parse_recovering, parse_with_base};

#[cfg(test)]
mod tests {
    use super::ast::*;
    use super::parse;

    fn module(src: &str) -> Module {
        parse(src).unwrap_or_else(|e| panic!("parse error: {} at {:?}", e.message, e.span))
    }

    #[test]
    fn record_type_with_method_signature_and_impl() {
        // A type body holds fields and method *signatures* (interface
        // requirements, no body); bodies are implemented with `fun T.m(...)`.
        let m = module(
            "type Point = {\n    x: float64\n    y: float64\n    dist(self, o: Point) -> float64\n}\nfun Point.new(x: float64, y: float64) {\n    return Self { x: x, y: y }\n}\n",
        );
        match &m.items[0] {
            TopLevel::Type(t) => {
                assert_eq!(t.name, "Point");
                match &t.body {
                    TypeBody::Record(members) => {
                        assert_eq!(members.len(), 3);
                        assert!(matches!(members[0], Member::Field(_)));
                        match &members[2] {
                            Member::Method(method) => assert!(method.body.is_none()),
                            _ => panic!("expected method signature"),
                        }
                    }
                    _ => panic!("expected record"),
                }
            }
            _ => panic!("expected type decl"),
        }
        match &m.items[1] {
            TopLevel::Fun(f) => {
                assert_eq!(f.name, "new");
                assert!(f.recv.is_some(), "method impl records its receiver");
            }
            _ => panic!("expected fun decl"),
        }
    }

    #[test]
    fn type_slot_spellings_are_equivalent() {
        // `type slot` and the older `slot: type` declare the same type slot:
        // a field whose type is `TypeExpr::TypeSlot`.
        let m = module("type Box = {\n    type key\n    value: type\n    data: Self.key[]\n}\n");
        let TopLevel::Type(t) = &m.items[0] else {
            panic!("expected a type");
        };
        let TypeBody::Record(members) = &t.body else {
            panic!("expected a record");
        };
        for (i, name) in [(0, "key"), (1, "value")] {
            let Member::Field(f) = &members[i] else {
                panic!("expected a field");
            };
            assert_eq!(f.name, name);
            assert!(
                matches!(f.ty, Some(TypeExpr::TypeSlot(_))),
                "{name} is a slot: {:?}",
                f.ty
            );
        }
    }

    #[test]
    fn in_type_method_body_is_rejected() {
        // A method body inside the type body is no longer accepted; it must be
        // `fun T.m(...)`.
        assert!(parse("type P = {\n    x: int32\n    get(self) { return self.x }\n}\n").is_err());
    }

    #[test]
    fn sum_type_with_leading_pipe() {
        let m = module("type Color =\n    | Red\n    | Green\n    | Blue\n");
        match &m.items[0] {
            TopLevel::Type(t) => match &t.body {
                TypeBody::Sum(vs) => {
                    let names: Vec<_> = vs.iter().map(|v| v.name.as_str()).collect();
                    assert_eq!(names, vec!["Red", "Green", "Blue"]);
                }
                _ => panic!("expected sum"),
            },
            _ => panic!("expected type"),
        }
    }

    #[test]
    fn interface_constraints() {
        let m = module("type User: Showable, Comparable = {\n    name: string\n}\n");
        match &m.items[0] {
            TopLevel::Type(t) => assert_eq!(t.interfaces, vec!["Showable", "Comparable"]),
            _ => panic!(),
        }
    }

    #[test]
    fn method_chain_newline_continuation() {
        let m = module(
            "fun main() {\n    let r = items\n        .filter((x) -> x > 0)\n        .map((x) -> x * 2)\n}\n",
        );
        // Should parse without treating the newline before `.` as a terminator.
        match &m.items[0] {
            TopLevel::Fun(f) => assert_eq!(f.body.stmts.len(), 1),
            _ => panic!(),
        }
    }

    #[test]
    fn trailing_operator_continuation() {
        let m = module("fun main() {\n    let total = price *\n        quantity\n}\n");
        match &m.items[0] {
            TopLevel::Fun(f) => {
                assert_eq!(f.body.stmts.len(), 1);
                match &f.body.stmts[0] {
                    Stmt::Let { value, .. } => {
                        assert!(matches!(value, Some(Expr::Binary(BinOp::Mul, ..))))
                    }
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn match_with_patterns() {
        let m = module(
            "fun f(s) {\n    return match s {\n        Circle { radius } => radius,\n        Point => 0,\n        _ => 1,\n    }\n}\n",
        );
        match &m.items[0] {
            TopLevel::Fun(f) => match &f.body.stmts[0] {
                Stmt::Return(Some(Expr::Match(_, arms, _)), _) => assert_eq!(arms.len(), 3),
                _ => panic!("expected match return"),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn variant_literal_and_field_access() {
        let m = module(
            "fun main() {\n    let c = Animal.Cat { name: \"Tama\", indoor: true }\n    let r = Color.Red\n}\n",
        );
        match &m.items[0] {
            TopLevel::Fun(f) => {
                match &f.body.stmts[0] {
                    Stmt::Let {
                        value: Some(Expr::VariantLit(t, v, fields, _)),
                        ..
                    } => {
                        assert_eq!(t, "Animal");
                        assert_eq!(v, "Cat");
                        assert_eq!(fields.len(), 2);
                    }
                    _ => panic!("expected variant literal"),
                }
                match &f.body.stmts[1] {
                    Stmt::Let {
                        value: Some(Expr::Field(_, name, _)),
                        ..
                    } => assert_eq!(name, "Red"),
                    _ => panic!("expected field access for unit variant"),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn array_destructuring_let() {
        let m = module("fun main() {\n    let [lo, hi] = [1, 10]\n}\n");
        match &m.items[0] {
            TopLevel::Fun(f) => match &f.body.stmts[0] {
                Stmt::Let {
                    pat: Pattern::Array(ps, _),
                    ..
                } => assert_eq!(ps.len(), 2),
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn string_interpolation_expr() {
        let m = module("fun main() {\n    let s = \"value = {x + 1}\"\n}\n");
        match &m.items[0] {
            TopLevel::Fun(f) => match &f.body.stmts[0] {
                Stmt::Let {
                    value: Some(Expr::Str(segs, _)),
                    ..
                } => {
                    assert_eq!(segs.len(), 2);
                    assert!(matches!(segs[0], StrSeg::Lit(_)));
                    assert!(matches!(segs[1], StrSeg::Expr(_)));
                }
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn imports() {
        let m = module("import math.vector.{ Vec2, Vec3 }\nimport config.{ Config }\n");
        assert_eq!(m.imports.len(), 2);
        assert_eq!(m.imports[0].path, vec!["math", "vector"]);
        let local_names: Vec<&str> = m.imports[0]
            .names
            .iter()
            .map(|n| n.local.as_str())
            .collect();
        assert_eq!(local_names, vec!["Vec2", "Vec3"]);
        assert_eq!(m.imports[1].path, vec!["config"]);
    }

    #[test]
    fn if_let_and_else() {
        let m = module(
            "fun f(s) {\n    if let Circle { radius } = s {\n        return radius\n    } else {\n        return 0\n    }\n}\n",
        );
        match &m.items[0] {
            TopLevel::Fun(f) => match &f.body.stmts[0] {
                Stmt::Expr(Expr::IfLet(_, _, _, els, _)) => assert!(els.is_some()),
                _ => panic!("expected if let"),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn closure_vs_grouping() {
        let m = module(
            "fun main() {\n    let a = (1 + 2)\n    let f = (x) -> x * 2\n    let g = () -> { return 1 }\n}\n",
        );
        match &m.items[0] {
            TopLevel::Fun(f) => {
                assert!(matches!(
                    f.body.stmts[0],
                    Stmt::Let {
                        value: Some(Expr::Binary(..)),
                        ..
                    }
                ));
                assert!(matches!(
                    f.body.stmts[1],
                    Stmt::Let {
                        value: Some(Expr::Closure(..)),
                        ..
                    }
                ));
                assert!(matches!(
                    f.body.stmts[2],
                    Stmt::Let {
                        value: Some(Expr::Closure(..)),
                        ..
                    }
                ));
            }
            _ => panic!(),
        }
    }

    #[test]
    fn star_star_is_not_an_operator() {
        // `**` was removed as an operator; exponentiation is the `pow` function in
        // std/math. `2 ** 3` no longer lexes as a single token, and `*` is not a
        // prefix operator, so the expression must fail to parse.
        assert!(parse("fun main() {\n    let x = 2 ** 3\n}\n").is_err());
    }

    #[test]
    fn nullable_and_array_types() {
        let m = module("fun f(a: int32?, b: string[], c: float64[3]) {\n}\n");
        match &m.items[0] {
            TopLevel::Fun(f) => {
                assert!(matches!(f.params[0].ty, Some(TypeExpr::Nullable(..))));
                assert!(matches!(f.params[1].ty, Some(TypeExpr::Array(_, None, _))));
                assert!(matches!(
                    f.params[2].ty,
                    Some(TypeExpr::Array(_, Some(3), _))
                ));
            }
            _ => panic!(),
        }
    }

    #[test]
    fn fallible_and_infer_types() {
        // `T!` is a fallible suffix; `infer` is a plain type word; suffixes stack
        // with the array/nullable suffixes (`infer[]`, `int32[]!`).
        let m = module(
            "fun f(a: infer, b: infer[]) -> string! {\n}\n\
             fun g(c: int32[]!) {\n}\n",
        );
        let (TopLevel::Fun(f), TopLevel::Fun(g)) = (&m.items[0], &m.items[1]) else {
            panic!("expected two functions");
        };
        assert!(matches!(f.params[0].ty, Some(TypeExpr::Named(ref n, _)) if n == "infer"));
        // `infer[]` is a slice of the `infer` word.
        match &f.params[1].ty {
            Some(TypeExpr::Array(inner, None, _)) => {
                assert!(matches!(**inner, TypeExpr::Named(ref n, _) if n == "infer"));
            }
            other => panic!("expected infer[], got {other:?}"),
        }
        assert!(matches!(f.ret, Some(TypeExpr::Fallible(..))));
        // `int32[]!` is a fallible wrapping a slice.
        match &g.params[0].ty {
            Some(TypeExpr::Fallible(inner, _)) => {
                assert!(matches!(**inner, TypeExpr::Array(_, None, _)));
            }
            other => panic!("expected int32[]!, got {other:?}"),
        }
    }

    #[test]
    fn fallible_then_nullable_return_type_parses() {
        // Postfix order is semantic: `T!?` is a nullable whose payload is the
        // fallible Result, the spelling an explicit two-layer return uses.
        let m = module("fun f() -> string!? {\n}\n");
        let TopLevel::Fun(f) = &m.items[0] else {
            panic!("expected a function");
        };
        let Some(TypeExpr::Nullable(inner, _)) = &f.ret else {
            panic!("expected nullable return, got {:?}", f.ret);
        };
        assert!(matches!(inner.as_ref(), TypeExpr::Fallible(..)));
    }

    #[test]
    fn tuple_type_annotation() {
        // A leading-bracket type `[T0, T1, ...]` is a tuple (distinct from the
        // postfix array `T[]`).
        let m = module("fun f(p: [int32, string, bool]) {\n}\n");
        let TopLevel::Fun(f) = &m.items[0] else {
            panic!("expected a function");
        };
        match &f.params[0].ty {
            Some(TypeExpr::Tuple(elems, _)) => {
                assert_eq!(elems.len(), 3);
                assert!(matches!(elems[0], TypeExpr::Named(ref n, _) if n == "int32"));
                assert!(matches!(elems[1], TypeExpr::Named(ref n, _) if n == "string"));
                assert!(matches!(elems[2], TypeExpr::Named(ref n, _) if n == "bool"));
            }
            other => panic!("expected a tuple type, got {other:?}"),
        }
    }

    #[test]
    fn recovery_collects_multiple_statement_errors() {
        // Two bad statements in one body: both are reported at the offending
        // token, and the rest of the body (and file) still parses.
        let src = "fun f() -> int32 {\n    let x = )\n    let y = ]\n    return 0\n}\nfun g() -> int32 {\n    return 1\n}\n";
        let (m, errors) = crate::parse_recovering(src, 0);
        assert_eq!(errors.len(), 2, "errors: {errors:?}");
        // Spans point at the offending tokens, not at the statement head.
        assert_eq!(errors[0].span.lo, src.find("= )").unwrap() + 2);
        assert_eq!(errors[1].span.lo, src.find("= ]").unwrap() + 2);
        // Both functions survive; f keeps its good trailing statement.
        assert_eq!(m.items.len(), 2);
        let TopLevel::Fun(f) = &m.items[0] else {
            panic!("expected a function");
        };
        assert_eq!(f.body.stmts.len(), 1);
    }

    #[test]
    fn recovery_resyncs_at_the_next_top_level_declaration() {
        // A broken declaration does not hide the ones after it.
        let src = "type Broken = {\n    x:\n}\nfun ok() -> int32 {\n    return 3\n}\n";
        let (m, errors) = crate::parse_recovering(src, 0);
        assert!(!errors.is_empty(), "expected at least one error");
        assert!(
            m.items
                .iter()
                .any(|i| matches!(i, TopLevel::Fun(f) if f.name == "ok")),
            "the following declaration should still parse: {:?}",
            m.items.len()
        );
    }

    #[test]
    fn recovery_keeps_a_function_left_unclosed_at_end_of_input() {
        // A body still being typed (no closing brace yet) keeps the function
        // and its parsed statements in the recovered AST; only the missing
        // brace is reported. Editor features rely on the partial body.
        let src = "fun f() -> int32 {\n    let x = 1\n    return x\n";
        let (m, errors) = crate::parse_recovering(src, 0);
        assert_eq!(errors.len(), 1, "errors: {errors:?}");
        assert!(errors[0].message.contains("expected '}'"));
        assert_eq!(m.items.len(), 1);
        let TopLevel::Fun(f) = &m.items[0] else {
            panic!("expected a function");
        };
        assert_eq!(f.body.stmts.len(), 2);
    }

    #[test]
    fn recovery_closes_nested_blocks_at_end_of_input() {
        // Every open block closes at end of input, so a statement inside a
        // half-typed `if` survives too.
        let src = "fun f() {\n    if true {\n        let x = 1\n";
        let (m, errors) = crate::parse_recovering(src, 0);
        // One missing '}' per open block.
        assert_eq!(errors.len(), 2, "errors: {errors:?}");
        assert_eq!(m.items.len(), 1);
    }

    #[test]
    fn recovery_is_capped() {
        // A pathological file stops at the error cap instead of flooding.
        let src = "let a = )\n".repeat(100);
        let (_m, errors) = crate::parse_recovering(&src, 0);
        assert_eq!(errors.len(), 20);
    }

    #[test]
    fn parse_reports_the_first_error_for_compatibility() {
        let src = "fun f() {\n    let x = )\n    let y = ]\n}\n";
        let e = crate::parse(src).unwrap_err();
        assert_eq!(e.span.lo, src.find("= )").unwrap() + 2);
    }

    #[test]
    fn bare_imports_parse_with_the_flag() {
        // `import a.b` and `import a.b.X` are syntactically one form; the
        // loader classifies them. Braced imports stay non-bare.
        let m =
            module("import geometry.vec\nimport lib.util.helper\nimport a.b.{ X }\nprintln(1)\n");
        assert_eq!(m.imports.len(), 3);
        assert!(m.imports[0].bare);
        assert_eq!(m.imports[0].path, vec!["geometry", "vec"]);
        assert!(m.imports[1].bare);
        assert_eq!(m.imports[1].path, vec!["lib", "util", "helper"]);
        assert!(!m.imports[2].bare);
        assert_eq!(m.imports[2].names.len(), 1);
        assert_eq!(m.imports[2].names[0].local, "X");
    }

    #[test]
    fn bare_import_with_as_renaming() {
        let m = module("import geometry.vec as g\nprintln(1)\n");
        assert_eq!(m.imports.len(), 1);
        assert!(m.imports[0].bare);
        assert_eq!(m.imports[0].path, vec!["geometry", "vec"]);
        assert_eq!(m.imports[0].alias, Some("g".to_string()));
        assert!(m.imports[0].explicit_alias);
    }

    #[test]
    fn braced_import_with_as_renaming() {
        let m = module("import a.b.{ X as Y, Z }\nprintln(1)\n");
        assert_eq!(m.imports.len(), 1);
        assert_eq!(m.imports[0].names.len(), 2);
        assert_eq!(m.imports[0].names[0].remote, "X");
        assert_eq!(m.imports[0].names[0].local, "Y");
        assert_eq!(m.imports[0].names[1].remote, "Z");
        assert_eq!(m.imports[0].names[1].local, "Z");
    }

    #[test]
    fn as_is_a_valid_identifier() {
        // `as` is contextual, not a keyword; it can be used as a variable name.
        let m = module("fun main() {\n    let as = 1\n    println(as)\n}\n");
        let TopLevel::Fun(f) = &m.items[0] else {
            panic!("expected a function");
        };
        match &f.body.stmts[0] {
            Stmt::Let {
                pat: Pattern::Binding(name, _),
                ..
            } => assert_eq!(name, "as"),
            other => panic!("expected let binding, got {other:?}"),
        }
    }

    #[test]
    fn qualified_type_names_parse_dotted() {
        let m = module("fun f(v: vec.Vec2) -> vec.Vec2 {\n    return v\n}\n");
        let TopLevel::Fun(f) = &m.items[0] else {
            panic!("expected a function");
        };
        assert!(matches!(&f.params[0].ty, Some(TypeExpr::Named(n, _)) if n == "vec.Vec2"));
        assert!(matches!(&f.ret, Some(TypeExpr::Named(n, _)) if n == "vec.Vec2"));
    }

    #[test]
    fn qualified_variant_literal_parses_dotted_ty() {
        // `q.Shape.Circle { r: 1.0 }` -> VariantLit("q.Shape", "Circle", ..)
        let m = module("fun main() {\n    let c = q.Shape.Circle { r: 1.0 }\n}\n");
        let TopLevel::Fun(f) = &m.items[0] else {
            panic!("expected a function");
        };
        match &f.body.stmts[0] {
            Stmt::Let {
                value: Some(Expr::VariantLit(t, v, fields, _)),
                ..
            } => {
                assert_eq!(t, "q.Shape");
                assert_eq!(v, "Circle");
                assert_eq!(fields.len(), 1);
            }
            other => panic!("expected qualified variant literal, got {other:?}"),
        }
    }

    // Doc comments: a `/** ... */` directly above a declaration lands in its
    // `doc` field, with the markers and per-line `*` decoration stripped.
    #[test]
    fn doc_comment_attaches_to_fun_and_type() {
        let m = module(
            "/** Adds one. */\nfun inc(x) {\n    return x + 1\n}\n\n/**\n * A 2D point.\n * Units are pixels.\n */\ntype Point = {\n    x: int32\n    y: int32\n}\n",
        );
        let TopLevel::Fun(f) = &m.items[0] else {
            panic!("expected a function");
        };
        assert_eq!(f.doc.as_deref(), Some("Adds one."));
        let TopLevel::Type(t) = &m.items[1] else {
            panic!("expected a type");
        };
        assert_eq!(t.doc.as_deref(), Some("A 2D point.\nUnits are pixels."));
    }

    // A doc comment buried inside an earlier body must not leak onto the next
    // declaration, and a plain `/* */` comment is not documentation.
    #[test]
    fn doc_comment_does_not_leak_or_misfire() {
        let m = module(
            "fun f() {\n    /** stray */\n    let x = 1\n}\n\n/* plain */\nfun g() {\n    return 0\n}\n",
        );
        let TopLevel::Fun(g) = &m.items[1] else {
            panic!("expected a function");
        };
        assert_eq!(g.doc, None);
        let TopLevel::Fun(f) = &m.items[0] else {
            panic!("expected a function");
        };
        assert_eq!(f.doc, None);
    }

    // Blank lines and `//` comments between the doc and the declaration do not
    // detach it; stacked doc comments join into paragraphs.
    #[test]
    fn doc_comment_attachment_is_tolerant() {
        let m = module("/** First. */\n/** Second. */\n\n// note\nfun h() {\n    return 0\n}\n");
        let TopLevel::Fun(h) = &m.items[0] else {
            panic!("expected a function");
        };
        assert_eq!(h.doc.as_deref(), Some("First.\n\nSecond."));
    }

    #[test]
    fn bare_variant_literal_is_unchanged() {
        // `Shape.Circle { r: 1.0 }` -> VariantLit("Shape", "Circle", ..)
        let m = module("fun main() {\n    let c = Shape.Circle { r: 1.0 }\n}\n");
        let TopLevel::Fun(f) = &m.items[0] else {
            panic!("expected a function");
        };
        match &f.body.stmts[0] {
            Stmt::Let {
                value: Some(Expr::VariantLit(t, v, _, _)),
                ..
            } => {
                assert_eq!(t, "Shape");
                assert_eq!(v, "Circle");
            }
            other => panic!("expected variant literal, got {other:?}"),
        }
    }

    #[test]
    fn deeply_nested_prefix_expressions_are_rejected_without_recursing() {
        // Prefix operators form nested AST nodes, so the common syntax budget
        // stops an adversarial chain before parsing or later visitors overflow.
        let src = format!("fun main() {{\n let x = {}true\n}}\n", "!".repeat(500));
        let err = parse(&src).expect_err("prefix chain should hit the nesting limit");
        assert_eq!(err.message, "expression nesting is too deep");
    }

    #[test]
    fn deeply_nested_types_and_patterns_are_rejected() {
        // Type and destructuring-pattern recursion share the expression budget
        // instead of bypassing the parser's stack bound.
        let ty = format!("{}int32{}", "[".repeat(500), "]".repeat(500));
        let err = parse(&format!("fun f(x: {ty}) {{}}\n"))
            .expect_err("tuple type should hit the nesting limit");
        assert_eq!(err.message, "type nesting is too deep");

        let pat = format!("{}x{}", "[".repeat(500), "]".repeat(500));
        let err = parse(&format!("fun f() {{\n let {pat} = value\n}}\n"))
            .expect_err("array pattern should hit the nesting limit");
        assert_eq!(err.message, "pattern nesting is too deep");
    }
}
