//! Lexer for the Brass language.
//!
//! Produces a token stream with explicit `Newline` tokens that the parser
//! uses to delimit statements, with parser-side whitespace fallback.
mod scan;
mod token;

pub use scan::{DocComment, LexError, lex, lex_with_docs};
pub use token::{Span, StrPart, Token, TokenKind, is_keyword, keyword_or_ident};

/// Compute a 1-based (line, column) for a byte offset in `src`, for error
/// reporting. Columns count Unicode scalar values within the line.
pub fn line_col(src: &str, byte_offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    for (i, ch) in src.char_indices() {
        if i >= byte_offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> Vec<TokenKind> {
        lex(src).unwrap().into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn keywords_and_idents() {
        let k = kinds("let x = foo");
        assert_eq!(
            k,
            vec![
                TokenKind::Let,
                TokenKind::Ident("x".into()),
                TokenKind::Eq,
                TokenKind::Ident("foo".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn integer_radixes_and_underscores() {
        assert_eq!(kinds("0xFF")[0], TokenKind::Int(255));
        assert_eq!(kinds("0b1010")[0], TokenKind::Int(10));
        assert_eq!(kinds("0o77")[0], TokenKind::Int(63));
        assert_eq!(kinds("1_000_000")[0], TokenKind::Int(1_000_000));
    }

    #[test]
    #[allow(clippy::approx_constant)] // `3.14` is lexer test input, not an approximation of PI
    fn floats_with_exponent() {
        assert_eq!(kinds("3.14")[0], TokenKind::Float(3.14));
        assert_eq!(kinds("1.0e-5")[0], TokenKind::Float(1.0e-5));
        // `42.foo` must lex as int then field access, not a float.
        assert_eq!(
            kinds("42.foo"),
            vec![
                TokenKind::Int(42),
                TokenKind::Dot,
                TokenKind::Ident("foo".into()),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn malformed_numbers_report_the_offending_character() {
        // Invalid digits, suffixes, and incomplete exponents must not split
        // into another statement. Spans identify the first offending character.
        for (src, offset, message) in [
            ("0b12", 3, "invalid digit `2` in binary literal"),
            ("0b1012", 5, "invalid digit `2` in binary literal"),
            ("0b2", 2, "invalid digit `2` in binary literal"),
            ("0o78", 3, "invalid digit `8` in octal literal"),
            ("0o9", 2, "invalid digit `9` in octal literal"),
            ("0xFFg", 4, "invalid suffix `g` on numeric literal"),
            ("12abc", 2, "invalid suffix `a` on numeric literal"),
            ("1.5f", 3, "invalid suffix `f` on numeric literal"),
            ("1e2x", 3, "invalid suffix `x` on numeric literal"),
            ("1e", 1, "missing digits after the exponent"),
            ("1e+", 1, "missing digits after the exponent"),
            ("1E-_", 1, "missing digits after the exponent"),
            ("1.0efoo", 3, "missing digits after the exponent"),
        ] {
            let err = lex(src).unwrap_err();
            assert_eq!(err.message, message, "{src}");
            assert_eq!(err.span, Span::new(offset, offset + 1), "{src}");
        }
    }

    #[test]
    fn valid_numeric_boundaries_and_separators() {
        // Separators, decimal leading zeros, ranges, and method calls remain valid.
        for (src, expected) in [
            ("0755", TokenKind::Int(755)),
            ("0b_10_", TokenKind::Int(2)),
            ("0o7_7", TokenKind::Int(63)),
            ("0xF_F", TokenKind::Int(255)),
            ("1_0.5_0e-1_0", TokenKind::Float(10.5e-10)),
            ("1e-400", TokenKind::Float(0.0)),
        ] {
            assert_eq!(kinds(src), vec![expected, TokenKind::Eof]);
        }
        assert_eq!(
            kinds("[0..n]"),
            vec![
                TokenKind::LBracket,
                TokenKind::Int(0),
                TokenKind::DotDot,
                TokenKind::Ident("n".into()),
                TokenKind::RBracket,
                TokenKind::Eof
            ]
        );
        assert_eq!(
            kinds("5.abs()"),
            vec![
                TokenKind::Int(5),
                TokenKind::Dot,
                TokenKind::Ident("abs".into()),
                TokenKind::LParen,
                TokenKind::RParen,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn non_finite_float_literals_are_rejected() {
        // Overflow is a literal error covering the number; finite extremes remain valid.
        for src in ["1e400", "1.8e308"] {
            let err = lex(src).unwrap_err();
            assert_eq!(err.message, "float literal out of range");
            assert_eq!(err.span, Span::new(0, src.len()));
        }
        assert_eq!(
            kinds("1.7976931348623157e308")[0],
            TokenKind::Float(f64::MAX)
        );
    }

    #[test]
    fn string_newlines_point_to_the_opening_quote() {
        // Raw LF, CRLF, CR, and escaped physical newlines fail in outer and nested text.
        for newline in ["\n", "\r\n", "\r", "\\\n"] {
            for prefix in ["let s = ", "\"{ id("] {
                let src = format!("{prefix}\"line1{newline}line2\"");
                let err = lex(&src).unwrap_err();
                assert_eq!(err.message, "unterminated string literal");
                assert_eq!(err.span, Span::new(prefix.len(), prefix.len() + 1));
            }
        }
        assert_eq!(
            kinds(r#""line1\nline2""#)[0],
            TokenKind::Str(vec![StrPart::Lit("line1\nline2".into())])
        );
    }

    #[test]
    fn recursive_interpolation_keeps_quoted_braces_and_newlines() {
        // A quoted closing brace inside a nested interpolation cannot close its parent.
        let src = "\"A{ id(\"x{\n \"}\" // }\n }y\") }B\"";
        assert_eq!(
            kinds(src)[0],
            TokenKind::Str(vec![
                StrPart::Lit("A".into()),
                StrPart::Interp(" id(\"x{\n \"}\" // }\n }y\") ".into(), 3),
                StrPart::Lit("B".into()),
            ])
        );
        // Nested strings use the same escape validation and absolute source spans.
        let src = r#""{ "\q" }""#;
        let err = lex(src).unwrap_err();
        assert_eq!(err.message, "unknown escape sequence");
        assert_eq!(err.span, Span::new(5, 6));
    }

    #[test]
    fn long_utf8_string_preserves_text_around_escapes() {
        // Large multibyte runs exercise text copying without per-character suffix validation.
        let text = "\u{3042}".repeat(80_000);
        let src = format!("\"{text}\\n{text}\"");
        assert_eq!(
            kinds(&src),
            vec![
                TokenKind::Str(vec![StrPart::Lit(format!("{text}\n{text}"))]),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn newline_collapsing() {
        // Leading and repeated newlines collapse; comment newline kept.
        let k = kinds("\n\nlet a = 1\n\n\nlet b = 2\n");
        assert_eq!(
            k,
            vec![
                TokenKind::Let,
                TokenKind::Ident("a".into()),
                TokenKind::Eq,
                TokenKind::Int(1),
                TokenKind::Newline,
                TokenKind::Let,
                TokenKind::Ident("b".into()),
                TokenKind::Eq,
                TokenKind::Int(2),
                TokenKind::Newline,
                TokenKind::Eof,
            ]
        );
    }

    // `#` comments run to end of line; the terminating newline still
    // separates statements, mirroring `//` behavior.
    #[test]
    fn hash_line_comment() {
        let k = kinds("let a = 1 # trailing comment\nlet b = 2");
        assert_eq!(
            k,
            vec![
                TokenKind::Let,
                TokenKind::Ident("a".into()),
                TokenKind::Eq,
                TokenKind::Int(1),
                TokenKind::Newline,
                TokenKind::Let,
                TokenKind::Ident("b".into()),
                TokenKind::Eq,
                TokenKind::Int(2),
                TokenKind::Eof,
            ]
        );
    }

    // A leading shebang line must lex as a comment so scripts can start with
    // `#!/usr/bin/env brass`.
    #[test]
    fn shebang_line() {
        let k = kinds("#!/usr/bin/env brass\nlet a = 1\n");
        assert_eq!(
            k,
            vec![
                TokenKind::Let,
                TokenKind::Ident("a".into()),
                TokenKind::Eq,
                TokenKind::Int(1),
                TokenKind::Newline,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn nested_block_comment() {
        let k = kinds("1 /* a /* b */ c */ 2");
        assert_eq!(
            k,
            vec![TokenKind::Int(1), TokenKind::Int(2), TokenKind::Eof]
        );
    }

    #[test]
    fn string_interpolation_parts() {
        let k = kinds("\"value = {x + 1}!\"");
        match &k[0] {
            TokenKind::Str(parts) => {
                assert_eq!(parts.len(), 3);
                assert_eq!(parts[0], StrPart::Lit("value = ".into()));
                // The fragment starts just past the `{` at byte 9.
                assert_eq!(parts[1], StrPart::Interp("x + 1".into(), 10));
                assert_eq!(parts[2], StrPart::Lit("!".into()));
            }
            other => panic!("expected string, got {other:?}"),
        }
    }

    #[test]
    fn string_with_nested_braces_and_strings() {
        // Interpolation containing a string literal with its own braces.
        // Source seen by the lexer: "{ f("a}b") }"
        let k = kinds("\"{ f(\"a}b\") }\"");
        match &k[0] {
            TokenKind::Str(parts) => {
                assert_eq!(parts.len(), 1);
                assert_eq!(parts[0], StrPart::Interp(" f(\"a}b\") ".into(), 2));
            }
            other => panic!("expected string, got {other:?}"),
        }
    }

    #[test]
    fn interpolation_braces_inside_comments_are_ignored() {
        // Both comment forms can contain unmatched braces without closing the
        // interpolation; block comments remain nested as in ordinary source.
        let k = kinds("\"{ value // }\n + other /* } /* { */ } */ }\"");
        let TokenKind::Str(parts) = &k[0] else {
            panic!("expected string");
        };
        assert_eq!(
            parts[0],
            StrPart::Interp(" value // }\n + other /* } /* { */ } */ ".into(), 2)
        );
    }

    #[test]
    fn trailing_nested_string_escape_has_an_in_bounds_error_span() {
        // A final backslash in a nested interpolation string has no escaped
        // byte; the diagnostic must still end at the source boundary.
        let src = "\"{ \"abc\\";
        let err = lex(src).expect_err("nested string is unterminated");
        assert_eq!(err.span.hi, src.len());
    }

    #[test]
    fn operators() {
        let k = kinds("a += b % c << d");
        assert_eq!(
            k,
            vec![
                TokenKind::Ident("a".into()),
                TokenKind::PlusEq,
                TokenKind::Ident("b".into()),
                TokenKind::Percent,
                TokenKind::Ident("c".into()),
                TokenKind::Shl,
                TokenKind::Ident("d".into()),
                TokenKind::Eof,
            ]
        );
    }

    // line_col is 1-based, resets the column on each newline, and counts columns
    // in Unicode scalar values (not bytes) so diagnostics point at the right
    // character in source with multi-byte characters.
    #[test]
    fn line_col_is_one_based_and_unicode_aware() {
        assert_eq!(line_col("abc", 0), (1, 1));
        assert_eq!(line_col("abc", 2), (1, 3));
        // After a newline the line advances and the column restarts.
        assert_eq!(line_col("a\nb", 2), (2, 1));
        assert_eq!(line_col("a\nbc", 3), (2, 2));
        // A two-byte 'e-acute' occupies one column: the byte-3 'x' is column 3,
        // not column 4.
        assert_eq!(line_col("\u{e9}=x", 3), (1, 3));
    }
}
