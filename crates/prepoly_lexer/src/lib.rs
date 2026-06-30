//! Lexer for the Prepoly language.
//!
//! Produces a token stream with explicit `Newline` tokens that the parser
//! uses to delimit statements, with parser-side whitespace fallback.
mod lexer;
mod token;

pub use lexer::{LexError, lex};
pub use token::{Span, StrPart, Token, TokenKind, keyword_or_ident};

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
                assert_eq!(parts[1], StrPart::Interp("x + 1".into()));
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
                assert_eq!(parts[0], StrPart::Interp(" f(\"a}b\") ".into()));
            }
            other => panic!("expected string, got {other:?}"),
        }
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
