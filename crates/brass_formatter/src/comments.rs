//! Comment extraction.
//!
//! The lexer discards comments, so the formatter re-scans the source and
//! re-attaches each comment by byte position while printing. The scan mirrors
//! the lexer's string handling (escapes, `{...}` interpolation with nested
//! strings) so comment markers inside string literals are not mistaken for
//! comments. Comments inside an interpolation fragment are left alone: the
//! formatter prints string literals verbatim from the source, so they survive
//! as part of the string's text.

use brass_parser::Span;

/// One comment, in source order. The span covers the comment markers; a `//`
/// comment ends just before its newline.
#[derive(Clone, Copy, Debug)]
pub struct Comment {
    pub span: Span,
}

/// Scan `src` for every comment outside string literals.
pub fn extract(src: &str) -> Vec<Comment> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'"' => i = skip_string(b, i),
            b'/' if b.get(i + 1) == Some(&b'/') => {
                let lo = i;
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
                out.push(Comment {
                    span: Span::new(lo, i),
                });
            }
            // `#` line comments (including a leading shebang), as in the lexer.
            b'#' => {
                let lo = i;
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
                out.push(Comment {
                    span: Span::new(lo, i),
                });
            }
            b'/' if b.get(i + 1) == Some(&b'*') => {
                let lo = i;
                i += 2;
                // Block comments nest, exactly as in the lexer.
                let mut depth = 1;
                while i < b.len() && depth > 0 {
                    if b[i] == b'/' && b.get(i + 1) == Some(&b'*') {
                        depth += 1;
                        i += 2;
                    } else if b[i] == b'*' && b.get(i + 1) == Some(&b'/') {
                        depth -= 1;
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                out.push(Comment {
                    span: Span::new(lo, i.min(b.len())),
                });
            }
            _ => i += 1,
        }
    }
    out
}

/// Skip a string literal whose opening quote is at `i`; returns the index just
/// past the closing quote.
fn skip_string(b: &[u8], mut i: usize) -> usize {
    i += 1;
    while i < b.len() {
        match b[i] {
            b'\\' => i += 2,
            b'"' => return i + 1,
            b'{' => i = skip_interpolation(b, i),
            _ => i += 1,
        }
    }
    i
}

/// Skip a `{expr}` interpolation, balancing braces and passing over nested
/// string literals so their quotes do not end the outer string early.
fn skip_interpolation(b: &[u8], mut i: usize) -> usize {
    i += 1;
    let mut depth = 1usize;
    while i < b.len() && depth > 0 {
        match b[i] {
            b'{' => {
                depth += 1;
                i += 1;
            }
            b'}' => {
                depth -= 1;
                i += 1;
            }
            // A nested string can itself interpolate, so use the same
            // recursive string state as the outer literal.
            b'"' => i = skip_string(b, i),
            b'/' if b.get(i + 1) == Some(&b'/') => i = skip_line_comment(b, i),
            b'#' => i = skip_line_comment(b, i),
            b'/' if b.get(i + 1) == Some(&b'*') => i = skip_block_comment(b, i),
            _ => i += 1,
        }
    }
    i
}

fn skip_line_comment(b: &[u8], mut i: usize) -> usize {
    while i < b.len() && b[i] != b'\n' {
        i += 1;
    }
    i
}

/// Skip one nested block comment using the lexer's nesting rule.
fn skip_block_comment(b: &[u8], mut i: usize) -> usize {
    i += 2;
    let mut depth = 1;
    while i < b.len() && depth > 0 {
        if b[i] == b'/' && b.get(i + 1) == Some(&b'*') {
            depth += 1;
            i += 2;
        } else if b[i] == b'*' && b.get(i + 1) == Some(&b'/') {
            depth -= 1;
            i += 2;
        } else {
            i += 1;
        }
    }
    i
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spans(src: &str) -> Vec<(usize, usize)> {
        extract(src)
            .into_iter()
            .map(|c| (c.span.lo, c.span.hi))
            .collect()
    }

    #[test]
    fn finds_line_and_block_comments() {
        let src = "let a = 1 // one\n/* two */ let b = 2\n";
        let s = spans(src);
        assert_eq!(s.len(), 2);
        assert_eq!(&src[s[0].0..s[0].1], "// one");
        assert_eq!(&src[s[1].0..s[1].1], "/* two */");
    }

    #[test]
    fn ignores_markers_inside_strings_and_interpolations() {
        // The `//` and `/*` inside the literal (and inside its interpolation)
        // are string content, not comments.
        let src = "let s = \"a // b {x /* c */} \\{\" // real\n";
        let s = spans(src);
        assert_eq!(s.len(), 1);
        assert_eq!(&src[s[0].0..s[0].1], "// real");
    }

    #[test]
    fn nested_block_comment_is_one_comment() {
        let src = "/* a /* b */ c */ let x = 1\n";
        let s = spans(src);
        assert_eq!(s.len(), 1);
        assert_eq!(&src[s[0].0..s[0].1], "/* a /* b */ c */");
    }

    /// Comments and strings nested recursively inside interpolation must not
    /// consume the real source comment that follows the outer literal.
    #[test]
    fn interpolation_comments_do_not_desynchronize_the_scan() {
        let src = r#"let s = "literal { value // }
            + "nested { inner # }
            }" /* } /* { */ */ }" // real
        let x = 1 /* after */"#;
        let found: Vec<&str> = spans(src).iter().map(|(lo, hi)| &src[*lo..*hi]).collect();
        assert_eq!(found, vec!["// real", "/* after */"]);
    }
}
