//! Newline-policy lookahead helpers.
//!
//! Prepoly treats a newline as a statement terminator by default, but as
//! whitespace when doing so lets parsing continue: inside brackets, after a
//! binary/assign operator at end of line, before a `.` that continues a method
//! chain, or before an `else`. The parser tracks bracket depth itself; the
//! lookahead predicates that peek past newlines live here.

use prepoly_lexer::{Token, TokenKind};

fn kind_at(tokens: &[Token], i: usize) -> &TokenKind {
    &tokens[i.min(tokens.len() - 1)].kind
}

/// Index of the first non-newline token at or after `pos`.
pub fn next_significant(tokens: &[Token], pos: usize) -> usize {
    let mut i = pos;
    while matches!(kind_at(tokens, i), TokenKind::Newline) {
        i += 1;
    }
    i
}

/// True when the cursor rests on a newline whose next significant token has the
/// same variant as `k`. Used to continue method chains (`\n .m()`) and to
/// attach an `else` that begins on a new line.
pub fn newline_then(tokens: &[Token], pos: usize, k: &TokenKind) -> bool {
    if !matches!(kind_at(tokens, pos), TokenKind::Newline) {
        return false;
    }
    let i = next_significant(tokens, pos);
    std::mem::discriminant(kind_at(tokens, i)) == std::mem::discriminant(k)
}

/// Lookahead from a `(` at `pos`: is the matching `)` followed (across
/// newlines) by `->`? This distinguishes a closure from a parenthesized group.
pub fn closure_ahead(tokens: &[Token], pos: usize) -> bool {
    let mut i = pos;
    let mut depth = 0usize;
    loop {
        match kind_at(tokens, i) {
            TokenKind::LParen => depth += 1,
            TokenKind::RParen => {
                depth -= 1;
                if depth == 0 {
                    i += 1;
                    break;
                }
            }
            TokenKind::Eof => return false,
            _ => {}
        }
        i += 1;
    }
    let i = next_significant(tokens, i);
    matches!(kind_at(tokens, i), TokenKind::Arrow)
}
