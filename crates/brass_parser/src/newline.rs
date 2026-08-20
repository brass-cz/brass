//! Newline-policy lookahead helpers.
//!
//! Brass treats a newline as a statement terminator by default, but as
//! whitespace when doing so lets parsing continue: inside brackets, after a
//! binary/assign operator at end of line, before a `.` that continues a method
//! chain, or before an `else`. The parser tracks bracket depth itself; the
//! lookahead predicates that peek past newlines live here.

use crate::lexer::{Token, TokenKind};

static EOF: TokenKind = TokenKind::Eof;

fn kind_at(tokens: &[Token], i: usize) -> &TokenKind {
    tokens
        .get(i)
        .or_else(|| tokens.last())
        .map(|token| &token.kind)
        .unwrap_or(&EOF)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_token_lookahead_is_safe() {
        // Public lookahead helpers also serve editor callers with an incomplete
        // token buffer, so an empty slice behaves like end-of-file.
        let tokens = Vec::new();
        assert_eq!(next_significant(&tokens, 0), 0);
        assert!(!newline_then(&tokens, 0, &TokenKind::Dot));
        assert!(!closure_ahead(&tokens, 0));
    }
}
