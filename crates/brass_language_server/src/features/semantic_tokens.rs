//! Semantic-token highlighting.
//!
//! Highlighting is built from the token stream so it survives a parse error:
//! every token is classified from its kind, and identifiers are refined with a
//! small amount of syntactic context (the previous and next significant token)
//! plus the set of declared type and function names gathered from a best-effort
//! parse of the document. Comments -- which the lexer discards -- are recovered
//! by a lexer-equivalent scan so they highlight too.

use fxhash::FxHashSet as HashSet;

use brass_parser::ast::{Member, Module, TopLevel, TypeBody};
use brass_parser::parse;
use brass_parser::{Span, TokenKind, lex};
use tower_lsp_server::ls_types::{SemanticToken, SemanticTokenModifier, SemanticTokenType};

/// The token-type legend, reported in the server capabilities. A token's
/// `token_type` field indexes into this array.
pub const TOKEN_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::NAMESPACE,   // 0
    SemanticTokenType::TYPE,        // 1
    SemanticTokenType::ENUM,        // 2
    SemanticTokenType::FUNCTION,    // 3
    SemanticTokenType::METHOD,      // 4
    SemanticTokenType::PROPERTY,    // 5
    SemanticTokenType::VARIABLE,    // 6
    SemanticTokenType::PARAMETER,   // 7
    SemanticTokenType::KEYWORD,     // 8
    SemanticTokenType::STRING,      // 9
    SemanticTokenType::NUMBER,      // 10
    SemanticTokenType::OPERATOR,    // 11
    SemanticTokenType::ENUM_MEMBER, // 12
    SemanticTokenType::COMMENT,     // 13
];

const T_NAMESPACE: u32 = 0;
const T_TYPE: u32 = 1;
const T_ENUM: u32 = 2;
const T_FUNCTION: u32 = 3;
const T_METHOD: u32 = 4;
const T_PROPERTY: u32 = 5;
const T_VARIABLE: u32 = 6;
const T_KEYWORD: u32 = 8;
const T_STRING: u32 = 9;
const T_NUMBER: u32 = 10;
const T_OPERATOR: u32 = 11;
const T_COMMENT: u32 = 13;

/// The modifier legend. A token's `token_modifiers_bitset` ORs the bit
/// `1 << index` for each modifier here.
pub const TOKEN_MODIFIERS: &[SemanticTokenModifier] = &[
    SemanticTokenModifier::DECLARATION,     // bit 0
    SemanticTokenModifier::DEFAULT_LIBRARY, // bit 1
];

const M_DECLARATION: u32 = 1 << 0;
const M_DEFAULT_LIBRARY: u32 = 1 << 1;

/// Built-in scalar and runtime type names that always highlight as types.
const BUILTIN_TYPES: &[&str] = &[
    "bool", "int8", "int16", "int32", "int64", "uint8", "uint16", "uint32", "uint64", "float32",
    "float64", "string", "void", "never", "Self", "Result",
];

/// A small set of prelude functions referenced by bare name (not via UFCS), so
/// they highlight as functions even outside call position.
const PRELUDE_FUNCTIONS: &[&str] = &[
    "print", "println", "input", "len", "assert", "panic", "range",
];

/// Compute the document's semantic tokens, delta-encoded as the protocol
/// requires (sorted by position; each token relative to the previous).
pub fn tokens(text: &str) -> Vec<SemanticToken> {
    let Ok(toks) = lex(text) else {
        return Vec::new();
    };
    let names = DeclaredNames::collect(text);
    let line_starts = line_starts(text);
    let comments = comment_spans(text);

    // Absolute tokens (line, start char in UTF-16, length, type, modifiers),
    // gathered then delta-encoded.
    let mut out: Vec<Abs> = Vec::new();

    // Significant (non-newline) token indices, for previous/next lookups.
    let sig: Vec<usize> = (0..toks.len())
        .filter(|&i| !matches!(toks[i].kind, TokenKind::Newline | TokenKind::Eof))
        .collect();
    let mut sig_pos = 0usize; // cursor into `sig`, advanced as we pass tokens

    for (i, tok) in toks.iter().enumerate() {
        if matches!(tok.kind, TokenKind::Newline | TokenKind::Eof) {
            continue;
        }
        // Keep `sig_pos` aligned so prev/next are O(1).
        while sig_pos < sig.len() && sig[sig_pos] != i {
            sig_pos += 1;
        }
        let prev = sig_pos
            .checked_sub(1)
            .and_then(|p| sig.get(p))
            .map(|&j| &toks[j].kind);
        let next = sig.get(sig_pos + 1).map(|&j| &toks[j].kind);

        if let Some((ty, modifiers)) = classify(&tok.kind, prev, next, &names) {
            if ty == T_STRING {
                push_span_excluding(&mut out, text, &line_starts, tok.span, &comments);
            } else {
                push_span(&mut out, text, &line_starts, tok.span, ty, modifiers);
            }
        }
    }

    // Comments are recovered separately since the lexer drops them.
    for span in comments {
        push_span(&mut out, text, &line_starts, span, T_COMMENT, 0);
    }

    out.sort_by_key(|a| (a.line, a.start));
    encode(out)
}

/// Classify a single token into a `(type, modifiers)` pair, or `None` to leave
/// it unhighlighted (brackets, commas, dots -- the client colours those).
fn classify(
    kind: &TokenKind,
    prev: Option<&TokenKind>,
    next: Option<&TokenKind>,
    names: &DeclaredNames,
) -> Option<(u32, u32)> {
    use TokenKind::*;
    let ty = match kind {
        Type | Fun | Let | Const | If | Else | Match | For | While | In | Return | Break
        | Continue | Import | True | False | Null | SelfLower | SelfUpper => {
            return Some((T_KEYWORD, 0));
        }
        Int(_) | Float(_) => T_NUMBER,
        Str(_) => T_STRING,
        Plus | Minus | Star | Slash | Percent | EqEq | NotEq | Lt | Gt | LtEq | GtEq | AmpAmp
        | PipePipe | Bang | Amp | Pipe | Caret | Tilde | Shl | Shr | Eq | PlusEq | MinusEq
        | StarEq | SlashEq | PercentEq | Arrow | FatArrow | Question => T_OPERATOR,
        Ident(name) => return Some(classify_ident(name, prev, next, names)),
        _ => return None,
    };
    Some((ty, 0))
}

/// Classify an identifier from its declaration context and the declared-name
/// sets. Declaration sites (after `fun`/`type`) win first; then member access
/// (`.name`); then call position; then the known-name sets; then a type
/// annotation position; otherwise a plain variable.
fn classify_ident(
    name: &str,
    prev: Option<&TokenKind>,
    next: Option<&TokenKind>,
    names: &DeclaredNames,
) -> (u32, u32) {
    use TokenKind::*;
    match prev {
        Some(Fun) => return (T_FUNCTION, M_DECLARATION),
        Some(Type) => {
            let ty = if names.sum_types.contains(name) {
                T_ENUM
            } else {
                T_TYPE
            };
            return (ty, M_DECLARATION);
        }
        Some(Dot) => {
            // Member access: a method when called, otherwise a field.
            let ty = if matches!(next, Some(LParen)) {
                T_METHOD
            } else {
                T_PROPERTY
            };
            return (ty, 0);
        }
        Some(Import) => return (T_NAMESPACE, 0),
        _ => {}
    }

    if names.sum_types.contains(name) {
        return (T_ENUM, 0);
    }
    if names.types.contains(name) {
        return (T_TYPE, 0);
    }
    if BUILTIN_TYPES.contains(&name) {
        return (T_TYPE, M_DEFAULT_LIBRARY);
    }
    if PRELUDE_FUNCTIONS.contains(&name) {
        return (T_FUNCTION, M_DEFAULT_LIBRARY);
    }
    if names.functions.contains(name) {
        return (T_FUNCTION, 0);
    }
    // A call `name(` not reached via `.` is a free-function reference.
    if matches!(next, Some(LParen)) {
        return (T_FUNCTION, 0);
    }
    // After `:` or `->`, an unknown name is most likely a type annotation.
    if matches!(prev, Some(Colon) | Some(Arrow)) {
        return (T_TYPE, 0);
    }
    (T_VARIABLE, 0)
}

/// Type and function names declared in the document, used to colour their
/// references. Gathered from a best-effort parse; an empty set on parse failure
/// just falls back to the contextual heuristics.
#[derive(Default)]
struct DeclaredNames {
    types: HashSet<String>,
    sum_types: HashSet<String>,
    functions: HashSet<String>,
}

impl DeclaredNames {
    fn collect(text: &str) -> Self {
        let mut names = DeclaredNames::default();
        let Ok(module) = parse(text) else {
            return names;
        };
        gather(&module, &mut names);
        names
    }
}

fn gather(module: &Module, names: &mut DeclaredNames) {
    for item in &module.items {
        match item {
            TopLevel::Fun(f) => {
                names.functions.insert(f.name.clone());
            }
            TopLevel::Type(t) => {
                names.types.insert(t.name.clone());
                if let TypeBody::Sum(_) = t.body {
                    names.sum_types.insert(t.name.clone());
                }
                // A record's methods are reachable by name through UFCS.
                if let TypeBody::Record(members) = &t.body {
                    for m in members {
                        if let Member::Method(method) = m {
                            names.functions.insert(method.name.clone());
                        }
                    }
                }
            }
            TopLevel::Stmt(_) => {}
        }
    }
}

/// An absolute (not yet delta-encoded) semantic token.
struct Abs {
    line: u32,
    start: u32,
    len: u32,
    ty: u32,
    modifiers: u32,
}

/// Push a span as one or more single-line tokens (the protocol forbids a token
/// crossing a line, so a multi-line string is split per line).
fn push_span(
    out: &mut Vec<Abs>,
    text: &str,
    line_starts: &[usize],
    span: Span,
    ty: u32,
    modifiers: u32,
) {
    let lo = span.lo.min(text.len());
    let hi = span.hi.min(text.len());
    if lo >= hi {
        return;
    }
    let mut line = match line_starts.binary_search(&lo) {
        Ok(l) => l,
        Err(next) => next - 1,
    };
    let mut seg_start = lo;
    while seg_start < hi {
        let line_end = line_starts.get(line + 1).copied().unwrap_or(text.len());
        let seg_end = hi.min(line_end);
        // Exclude a trailing newline from the highlighted segment.
        let content_end = text[seg_start..seg_end]
            .find('\n')
            .map(|n| seg_start + n)
            .unwrap_or(seg_end);
        let content_end =
            if content_end > seg_start && text.as_bytes().get(content_end - 1) == Some(&b'\r') {
                content_end - 1
            } else {
                content_end
            };
        if content_end > seg_start {
            let line_start = line_starts[line];
            let start = utf16_len(&text[line_start..seg_start]);
            let len = utf16_len(&text[seg_start..content_end]);
            out.push(Abs {
                line: line as u32,
                start,
                len,
                ty,
                modifiers,
            });
        }
        seg_start = seg_end;
        line += 1;
    }
}

/// Push the portions of `span` not occupied by recovered comments. String
/// tokens cover their interpolation source as one lexer token, so carving out
/// interpolation comments prevents overlapping semantic tokens.
fn push_span_excluding(
    out: &mut Vec<Abs>,
    text: &str,
    line_starts: &[usize],
    span: Span,
    excluded: &[Span],
) {
    let mut start = span.lo;
    for exclusion in excluded
        .iter()
        .filter(|exclusion| exclusion.lo < span.hi && exclusion.hi > span.lo)
    {
        if exclusion.lo > start {
            push_span(
                out,
                text,
                line_starts,
                Span::new(start, exclusion.lo.min(span.hi)),
                T_STRING,
                0,
            );
        }
        start = start.max(exclusion.hi);
    }
    if start < span.hi {
        push_span(
            out,
            text,
            line_starts,
            Span::new(start, span.hi),
            T_STRING,
            0,
        );
    }
}

/// Delta-encode absolute tokens into the protocol's flat `SemanticToken` form.
fn encode(abs: Vec<Abs>) -> Vec<SemanticToken> {
    let mut out = Vec::with_capacity(abs.len());
    let mut prev_line = 0u32;
    let mut prev_start = 0u32;
    for a in abs {
        let delta_line = a.line - prev_line;
        let delta_start = if delta_line == 0 {
            a.start - prev_start
        } else {
            a.start
        };
        out.push(SemanticToken {
            delta_line,
            delta_start,
            length: a.len,
            token_type: a.ty,
            token_modifiers_bitset: a.modifiers,
        });
        prev_line = a.line;
        prev_start = a.start;
    }
    out
}

/// Byte offsets of comments in source code and interpolation expressions.
/// String and interpolation recursion mirrors the lexer so braces, quotes, or
/// comment markers in any nested state cannot desynchronize the scan.
fn comment_spans(text: &str) -> Vec<Span> {
    let mut scanner = CommentScanner {
        bytes: text.as_bytes(),
        spans: Vec::new(),
    };
    scanner.scan_code(0, false);
    scanner.spans
}

struct CommentScanner<'a> {
    bytes: &'a [u8],
    spans: Vec<Span>,
}

impl CommentScanner<'_> {
    /// Scan code until EOF or the `}` closing a recursive interpolation/brace.
    fn scan_code(&mut self, mut i: usize, stop_at_brace: bool) -> usize {
        while i < self.bytes.len() {
            match self.bytes[i] {
                b'"' => i = self.skip_string(i),
                b'/' if self.bytes.get(i + 1) == Some(&b'/') => {
                    i = self.line_comment(i);
                }
                b'#' => i = self.line_comment(i),
                b'/' if self.bytes.get(i + 1) == Some(&b'*') => {
                    i = self.block_comment(i);
                }
                b'{' if stop_at_brace => i = self.scan_code(i + 1, true),
                b'}' if stop_at_brace => return i + 1,
                _ => i += 1,
            }
        }
        i
    }

    fn skip_string(&mut self, mut i: usize) -> usize {
        i += 1;
        while i < self.bytes.len() {
            match self.bytes[i] {
                b'\\' => i = (i + 2).min(self.bytes.len()),
                b'"' => return i + 1,
                b'{' => i = self.scan_code(i + 1, true),
                _ => i += 1,
            }
        }
        i
    }

    fn line_comment(&mut self, mut i: usize) -> usize {
        let start = i;
        while i < self.bytes.len() && self.bytes[i] != b'\n' {
            i += 1;
        }
        self.spans.push(Span::new(start, i));
        i
    }

    fn block_comment(&mut self, mut i: usize) -> usize {
        let start = i;
        i += 2;
        let mut depth = 1;
        while i < self.bytes.len() && depth > 0 {
            if self.bytes[i] == b'/' && self.bytes.get(i + 1) == Some(&b'*') {
                depth += 1;
                i += 2;
            } else if self.bytes[i] == b'*' && self.bytes.get(i + 1) == Some(&b'/') {
                depth -= 1;
                i += 2;
            } else {
                i += 1;
            }
        }
        self.spans.push(Span::new(start, i.min(self.bytes.len())));
        i
    }
}

fn utf16_len(s: &str) -> u32 {
    s.chars().map(|c| c.len_utf16() as u32).sum()
}

fn line_starts(text: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (i, b) in text.bytes().enumerate() {
        if b == b'\n' {
            starts.push(i + 1);
        }
    }
    starts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crlf_is_not_part_of_multiline_token_lengths() {
        let lengths: Vec<u32> = tokens("\"a\r\nb\"")
            .into_iter()
            .filter(|token| token.token_type == T_STRING)
            .map(|token| token.length)
            .collect();
        assert_eq!(lengths, vec![2, 2]);
    }

    /// Nested interpolation comments may contain unmatched braces and quotes;
    /// each remains a comment without hiding the real comment after the string.
    #[test]
    fn comments_follow_nested_string_and_interpolation_states() {
        let src = r#""literal // text { value // }
            + "nested { inner # }
            }" /* } */ }" // real"#;
        let found: Vec<&str> = comment_spans(src)
            .iter()
            .map(|span| &src[span.lo..span.hi])
            .collect();
        assert_eq!(found, vec!["// }", "# }", "/* } */", "// real"]);
    }
}
