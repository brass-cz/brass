//! Token definitions for the Prepoly lexer.
//!
//! Prepoly uses newlines as statement separators, so the lexer emits an
//! explicit `Newline` token. The parser decides per-position whether a
//! newline terminates a statement or should be treated as whitespace
//! (the newline-fallback strategy lives in the parser).

/// A byte-offset source span. `lo`/`hi` are byte indices into the source,
/// usable for slicing and for computing line/column on demand.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
}

impl Span {
    pub fn new(lo: usize, hi: usize) -> Self {
        Span { lo, hi }
    }

    /// Merge two spans into one covering both.
    pub fn merge(self, other: Span) -> Span {
        Span {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
        }
    }
}

/// One fragment of a string literal. String literals support `{expr}`
/// interpolation, so a literal is lexed into an ordered list of fragments:
/// raw text and the raw source of embedded expressions. The parser later
/// parses each `Interp` fragment as a sub-expression.
#[derive(Clone, Debug, PartialEq)]
pub enum StrPart {
    /// Literal text with escapes already resolved.
    Lit(String),
    /// Raw source text of an interpolated expression (between `{` and `}`).
    Interp(String),
}

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    // Literals
    Int(i64),
    Float(f64),
    Str(Vec<StrPart>),
    True,
    False,
    Null,

    // Identifiers and keywords
    Ident(String),
    Type,
    Fun,
    Let,
    Const,
    If,
    Else,
    Match,
    For,
    While,
    In,
    Return,
    Break,
    Continue,
    SelfLower, // self
    SelfUpper, // Self
    Import,

    // Punctuation / operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    EqEq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    AmpAmp,
    PipePipe,
    Bang,
    Amp,
    Pipe,
    Caret,
    Tilde,
    Shl, // <<
    Shr, // >>
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    PercentEq,
    Arrow,    // ->
    FatArrow, // =>
    Question, // ?
    Dot,
    DotDot, // ..
    Comma,
    Colon,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,

    /// Statement separator. The parser may treat this as whitespace.
    Newline,
    /// End of input.
    Eof,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Token { kind, span }
    }
}

/// Resolve a bare identifier to its keyword token, or `Ident` if not a keyword.
pub fn keyword_or_ident(s: &str) -> TokenKind {
    match s {
        "type" => TokenKind::Type,
        "fun" => TokenKind::Fun,
        "let" => TokenKind::Let,
        "const" => TokenKind::Const,
        "if" => TokenKind::If,
        "else" => TokenKind::Else,
        "match" => TokenKind::Match,
        "for" => TokenKind::For,
        "while" => TokenKind::While,
        "in" => TokenKind::In,
        "return" => TokenKind::Return,
        "break" => TokenKind::Break,
        "continue" => TokenKind::Continue,
        "null" => TokenKind::Null,
        "true" => TokenKind::True,
        "false" => TokenKind::False,
        "self" => TokenKind::SelfLower,
        "Self" => TokenKind::SelfUpper,
        "import" => TokenKind::Import,
        _ => TokenKind::Ident(s.to_string()),
    }
}
