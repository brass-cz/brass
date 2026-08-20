//! Token definitions for the Brass lexer.
//!
//! Brass uses newlines as statement separators, so the lexer emits an
//! explicit `Newline` token. The parser decides per-position whether a
//! newline terminates a statement or should be treated as whitespace
//! (the newline-fallback strategy lives in the parser).

/// A byte-offset source span. `lo`/`hi` are byte indices into the source,
/// usable for slicing and for computing line/column on demand.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
    /// Source coordinates retained by synthetic span shifts. Keeping this
    /// provenance in the span makes diagnostic restoration independent of any
    /// assumed maximum source-map offset.
    #[serde(default)]
    source: Option<(usize, usize)>,
}

impl Span {
    pub fn new(lo: usize, hi: usize) -> Self {
        Span {
            lo,
            hi,
            source: None,
        }
    }

    /// Merge two spans into one covering both.
    pub fn merge(self, other: Span) -> Span {
        let source = if self.source.is_some() || other.source.is_some() {
            let left = self.source_span();
            let right = other.source_span();
            Some((left.lo.min(right.lo), left.hi.max(right.hi)))
        } else {
            None
        };
        Span {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
            source,
        }
    }

    /// Return a synthetic copy shifted by `delta`, retaining the first source
    /// coordinates across any later nested shifts.
    pub fn shifted(self, delta: usize) -> Span {
        Span {
            lo: self.lo.checked_add(delta).expect("synthetic span overflow"),
            hi: self.hi.checked_add(delta).expect("synthetic span overflow"),
            source: self.source.or(Some((self.lo, self.hi))),
        }
    }

    /// Restore the original source coordinates of a synthetic span. Ordinary
    /// parser spans are returned unchanged.
    pub fn source_span(self) -> Span {
        self.source
            .map(|(lo, hi)| Span::new(lo, hi))
            .unwrap_or(self)
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
    /// Raw source text of an interpolated expression (between `{` and `}`),
    /// with the fragment's byte offset in the lexed source. The parser re-lexes
    /// the fragment from offset zero and shifts its spans by this offset (plus
    /// the file base), so diagnostics inside an interpolation point at the real
    /// location instead of the first file in the source map.
    Interp(String, usize),
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

/// Whether `s` lexes as a keyword rather than an identifier, so it cannot name
/// a binding, parameter, or function. Callers that synthesize source (the
/// plugin-module loader) consult this instead of keeping their own list.
pub fn is_keyword(s: &str) -> bool {
    !matches!(keyword_or_ident(s), TokenKind::Ident(_))
}
