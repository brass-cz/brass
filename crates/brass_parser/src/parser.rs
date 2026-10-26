//! Recursive-descent parser for Brass.
//!
//! Newlines: the lexer emits `Newline` tokens. Inside brackets (`()`, `[]`,
//! and type-literal / match braces) newlines are insignificant and skipped
//! automatically (`depth > 0`). At statement level a newline terminates a
//! statement, with three continuation allowances (see the `newline` module):
//!   - a binary/assign operator at end of line continues onto the next line
//!     (operators call `eat_newlines` before parsing their right operand);
//!   - a `.` at the start of the next line continues a method chain;
//!   - an `else` at the start of the next line continues the `if`.
//!
//! Inside a `match` arm body, a line that parses as `pattern =>` starts the
//! next arm even when its first token (`-`, `[`) could continue the arm's
//! expression (see `Parser::at_arm_boundary`).
//!
//! Statement blocks reset to `depth == 0` so newlines separate their
//! statements even when the block is nested inside brackets (closure bodies).

use crate::lexer::{DocComment, Span, StrPart, Token, TokenKind, lex_with_docs};

use crate::ast::*;

#[derive(Clone, Debug, PartialEq)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

/// Parse one source file into a `Module`. Fails on the first syntax error;
/// use [`parse_recovering`] to collect every error with a best-effort AST.
pub fn parse(src: &str) -> Result<Module, ParseError> {
    parse_with_base(src, 0)
}

/// Parse `src` with every span shifted by `base`. A multi-file driver assigns
/// each source a disjoint `base`, so a span's byte offset uniquely identifies the
/// file it came from -- which lets a diagnostic be attributed to the right file
/// and line even though each file is lexed from offset zero. Spans are
/// token-derived (the lexer shift carries through the parser's `merge`s); an
/// interpolation sub-expression, re-lexed from its fragment, is shifted by the
/// fragment's in-file offset as well.
pub fn parse_with_base(src: &str, base: usize) -> Result<Module, ParseError> {
    let (module, mut errors) = parse_recovering(src, base);
    match errors.is_empty() {
        true => Ok(module),
        false => Err(errors.remove(0)),
    }
}

/// Parse with error recovery: on a syntax error the parser records it and
/// resynchronizes -- to the next statement boundary inside a block, or to the
/// next plausible declaration at the top level -- and keeps going. Returns
/// everything that parsed plus every error, in source order, each at the span
/// of the offending token. An empty error list means the module is complete;
/// with errors the module is best-effort (the erroneous constructs are
/// dropped), suitable for diagnostics and editor features but not execution.
pub fn parse_recovering(src: &str, base: usize) -> (Module, Vec<ParseError>) {
    let empty = Module {
        imports: Vec::new(),
        items: Vec::new(),
    };
    // A lexing error is unrecoverable (the token stream ends there); report it
    // alone with whatever an empty module gives the caller.
    let (mut tokens, mut docs) = match lex_with_docs(src) {
        Ok(t) => t,
        Err(e) => {
            let err = ParseError {
                message: e.message,
                span: Span::new(e.span.lo + base, e.span.hi + base),
            };
            return (empty, vec![err]);
        }
    };
    for t in &mut tokens {
        t.span = Span::new(t.span.lo + base, t.span.hi + base);
    }
    for d in &mut docs {
        d.span = Span::new(d.span.lo + base, d.span.hi + base);
    }
    let mut p = Parser::new(tokens, docs, base);
    let module = p.parse_module();
    (module, p.errors)
}

struct Parser {
    tokens: Vec<Token>,
    /// Doc comments collected by the lexer, in source order. Attachment is by
    /// span: a doc comment belongs to the declaration whose first token it
    /// directly precedes (see [`Parser::doc_before`]).
    docs: Vec<DocComment>,
    pos: usize,
    /// The file's span base (multi-file offset). Interpolation fragments are
    /// re-lexed from offset zero, so their sub-parser shifts spans by this base
    /// plus the fragment's in-file offset to stay file-attributable.
    base: usize,
    /// Current recursive syntax nesting depth; bounded by [`MAX_SYNTAX_DEPTH`].
    syntax_depth: usize,
    /// Bracket nesting depth; when > 0 newlines are skipped automatically.
    depth: usize,
    /// Whether return statements target an enclosing function or closure.
    in_function: bool,
    /// When true, a bare `Ident {` is NOT a type literal (used inside `if`,
    /// `while`, `for`, and `match` head expressions).
    no_struct: bool,
    /// Saved `no_struct` values for bracket scopes.
    ns_save: Vec<bool>,
    /// Syntax errors recovered from so far, in source order; bounded by
    /// [`MAX_PARSE_ERRORS`].
    errors: Vec<ParseError>,
    /// While a `match` arm body is parsed: the bracket depth of that match's
    /// braces. At exactly this depth (not nested in brackets or a block) a
    /// newline followed by a line that parses as `pattern =>` ends the arm,
    /// even when the line begins with a token that could otherwise continue
    /// the expression (`-1 =>`, `[x, y] =>`). `None` outside arm bodies.
    arm_depth: Option<usize>,
}

type PResult<T> = Result<T, ParseError>;

/// Cap on recovered syntax errors per file. Past the first few, errors are
/// usually cascades of one real mistake; stopping keeps the report readable
/// and bounds the work on adversarial input.
const MAX_PARSE_ERRORS: usize = 20;

/// Maximum expression nesting the recursive-descent parser accepts. Deep enough
/// for any hand-written program; bounded so adversarial input gets a diagnostic
/// rather than a native stack overflow. The bound must hold for DEBUG builds
/// too, whose stack frames are several times larger. Type and pattern forms use
/// more frames per level than expressions, so 64 leaves headroom for every
/// guarded syntax kind and for the later visitors that consume the AST.
const MAX_SYNTAX_DEPTH: usize = 64;

impl Parser {
    fn new(tokens: Vec<Token>, docs: Vec<DocComment>, base: usize) -> Self {
        Parser {
            tokens,
            docs,
            pos: 0,
            base,
            syntax_depth: 0,
            depth: 0,
            in_function: false,
            no_struct: false,
            ns_save: Vec::new(),
            errors: Vec::new(),
            arm_depth: None,
        }
    }

    // ----- token cursor -----

    fn peek(&self) -> &TokenKind {
        &self.tokens[self.pos].kind
    }

    fn span(&self) -> Span {
        self.tokens[self.pos].span
    }

    /// True when the current token has the same variant as `k`.
    fn at_p(&self, k: TokenKind) -> bool {
        std::mem::discriminant(self.peek()) == std::mem::discriminant(&k)
    }

    /// True when the current `{` opens an anonymous-record literal rather than
    /// a block: the next non-newline token is an identifier followed by a `:`
    /// (`{ field: ... }`), or -- the field-shorthand form -- by a `,` or the
    /// closing `}` (`{ field }`, `{ field, ... }`). A lone identifier as a
    /// BLOCK expression yielded void (a block's value comes only from
    /// `return`), so reading it as a record takes over no meaningful program.
    /// Lookahead only -- the parser position is unchanged.
    fn at_anon_record(&self) -> bool {
        let skip_newlines = |mut i: usize| {
            while i < self.tokens.len() && matches!(self.tokens[i].kind, TokenKind::Newline) {
                i += 1;
            }
            i
        };
        let name = skip_newlines(self.pos + 1);
        if name >= self.tokens.len() || !matches!(self.tokens[name].kind, TokenKind::Ident(_)) {
            return false;
        }
        let colon = skip_newlines(name + 1);
        colon < self.tokens.len()
            && matches!(
                self.tokens[colon].kind,
                TokenKind::Colon | TokenKind::Comma | TokenKind::RBrace
            )
    }

    /// Skip newline tokens when inside brackets. Maintains the invariant that
    /// `pos` never rests on a newline while `depth > 0`.
    fn norm(&mut self) {
        if self.depth > 0 {
            while matches!(self.tokens[self.pos].kind, TokenKind::Newline) {
                self.pos += 1;
            }
        }
    }

    /// Unconditionally consume any run of newline tokens.
    fn eat_newlines(&mut self) {
        while matches!(self.tokens[self.pos].kind, TokenKind::Newline) {
            self.pos += 1;
        }
    }

    fn bump(&mut self) -> Token {
        let t = self.tokens[self.pos].clone();
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        self.norm();
        t
    }

    fn eat(&mut self, k: TokenKind) -> bool {
        if self.at_p(k) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, k: TokenKind, what: &str) -> PResult<Token> {
        if self.at_p(k) {
            Ok(self.bump())
        } else {
            Err(self.error(format!("expected {what}, found {}", describe(self.peek()))))
        }
    }

    fn error(&self, message: String) -> ParseError {
        ParseError {
            message,
            span: self.span(),
        }
    }

    /// True when the cursor is on a newline whose next non-newline token has
    /// the variant of `k` (used for `.`-chain and `else` continuation).
    fn newline_then(&self, k: TokenKind) -> bool {
        crate::newline::newline_then(&self.tokens, self.pos, &k)
    }

    fn ident(&mut self) -> PResult<(String, Span)> {
        let span = self.span();
        match self.peek().clone() {
            TokenKind::Ident(name) => {
                self.bump();
                Ok((name, span))
            }
            other => Err(self.error(format!("expected identifier, found {}", describe(&other)))),
        }
    }

    // ----- bracket scopes -----

    fn open(&mut self, open: TokenKind, what: &str) -> PResult<Span> {
        let s = self.expect(open, what)?.span;
        self.ns_save.push(self.no_struct);
        self.no_struct = false;
        self.depth += 1;
        self.norm();
        Ok(s)
    }

    fn close(&mut self, close: TokenKind, what: &str) -> PResult<Span> {
        self.depth -= 1;
        let s = self.expect(close, what)?.span;
        self.no_struct = self.ns_save.pop().unwrap_or(false);
        Ok(s)
    }

    // ----- top level -----

    fn parse_module(&mut self) -> Module {
        let mut imports = Vec::new();
        let mut items = Vec::new();
        self.eat_newlines();
        while !self.at_p(TokenKind::Eof) {
            let r = if self.at_p(TokenKind::Import) {
                self.parse_import().map(|i| imports.push(i))
            } else {
                self.parse_top_level().map(|t| items.push(t))
            };
            if let Err(e) = r.and_then(|()| self.statement_end(false)) {
                if !self.record_error(e) {
                    break;
                }
                self.recover_to_top_level();
            }
            self.eat_newlines();
        }
        Module { imports, items }
    }

    /// Require a statement boundary without consuming continuation tokens.
    fn statement_end(&self, in_block: bool) -> PResult<()> {
        if self.at_p(TokenKind::Newline)
            || self.at_p(TokenKind::Eof)
            || (in_block && self.at_p(TokenKind::RBrace))
        {
            Ok(())
        } else {
            Err(self.error(format!(
                "expected a newline after this statement, found {}",
                describe(self.peek())
            )))
        }
    }

    /// Braced member lists accept commas or newlines, including newlines
    /// skipped by bracket normalization after the final token of a member.
    fn member_separator(&mut self) -> PResult<()> {
        if self.eat(TokenKind::Comma)
            || self.at_p(TokenKind::RBrace)
            || self.at_p(TokenKind::Newline)
            || self
                .pos
                .checked_sub(1)
                .is_some_and(|i| matches!(self.tokens[i].kind, TokenKind::Newline))
        {
            self.eat_newlines();
            Ok(())
        } else {
            Err(self.error(format!(
                "expected a comma or newline, found {}",
                describe(self.peek())
            )))
        }
    }

    /// Record a recovered syntax error, keeping source order. At the cap the
    /// error is dropped and false is returned: the caller stops parsing
    /// (further errors are almost certainly cascades of the ones already
    /// reported), and a propagated copy is not double-recorded on the way out.
    fn record_error(&mut self, e: ParseError) -> bool {
        if self.errors.len() >= MAX_PARSE_ERRORS {
            return false;
        }
        self.errors.push(e);
        true
    }

    /// Reset the bracket bookkeeping a half-parsed top-level construct left
    /// behind (an `open()` whose `close()` never ran). `syntax_depth` is NOT
    /// reset: each guarded parser re-balances it even when an error propagates,
    /// and live enclosing frames still decrement it on their way out.
    fn reset_nesting(&mut self) {
        self.depth = 0;
        self.no_struct = false;
        self.ns_save.clear();
    }

    /// Panic-mode resynchronization to the next plausible top-level
    /// declaration: a `fun`/`type`/`import` keyword (which cannot occur inside
    /// an expression, so it is a safe restart anchor even when the skip began
    /// mid-construct), or a newline once at least as many brackets have closed
    /// as opened since the error. Always consumes at least one token so
    /// recovery makes progress.
    fn recover_to_top_level(&mut self) {
        self.reset_nesting();
        let mut depth: i64 = 0;
        let mut first = true;
        loop {
            match self.peek() {
                TokenKind::Eof => return,
                TokenKind::Fun | TokenKind::Type | TokenKind::Import if !first && depth <= 0 => {
                    return;
                }
                TokenKind::Newline if depth <= 0 => {
                    self.eat_newlines();
                    return;
                }
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
                _ => {}
            }
            self.pos += 1;
            first = false;
        }
    }

    /// Panic-mode resynchronization to the next statement boundary inside a
    /// block: a newline at bracket depth zero (relative to the error point),
    /// or a closing `}` once brackets balance -- left unconsumed so the block
    /// loop closes normally. The caller restores the block's own nesting
    /// state; this only skips tokens.
    fn recover_to_stmt_boundary(&mut self) {
        let mut depth: i64 = 0;
        loop {
            match self.peek() {
                TokenKind::Eof => return,
                TokenKind::Newline if depth <= 0 => {
                    self.eat_newlines();
                    return;
                }
                TokenKind::RBrace if depth <= 0 => return,
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
                _ => {}
            }
            self.pos += 1;
        }
    }

    /// `import a.b.{ Name, Name }`
    /// `import a.b.{ Name, Name }` (braced names), `import a.b.Name` (one
    /// name), or `import a.b` (the whole module, used qualified as `b.x`).
    /// The two brace-less forms are syntactically identical; the loader, which
    /// knows which modules exist, decides between them (`ImportDecl::bare`).
    fn parse_import(&mut self) -> PResult<ImportDecl> {
        let lo = self.expect(TokenKind::Import, "import")?.span;
        let mut path = Vec::new();
        let (first, mut hi) = self.ident()?;
        path.push(first);
        loop {
            if !self.at_p(TokenKind::Dot) {
                // Statement end: a bare module/single-name import.
                // Check for `as alias` renaming.
                let (alias, explicit_alias, hi) = if matches!(self.peek(), TokenKind::Ident(s) if s == "as")
                {
                    self.bump();
                    let (a, aspan) = self.ident()?;
                    (Some(a), true, aspan)
                } else {
                    (None, false, hi)
                };
                return Ok(ImportDecl {
                    path,
                    names: Vec::new(),
                    bare: true,
                    alias,
                    explicit_alias,
                    span: lo.merge(hi),
                });
            }
            self.expect(TokenKind::Dot, "'.'")?;
            if self.at_p(TokenKind::LBrace) {
                break;
            }
            let (seg, sspan) = self.ident()?;
            hi = sspan;
            path.push(seg);
        }
        self.open(TokenKind::LBrace, "'{'")?;
        let mut names = Vec::new();
        while !self.at_p(TokenKind::RBrace) {
            let (n, nspan) = self.ident()?;
            let name = if matches!(self.peek(), TokenKind::Ident(s) if s == "as") {
                self.bump();
                let (local, lspan) = self.ident()?;
                ImportedName {
                    remote: n,
                    local,
                    span: lspan,
                }
            } else {
                ImportedName::plain(n, nspan)
            };
            names.push(name);
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        let hi = self.close(TokenKind::RBrace, "'}'")?;
        Ok(ImportDecl {
            path,
            names,
            bare: false,
            alias: None,
            explicit_alias: false,
            span: lo.merge(hi),
        })
    }

    fn parse_top_level(&mut self) -> PResult<TopLevel> {
        match self.peek() {
            TokenKind::Type => {
                let doc = self.doc_before();
                let mut d = self.parse_type_decl()?;
                d.doc = doc;
                Ok(TopLevel::Type(d))
            }
            TokenKind::Fun => {
                let doc = self.doc_before();
                let mut d = self.parse_fun_decl()?;
                d.doc = doc;
                Ok(TopLevel::Fun(d))
            }
            _ => Ok(TopLevel::Stmt(self.parse_stmt()?)),
        }
    }

    /// The doc comment(s) written directly above the declaration that starts
    /// at the current token: every doc comment lying between the previous
    /// non-newline token and the current one (i.e. with nothing but line
    /// breaks and plain comments in between). Stacked doc comments join into
    /// paragraphs. Comments are matched by span, so a doc comment buried
    /// inside an earlier construct never leaks onto a later declaration.
    fn doc_before(&self) -> Option<String> {
        let cur_lo = self.tokens[self.pos].span.lo;
        let prev_hi = self.tokens[..self.pos]
            .iter()
            .rev()
            .find(|t| !matches!(t.kind, TokenKind::Newline))
            .map(|t| t.span.hi)
            .unwrap_or(self.base);
        let texts: Vec<&str> = self
            .docs
            .iter()
            .filter(|d| d.span.lo >= prev_hi && d.span.hi <= cur_lo)
            .map(|d| d.text.as_str())
            .collect();
        if texts.is_empty() {
            None
        } else {
            Some(texts.join("\n\n"))
        }
    }

    fn parse_type_decl(&mut self) -> PResult<TypeDecl> {
        let lo = self.expect(TokenKind::Type, "'type'")?.span;
        let (name, name_span) = self.ident()?;
        let mut interface_spans = Vec::new();
        let mut interfaces = Vec::new();
        if self.eat(TokenKind::Colon) {
            loop {
                let (n, span) = self.ident()?;
                interfaces.push(n);
                interface_spans.push(span);
                if !self.eat(TokenKind::Comma) {
                    break;
                }
                self.eat_newlines();
                if self.at_p(TokenKind::Eq) {
                    break;
                }
            }
        }
        self.expect(TokenKind::Eq, "'='")?;
        self.eat_newlines();
        let body = if self.at_p(TokenKind::LBrace) {
            TypeBody::Record(self.parse_member_block()?)
        } else if self.at_p(TokenKind::Pipe)
            || self.variant_name_ahead()
            || crate::newline::braced_variant_ahead(&self.tokens, self.pos)
        {
            // A leading `|` unambiguously marks a sum, and so does a braced
            // head followed by `|` (`type R = Ok { value } | Err { error }`).
            TypeBody::Sum(self.parse_variants()?)
        } else {
            // Ambiguous head: an inline sum (`Red | Green`), a refinement alias
            // (`Base { .. }`), or a plain alias (`Base`). Parse the first unit as a
            // type expression; a following `|` makes it a sum whose first variant
            // is that unit, otherwise it is an alias. (A single-variant sum must
            // use a leading `|`, freeing `type X = Base { .. }` to be a refinement.)
            let te = self.parse_type()?;
            if self.at_p(TokenKind::Pipe) || self.newline_then(TokenKind::Pipe) {
                let mut variants = vec![self.type_to_variant(te)?];
                while self.at_p(TokenKind::Pipe) || self.newline_then(TokenKind::Pipe) {
                    self.eat_newlines();
                    self.bump(); // '|'
                    self.eat_newlines();
                    variants.push(self.parse_one_variant()?);
                }
                TypeBody::Sum(variants)
            } else {
                TypeBody::Alias(te)
            }
        };
        Ok(TypeDecl {
            span: lo.merge(self.tokens[self.pos.saturating_sub(1)].span),
            name,
            name_span,
            interfaces,
            interface_spans,
            body,
            doc: None,
        })
    }

    /// Parse a comma- or newline-separated list of fields and signatures.
    fn parse_member_block(&mut self) -> PResult<Vec<Member>> {
        self.open(TokenKind::LBrace, "'{'")?;
        let mut members = Vec::new();
        while !self.at_p(TokenKind::RBrace) && !self.at_p(TokenKind::Eof) {
            members.push(self.parse_member()?);
            self.member_separator()?;
        }
        self.close(TokenKind::RBrace, "'}'")?;
        Ok(members)
    }

    fn parse_member(&mut self) -> PResult<Member> {
        // `type name` declares a type SLOT: a type parameter of the enclosing
        // record with no runtime storage. The older spelling `name: type` is
        // still accepted below (the `type` keyword in type position parses to
        // `TypeExpr::TypeSlot`); both forms produce the same AST.
        if self.at_p(TokenKind::Type) {
            let kw = self.bump().span;
            let (name, nspan) = self.ident()?;
            return Ok(Member::Field(Field {
                name,
                ty: Some(TypeExpr::TypeSlot(kw)),
                span: kw.merge(nspan),
            }));
        }
        let (name, lo) = self.ident()?;
        if self.at_p(TokenKind::LParen) {
            // Method: name(params) [-> type] block
            self.open(TokenKind::LParen, "'('")?;
            let params = self.parse_param_list(TokenKind::RParen, true)?;
            let params_hi = self.close(TokenKind::RParen, "')'")?;
            let ret = if self.eat(TokenKind::Arrow) {
                Some(self.parse_return_type()?)
            } else {
                None
            };
            // A type body declares fields and method *signatures* (interface
            // requirements) only. A method with a body is implemented outside the
            // type with `fun T.m(...)`, not inside the braces.
            if self.at_p(TokenKind::LBrace) {
                return Err(self.error(format!(
                    "implement method `{name}` with `fun T.{name}(...)` outside the type body, \
                     not inside it"
                )));
            }
            let hi = ret.as_ref().map(|r| r.span()).unwrap_or(params_hi);
            Ok(Member::Method(Method {
                span: lo.merge(hi),
                name_span: lo,
                name,
                params,
                ret,
                body: None,
                doc: None,
            }))
        } else {
            let ty = if self.eat(TokenKind::Colon) {
                Some(self.parse_type()?)
            } else {
                None
            };
            Ok(Member::Field(Field { name, ty, span: lo }))
        }
    }

    /// A name followed by a pipe is a variant head, including invalid dotted
    /// or keyword names that need a diagnostic at the head itself.
    fn variant_name_ahead(&self) -> bool {
        let mut end = self.pos + 1;
        while self
            .tokens
            .get(end)
            .is_some_and(|t| t.kind == TokenKind::Dot)
            && self
                .tokens
                .get(end + 1)
                .is_some_and(|t| matches!(t.kind, TokenKind::Ident(_)))
        {
            end += 2;
        }
        let end = crate::newline::next_significant(&self.tokens, end);
        self.tokens
            .get(end)
            .is_some_and(|t| t.kind == TokenKind::Pipe)
    }

    fn parse_variants(&mut self) -> PResult<Vec<Variant>> {
        let mut variants = Vec::new();
        self.eat_newlines();
        self.eat(TokenKind::Pipe); // optional leading '|'
        loop {
            variants.push(self.parse_one_variant()?);
            if self.at_p(TokenKind::Pipe) || self.newline_then(TokenKind::Pipe) {
                self.eat_newlines();
                self.bump(); // consume '|'
            } else {
                break;
            }
        }
        Ok(variants)
    }

    /// Parse one sum variant: a name and an optional `{ member ... }` block.
    fn parse_one_variant(&mut self) -> PResult<Variant> {
        self.eat_newlines();
        let lo = self.span();
        let mut name = match self.peek().clone() {
            TokenKind::Ident(name) => {
                self.bump();
                name
            }
            other => return Err(self.error(format!("invalid variant name {}", describe(&other)))),
        };
        let mut name_span = lo;
        while self.eat(TokenKind::Dot) {
            let (part, span) = self.ident()?;
            name.push('.');
            name.push_str(&part);
            name_span = name_span.merge(span);
        }
        Self::check_variant_name(&name, name_span)?;
        let members = if self.at_p(TokenKind::LBrace) {
            self.parse_member_block()?
        } else {
            Vec::new()
        };
        Ok(Variant {
            span: lo.merge(self.tokens[self.pos - 1].span),
            name,
            members,
        })
    }

    /// Variant declarations cannot use qualified names or keyword type references.
    fn check_variant_name(name: &str, span: Span) -> PResult<()> {
        if name.contains('.') || crate::lexer::is_keyword(name) {
            Err(ParseError {
                message: format!("invalid variant name `{name}`"),
                span,
            })
        } else {
            Ok(())
        }
    }

    /// Reinterpret a type expression as a sum variant, used when a `type X = A |
    /// B` inline sum was first parsed head-first as a type. Only a bare name
    /// (`A`) or a braced form (`A { f: T }`) is a valid variant.
    fn type_to_variant(&self, te: TypeExpr) -> PResult<Variant> {
        match te {
            TypeExpr::Named(name, span) => {
                Self::check_variant_name(&name, span)?;
                Ok(Variant {
                    span,
                    name,
                    members: Vec::new(),
                })
            }
            TypeExpr::Refine(base, fields, span) => {
                let TypeExpr::Named(name, name_span) = *base else {
                    return Err(self.error("invalid sum variant".to_string()));
                };
                Self::check_variant_name(&name, name_span)?;
                let members = fields
                    .into_iter()
                    .map(|(fname, fty, fspan)| {
                        Member::Field(Field {
                            span: fspan,
                            name: fname,
                            ty: Some(fty),
                        })
                    })
                    .collect();
                Ok(Variant {
                    span,
                    name,
                    members,
                })
            }
            other => Err(ParseError {
                message: "expected a sum variant name".into(),
                span: other.span(),
            }),
        }
    }

    fn parse_fun_decl(&mut self) -> PResult<FunDecl> {
        let lo = self.expect(TokenKind::Fun, "'fun'")?.span;
        let (first, first_span) = self.ident()?;
        // `fun T.m(...)` / `fun T[].m(...)` implements method `m` on the receiver
        // type `T` (an `T[]` receiver is the array type, used by stdlib for
        // primitive-array methods). Without a receiver, `first` is the free
        // function's own name.
        let (recv, name, name_span) = if self.at_p(TokenKind::LBracket) || self.at_p(TokenKind::Dot)
        {
            let mut recv_ty = TypeExpr::Named(first, first_span);
            if self.eat(TokenKind::LBracket) {
                let hi = self.expect(TokenKind::RBracket, "']'")?.span;
                recv_ty = TypeExpr::Array(Box::new(recv_ty), None, first_span.merge(hi));
            }
            self.expect(TokenKind::Dot, "'.'")?;
            let (m, mspan) = self.ident()?;
            (Some(recv_ty), m, mspan)
        } else {
            (None, first, first_span)
        };
        self.open(TokenKind::LParen, "'('")?;
        let params = self.parse_param_list(TokenKind::RParen, recv.is_some())?;
        self.close(TokenKind::RParen, "')'")?;
        let ret = if self.eat(TokenKind::Arrow) {
            Some(self.parse_return_type()?)
        } else {
            None
        };
        let saved_function = self.in_function;
        self.in_function = true;
        let body = self.parse_block();
        self.in_function = saved_function;
        let body = body?;
        Ok(FunDecl {
            span: lo.merge(body.span),
            name_span,
            name,
            recv,
            params,
            ret,
            body,
            doc: None,
        })
    }

    fn parse_param_list(&mut self, end: TokenKind, method: bool) -> PResult<Vec<Param>> {
        let mut params = Vec::new();
        while !self.at_p(end.clone()) {
            let span = self.span();
            let name = if self.at_p(TokenKind::SelfLower) {
                if !method || !params.is_empty() {
                    return Err(self.error(
                        "`self` is only allowed as the first parameter of a method".into(),
                    ));
                }
                self.bump();
                "self".to_string()
            } else {
                self.ident()?.0
            };
            let ty = if self.eat(TokenKind::Colon) {
                Some(self.parse_parameter_type()?)
            } else {
                None
            };
            params.push(Param { name, ty, span });
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        Ok(params)
    }

    // ----- statements -----

    fn parse_block(&mut self) -> PResult<Block> {
        let saved_arm = self.arm_depth.take();
        let block = self.parse_block_inner();
        self.arm_depth = saved_arm;
        block
    }

    fn parse_block_inner(&mut self) -> PResult<Block> {
        let saved_depth = self.depth;
        let saved_ns = self.no_struct;
        let saved_ns_len = self.ns_save.len();
        let lo = self.expect(TokenKind::LBrace, "'{'")?.span;
        self.depth = 0;
        self.no_struct = false;
        self.eat_newlines();
        let mut stmts = Vec::new();
        while !self.at_p(TokenKind::RBrace) && !self.at_p(TokenKind::Eof) {
            match self.parse_stmt().and_then(|stmt| {
                self.statement_end(true)?;
                Ok(stmt)
            }) {
                Ok(s) => stmts.push(s),
                // Record and resynchronize to the next statement in this
                // block, so one bad statement does not hide the rest of the
                // body (or the rest of the file). The failed statement may
                // have left `open()`s unclosed; restore this block's resting
                // state before continuing. At the error cap the error
                // propagates instead, unwinding the whole parse.
                Err(e) => {
                    if !self.record_error(e.clone()) {
                        return Err(e);
                    }
                    self.depth = 0;
                    self.no_struct = false;
                    self.ns_save.truncate(saved_ns_len);
                    self.recover_to_stmt_boundary();
                }
            }
            self.eat_newlines();
        }
        // End of input inside the block: report the missing '}' but close the
        // block implicitly, so the enclosing declaration and every statement
        // parsed so far survive in the recovered AST (editor features analyze
        // half-typed bodies; dropping the whole item would blind them). At the
        // error cap the error propagates and unwinds as before.
        let hi = if self.at_p(TokenKind::Eof) {
            let e = self.error(format!("expected '}}', found {}", describe(self.peek())));
            if !self.record_error(e.clone()) {
                return Err(e);
            }
            self.span()
        } else {
            self.expect(TokenKind::RBrace, "'}'")?.span
        };
        self.depth = saved_depth;
        self.no_struct = saved_ns;
        self.norm();
        Ok(Block {
            stmts,
            span: lo.merge(hi),
        })
    }

    fn parse_stmt(&mut self) -> PResult<Stmt> {
        match self.peek() {
            TokenKind::Let => self.parse_let(false),
            TokenKind::Const => self.parse_let(true),
            TokenKind::While => self.parse_while(),
            TokenKind::For => self.parse_for(),
            TokenKind::Return => self.parse_return(),
            TokenKind::Break => {
                let s = self.bump().span;
                Ok(Stmt::Break(s))
            }
            TokenKind::Continue => {
                let s = self.bump().span;
                Ok(Stmt::Continue(s))
            }
            _ => {
                let e = self.parse_expr()?;
                if let Some(op) = self.assign_op() {
                    let lo = e.span();
                    self.bump();
                    self.eat_newlines();
                    let value = self.parse_expr()?;
                    Ok(Stmt::Assign {
                        span: lo.merge(value.span()),
                        target: e,
                        op,
                        value,
                    })
                } else {
                    Ok(Stmt::Expr(e))
                }
            }
        }
    }

    fn assign_op(&self) -> Option<AssignOp> {
        Some(match self.peek() {
            TokenKind::Eq => AssignOp::Eq,
            TokenKind::PlusEq => AssignOp::Add,
            TokenKind::MinusEq => AssignOp::Sub,
            TokenKind::StarEq => AssignOp::Mul,
            TokenKind::SlashEq => AssignOp::Div,
            TokenKind::PercentEq => AssignOp::Rem,
            _ => return None,
        })
    }

    fn parse_let(&mut self, is_const: bool) -> PResult<Stmt> {
        let lo = self.bump().span; // let / const
        let pat = self.parse_pattern()?;
        let ty = if self.eat(TokenKind::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };
        // An annotated `let` may omit the initializer; the checker then
        // enforces definite assignment before any read. A `const` cannot (it is
        // never assignable afterwards), and an unannotated `let` has no type to
        // declare the binding with.
        if !is_const
            && !matches!(self.peek(), TokenKind::Eq)
            && let Some(ty) = ty
        {
            let hi = ty.span();
            return Ok(Stmt::Let {
                span: lo.merge(hi),
                pat,
                ty: Some(ty),
                value: None,
                is_const,
            });
        }
        self.expect(TokenKind::Eq, "'='")?;
        self.eat_newlines();
        let value = self.parse_expr()?;
        Ok(Stmt::Let {
            span: lo.merge(value.span()),
            pat,
            ty,
            value: Some(value),
            is_const,
        })
    }

    fn parse_while(&mut self) -> PResult<Stmt> {
        let lo = self.bump().span;
        let cond = self.parse_cond()?;
        let body = self.parse_block()?;
        Ok(Stmt::While {
            span: lo.merge(body.span),
            cond,
            body,
        })
    }

    fn parse_for(&mut self) -> PResult<Stmt> {
        let lo = self.bump().span;
        // A pattern, not just a name: `for [k, v] in map.pairs()` destructures each
        // element the way a `let` does.
        let pat = self.parse_pattern()?;
        self.expect(TokenKind::In, "'in'")?;
        let iter = self.parse_cond()?;
        let body = self.parse_block()?;
        Ok(Stmt::For {
            span: lo.merge(body.span),
            pat,
            iter,
            body,
        })
    }

    fn parse_return(&mut self) -> PResult<Stmt> {
        if !self.in_function {
            return Err(self.error("`return` outside a function".into()));
        }
        let lo = self.bump().span;
        let value = if self.at_p(TokenKind::Newline)
            || self.at_p(TokenKind::RBrace)
            || self.at_p(TokenKind::Eof)
        {
            None
        } else {
            Some(self.parse_expr()?)
        };
        let hi = value.as_ref().map(|e| e.span()).unwrap_or(lo);
        Ok(Stmt::Return(value, lo.merge(hi)))
    }

    /// Parse a head expression (if/while/for/match) with struct literals
    /// disabled so the following `{` is read as a block, not a type literal.
    fn parse_cond(&mut self) -> PResult<Expr> {
        let saved = self.no_struct;
        self.no_struct = true;
        let e = self.parse_expr();
        self.no_struct = saved;
        e
    }

    // ----- expressions (precedence cascade) -----

    fn parse_expr(&mut self) -> PResult<Expr> {
        // Recursive descent consumes native stack per nesting level; without a
        // bound, deeply nested source (thousands of `(`) aborts the whole
        // process with a stack overflow instead of a diagnostic.
        if self.syntax_depth >= MAX_SYNTAX_DEPTH {
            return Err(ParseError {
                message: "expression nesting is too deep".into(),
                span: self.span(),
            });
        }
        self.syntax_depth += 1;
        let result = self.parse_or();
        self.syntax_depth -= 1;
        result
    }

    fn parse_or(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_and()?;
        while self.at_p(TokenKind::PipePipe) {
            self.bump();
            self.eat_newlines();
            let rhs = self.parse_and()?;
            lhs = bin(BinOp::Or, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_and(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_cmp()?;
        while self.at_p(TokenKind::AmpAmp) {
            self.bump();
            self.eat_newlines();
            let rhs = self.parse_cmp()?;
            lhs = bin(BinOp::And, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_cmp(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_bitor()?;
        loop {
            let op = match self.peek() {
                TokenKind::EqEq => BinOp::Eq,
                TokenKind::NotEq => BinOp::Ne,
                TokenKind::Lt => BinOp::Lt,
                TokenKind::Gt => BinOp::Gt,
                TokenKind::LtEq => BinOp::Le,
                TokenKind::GtEq => BinOp::Ge,
                _ => break,
            };
            self.bump();
            self.eat_newlines();
            let rhs = self.parse_bitor()?;
            lhs = bin(op, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_bitor(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_bitxor()?;
        while self.at_p(TokenKind::Pipe) {
            self.bump();
            self.eat_newlines();
            let rhs = self.parse_bitxor()?;
            lhs = bin(BinOp::BitOr, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_bitxor(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_bitand()?;
        while self.at_p(TokenKind::Caret) {
            self.bump();
            self.eat_newlines();
            let rhs = self.parse_bitand()?;
            lhs = bin(BinOp::BitXor, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_bitand(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_shift()?;
        while self.at_p(TokenKind::Amp) {
            self.bump();
            self.eat_newlines();
            let rhs = self.parse_shift()?;
            lhs = bin(BinOp::BitAnd, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_shift(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_add()?;
        loop {
            let op = match self.peek() {
                TokenKind::Shl => BinOp::Shl,
                TokenKind::Shr => BinOp::Shr,
                _ => break,
            };
            self.bump();
            self.eat_newlines();
            let rhs = self.parse_add()?;
            lhs = bin(op, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_add(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_mul()?;
        loop {
            if self.at_p(TokenKind::Minus) && self.at_arm_boundary() {
                break;
            }
            let op = match self.peek() {
                TokenKind::Plus => BinOp::Add,
                TokenKind::Minus => BinOp::Sub,
                _ => break,
            };
            self.bump();
            self.eat_newlines();
            let rhs = self.parse_mul()?;
            lhs = bin(op, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_mul(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_unary()?;
        loop {
            let op = match self.peek() {
                TokenKind::Star => BinOp::Mul,
                TokenKind::Slash => BinOp::Div,
                TokenKind::Percent => BinOp::Rem,
                _ => break,
            };
            self.bump();
            self.eat_newlines();
            let rhs = self.parse_unary()?;
            lhs = bin(op, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_unary(&mut self) -> PResult<Expr> {
        // Prefix chains are collected iteratively so adversarial input cannot
        // consume one native stack frame per operator. They still count as
        // syntax nesting because the resulting AST and later visitors recurse
        // through the same chain.
        let mut prefixes = Vec::new();
        loop {
            let op = match self.peek() {
                TokenKind::Minus => UnaryOp::Neg,
                TokenKind::Bang => UnaryOp::Not,
                TokenKind::Tilde => UnaryOp::BitNot,
                _ => break,
            };
            if self.syntax_depth + prefixes.len() >= MAX_SYNTAX_DEPTH {
                return Err(ParseError {
                    message: "expression nesting is too deep".into(),
                    span: self.span(),
                });
            }
            prefixes.push((op, self.bump().span));
        }
        let mut inner = self.parse_postfix()?;
        for (op, lo) in prefixes.into_iter().rev() {
            let span = lo.merge(inner.span());
            inner = Expr::Unary(op, Box::new(inner), span);
        }
        Ok(inner)
    }

    fn parse_postfix(&mut self) -> PResult<Expr> {
        let mut e = self.parse_primary()?;
        loop {
            // Continue a method chain that breaks across a line: `expr \n .m()`.
            if self.depth == 0 && self.newline_then(TokenKind::Dot) {
                self.eat_newlines();
            }
            if self.at_p(TokenKind::LBracket) && self.at_arm_boundary() {
                break;
            }
            match self.peek() {
                TokenKind::Dot => {
                    self.bump();
                    let (name, nspan) = self.ident()?;
                    // `Type.Variant { fields }` variant construction.
                    if self.at_p(TokenKind::LBrace)
                        && !self.no_struct
                        && let Expr::Ident(tname, tspan) = &e
                    {
                        let (fields, hi) = self.parse_field_inits()?;
                        e = Expr::VariantLit(tname.clone(), name, fields, tspan.merge(hi));
                        continue;
                    }
                    // `qualifier.Type.Variant { fields }` — qualified variant.
                    if self.at_p(TokenKind::LBrace)
                        && !self.no_struct
                        && let Expr::Field(base, mid, _) = &e
                        && let Expr::Ident(q, qspan) = base.as_ref()
                    {
                        let dotted = format!("{q}.{mid}");
                        let qspan = *qspan;
                        let (fields, hi) = self.parse_field_inits()?;
                        e = Expr::VariantLit(dotted, name, fields, qspan.merge(hi));
                        continue;
                    }
                    let span = e.span().merge(nspan);
                    e = Expr::Field(Box::new(e), name, span);
                }
                TokenKind::LParen => {
                    let (args, hi) = self.parse_call_args()?;
                    let span = e.span().merge(hi);
                    e = Expr::Call(Box::new(e), args, span);
                }
                TokenKind::LBracket => {
                    self.open(TokenKind::LBracket, "'['")?;
                    let idx = self.parse_expr()?;
                    let hi = self.close(TokenKind::RBracket, "']'")?;
                    let span = e.span().merge(hi);
                    e = Expr::Index(Box::new(e), Box::new(idx), span);
                }
                TokenKind::Bang => {
                    let hi = self.bump().span;
                    let span = e.span().merge(hi);
                    e = Expr::ErrorProp(Box::new(e), span);
                }
                _ => break,
            }
        }
        Ok(e)
    }

    fn parse_call_args(&mut self) -> PResult<(Vec<Arg>, Span)> {
        self.open(TokenKind::LParen, "'('")?;
        let mut args = Vec::new();
        while !self.at_p(TokenKind::RParen) {
            let expr = self.parse_expr()?;
            args.push(Arg { expr });
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        let hi = self.close(TokenKind::RParen, "')'")?;
        Ok((args, hi))
    }

    fn check_value_name(name: &str, span: Span) -> PResult<()> {
        if name == "_" {
            Err(ParseError {
                message: "`_` is not a value".into(),
                span,
            })
        } else {
            Ok(())
        }
    }

    fn parse_primary(&mut self) -> PResult<Expr> {
        let span = self.span();
        match self.peek().clone() {
            TokenKind::Int(v) => {
                self.bump();
                Ok(Expr::Int(v, span))
            }
            TokenKind::Float(v) => {
                self.bump();
                Ok(Expr::Float(v, span))
            }
            TokenKind::Str(parts) => {
                self.bump();
                Ok(Expr::Str(self.lower_str(parts, span)?, span))
            }
            TokenKind::True => {
                self.bump();
                Ok(Expr::Bool(true, span))
            }
            TokenKind::False => {
                self.bump();
                Ok(Expr::Bool(false, span))
            }
            TokenKind::Null => {
                self.bump();
                Ok(Expr::Null(span))
            }
            TokenKind::SelfLower => {
                self.bump();
                Ok(Expr::SelfExpr(span))
            }
            TokenKind::SelfUpper => {
                self.bump();
                if self.at_p(TokenKind::LBrace) && !self.no_struct {
                    let (fields, hi) = self.parse_field_inits()?;
                    Ok(Expr::TypeLit("Self".into(), fields, span.merge(hi)))
                } else {
                    Ok(Expr::Ident("Self".into(), span))
                }
            }
            TokenKind::Ident(name) => {
                Self::check_value_name(&name, span)?;
                self.bump();
                if self.at_p(TokenKind::LBrace) && !self.no_struct {
                    let (fields, hi) = self.parse_field_inits()?;
                    Ok(Expr::TypeLit(name, fields, span.merge(hi)))
                } else {
                    Ok(Expr::Ident(name, span))
                }
            }
            TokenKind::LParen => self.parse_paren_or_closure(),
            TokenKind::LBracket => self.parse_array_lit(),
            TokenKind::LBrace => {
                // `{ field: value, ... }` in expression position is an anonymous
                // record literal (a structural record value); otherwise a block.
                // `no_struct` (an `if`/`while`/`for` header) keeps it a block.
                if !self.no_struct && self.at_anon_record() {
                    let (fields, hi) = self.parse_anonymous_field_inits()?;
                    Ok(Expr::TypeLit(String::new(), fields, span.merge(hi)))
                } else {
                    let b = self.parse_block()?;
                    let s = b.span;
                    Ok(Expr::Block(b, s))
                }
            }
            TokenKind::If => self.parse_if(),
            TokenKind::Match => self.parse_match(),
            other => Err(self.error(format!("unexpected token {}", describe(&other)))),
        }
    }

    fn parse_field_inits(&mut self) -> PResult<(Vec<(String, Expr)>, Span)> {
        self.parse_field_inits_inner(false)
    }

    fn parse_anonymous_field_inits(&mut self) -> PResult<(Vec<(String, Expr)>, Span)> {
        self.parse_field_inits_inner(true)
    }

    fn parse_field_inits_inner(&mut self, anonymous: bool) -> PResult<(Vec<(String, Expr)>, Span)> {
        self.open(TokenKind::LBrace, "'{'")?;
        let mut fields = Vec::new();
        let mut names = std::collections::HashSet::new();
        while !self.at_p(TokenKind::RBrace) {
            let (name, nspan) = self.ident()?;
            if anonymous {
                Self::check_field_name(&mut names, &name, nspan)?;
            }
            // `name: value`, or the shorthand `name` alone -- sugar for
            // `name: name`, initializing the field from the same-named binding
            // in scope (the pattern side already binds this way:
            // `Circle { radius }`). Desugared here, so the checker and the
            // back ends see an ordinary identifier read at the name's span.
            let value = if self.eat(TokenKind::Colon) {
                self.parse_expr()?
            } else {
                Self::check_value_name(&name, nspan)?;
                Expr::Ident(name.clone(), nspan)
            };
            fields.push((name, value));
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        let hi = self.close(TokenKind::RBrace, "'}'")?;
        Ok((fields, hi))
    }

    fn parse_array_lit(&mut self) -> PResult<Expr> {
        let lo = self.open(TokenKind::LBracket, "'['")?;
        if self.at_p(TokenKind::RBracket) {
            let hi = self.close(TokenKind::RBracket, "']'")?;
            return Ok(Expr::Array(Vec::new(), lo.merge(hi)));
        }
        let first = self.parse_expr()?;
        // `[lo..hi]` -- an integer range, distinguished from a list by the `..`.
        if self.eat(TokenKind::DotDot) {
            let end = self.parse_expr()?;
            let hi = self.close(TokenKind::RBracket, "']'")?;
            return Ok(Expr::Range(Box::new(first), Box::new(end), lo.merge(hi)));
        }
        let mut elems = vec![first];
        if self.eat(TokenKind::Comma) {
            while !self.at_p(TokenKind::RBracket) {
                elems.push(self.parse_expr()?);
                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
        }
        let hi = self.close(TokenKind::RBracket, "']'")?;
        Ok(Expr::Array(elems, lo.merge(hi)))
    }

    fn parse_paren_or_closure(&mut self) -> PResult<Expr> {
        if self.closure_ahead() {
            let lo = self.open(TokenKind::LParen, "'('")?;
            let params = self.parse_param_list(TokenKind::RParen, false)?;
            self.close(TokenKind::RParen, "')'")?;
            self.expect(TokenKind::Arrow, "'->'")?;
            self.eat_newlines();
            let saved_function = self.in_function;
            self.in_function = true;
            let body = (|| {
                if self.at_p(TokenKind::LBrace) {
                    let b = self.parse_block()?;
                    let s = b.span;
                    Ok(Expr::Block(b, s))
                } else {
                    self.parse_expr()
                }
            })();
            self.in_function = saved_function;
            let body = body?;
            let span = lo.merge(body.span());
            Ok(Expr::Closure(params, Box::new(body), span))
        } else {
            let lo = self.open(TokenKind::LParen, "'('")?;
            let mut e = self.parse_expr()?;
            let hi = self.close(TokenKind::RParen, "')'")?;
            *e.span_mut() = e.span().with_parentheses(lo.merge(hi));
            Ok(e)
        }
    }

    /// Lookahead: from a `(`, is the matching `)` followed by `->`?
    fn closure_ahead(&self) -> bool {
        crate::newline::closure_ahead(&self.tokens, self.pos)
    }

    fn parse_if(&mut self) -> PResult<Expr> {
        let lo = self.expect(TokenKind::If, "'if'")?.span;
        if self.eat(TokenKind::Let) {
            let pat = self.parse_pattern()?;
            self.expect(TokenKind::Eq, "'='")?;
            let scrut = self.parse_cond()?;
            let then = self.parse_block()?;
            let els = self.parse_else()?;
            let hi = els.as_ref().map(|e| e.span()).unwrap_or(then.span);
            Ok(Expr::IfLet(pat, Box::new(scrut), then, els, lo.merge(hi)))
        } else {
            let cond = if self.negated_type_test_ahead() {
                let bang = self.bump().span;
                self.open(TokenKind::LParen, "'('")?;
                let subject = self.parse_expr()?;
                self.validate_type_test_subject(&subject)?;
                self.expect(TokenKind::Colon, "':'")?;
                let te = self.parse_return_type()?;
                let hi = self.close(TokenKind::RParen, "')'")?;
                Expr::TypeTest(Box::new(subject), te, true, bang.merge(hi))
            } else {
                let subject = self.parse_cond()?;
                if self.eat(TokenKind::Colon) {
                    self.validate_type_test_subject(&subject)?;
                    // The next brace belongs to the arm, not a refinement.
                    let te = self.parse_return_type()?;
                    let span = subject.span().merge(te.span());
                    Expr::TypeTest(Box::new(subject), te, false, span)
                } else {
                    subject
                }
            };
            let then = self.parse_block()?;
            let els = self.parse_else()?;
            let hi = els.as_ref().map(|e| e.span()).unwrap_or(then.span);
            Ok(Expr::If(Box::new(cond), then, els, lo.merge(hi)))
        }
    }

    /// Recognize only the complete negated head; ordinary `!(value)` remains
    /// a unary expression and cannot introduce a type test in a larger value.
    fn negated_type_test_ahead(&self) -> bool {
        if !self.at_p(TokenKind::Bang)
            || !matches!(
                self.tokens.get(self.pos + 1).map(|t| &t.kind),
                Some(TokenKind::LParen)
            )
        {
            return false;
        }
        let mut depth = 0usize;
        for token in &self.tokens[self.pos + 1..] {
            match token.kind {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return false;
                    }
                }
                TokenKind::Colon if depth == 1 => return true,
                _ => {}
            }
        }
        false
    }

    fn validate_type_test_subject(&self, subject: &Expr) -> PResult<()> {
        if subject.span().is_parenthesized()
            || matches!(
                subject,
                Expr::Ident(..)
                    | Expr::Int(..)
                    | Expr::Float(..)
                    | Expr::Str(..)
                    | Expr::Bool(..)
                    | Expr::Null(..)
                    | Expr::SelfExpr(..)
                    | Expr::Field(..)
                    | Expr::Call(..)
                    | Expr::Index(..)
                    | Expr::ErrorProp(..)
                    | Expr::Array(..)
                    | Expr::Range(..)
                    | Expr::TypeLit(..)
                    | Expr::VariantLit(..)
            )
        {
            return Ok(());
        }
        let span = subject.span();
        if let Expr::Unary(UnaryOp::Not, inner, _) = subject {
            let operand = self.type_test_subject_text(inner.span());
            return Err(ParseError {
                message: format!("write `!({operand}: T)` to negate a type test"),
                span: Span::new(span.lo, span.lo + 1),
            });
        }
        let operand = self.type_test_subject_text(span);
        Err(ParseError {
            message: format!(
                "a type test applies to one operand; parenthesize it: `({operand}): T`"
            ),
            span,
        })
    }

    fn type_test_subject_text(&self, span: Span) -> String {
        let mut text = String::new();
        let mut end = span.lo;
        for token in self
            .tokens
            .iter()
            .filter(|t| t.span.lo >= span.lo && t.span.hi <= span.hi)
        {
            if matches!(token.kind, TokenKind::Newline) {
                continue;
            }
            if token.span.lo > end && !text.is_empty() {
                text.push(' ');
            }
            text.push_str(describe(&token.kind).trim_matches('`'));
            end = token.span.hi;
        }
        text
    }

    fn parse_else(&mut self) -> PResult<Option<Box<Expr>>> {
        let has_else =
            self.at_p(TokenKind::Else) || (self.depth == 0 && self.newline_then(TokenKind::Else));
        if !has_else {
            return Ok(None);
        }
        if !self.at_p(TokenKind::Else) {
            self.eat_newlines();
        }
        self.bump(); // 'else'
        if self.at_p(TokenKind::If) {
            Ok(Some(Box::new(self.parse_if()?)))
        } else {
            let b = self.parse_block()?;
            let s = b.span;
            Ok(Some(Box::new(Expr::Block(b, s))))
        }
    }

    fn parse_match(&mut self) -> PResult<Expr> {
        let lo = self.expect(TokenKind::Match, "'match'")?.span;
        let scrut = self.parse_cond()?;
        self.open(TokenKind::LBrace, "'{'")?;
        let mut arms = Vec::new();
        while !self.at_p(TokenKind::RBrace) && !self.at_p(TokenKind::Eof) {
            let pat = self.parse_pattern()?;
            self.expect(TokenKind::FatArrow, "'=>'")?;
            self.eat_newlines();
            let saved_arm = self.arm_depth.replace(self.depth);
            let body = self.parse_arm_body();
            self.arm_depth = saved_arm;
            let body = body?;
            arms.push(MatchArm {
                span: pat.span().merge(body.span()),
                pattern: pat,
                body,
            });
            self.member_separator()?;
        }
        let hi = self.close(TokenKind::RBrace, "'}'")?;
        Ok(Expr::Match(Box::new(scrut), arms, lo.merge(hi)))
    }

    /// Whether the cursor starts the next arm of the match whose arm body is
    /// being parsed: it sits at that match's own bracket depth, the token
    /// before it was a newline, and the line parses as `pattern =>`. The
    /// tokens that both start a pattern and continue an expression (`-`,
    /// `[`) consult this before continuing; the lookahead is speculative and
    /// leaves the parser untouched.
    fn at_arm_boundary(&mut self) -> bool {
        if self.arm_depth != Some(self.depth)
            || !self
                .pos
                .checked_sub(1)
                .is_some_and(|i| matches!(self.tokens[i].kind, TokenKind::Newline))
        {
            return false;
        }
        let pos = self.pos;
        let depth = self.depth;
        let syntax_depth = self.syntax_depth;
        let no_struct = self.no_struct;
        let ns_len = self.ns_save.len();
        let errors = self.errors.len();
        let arm = self.parse_pattern().is_ok() && self.at_p(TokenKind::FatArrow);
        self.pos = pos;
        self.depth = depth;
        self.syntax_depth = syntax_depth;
        self.no_struct = no_struct;
        self.ns_save.truncate(ns_len);
        self.errors.truncate(errors);
        arm
    }

    /// A match arm body is a block, an expression, or an assignment (the
    /// assignment form is used to mutate captured state).
    fn parse_arm_body(&mut self) -> PResult<Expr> {
        if self.at_p(TokenKind::LBrace) {
            let b = self.parse_block()?;
            let s = b.span;
            return Ok(Expr::Block(b, s));
        }
        let e = self.parse_expr()?;
        if let Some(op) = self.assign_op() {
            let lo = e.span();
            self.bump();
            self.eat_newlines();
            let value = self.parse_expr()?;
            let span = lo.merge(value.span());
            let stmt = Stmt::Assign {
                target: e,
                op,
                value,
                span,
            };
            Ok(Expr::Block(
                Block {
                    stmts: vec![stmt],
                    span,
                },
                span,
            ))
        } else {
            Ok(e)
        }
    }

    // ----- patterns -----

    fn parse_pattern(&mut self) -> PResult<Pattern> {
        if self.syntax_depth >= MAX_SYNTAX_DEPTH {
            return Err(ParseError {
                message: "pattern nesting is too deep".into(),
                span: self.span(),
            });
        }
        self.syntax_depth += 1;
        let result = self.parse_pattern_inner();
        self.syntax_depth -= 1;
        result
    }

    fn parse_pattern_inner(&mut self) -> PResult<Pattern> {
        let span = self.span();
        match self.peek().clone() {
            TokenKind::Ident(name) => {
                self.bump();
                if name == "_" {
                    return Ok(Pattern::Wildcard(span));
                }
                // Keep the type path separate from the final variant name:
                // unrelated sums can declare variants with the same name.
                let mut name = name;
                let mut name_span = span;
                let mut qualifier: Option<PatternQualifier> = None;
                while self.eat(TokenKind::Dot) {
                    qualifier = Some(match qualifier {
                        Some(q) => PatternQualifier {
                            ty: format!("{}.{name}", q.ty),
                            span: q.span.merge(name_span),
                        },
                        None => PatternQualifier {
                            ty: name,
                            span: name_span,
                        },
                    });
                    (name, name_span) = self.ident()?;
                }
                if self.at_p(TokenKind::LBrace) {
                    let (fields, hi) = self.parse_field_pats()?;
                    Ok(Pattern::Record(name, qualifier, fields, span.merge(hi)))
                } else {
                    Ok(Pattern::Binding(name, qualifier, span.merge(name_span)))
                }
            }
            TokenKind::Int(v) => {
                self.bump();
                Ok(Pattern::Literal(Box::new(Expr::Int(v, span)), span))
            }
            TokenKind::Float(v) => {
                self.bump();
                Ok(Pattern::Literal(Box::new(Expr::Float(v, span)), span))
            }
            TokenKind::Str(parts) => {
                self.bump();
                if parts.iter().any(|part| matches!(part, StrPart::Interp(..))) {
                    return Err(ParseError {
                        message: "string patterns cannot contain interpolation".into(),
                        span,
                    });
                }
                Ok(Pattern::Literal(
                    Box::new(Expr::Str(self.lower_str(parts, span)?, span)),
                    span,
                ))
            }
            TokenKind::True => {
                self.bump();
                Ok(Pattern::Literal(Box::new(Expr::Bool(true, span)), span))
            }
            TokenKind::False => {
                self.bump();
                Ok(Pattern::Literal(Box::new(Expr::Bool(false, span)), span))
            }
            TokenKind::Null => {
                self.bump();
                Ok(Pattern::Literal(Box::new(Expr::Null(span)), span))
            }
            TokenKind::Minus => {
                self.bump();
                match self.peek().clone() {
                    TokenKind::Int(v) => {
                        let span = span.merge(self.bump().span);
                        Ok(Pattern::Literal(Box::new(Expr::Int(-v, span)), span))
                    }
                    TokenKind::Float(v) => {
                        let span = span.merge(self.bump().span);
                        Ok(Pattern::Literal(Box::new(Expr::Float(-v, span)), span))
                    }
                    other => Err(self.error(format!(
                        "expected number after '-', found {}",
                        describe(&other)
                    ))),
                }
            }
            TokenKind::LBracket => {
                self.open(TokenKind::LBracket, "'['")?;
                let mut pats = Vec::new();
                while !self.at_p(TokenKind::RBracket) {
                    pats.push(self.parse_pattern()?);
                    if !self.eat(TokenKind::Comma) {
                        break;
                    }
                }
                let hi = self.close(TokenKind::RBracket, "']'")?;
                Ok(Pattern::Array(pats, span.merge(hi)))
            }
            other => Err(self.error(format!("expected pattern, found {}", describe(&other)))),
        }
    }

    fn parse_field_pats(&mut self) -> PResult<(Vec<FieldPat>, Span)> {
        self.open(TokenKind::LBrace, "'{'")?;
        let mut fields = Vec::new();
        while !self.at_p(TokenKind::RBrace) {
            // `..` -- match the remaining fields without binding them.
            if self.eat(TokenKind::DotDot) {
                self.eat(TokenKind::Comma);
                break;
            }
            let (name, fspan) = self.ident()?;
            let pat = if self.eat(TokenKind::Colon) {
                Some(self.parse_pattern()?)
            } else {
                None
            };
            fields.push(FieldPat {
                name,
                pat,
                span: fspan,
            });
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        let hi = self.close(TokenKind::RBrace, "'}'")?;
        Ok((fields, hi))
    }

    // ----- types -----

    fn parse_type(&mut self) -> PResult<TypeExpr> {
        let ty = self.parse_nested_type(true)?;
        self.check_passing_modes(&ty, false);
        Ok(ty)
    }

    fn parse_parameter_type(&mut self) -> PResult<TypeExpr> {
        let ty = self.parse_nested_type(true)?;
        self.check_passing_modes(&ty, true);
        Ok(ty)
    }

    /// Report a misplaced `ref`/`mut` without abandoning the enclosing
    /// declaration: the type itself parsed fine, so the rest of the
    /// declaration still parses and no cascade errors follow from recovery.
    fn check_passing_modes(&mut self, ty: &TypeExpr, parameter: bool) {
        if let Err(e) = validate_passing_modes(ty, parameter, false) {
            self.record_error(e);
        }
    }

    /// A return type (after `->`) never grabs a `Base { .. }` refinement: the
    /// `{` there begins the function body, not a refinement. Refinements in a
    /// return position are written through a type alias instead.
    fn parse_return_type(&mut self) -> PResult<TypeExpr> {
        let ty = self.parse_nested_type(false)?;
        self.check_passing_modes(&ty, false);
        Ok(ty)
    }

    /// Guard every recursive type form with the same budget as expressions and
    /// patterns. Keeping one counter also bounds mixed nesting such as
    /// `typeof` inside an anonymous-record annotation.
    fn parse_nested_type(&mut self, allow_refine: bool) -> PResult<TypeExpr> {
        if self.syntax_depth >= MAX_SYNTAX_DEPTH {
            return Err(ParseError {
                message: "type nesting is too deep".into(),
                span: self.span(),
            });
        }
        self.syntax_depth += 1;
        let result = self.parse_type_refine(allow_refine);
        self.syntax_depth -= 1;
        result
    }

    /// Parse a type with its postfix suffixes. `allow_refine` gates whether a
    /// bare `Base { .. }` at the head is read as a refinement (disabled for
    /// return types, where a following `{` is the body).
    fn parse_type_refine(&mut self, allow_refine: bool) -> PResult<TypeExpr> {
        let mut base = self.parse_base_type(allow_refine)?;
        // Postfix suffixes in any order, each wrapping the type built so far: array
        // `T[n]`/`T[]`, nullable `T?`, fallible `T!`. Interleaving them lets both
        // `T[]?` (a nullable array) and `T?[]` (an array of nullable elements) be
        // written, the latter needed for a slot array of optional records.
        loop {
            let lo = base.span();
            if self.at_p(TokenKind::LBracket) {
                self.open(TokenKind::LBracket, "'['")?;
                let len = if self.at_p(TokenKind::RBracket) {
                    None
                } else {
                    match self.peek().clone() {
                        TokenKind::Int(n) if n >= 0 => {
                            self.bump();
                            Some(n as usize)
                        }
                        other => {
                            return Err(self.error(format!(
                                "expected array length, found {}",
                                describe(&other)
                            )));
                        }
                    }
                };
                let hi = self.close(TokenKind::RBracket, "']'")?;
                base = TypeExpr::Array(Box::new(base), len, lo.merge(hi));
            } else if self.at_p(TokenKind::Question) {
                let hi = self.bump().span;
                base = TypeExpr::Nullable(Box::new(base), lo.merge(hi));
            } else if self.at_p(TokenKind::Bang) {
                let hi = self.bump().span;
                base = TypeExpr::Fallible(Box::new(base), lo.merge(hi));
            } else {
                break;
            }
        }
        Ok(base)
    }

    fn parse_base_type(&mut self, allow_refine: bool) -> PResult<TypeExpr> {
        let span = self.span();
        if self.at_p(TokenKind::Type) {
            // The `type` keyword as a field's declared type: a type SLOT, a
            // type-parameter with no runtime storage.
            self.bump();
            Ok(TypeExpr::TypeSlot(span))
        } else if self.at_p(TokenKind::LBracket) {
            // Tuple type: `[T0, T1, ...]`. (Array types are the postfix `T[]`/`T[n]`
            // handled in `parse_type`; a leading `[` is unambiguously a tuple.)
            self.open(TokenKind::LBracket, "'['")?;
            let mut elems = Vec::new();
            while !self.at_p(TokenKind::RBracket) {
                elems.push(self.parse_nested_type(true)?);
                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
            let hi = self.close(TokenKind::RBracket, "']'")?;
            Ok(TypeExpr::Tuple(elems, span.merge(hi)))
        } else if self.at_p(TokenKind::LParen) {
            // Function type: (T, ...) -> U
            self.open(TokenKind::LParen, "'('")?;
            let mut params = Vec::new();
            while !self.at_p(TokenKind::RParen) {
                params.push(self.parse_nested_type(true)?);
                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
            self.close(TokenKind::RParen, "')'")?;
            self.expect(TokenKind::Arrow, "'->'")?;
            let ret = self.parse_nested_type(false)?;
            let hi = ret.span();
            Ok(TypeExpr::Fun(params, Box::new(ret), span.merge(hi)))
        } else if self.at_p(TokenKind::SelfLower) || self.at_p(TokenKind::SelfUpper) {
            // `self`/`Self` in type position denote the enclosing type, so a
            // closure-typed field may take the enclosing type as a parameter,
            // e.g. `join: (self, string) -> string`. Both spellings resolve to
            // `Self`. `Self.field` names the enclosing type's field type (a slot
            // reference), used to express one field's type over another's.
            self.bump();
            if self.eat(TokenKind::Dot) {
                let (field, fspan) = self.ident()?;
                Ok(TypeExpr::SelfField(field, span.merge(fspan)))
            } else {
                Ok(TypeExpr::Named("Self".to_string(), span))
            }
        } else {
            let (name, _) = self.ident()?;
            // `mut(T)` -- a mutable `T`; `ref(T)` / `ref(mut(T))` -- a reference.
            // Neither is a keyword, so both are read as identifiers and only treated
            // specially when applied to a parenthesized type.
            if matches!(name.as_str(), "mut" | "ref") && self.at_p(TokenKind::LParen) {
                self.open(TokenKind::LParen, "'('")?;
                let inner = self.parse_nested_type(true)?;
                let hi = self.close(TokenKind::RParen, "')'")?;
                let inner = Box::new(inner);
                return Ok(if name == "mut" {
                    TypeExpr::Mut(inner, span.merge(hi))
                } else {
                    TypeExpr::Ref(inner, span.merge(hi))
                });
            }
            // `typeof(e)` -- the static type of the value expression `e`. Not a
            // keyword; read as an identifier applied to a parenthesized value.
            if name == "typeof" && self.at_p(TokenKind::LParen) {
                self.open(TokenKind::LParen, "'('")?;
                let e = self.parse_expr()?;
                let hi = self.close(TokenKind::RParen, "')'")?;
                return Ok(TypeExpr::TypeOf(Box::new(e), span.merge(hi)));
            }
            // `anonymous { field: T, ... }` -- an inline structural record type.
            if name == "anonymous" && self.at_p(TokenKind::LBrace) {
                self.open(TokenKind::LBrace, "'{'")?;
                let mut fields = Vec::new();
                let mut names = std::collections::HashSet::new();
                while !self.at_p(TokenKind::RBrace) {
                    let (fname, fspan) = self.ident()?;
                    Self::check_field_name(&mut names, &fname, fspan)?;
                    self.expect(TokenKind::Colon, "':'")?;
                    let fty = self.parse_nested_type(true)?;
                    fields.push((fname, fty, fspan));
                    if !self.eat(TokenKind::Comma) {
                        break;
                    }
                }
                let hi = self.close(TokenKind::RBrace, "'}'")?;
                return Ok(TypeExpr::Anonymous(fields, span.merge(hi)));
            }
            // `alias.Type` -- a type of a module imported whole (`import
            // geometry.vec` then `vec.Vec2`). Kept as a dotted name here; the
            // qualified-use resolution pass rewrites it to the bare name.
            let mut name = name;
            let mut span = span;
            if self.at_p(TokenKind::Dot)
                && matches!(&self.tokens[self.pos + 1].kind, TokenKind::Ident(_))
            {
                self.bump();
                let (seg, sspan) = self.ident()?;
                name = format!("{name}.{seg}");
                span = span.merge(sspan);
            }
            // `Base { field: T, ... }` -- refine nominal record `Base` by pinning
            // the named fields/slots. Gated by `allow_refine` so a return type's
            // following `{` (the function body) is not mistaken for a refinement.
            if allow_refine && self.at_p(TokenKind::LBrace) {
                let base = TypeExpr::Named(name, span);
                let (fields, hi) = self.parse_refine_fields()?;
                return Ok(TypeExpr::Refine(Box::new(base), fields, span.merge(hi)));
            }
            Ok(TypeExpr::Named(name, span))
        }
    }

    /// Parse a refinement's `{ field: T, ... }` body (also `Self.field: T`
    /// entries): each pins a base field/slot to a type. Returns the entries and
    /// the closing-brace span.
    fn parse_refine_fields(&mut self) -> PResult<(Vec<TypeField>, Span)> {
        self.open(TokenKind::LBrace, "'{'")?;
        self.eat_newlines();
        let mut fields = Vec::new();
        let mut names = std::collections::HashSet::new();
        while !self.at_p(TokenKind::RBrace) {
            let (fname, fspan) = self.ident()?;
            Self::check_field_name(&mut names, &fname, fspan)?;
            self.expect(TokenKind::Colon, "':'")?;
            let fty = self.parse_nested_type(true)?;
            fields.push((fname, fty, fspan));
            self.member_separator()?;
        }
        let hi = self.close(TokenKind::RBrace, "'}'")?;
        Ok((fields, hi))
    }

    /// Reject duplicate structural fields while their name tokens are available.
    fn check_field_name(
        names: &mut std::collections::HashSet<String>,
        name: &str,
        span: Span,
    ) -> PResult<()> {
        if names.insert(name.to_string()) {
            Ok(())
        } else {
            Err(ParseError {
                message: format!("duplicate field `{name}`"),
                span,
            })
        }
    }

    // ----- string interpolation -----

    fn lower_str(&self, parts: Vec<StrPart>, _span: Span) -> PResult<Vec<StrSeg>> {
        let mut segs = Vec::new();
        for part in parts {
            match part {
                StrPart::Lit(s) => segs.push(StrSeg::Lit(s)),
                StrPart::Interp(raw, frag_lo) => {
                    let e = parse_sub_expr(&raw, self.base + frag_lo, self.in_function)?;
                    segs.push(StrSeg::Expr(Box::new(e)));
                }
            }
        }
        Ok(segs)
    }
}

/// Parse the raw source of an interpolation `{...}` as a single expression.
/// `shift` is the fragment's absolute offset (file base + in-file position of
/// the byte after the `{`); the fragment is lexed from zero, so every span is
/// shifted to stay attributable to the real file and line.
fn parse_sub_expr(raw: &str, shift: usize, in_function: bool) -> PResult<Expr> {
    let reattribute = |s: Span| Span::new(s.lo + shift, s.hi + shift);
    let mut tokens = crate::lexer::lex(raw).map_err(|e| ParseError {
        message: format!("in string interpolation: {}", e.message),
        span: reattribute(e.span),
    })?;
    for t in &mut tokens {
        t.span = reattribute(t.span);
    }
    // An interpolation fragment is an expression; no declarations, no docs.
    let mut p = Parser::new(tokens, Vec::new(), shift);
    p.in_function = in_function;
    p.eat_newlines();
    let e = p.parse_expr()?;
    if let Some(error) = p.errors.first().cloned() {
        return Err(error);
    }
    p.eat_newlines();
    if !p.at_p(TokenKind::Eof) {
        return Err(ParseError {
            message: "unexpected trailing tokens in string interpolation".into(),
            span: p.span(),
        });
    }
    Ok(e)
}

fn bin(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
    let span = lhs.span().merge(rhs.span());
    Expr::Binary(op, Box::new(lhs), Box::new(rhs), span)
}

/// Human-readable token name for error messages.
fn describe(k: &TokenKind) -> String {
    use TokenKind::*;
    let sym = match k {
        Eof => return "end of input".into(),
        Newline => return "newline".into(),
        Ident(s) => return format!("`{s}`"),
        Int(v) => return format!("`{v}`"),
        Float(v) => return format!("`{v}`"),
        Str(_) => return "string literal".into(),
        True => "true",
        False => "false",
        Null => "null",
        Type => "type",
        Fun => "fun",
        Let => "let",
        Const => "const",
        If => "if",
        Else => "else",
        Match => "match",
        For => "for",
        While => "while",
        In => "in",
        Return => "return",
        Break => "break",
        Continue => "continue",
        SelfLower => "self",
        SelfUpper => "Self",
        Import => "import",
        Plus => "+",
        Minus => "-",
        Star => "*",
        Slash => "/",
        Percent => "%",
        EqEq => "==",
        NotEq => "!=",
        Lt => "<",
        Gt => ">",
        LtEq => "<=",
        GtEq => ">=",
        AmpAmp => "&&",
        PipePipe => "||",
        Bang => "!",
        Amp => "&",
        Pipe => "|",
        Caret => "^",
        Tilde => "~",
        Shl => "<<",
        Shr => ">>",
        Eq => "=",
        PlusEq => "+=",
        MinusEq => "-=",
        StarEq => "*=",
        SlashEq => "/=",
        PercentEq => "%=",
        Arrow => "->",
        FatArrow => "=>",
        Question => "?",
        Dot => ".",
        DotDot => "..",
        Comma => ",",
        Colon => ":",
        LParen => "(",
        RParen => ")",
        LBracket => "[",
        RBracket => "]",
        LBrace => "{",
        RBrace => "}",
    };
    format!("`{sym}`")
}

/// Passing modes describe a parameter boundary, never a stored value type.
/// Once inside a mode, even nested function types cannot introduce another mode.
fn validate_passing_modes(ty: &TypeExpr, parameter: bool, inside_mode: bool) -> PResult<()> {
    match ty {
        TypeExpr::Ref(inner, span) | TypeExpr::Mut(inner, span) => {
            if !parameter || inside_mode {
                let name = if matches!(ty, TypeExpr::Ref(..)) {
                    "ref"
                } else {
                    "mut"
                };
                return Err(ParseError {
                    message: format!("`{name}(...)` is only allowed as a parameter's type"),
                    span: *span,
                });
            }
            let value = if matches!(ty, TypeExpr::Ref(..)) {
                match &**inner {
                    TypeExpr::Mut(value, _) => value,
                    other => other,
                }
            } else {
                inner
            };
            validate_passing_modes(value, false, true)
        }
        TypeExpr::Array(inner, _, _)
        | TypeExpr::Nullable(inner, _)
        | TypeExpr::Fallible(inner, _) => validate_passing_modes(inner, false, inside_mode),
        TypeExpr::Fun(params, ret, _) => {
            for param in params {
                validate_passing_modes(param, true, inside_mode)?;
            }
            validate_passing_modes(ret, false, inside_mode)
        }
        TypeExpr::Tuple(types, _) => types
            .iter()
            .try_for_each(|ty| validate_passing_modes(ty, false, inside_mode)),
        TypeExpr::Anonymous(fields, _) => fields
            .iter()
            .try_for_each(|(_, ty, _)| validate_passing_modes(ty, false, inside_mode)),
        TypeExpr::Refine(base, fields, _) => {
            validate_passing_modes(base, false, inside_mode)?;
            fields
                .iter()
                .try_for_each(|(_, ty, _)| validate_passing_modes(ty, false, inside_mode))
        }
        TypeExpr::Named(..)
        | TypeExpr::SelfField(..)
        | TypeExpr::TypeSlot(..)
        | TypeExpr::TypeOf(..) => Ok(()),
    }
}
