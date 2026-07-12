//! Recursive-descent parser for Prepoly.
//!
//! Newlines: the lexer emits `Newline` tokens. Inside brackets (`()`, `[]`,
//! and type-literal / match braces) newlines are insignificant and skipped
//! automatically (`depth > 0`). At statement level a newline terminates a
//! statement, with two continuation allowances:
//!   - a binary/assign operator at end of line continues onto the next line
//!     (operators call `eat_newlines` before parsing their right operand);
//!   - a `.` at the start of the next line continues a method chain.
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
/// token-derived (the lexer shift carries through the parser's `merge`s); only an
/// interpolation sub-expression, re-lexed from its fragment, stays
/// fragment-relative, which is a pre-existing limitation unaffected here.
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
    /// Current expression nesting depth; bounded by [`MAX_EXPR_DEPTH`].
    expr_depth: usize,
    /// Bracket nesting depth; when > 0 newlines are skipped automatically.
    depth: usize,
    /// When true, a bare `Ident {` is NOT a type literal (used inside `if`,
    /// `while`, `for`, and `match` head expressions).
    no_struct: bool,
    /// Saved `no_struct` values for bracket scopes.
    ns_save: Vec<bool>,
    /// Syntax errors recovered from so far, in source order; bounded by
    /// [`MAX_PARSE_ERRORS`].
    errors: Vec<ParseError>,
}

type PResult<T> = Result<T, ParseError>;

/// Cap on recovered syntax errors per file. Past the first few, errors are
/// usually cascades of one real mistake; stopping keeps the report readable
/// and bounds the work on adversarial input.
const MAX_PARSE_ERRORS: usize = 20;

/// Maximum expression nesting the recursive-descent parser accepts. Deep enough
/// for any hand-written program; bounded so adversarial input gets a diagnostic
/// rather than a native stack overflow. The bound must hold for DEBUG builds
/// too, whose stack frames are several times larger (a debug binary overflows
/// near depth 300; 150 leaves the rest of the pipeline headroom as well).
const MAX_EXPR_DEPTH: usize = 150;

impl Parser {
    fn new(tokens: Vec<Token>, docs: Vec<DocComment>, base: usize) -> Self {
        Parser {
            tokens,
            docs,
            pos: 0,
            base,
            expr_depth: 0,
            depth: 0,
            no_struct: false,
            ns_save: Vec::new(),
            errors: Vec::new(),
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

    /// True when the current `{` opens an anonymous-record literal (`{ field: ...`)
    /// rather than a block: the next non-newline token is an identifier followed by
    /// a `:`. Lookahead only -- the parser position is unchanged.
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
        colon < self.tokens.len() && matches!(self.tokens[colon].kind, TokenKind::Colon)
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
            if let Err(e) = r {
                if !self.record_error(e) {
                    break;
                }
                self.recover_to_top_level();
            }
            self.eat_newlines();
        }
        Module { imports, items }
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
    /// behind (an `open()` whose `close()` never ran). `expr_depth` is NOT
    /// reset: `parse_expr` re-balances it even when an error propagates, and
    /// live enclosing frames still decrement it on their way out.
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
                    span: nspan.merge(lspan),
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
        let (name, _) = self.ident()?;
        let mut interfaces = Vec::new();
        if self.eat(TokenKind::Colon) {
            loop {
                let (n, _) = self.ident()?;
                interfaces.push(n);
                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
        }
        self.expect(TokenKind::Eq, "'='")?;
        self.eat_newlines();
        let body = if self.at_p(TokenKind::LBrace) {
            TypeBody::Record(self.parse_member_block()?)
        } else if self.at_p(TokenKind::Pipe) {
            // A leading `|` unambiguously marks a sum.
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
            interfaces,
            body,
            doc: None,
        })
    }

    /// Parse `{ field/method ... }`. Members are self-delimiting; newlines
    /// inside the braces are insignificant.
    fn parse_member_block(&mut self) -> PResult<Vec<Member>> {
        self.open(TokenKind::LBrace, "'{'")?;
        let mut members = Vec::new();
        while !self.at_p(TokenKind::RBrace) && !self.at_p(TokenKind::Eof) {
            members.push(self.parse_member()?);
            // Members may be separated by commas (inline) or newlines.
            self.eat(TokenKind::Comma);
        }
        self.close(TokenKind::RBrace, "'}'")?;
        Ok(members)
    }

    fn parse_member(&mut self) -> PResult<Member> {
        let (name, lo) = self.ident()?;
        if self.at_p(TokenKind::LParen) {
            // Method: name(params) [-> type] block
            self.open(TokenKind::LParen, "'('")?;
            let params = self.parse_param_list(TokenKind::RParen)?;
            self.close(TokenKind::RParen, "')'")?;
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
            let hi = ret.as_ref().map(|r| r.span()).unwrap_or(lo);
            Ok(Member::Method(Method {
                span: lo.merge(hi),
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
        let (name, lo) = self.ident()?;
        let members = if self.at_p(TokenKind::LBrace) {
            self.parse_member_block()?
        } else {
            Vec::new()
        };
        Ok(Variant {
            span: lo,
            name,
            members,
        })
    }

    /// Reinterpret a type expression as a sum variant, used when a `type X = A |
    /// B` inline sum was first parsed head-first as a type. Only a bare name
    /// (`A`) or a braced form (`A { f: T }`) is a valid variant.
    fn type_to_variant(&self, te: TypeExpr) -> PResult<Variant> {
        match te {
            TypeExpr::Named(name, span) => Ok(Variant {
                span,
                name,
                members: Vec::new(),
            }),
            TypeExpr::Refine(base, fields, span) => {
                let TypeExpr::Named(name, _) = *base else {
                    return Err(self.error("invalid sum variant".to_string()));
                };
                let members = fields
                    .into_iter()
                    .map(|(fname, fty)| {
                        Member::Field(Field {
                            span: fty.span(),
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
            _ => Err(self.error("expected a sum variant name".to_string())),
        }
    }

    fn parse_fun_decl(&mut self) -> PResult<FunDecl> {
        let lo = self.expect(TokenKind::Fun, "'fun'")?.span;
        let (first, first_span) = self.ident()?;
        // `fun T.m(...)` / `fun T[].m(...)` implements method `m` on the receiver
        // type `T` (an `T[]` receiver is the array type, used by stdlib for
        // primitive-array methods). Without a receiver, `first` is the free
        // function's own name.
        let (recv, name) = if self.at_p(TokenKind::LBracket) || self.at_p(TokenKind::Dot) {
            let mut recv_ty = TypeExpr::Named(first, first_span);
            if self.eat(TokenKind::LBracket) {
                let hi = self.expect(TokenKind::RBracket, "']'")?.span;
                recv_ty = TypeExpr::Array(Box::new(recv_ty), None, first_span.merge(hi));
            }
            self.expect(TokenKind::Dot, "'.'")?;
            let (m, _) = self.ident()?;
            (Some(recv_ty), m)
        } else {
            (None, first)
        };
        self.open(TokenKind::LParen, "'('")?;
        let params = self.parse_param_list(TokenKind::RParen)?;
        self.close(TokenKind::RParen, "')'")?;
        let ret = if self.eat(TokenKind::Arrow) {
            Some(self.parse_return_type()?)
        } else {
            None
        };
        let body = self.parse_block()?;
        Ok(FunDecl {
            span: lo.merge(body.span),
            name,
            recv,
            params,
            ret,
            body,
            doc: None,
        })
    }

    fn parse_param_list(&mut self, end: TokenKind) -> PResult<Vec<Param>> {
        let mut params = Vec::new();
        while !self.at_p(end.clone()) {
            let span = self.span();
            let name = if self.at_p(TokenKind::SelfLower) {
                self.bump();
                "self".to_string()
            } else {
                self.ident()?.0
            };
            let ty = if self.eat(TokenKind::Colon) {
                Some(self.parse_type()?)
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
        let saved_depth = self.depth;
        let saved_ns = self.no_struct;
        let saved_ns_len = self.ns_save.len();
        let lo = self.expect(TokenKind::LBrace, "'{'")?.span;
        self.depth = 0;
        self.no_struct = false;
        self.eat_newlines();
        let mut stmts = Vec::new();
        while !self.at_p(TokenKind::RBrace) && !self.at_p(TokenKind::Eof) {
            match self.parse_stmt() {
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
        let hi = self.expect(TokenKind::RBrace, "'}'")?.span;
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
        if self.expr_depth >= MAX_EXPR_DEPTH {
            return Err(ParseError {
                message: "expression nesting is too deep".into(),
                span: self.span(),
            });
        }
        self.expr_depth += 1;
        let result = self.parse_or();
        self.expr_depth -= 1;
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
        let op = match self.peek() {
            TokenKind::Minus => Some(UnaryOp::Neg),
            TokenKind::Bang => Some(UnaryOp::Not),
            TokenKind::Tilde => Some(UnaryOp::BitNot),
            _ => None,
        };
        if let Some(op) = op {
            let lo = self.bump().span;
            let inner = self.parse_unary()?;
            Ok(Expr::Unary(
                op,
                Box::new(inner.clone()),
                lo.merge(inner.span()),
            ))
        } else {
            self.parse_postfix()
        }
    }

    fn parse_postfix(&mut self) -> PResult<Expr> {
        let mut e = self.parse_primary()?;
        loop {
            // Continue a method chain that breaks across a line: `expr \n .m()`.
            if self.depth == 0 && self.newline_then(TokenKind::Dot) {
                self.eat_newlines();
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
                    let (fields, hi) = self.parse_field_inits()?;
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
        self.open(TokenKind::LBrace, "'{'")?;
        let mut fields = Vec::new();
        while !self.at_p(TokenKind::RBrace) {
            let (name, _) = self.ident()?;
            self.expect(TokenKind::Colon, "':'")?;
            let value = self.parse_expr()?;
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
            let params = self.parse_param_list(TokenKind::RParen)?;
            self.close(TokenKind::RParen, "')'")?;
            self.expect(TokenKind::Arrow, "'->'")?;
            self.eat_newlines();
            let body = if self.at_p(TokenKind::LBrace) {
                let b = self.parse_block()?;
                let s = b.span;
                Expr::Block(b, s)
            } else {
                self.parse_expr()?
            };
            let span = lo.merge(body.span());
            Ok(Expr::Closure(params, Box::new(body), span))
        } else {
            self.open(TokenKind::LParen, "'('")?;
            let e = self.parse_expr()?;
            self.close(TokenKind::RParen, "')'")?;
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
            let cond = self.parse_cond()?;
            let then = self.parse_block()?;
            let els = self.parse_else()?;
            let hi = els.as_ref().map(|e| e.span()).unwrap_or(then.span);
            Ok(Expr::If(Box::new(cond), then, els, lo.merge(hi)))
        }
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
            let body = self.parse_arm_body()?;
            arms.push(MatchArm {
                span: pat.span().merge(body.span()),
                pattern: pat,
                body,
            });
            self.eat(TokenKind::Comma);
        }
        let hi = self.close(TokenKind::RBrace, "'}'")?;
        Ok(Expr::Match(Box::new(scrut), arms, lo.merge(hi)))
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
        let span = self.span();
        match self.peek().clone() {
            TokenKind::Ident(name) => {
                self.bump();
                if name == "_" {
                    return Ok(Pattern::Wildcard(span));
                }
                // A qualified variant pattern `T.A { ... }` / `T.A`, possibly
                // module-qualified (`alias.T.A`): the variant name alone
                // identifies it (its owning type is resolved later against the
                // scrutinee), so every qualifier segment is consumed and the
                // last name kept.
                let mut name = name;
                while self.eat(TokenKind::Dot) {
                    name = self.ident()?.0;
                }
                if self.at_p(TokenKind::LBrace) {
                    let (fields, hi) = self.parse_field_pats()?;
                    Ok(Pattern::Record(name, fields, span.merge(hi)))
                } else {
                    Ok(Pattern::Binding(name, span))
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
                        self.bump();
                        Ok(Pattern::Literal(Box::new(Expr::Int(-v, span)), span))
                    }
                    TokenKind::Float(v) => {
                        self.bump();
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
        self.parse_type_refine(true)
    }

    /// A return type (after `->`) never grabs a `Base { .. }` refinement: the
    /// `{` there begins the function body, not a refinement. Refinements in a
    /// return position are written through a type alias instead.
    fn parse_return_type(&mut self) -> PResult<TypeExpr> {
        self.parse_type_refine(false)
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
                elems.push(self.parse_type()?);
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
                params.push(self.parse_type()?);
                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
            self.close(TokenKind::RParen, "')'")?;
            self.expect(TokenKind::Arrow, "'->'")?;
            let ret = self.parse_return_type()?;
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
                let inner = self.parse_type()?;
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
                while !self.at_p(TokenKind::RBrace) {
                    let (fname, _) = self.ident()?;
                    self.expect(TokenKind::Colon, "':'")?;
                    let fty = self.parse_type()?;
                    fields.push((fname, fty));
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
    fn parse_refine_fields(&mut self) -> PResult<(Vec<(String, TypeExpr)>, Span)> {
        self.open(TokenKind::LBrace, "'{'")?;
        self.eat_newlines();
        let mut fields = Vec::new();
        while !self.at_p(TokenKind::RBrace) {
            let (fname, _) = self.ident()?;
            self.expect(TokenKind::Colon, "':'")?;
            let fty = self.parse_type()?;
            fields.push((fname, fty));
            self.eat(TokenKind::Comma);
            self.eat_newlines();
        }
        let hi = self.close(TokenKind::RBrace, "'}'")?;
        Ok((fields, hi))
    }

    // ----- string interpolation -----

    fn lower_str(&self, parts: Vec<StrPart>, _span: Span) -> PResult<Vec<StrSeg>> {
        let mut segs = Vec::new();
        for part in parts {
            match part {
                StrPart::Lit(s) => segs.push(StrSeg::Lit(s)),
                StrPart::Interp(raw, frag_lo) => {
                    let e = parse_sub_expr(&raw, self.base + frag_lo)?;
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
fn parse_sub_expr(raw: &str, shift: usize) -> PResult<Expr> {
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
    p.eat_newlines();
    let e = p.parse_expr()?;
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
