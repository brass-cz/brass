//! Recursive-descent parser for Prepoly.
//!
//! Newlines: the lexer emits `Newline` tokens. Inside brackets (`()`, `[]`,
//! and type-literal / match braces) newlines are insignificant and skipped
//! automatically (`depth > 0`). At statement level a newline terminates a
//! statement, with two continuation allowances that cover DESIGN.md 3.2:
//!   - a binary/assign operator at end of line continues onto the next line
//!     (operators call `eat_newlines` before parsing their right operand);
//!   - a `.` at the start of the next line continues a method chain.
//!
//! Statement blocks reset to `depth == 0` so newlines separate their
//! statements even when the block is nested inside brackets (closure bodies).

use prepoly_lexer::{Span, StrPart, Token, TokenKind, lex};

use crate::ast::*;

#[derive(Clone, Debug, PartialEq)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

/// Parse one source file into a `Module`.
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
    let mut tokens = lex(src).map_err(|e| ParseError {
        message: e.message,
        span: Span::new(e.span.lo + base, e.span.hi + base),
    })?;
    for t in &mut tokens {
        t.span = Span::new(t.span.lo + base, t.span.hi + base);
    }
    let mut p = Parser::new(tokens);
    p.parse_module()
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    /// Bracket nesting depth; when > 0 newlines are skipped automatically.
    depth: usize,
    /// When true, a bare `Ident {` is NOT a type literal (used inside `if`,
    /// `while`, `for`, and `match` head expressions).
    no_struct: bool,
    /// Saved `no_struct` values for bracket scopes.
    ns_save: Vec<bool>,
}

type PResult<T> = Result<T, ParseError>;

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens,
            pos: 0,
            depth: 0,
            no_struct: false,
            ns_save: Vec::new(),
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

    fn parse_module(&mut self) -> PResult<Module> {
        let mut imports = Vec::new();
        let mut items = Vec::new();
        self.eat_newlines();
        while !self.at_p(TokenKind::Eof) {
            if self.at_p(TokenKind::Import) {
                imports.push(self.parse_import()?);
            } else {
                items.push(self.parse_top_level()?);
            }
            self.eat_newlines();
        }
        Ok(Module { imports, items })
    }

    /// `import a.b.{ Name, Name }`
    fn parse_import(&mut self) -> PResult<ImportDecl> {
        let lo = self.expect(TokenKind::Import, "import")?.span;
        let mut path = Vec::new();
        let (first, _) = self.ident()?;
        path.push(first);
        loop {
            self.expect(TokenKind::Dot, "'.'")?;
            if self.at_p(TokenKind::LBrace) {
                break;
            }
            let (seg, _) = self.ident()?;
            path.push(seg);
        }
        self.open(TokenKind::LBrace, "'{'")?;
        let mut names = Vec::new();
        while !self.at_p(TokenKind::RBrace) {
            let (n, _) = self.ident()?;
            names.push(n);
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        let hi = self.close(TokenKind::RBrace, "'}'")?;
        Ok(ImportDecl {
            path,
            names,
            span: lo.merge(hi),
        })
    }

    fn parse_top_level(&mut self) -> PResult<TopLevel> {
        match self.peek() {
            TokenKind::Type => Ok(TopLevel::Type(self.parse_type_decl()?)),
            TokenKind::Fun => Ok(TopLevel::Fun(self.parse_fun_decl()?)),
            _ => Ok(TopLevel::Stmt(self.parse_stmt()?)),
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
        } else {
            TypeBody::Sum(self.parse_variants()?)
        };
        Ok(TypeDecl {
            span: lo.merge(self.tokens[self.pos.saturating_sub(1)].span),
            name,
            interfaces,
            body,
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
                Some(self.parse_type()?)
            } else {
                None
            };
            // Interface methods declare only a signature (no block body).
            let (body, hi) = if self.at_p(TokenKind::LBrace) {
                let b = self.parse_block()?;
                let s = b.span;
                (Some(b), s)
            } else {
                (None, ret.as_ref().map(|r| r.span()).unwrap_or(lo))
            };
            Ok(Member::Method(Method {
                span: lo.merge(hi),
                name,
                params,
                ret,
                body,
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
            let (name, lo) = self.ident()?;
            let members = if self.at_p(TokenKind::LBrace) {
                self.parse_member_block()?
            } else {
                Vec::new()
            };
            variants.push(Variant {
                span: lo,
                name,
                members,
            });
            if self.at_p(TokenKind::Pipe) || self.newline_then(TokenKind::Pipe) {
                self.eat_newlines();
                self.bump(); // consume '|'
            } else {
                break;
            }
        }
        Ok(variants)
    }

    fn parse_fun_decl(&mut self) -> PResult<FunDecl> {
        let lo = self.expect(TokenKind::Fun, "'fun'")?.span;
        let (name, _) = self.ident()?;
        self.open(TokenKind::LParen, "'('")?;
        let params = self.parse_param_list(TokenKind::RParen)?;
        self.close(TokenKind::RParen, "')'")?;
        let ret = if self.eat(TokenKind::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        let body = self.parse_block()?;
        Ok(FunDecl {
            span: lo.merge(body.span),
            name,
            params,
            ret,
            body,
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
        let lo = self.expect(TokenKind::LBrace, "'{'")?.span;
        self.depth = 0;
        self.no_struct = false;
        self.eat_newlines();
        let mut stmts = Vec::new();
        while !self.at_p(TokenKind::RBrace) && !self.at_p(TokenKind::Eof) {
            stmts.push(self.parse_stmt()?);
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
        self.expect(TokenKind::Eq, "'='")?;
        self.eat_newlines();
        let value = self.parse_expr()?;
        Ok(Stmt::Let {
            span: lo.merge(value.span()),
            pat,
            ty,
            value,
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
        let (var, _) = self.ident()?;
        self.expect(TokenKind::In, "'in'")?;
        let iter = self.parse_cond()?;
        let body = self.parse_block()?;
        Ok(Stmt::For {
            span: lo.merge(body.span),
            var,
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
        self.parse_or()
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
        let mut elems = Vec::new();
        while !self.at_p(TokenKind::RBracket) {
            elems.push(self.parse_expr()?);
            if !self.eat(TokenKind::Comma) {
                break;
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
    /// assignment form is used to mutate captured state, see DESIGN.md 11.6).
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
        let mut base = self.parse_base_type()?;
        // Array suffixes: T[n] or T[].
        while self.at_p(TokenKind::LBracket) {
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
                        return Err(self
                            .error(format!("expected array length, found {}", describe(&other))));
                    }
                }
            };
            let hi = self.close(TokenKind::RBracket, "']'")?;
            base = TypeExpr::Array(Box::new(base.clone()), len, base.span().merge(hi));
        }
        // Trailing `?` (nullable) and `!` (fallible Result) suffixes, in any order
        // (`T?`, `T!`, `T[]?`, ...). Each wraps the type built so far.
        loop {
            let lo = base.span();
            if self.at_p(TokenKind::Question) {
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

    fn parse_base_type(&mut self) -> PResult<TypeExpr> {
        let span = self.span();
        if self.at_p(TokenKind::LBracket) {
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
            let ret = self.parse_type()?;
            let hi = ret.span();
            Ok(TypeExpr::Fun(params, Box::new(ret), span.merge(hi)))
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
            Ok(TypeExpr::Named(name, span))
        }
    }

    // ----- string interpolation -----

    fn lower_str(&self, parts: Vec<StrPart>, span: Span) -> PResult<Vec<StrSeg>> {
        let mut segs = Vec::new();
        for part in parts {
            match part {
                StrPart::Lit(s) => segs.push(StrSeg::Lit(s)),
                StrPart::Interp(raw) => {
                    let e = parse_sub_expr(&raw, span)?;
                    segs.push(StrSeg::Expr(Box::new(e)));
                }
            }
        }
        Ok(segs)
    }
}

/// Parse the raw source of an interpolation `{...}` as a single expression.
fn parse_sub_expr(raw: &str, _outer: Span) -> PResult<Expr> {
    let tokens = lex(raw).map_err(|e| ParseError {
        message: format!("in string interpolation: {}", e.message),
        span: e.span,
    })?;
    let mut p = Parser::new(tokens);
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
    match k {
        TokenKind::Eof => "end of input".into(),
        TokenKind::Newline => "newline".into(),
        TokenKind::Ident(s) => format!("`{s}`"),
        TokenKind::Int(v) => format!("`{v}`"),
        TokenKind::Float(v) => format!("`{v}`"),
        TokenKind::Str(_) => "string literal".into(),
        other => format!("{other:?}"),
    }
}
