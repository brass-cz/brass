//! Expression, pattern, and type rendering.
//!
//! Every expression first tries a one-line ("flat") rendering; when that
//! overflows [`MAX_WIDTH`](crate::MAX_WIDTH) a per-construct breaking rule
//! applies:
//!   - a method chain (two or more `.m(...)` calls) breaks every chain
//!     segment onto its own indented line;
//!   - an array literal breaks one element per line;
//!   - a call breaks after the `(`, one argument per line;
//!   - a binary chain breaks after each operator (the parser continues a
//!     statement whose line ends in an operator);
//!   - record/variant literals break one field per line.
//!
//! `if`/`match`/block expressions never render flat: their bodies always sit
//! on indented lines of their own.
//!
//! The AST records no grouping parentheses, so they are re-inserted from
//! operator precedence. The `ns` ("no struct") flag mirrors the parser's rule
//! that a bare `Name { ... }` literal in an `if`/`while`/`for`/`match` head
//! must be parenthesized to not be read as the statement's block.

use brass_parser::ast::*;
use brass_parser::{Span, TokenKind, lex};

use crate::printer::Printer;

/// Binding strength used to re-insert grouping parentheses: an operand whose
/// own strength is below its context is printed in parentheses.
fn prec(e: &Expr) -> u8 {
    match e {
        // A closure's body extends as far as possible, so a closure used as an
        // operand always needs parentheses.
        Expr::Closure(..) => 0,
        Expr::Binary(op, ..) => op.precedence(),
        Expr::Unary(..) => PREC_UNARY,
        Expr::Call(..) | Expr::Field(..) | Expr::Index(..) | Expr::ErrorProp(..) => PREC_POSTFIX,
        _ => PREC_PRIMARY,
    }
}

const PREC_UNARY: u8 = 10;
const PREC_POSTFIX: u8 = 11;
const PREC_PRIMARY: u8 = 12;

/// One postfix link of a call/field/index chain, outermost decomposition
/// reversed into source order.
enum Link<'e> {
    Field(&'e str),
    /// Call arguments plus the span of the whole call expression (its `hi`
    /// ends just past the `)`, used as a comment anchor when breaking).
    Call(&'e [Arg], Span),
    Index(&'e Expr),
    Bang,
}

fn split_chain<'e>(mut e: &'e Expr) -> (&'e Expr, Vec<Link<'e>>) {
    let mut links = Vec::new();
    loop {
        match e {
            Expr::Call(f, args, span) => {
                links.push(Link::Call(args, *span));
                e = f;
            }
            Expr::Field(b, n, _) => {
                links.push(Link::Field(n));
                e = b;
            }
            Expr::Index(b, i, _) => {
                links.push(Link::Index(i));
                e = b;
            }
            Expr::ErrorProp(b, _) => {
                links.push(Link::Bang);
                e = b;
            }
            _ => break,
        }
    }
    links.reverse();
    (e, links)
}

impl<'a> Printer<'a> {
    // ----- entry points -----

    /// Emit `head` + expression + `tail` as one line when it fits, otherwise
    /// via the expression's breaking rule. `ns` marks an `if`/`while`/`for`/
    /// `match` head position (see module docs).
    pub(crate) fn expr_lines(&mut self, head: String, e: &Expr, tail: &str, ns: bool) {
        if let Some(flat) = self.flat_expr(e, ns) {
            let full = format!("{head}{flat}{tail}");
            if self.fits(&full) {
                self.line(&full);
                return;
            }
        }
        self.break_expr(head, e, tail, ns);
    }

    /// The one-line rendering, or `None` for constructs that always break
    /// (`if`, `match`, blocks, and anything containing one).
    pub(crate) fn flat_expr(&self, e: &Expr, ns: bool) -> Option<String> {
        Some(match e {
            Expr::Int(v, s) => self.int_text(*v, *s),
            Expr::Float(v, s) => self.float_text(*v, *s),
            // String literals (with their interpolations) print verbatim.
            Expr::Str(_, s) => self.slice(*s).to_string(),
            Expr::Bool(b, _) => b.to_string(),
            Expr::Null(_) => "null".to_string(),
            Expr::Ident(n, _) => n.clone(),
            Expr::SelfExpr(_) => "self".to_string(),
            Expr::Unary(op, inner, _) => {
                format!("{}{}", op.symbol(), self.flat_prec(inner, PREC_UNARY, ns)?)
            }
            Expr::Binary(op, l, r, _) => {
                let p = op.precedence();
                // Left-associative: an equal-precedence right operand keeps
                // its parentheses.
                format!(
                    "{} {} {}",
                    self.flat_prec(l, p, ns)?,
                    op.symbol(),
                    self.flat_prec(r, p + 1, ns)?
                )
            }
            Expr::Call(f, args, _) => {
                let mut s = self.flat_prec(f, PREC_POSTFIX, ns)?;
                s.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&self.flat_expr(&a.expr, false)?);
                }
                s.push(')');
                s
            }
            Expr::Field(b, n, _) => format!("{}.{}", self.flat_prec(b, PREC_POSTFIX, ns)?, n),
            Expr::Index(b, i, _) => format!(
                "{}[{}]",
                self.flat_prec(b, PREC_POSTFIX, ns)?,
                self.flat_expr(i, false)?
            ),
            Expr::ErrorProp(b, _) => format!("{}!", self.flat_prec(b, PREC_POSTFIX, ns)?),
            Expr::Closure(params, body, _) => {
                let params: Vec<String> = params.iter().map(|p| self.param_flat(p)).collect();
                // The parser's `no_struct` head flag stays active inside a
                // closure body written in a statement head, so `ns` carries on.
                format!("({}) -> {}", params.join(", "), self.flat_expr(body, ns)?)
            }
            Expr::Array(elems, _) => {
                let mut parts = Vec::with_capacity(elems.len());
                for el in elems {
                    parts.push(self.flat_expr(el, false)?);
                }
                format!("[{}]", parts.join(", "))
            }
            Expr::Range(a, b, _) => format!(
                "[{}..{}]",
                self.flat_expr(a, false)?,
                self.flat_expr(b, false)?
            ),
            Expr::TypeLit(name, fields, _) => self.type_lit_flat(name, fields, ns)?,
            Expr::VariantLit(t, v, fields, _) => {
                self.type_lit_flat(&format!("{t}.{v}"), fields, ns)?
            }
            Expr::TypeTest(subject, te, _) => {
                format!("{}: {}", self.flat_expr(subject, ns)?, self.type_flat(te))
            }
            Expr::If(..) | Expr::IfLet(..) | Expr::Match(..) | Expr::Block(..) => return None,
        })
    }

    fn flat_prec(&self, e: &Expr, min: u8, ns: bool) -> Option<String> {
        if prec(e) < min {
            Some(format!("({})", self.flat_expr(e, false)?))
        } else {
            self.flat_expr(e, ns)
        }
    }

    /// Flat rendering with a last-resort fallback to the original source text
    /// (used where a rendering must not fail, e.g. an assignment target).
    pub(crate) fn flat_or_src(&self, e: &Expr, ns: bool) -> String {
        self.flat_expr(e, ns)
            .unwrap_or_else(|| self.slice(e.span()).to_string())
    }

    fn type_lit_flat(&self, name: &str, fields: &[(String, Expr)], ns: bool) -> Option<String> {
        let inner = if fields.is_empty() {
            "{ }".to_string()
        } else {
            let mut parts = Vec::with_capacity(fields.len());
            for (n, v) in fields {
                if field_shorthand(n, v) {
                    parts.push(n.clone());
                } else {
                    parts.push(format!("{n}: {}", self.flat_expr(v, false)?));
                }
            }
            format!("{{ {} }}", parts.join(", "))
        };
        let body = if name.is_empty() {
            inner
        } else {
            format!("{name} {inner}")
        };
        Some(if ns { format!("({body})") } else { body })
    }

    // ----- literals from source -----

    /// The literal's original spelling (radix prefixes, `_` separators,
    /// exponents survive), validated by re-lexing; falls back to the value.
    fn int_text(&self, v: i64, span: Span) -> String {
        let slice = self.slice(span);
        if let Ok(tokens) = brass_parser::lex(slice)
            && let [tok, _eof] = &tokens[..]
            && matches!(&tok.kind, brass_parser::TokenKind::Int(v2) if *v2 == v)
        {
            return slice.to_string();
        }
        v.to_string()
    }

    fn float_text(&self, v: f64, span: Span) -> String {
        let slice = self.slice(span);
        if let Ok(tokens) = brass_parser::lex(slice)
            && let [tok, _eof] = &tokens[..]
            && matches!(&tok.kind, brass_parser::TokenKind::Float(v2) if v2.to_bits() == v.to_bits())
        {
            return slice.to_string();
        }
        if v.fract() == 0.0 && v.is_finite() {
            format!("{v:.1}")
        } else {
            format!("{v}")
        }
    }

    // ----- breaking -----

    fn break_expr(&mut self, head: String, e: &Expr, tail: &str, ns: bool) {
        match e {
            Expr::If(..) | Expr::IfLet(..) => self.emit_if(head, e, tail),
            Expr::Match(scrut, arms, span) => self.emit_match(head, scrut, arms, *span, tail),
            Expr::Block(b, _) => {
                self.line(&format!("{head}{{"));
                self.block_body(b);
                self.line(&format!("}}{tail}"));
            }
            Expr::Closure(params, body, _) => {
                let params: Vec<String> = params.iter().map(|p| self.param_flat(p)).collect();
                let params = format!("({})", params.join(", "));
                match body.as_ref() {
                    Expr::Block(b, _) => {
                        self.line(&format!("{head}{params} -> {{"));
                        self.block_body(b);
                        self.line(&format!("}}{tail}"));
                    }
                    body => {
                        // The parser skips newlines after a closure's `->`.
                        self.line(&format!("{head}{params} ->"));
                        self.level += 1;
                        self.expr_lines(String::new(), body, tail, false);
                        self.level -= 1;
                    }
                }
            }
            Expr::Call(..) | Expr::Field(..) | Expr::Index(..) | Expr::ErrorProp(..) => {
                self.break_postfix(head, e, tail, ns)
            }
            Expr::Array(elems, span) => {
                self.line(&format!("{head}["));
                self.level += 1;
                // Anchor at the first element so the text before the `[` does
                // not count as a blank line in front of it.
                if let Some(first) = elems.first() {
                    self.finish(first.span().lo);
                }
                for el in elems {
                    self.start(el.span().lo);
                    self.expr_lines(String::new(), el, ",", false);
                    self.finish(el.span().hi);
                }
                self.flush_comments(span.hi);
                self.level -= 1;
                self.line(&format!("]{tail}"));
            }
            Expr::TypeLit(name, fields, span) => {
                self.break_type_lit(head, name, fields, *span, tail, ns)
            }
            Expr::VariantLit(t, v, fields, span) => {
                self.break_type_lit(head, &format!("{t}.{v}"), fields, *span, tail, ns)
            }
            Expr::Binary(..) => self.break_binary(head, e, tail, ns),
            Expr::Unary(op, inner, _) => {
                let h = format!("{head}{}", op.symbol());
                self.operand_lines(h, inner, PREC_UNARY, tail, ns);
            }
            // Atoms have no breaking rule: emit the line over-width.
            _ => {
                let flat = self.flat_or_src(e, ns);
                self.line(&format!("{head}{flat}{tail}"));
            }
        }
    }

    /// Emit an operand, re-inserting its grouping parentheses when its own
    /// binding strength is below the context's.
    fn operand_lines(&mut self, head: String, e: &Expr, min_prec: u8, tail: &str, ns: bool) {
        if prec(e) < min_prec {
            self.expr_lines(format!("{head}("), e, &format!("){tail}"), false);
        } else {
            self.expr_lines(head, e, tail, ns);
        }
    }

    fn break_binary(&mut self, head: String, e: &Expr, tail: &str, ns: bool) {
        let Expr::Binary(op, ..) = e else {
            unreachable!()
        };
        let p = op.precedence();
        let mut operands = Vec::new();
        let mut ops = Vec::new();
        collect_operands(e, p, &mut operands, &mut ops);
        // First operand keeps the head; the rest continue one level deeper,
        // each line ending in its operator so the parser reads on.
        for (i, operand) in operands.iter().enumerate() {
            let suffix = match ops.get(i) {
                Some(op) => format!(" {}", op.symbol()),
                None => tail.to_string(),
            };
            let min = if i == 0 { p } else { p + 1 };
            let h = if i == 0 { head.clone() } else { String::new() };
            if i == 1 {
                self.level += 1;
            }
            self.operand_lines(h, operand, min, &suffix, ns);
        }
        if operands.len() > 1 {
            self.level -= 1;
        }
    }

    fn break_postfix(&mut self, head: String, e: &Expr, tail: &str, ns: bool) {
        let (base, links) = split_chain(e);
        let methods = links
            .windows(2)
            .filter(|w| matches!(w, [Link::Field(_), Link::Call(..)]))
            .count();
        if methods >= 2 {
            self.break_chain(head, base, &links, tail, ns);
            return;
        }
        // Break the call after its `(`, one argument per line. Prefer the
        // first call with an argument that cannot render flat (everything
        // before it then still fits on the opening line), else the outermost
        // call that has arguments at all.
        let k = links
            .iter()
            .position(|l| matches!(l, Link::Call(args, _) if !self.args_flat(args)))
            .or_else(|| {
                links
                    .iter()
                    .rposition(|l| matches!(l, Link::Call(args, _) if !args.is_empty()))
            });
        let Some(k) = k else {
            // No arguments to break at; emit over-width.
            let flat = self.flat_or_src(e, ns);
            self.line(&format!("{head}{flat}{tail}"));
            return;
        };
        let Link::Call(args, call_span) = &links[k] else {
            unreachable!()
        };
        let callee = format!(
            "{}{}",
            self.postfix_base_text(base, ns),
            self.flat_links(&links[..k])
        );
        let suffix = self.flat_links(&links[k + 1..]);
        self.line(&format!("{head}{callee}("));
        self.level += 1;
        self.arg_lines(args, *call_span);
        self.level -= 1;
        self.line(&format!("){suffix}{tail}"));
    }

    /// Emit a broken argument list, one argument per line with a trailing
    /// comma, running the comment/blank-line bookkeeping per argument.
    fn arg_lines(&mut self, args: &[Arg], call_span: Span) {
        if let Some(first) = args.first() {
            self.finish(first.expr.span().lo);
        }
        for a in args {
            self.start(a.expr.span().lo);
            self.expr_lines(String::new(), &a.expr, ",", false);
            self.finish(a.expr.span().hi);
        }
        self.flush_comments(call_span.hi);
    }

    /// Break a method chain: the base stays on the head line, then every
    /// `.segment` (a field run ending in its call and trailing `[..]`/`!`)
    /// gets an indented line of its own.
    fn break_chain(&mut self, head: String, base: &Expr, links: &[Link], tail: &str, ns: bool) {
        let first_field = links
            .iter()
            .position(|l| matches!(l, Link::Field(_)))
            .unwrap_or(links.len());
        let base_text = format!(
            "{}{}",
            self.postfix_base_text(base, ns),
            self.flat_links(&links[..first_field])
        );
        self.line(&format!("{head}{base_text}"));
        self.level += 1;
        // Segment boundaries: each `.field` starts a new segment.
        let mut starts = Vec::new();
        let mut i = first_field;
        while i < links.len() {
            starts.push(i);
            i += 1;
            while i < links.len() && !matches!(links[i], Link::Field(_)) {
                i += 1;
            }
        }
        for (n, &s) in starts.iter().enumerate() {
            let e = starts.get(n + 1).copied().unwrap_or(links.len());
            let seg = &links[s..e];
            let gtail = if n + 1 == starts.len() { tail } else { "" };
            let text = format!("{}{gtail}", self.flat_links(seg));
            let all_flat = seg.iter().all(|l| match l {
                Link::Call(args, _) => self.args_flat(args),
                _ => true,
            });
            if self.fits(&text) && all_flat {
                self.line(&text);
                continue;
            }
            // The segment alone overflows: break its call's arguments.
            let Some(ci) = seg
                .iter()
                .position(|l| matches!(l, Link::Call(args, _) if !args.is_empty()))
            else {
                self.line(&text);
                continue;
            };
            let Link::Call(args, call_span) = &seg[ci] else {
                unreachable!()
            };
            let prefix = self.flat_links(&seg[..ci]);
            let suffix = self.flat_links(&seg[ci + 1..]);
            self.line(&format!("{prefix}("));
            self.level += 1;
            self.arg_lines(args, *call_span);
            self.level -= 1;
            self.line(&format!("){suffix}{gtail}"));
        }
        self.level -= 1;
    }

    fn postfix_base_text(&self, base: &Expr, ns: bool) -> String {
        if prec(base) < PREC_POSTFIX {
            format!("({})", self.flat_or_src(base, false))
        } else {
            self.flat_or_src(base, ns)
        }
    }

    fn args_flat(&self, args: &[Arg]) -> bool {
        args.iter()
            .all(|a| self.flat_expr(&a.expr, false).is_some())
    }

    /// Flat text of a run of postfix links (infallible: call arguments fall
    /// back to their source text).
    fn flat_links(&self, links: &[Link]) -> String {
        let mut s = String::new();
        for l in links {
            match l {
                Link::Field(n) => {
                    s.push('.');
                    s.push_str(n);
                }
                Link::Call(args, _) => {
                    s.push('(');
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&self.flat_or_src(&a.expr, false));
                    }
                    s.push(')');
                }
                Link::Index(i) => {
                    s.push('[');
                    s.push_str(&self.flat_or_src(i, false));
                    s.push(']');
                }
                Link::Bang => s.push('!'),
            }
        }
        s
    }

    fn break_type_lit(
        &mut self,
        head: String,
        name: &str,
        fields: &[(String, Expr)],
        span: Span,
        tail: &str,
        ns: bool,
    ) {
        // In a statement head the literal must sit in parentheses (module docs).
        let (head, tail) = if ns {
            (format!("{head}("), format!("){tail}"))
        } else {
            (head, tail.to_string())
        };
        let opener = if name.is_empty() {
            format!("{head}{{")
        } else {
            format!("{head}{name} {{")
        };
        self.line(&opener);
        self.level += 1;
        if let Some((_, first)) = fields.first() {
            self.finish(first.span().lo);
        }
        for (fname, v) in fields {
            self.start(v.span().lo);
            // The shorthand head is empty: the value IS the same-named
            // identifier, so emitting it alone prints `field,`.
            let head = if field_shorthand(fname, v) {
                String::new()
            } else {
                format!("{fname}: ")
            };
            self.expr_lines(head, v, ",", false);
            self.finish(v.span().hi);
        }
        self.flush_comments(span.hi);
        self.level -= 1;
        self.line(&format!("}}{tail}"));
    }

    // ----- if / match -----

    /// `if`/`if let` always renders in block form. `head` precedes the `if`
    /// keyword (e.g. `let x = ` or `} else `); `tail` follows the final `}`.
    fn emit_if(&mut self, head: String, e: &Expr, tail: &str) {
        match e {
            Expr::If(cond, then, els, _) => {
                self.expr_lines(format!("{head}if "), cond, " {", true);
                self.block_body(then);
                self.emit_else(els.as_deref(), tail);
            }
            Expr::IfLet(pat, scrut, then, els, _) => {
                let h = format!("{head}if let {} = ", self.pattern_flat(pat));
                self.expr_lines(h, scrut, " {", true);
                self.block_body(then);
                self.emit_else(els.as_deref(), tail);
            }
            _ => unreachable!(),
        }
    }

    fn emit_else(&mut self, els: Option<&Expr>, tail: &str) {
        match els {
            None => self.line(&format!("}}{tail}")),
            Some(e @ (Expr::If(..) | Expr::IfLet(..))) => {
                self.emit_if("} else ".to_string(), e, tail)
            }
            Some(Expr::Block(b, _)) => {
                self.line("} else {");
                self.block_body(b);
                self.line(&format!("}}{tail}"));
            }
            // The parser only produces a block or a chained if here; keep a
            // safe fallback for hand-built ASTs.
            Some(other) => {
                self.line("} else {");
                self.level += 1;
                self.expr_lines(String::new(), other, "", false);
                self.level -= 1;
                self.line(&format!("}}{tail}"));
            }
        }
    }

    fn emit_match(
        &mut self,
        head: String,
        scrut: &Expr,
        arms: &[MatchArm],
        span: Span,
        tail: &str,
    ) {
        self.expr_lines(format!("{head}match "), scrut, " {", true);
        self.finish(scrut.span().hi);
        self.level += 1;
        for arm in arms {
            self.start(arm.span.lo);
            self.match_arm(arm);
            self.finish(arm.span.hi);
        }
        self.flush_comments(span.hi);
        self.level -= 1;
        self.line(&format!("}}{tail}"));
    }

    fn match_arm(&mut self, arm: &MatchArm) {
        let pat = self.pattern_flat(&arm.pattern);
        match &arm.body {
            Expr::Block(b, bspan) => {
                // `pat => x += 1`: the parser wraps a bare assignment arm in a
                // block sharing the assignment's span; print it back inline.
                if let [
                    Stmt::Assign {
                        target,
                        op,
                        value,
                        span,
                    },
                ] = &b.stmts[..]
                    && span == bspan
                {
                    let head = format!(
                        "{pat} => {} {} ",
                        self.flat_or_src(target, false),
                        op.symbol()
                    );
                    self.expr_lines(head, value, ",", false);
                } else {
                    self.line(&format!("{pat} => {{"));
                    self.block_body(b);
                    self.line("},");
                }
            }
            body => self.expr_lines(format!("{pat} => "), body, ",", false),
        }
    }

    // ----- patterns -----

    pub(crate) fn pattern_flat(&self, p: &Pattern) -> String {
        match p {
            Pattern::Wildcard(_) => "_".to_string(),
            Pattern::Binding(n, _) => n.clone(),
            Pattern::Literal(e, _) => self.flat_or_src(e, false),
            Pattern::Record(name, fields, span) => {
                let mut parts: Vec<String> = fields
                    .iter()
                    .map(|f| match &f.pat {
                        None => f.name.clone(),
                        Some(p) => format!("{}: {}", f.name, self.pattern_flat(p)),
                    })
                    .collect();
                if self.has_rest(*span) {
                    parts.push("..".to_string());
                }
                if parts.is_empty() {
                    format!("{name} {{ }}")
                } else {
                    format!("{name} {{ {} }}", parts.join(", "))
                }
            }
            Pattern::Array(pats, _) => {
                let parts: Vec<String> = pats.iter().map(|p| self.pattern_flat(p)).collect();
                format!("[{}]", parts.join(", "))
            }
        }
    }

    /// The AST does not record a record pattern's trailing `..`; recover it
    /// from the source: the last tokens before the pattern's closing brace.
    fn has_rest(&self, span: Span) -> bool {
        let Ok(tokens) = lex(self.slice(span)) else {
            return false;
        };
        let mut significant = tokens
            .iter()
            .rev()
            .filter(|token| !matches!(token.kind, TokenKind::Newline | TokenKind::Eof));
        matches!(
            significant.next().map(|token| &token.kind),
            Some(TokenKind::RBrace)
        ) && matches!(
            significant.next().map(|token| &token.kind),
            Some(TokenKind::DotDot)
        )
    }

    // ----- types -----

    pub(crate) fn type_flat(&self, t: &TypeExpr) -> String {
        match t {
            TypeExpr::Named(n, _) => n.clone(),
            TypeExpr::Array(inner, len, _) => {
                let len = match len {
                    Some(n) => n.to_string(),
                    None => String::new(),
                };
                format!("{}[{len}]", self.type_flat(inner))
            }
            TypeExpr::Fun(params, ret, _) => {
                let params: Vec<String> = params.iter().map(|p| self.type_flat(p)).collect();
                format!("({}) -> {}", params.join(", "), self.type_flat(ret))
            }
            TypeExpr::Nullable(inner, _) => format!("{}?", self.type_flat(inner)),
            TypeExpr::Fallible(inner, _) => format!("{}!", self.type_flat(inner)),
            TypeExpr::Tuple(elems, _) => {
                let elems: Vec<String> = elems.iter().map(|e| self.type_flat(e)).collect();
                format!("[{}]", elems.join(", "))
            }
            TypeExpr::Anonymous(fields, _) => {
                format!("anonymous {{ {} }}", self.type_fields_flat(fields))
            }
            TypeExpr::Mut(inner, _) => format!("mut({})", self.type_flat(inner)),
            TypeExpr::Ref(inner, _) => format!("ref({})", self.type_flat(inner)),
            TypeExpr::TypeOf(e, _) => format!("typeof({})", self.flat_or_src(e, false)),
            TypeExpr::TypeSlot(_) => "type".to_string(),
            TypeExpr::SelfField(f, _) => format!("Self.{f}"),
            TypeExpr::Refine(base, fields, _) => {
                if fields.is_empty() {
                    format!("{} {{ }}", self.type_flat(base))
                } else {
                    format!(
                        "{} {{ {} }}",
                        self.type_flat(base),
                        self.type_fields_flat(fields)
                    )
                }
            }
        }
    }

    fn type_fields_flat(&self, fields: &[(String, TypeExpr)]) -> String {
        let parts: Vec<String> = fields
            .iter()
            .map(|(n, t)| format!("{n}: {}", self.type_flat(t)))
            .collect();
        parts.join(", ")
    }

    /// Emit a type annotation line, breaking a refinement or anonymous record
    /// one field per line when the flat form overflows. Other type forms have
    /// no breaking rule and print over-width.
    pub(crate) fn type_lines(&mut self, head: String, ty: &TypeExpr, tail: &str) {
        let flat = format!("{head}{}{tail}", self.type_flat(ty));
        if self.fits(&flat) {
            self.line(&flat);
            return;
        }
        let (opener, fields) = match ty {
            TypeExpr::Refine(base, fields, _) if !fields.is_empty() => {
                (format!("{head}{} {{", self.type_flat(base)), fields)
            }
            TypeExpr::Anonymous(fields, _) if !fields.is_empty() => {
                (format!("{head}anonymous {{"), fields)
            }
            _ => {
                self.line(&flat);
                return;
            }
        };
        self.line(&opener);
        self.level += 1;
        for (n, t) in fields {
            self.type_lines(format!("{n}: "), t, ",");
        }
        self.level -= 1;
        self.line(&format!("}}{tail}"));
    }
}

fn collect_operands<'e>(e: &'e Expr, p: u8, operands: &mut Vec<&'e Expr>, ops: &mut Vec<BinOp>) {
    match e {
        // Only the left spine flattens: a same-precedence right operand came
        // from explicit parentheses and keeps them.
        Expr::Binary(op, l, r, _) if op.precedence() == p => {
            collect_operands(l, p, operands, ops);
            ops.push(*op);
            operands.push(r);
        }
        _ => operands.push(e),
    }
}

/// Whether a literal field renders in the shorthand form `{ field }`: its
/// value is the same-named identifier. The parser desugars the shorthand to
/// exactly this shape, and a written `field: field` normalizes to it -- the
/// two are indistinguishable in the AST and mean the same read.
fn field_shorthand(name: &str, v: &Expr) -> bool {
    matches!(v, Expr::Ident(n, _) if n == name)
}
