//! The printing engine: declarations, statements, and the line/comment
//! bookkeeping. Expression, pattern, and type rendering live in `expr`.
//!
//! Output is built line by line. Every element (declaration, statement, type
//! member, match arm, broken-out argument) is emitted through the same
//! `start`/`finish` bookkeeping: `start` flushes the comments that precede the
//! element and re-inserts one blank line where the source had any, and
//! `finish` advances the cursor used for those decisions. A comment that sits
//! on the same source line as the previously emitted element is re-attached to
//! the end of that output line.

use prepoly_parser::Span;
use prepoly_parser::ast::*;

use crate::comments::{self, Comment};

/// Target maximum line width, in characters. Lines that no breaking rule
/// applies to (single atoms, long signatures inside type bodies) may exceed it.
pub const MAX_WIDTH: usize = 80;
/// Spaces per indentation level.
pub const INDENT: usize = 4;

/// Print a parsed module back to formatted source. `src` must be the exact
/// text `module` was parsed from: literals and comments are re-read from it.
pub(crate) fn print_module(src: &str, module: &Module) -> String {
    let mut p = Printer::new(src);
    p.module(module);
    p.out
}

pub(crate) struct Printer<'a> {
    pub(crate) src: &'a str,
    comments: Vec<Comment>,
    next_comment: usize,
    pub(crate) out: String,
    pub(crate) level: usize,
    /// Byte offset just past the last emitted source element; drives blank-line
    /// collapsing and same-line comment attachment.
    last_end: usize,
    /// False until the first line is emitted (suppresses a leading blank line).
    started: bool,
}

impl<'a> Printer<'a> {
    fn new(src: &'a str) -> Self {
        Printer {
            src,
            comments: comments::extract(src),
            next_comment: 0,
            out: String::new(),
            level: 0,
            last_end: 0,
            started: false,
        }
    }

    // ----- low-level emission -----

    /// Emit one line at the current indentation.
    pub(crate) fn line(&mut self, s: &str) {
        for _ in 0..self.level * INDENT {
            self.out.push(' ');
        }
        self.out.push_str(s.trim_end());
        self.out.push('\n');
        self.started = true;
    }

    /// Would `s` fit on one line at the current indentation?
    pub(crate) fn fits(&self, s: &str) -> bool {
        self.level * INDENT + s.chars().count() <= MAX_WIDTH
    }

    pub(crate) fn slice(&self, span: Span) -> &str {
        self.src.get(span.lo..span.hi).unwrap_or("")
    }

    // ----- comments and blank lines -----

    /// Begin an element whose source starts at `lo`: emit the comments that
    /// precede it, then a blank line if the source had one.
    pub(crate) fn start(&mut self, lo: usize) {
        self.flush_comments(lo);
        self.gap(lo);
    }

    /// Record that the element ending at source offset `hi` has been emitted.
    /// `max` keeps a hoisted comment (one that sat inside the element's span)
    /// from moving the cursor backwards.
    pub(crate) fn finish(&mut self, hi: usize) {
        self.last_end = self.last_end.max(hi);
    }

    /// Collapse the source's blank lines before `lo` into at most one.
    fn gap(&mut self, lo: usize) {
        if !self.started || lo <= self.last_end {
            return;
        }
        let between = self.src.get(self.last_end..lo).unwrap_or("");
        if between.matches('\n').count() >= 2 {
            self.out.push('\n');
        }
    }

    /// Emit every not-yet-emitted comment that starts before `before`.
    pub(crate) fn flush_comments(&mut self, before: usize) {
        while self.next_comment < self.comments.len() {
            let c = self.comments[self.next_comment];
            if c.span.lo >= before {
                break;
            }
            self.next_comment += 1;
            self.emit_comment(c);
        }
    }

    fn emit_comment(&mut self, c: Comment) {
        let text = &self.src[c.span.lo..c.span.hi];
        // A comment on the same source line as the previous element re-attaches
        // to the end of the line just emitted.
        let attaches = self.started
            && c.span.lo >= self.last_end
            && !self.src[self.last_end..c.span.lo].contains('\n')
            && !text.contains('\n')
            && self.out.ends_with('\n')
            && !self.out.ends_with("\n\n");
        if attaches {
            self.out.pop();
            self.out.push(' ');
            self.out.push_str(text.trim_end());
            self.out.push('\n');
        } else {
            self.gap(c.span.lo);
            let mut lines = text.split('\n');
            if let Some(first) = lines.next() {
                self.line(first.trim_end());
            }
            // Continuation lines of a block comment keep their original layout
            // (they may carry deliberate alignment).
            for l in lines {
                self.out.push_str(l.trim_end());
                self.out.push('\n');
            }
        }
        self.finish(c.span.hi);
    }

    // ----- module -----

    fn module(&mut self, m: &Module) {
        enum El<'m> {
            Import(&'m ImportDecl),
            Item(&'m TopLevel),
        }
        // The AST separates imports from items but the source may interleave
        // them; emit in source order.
        let mut els: Vec<(Span, El)> = Vec::new();
        for d in &m.imports {
            els.push((d.span, El::Import(d)));
        }
        for t in &m.items {
            let span = match t {
                TopLevel::Type(d) => d.span,
                TopLevel::Fun(f) => f.span,
                TopLevel::Stmt(s) => s.span(),
            };
            els.push((span, El::Item(t)));
        }
        els.sort_by_key(|(span, _)| span.lo);
        for (span, el) in els {
            self.start(span.lo);
            match el {
                El::Import(d) => self.import_decl(d),
                El::Item(TopLevel::Type(d)) => self.type_decl(d),
                El::Item(TopLevel::Fun(f)) => self.fun_decl(f),
                El::Item(TopLevel::Stmt(s)) => self.stmt(s),
            }
            self.finish(span.hi);
        }
        self.flush_comments(usize::MAX);
    }

    // ----- imports -----

    fn import_decl(&mut self, d: &ImportDecl) {
        let path = d.path.join(".");
        if d.bare {
            let mut s = format!("import {path}");
            // Only a source-written rename is printed; a loader-derived alias
            // never reaches a freshly parsed module.
            if d.explicit_alias
                && let Some(a) = &d.alias
            {
                s.push_str(&format!(" as {a}"));
            }
            self.line(&s);
            return;
        }
        let names: Vec<String> = d.names.iter().map(imported_name).collect();
        let flat = if names.is_empty() {
            format!("import {path}.{{}}")
        } else {
            format!("import {path}.{{ {} }}", names.join(", "))
        };
        if self.fits(&flat) || names.is_empty() {
            self.line(&flat);
            return;
        }
        self.line(&format!("import {path}.{{"));
        self.level += 1;
        // Anchor at the first name so text before the `{` does not count as a
        // blank line in front of it.
        if let Some(first) = d.names.first() {
            self.finish(first.span.lo);
        }
        for n in &d.names {
            self.start(n.span.lo);
            self.line(&format!("{},", imported_name(n)));
            self.finish(n.span.hi);
        }
        self.level -= 1;
        self.line("}");
    }

    // ----- type declarations -----

    fn type_decl(&mut self, t: &TypeDecl) {
        let mut head = format!("type {}", t.name);
        if !t.interfaces.is_empty() {
            head.push_str(&format!(": {}", t.interfaces.join(", ")));
        }
        head.push_str(" =");
        match &t.body {
            TypeBody::Record(members) => {
                self.line(&format!("{head} {{"));
                // Anchor same-line comment attachment just past the opening
                // brace (name and interfaces cannot contain one).
                if let Some(brace) = self.src.get(t.span.lo..t.span.hi).and_then(|s| s.find('{')) {
                    self.finish(t.span.lo + brace + 1);
                }
                self.level += 1;
                for m in members {
                    let (lo, hi) = member_span(m);
                    self.start(lo);
                    self.member(m);
                    self.finish(hi);
                }
                self.flush_comments(t.span.hi);
                self.level -= 1;
                self.line("}");
            }
            TypeBody::Sum(variants) => self.sum_body(&head, variants),
            TypeBody::Alias(ty) => self.type_lines(format!("{head} "), ty, ""),
        }
    }

    fn sum_body(&mut self, head: &str, variants: &[Variant]) {
        let flats: Vec<String> = variants.iter().map(|v| self.variant_flat(v)).collect();
        // Inline when it fits. The leading `|` is kept in every inline form:
        // without it, `type X = A` re-parses as an alias, and `type X = A {
        // f } | ..` re-parses as a refinement whose braces then fail.
        let inline = format!("{head} | {}", flats.join(" | "));
        if self.fits(&inline) {
            self.line(&inline);
            return;
        }
        self.line(head);
        self.level += 1;
        if let Some(first) = variants.first() {
            self.finish(first.span.lo);
        }
        for (v, flat) in variants.iter().zip(&flats) {
            self.start(v.span.lo);
            let one = format!("| {flat}");
            if self.fits(&one) || v.members.is_empty() {
                self.line(&one);
            } else {
                self.line(&format!("| {} {{", v.name));
                self.level += 1;
                for m in &v.members {
                    let (lo, hi) = member_span(m);
                    self.start(lo);
                    self.member(m);
                    self.finish(hi);
                }
                self.level -= 1;
                self.line("}");
            }
            self.finish(v.span.hi);
        }
        self.level -= 1;
    }

    fn variant_flat(&self, v: &Variant) -> String {
        if v.members.is_empty() {
            return v.name.clone();
        }
        let members: Vec<String> = v.members.iter().map(|m| self.member_flat(m)).collect();
        format!("{} {{ {} }}", v.name, members.join(", "))
    }

    fn member(&mut self, m: &Member) {
        match m {
            // A field's type gets the refinement/anonymous breaking rules; a
            // method signature is always one line.
            Member::Field(f) => match &f.ty {
                Some(ty) => self.type_lines(format!("{}: ", f.name), ty, ""),
                None => self.line(&f.name.clone()),
            },
            Member::Method(_) => {
                let s = self.member_flat(m);
                self.line(&s);
            }
        }
    }

    fn member_flat(&self, m: &Member) -> String {
        match m {
            Member::Field(f) => match &f.ty {
                Some(ty) => format!("{}: {}", f.name, self.type_flat(ty)),
                None => f.name.clone(),
            },
            Member::Method(me) => {
                let params: Vec<String> = me.params.iter().map(|p| self.param_flat(p)).collect();
                let mut s = format!("{}({})", me.name, params.join(", "));
                if let Some(r) = &me.ret {
                    s.push_str(&format!(" -> {}", self.type_flat(r)));
                }
                s
            }
        }
    }

    // ----- functions -----

    fn fun_decl(&mut self, f: &FunDecl) {
        let recv = f
            .recv
            .as_ref()
            .map(|r| format!("{}.", self.type_flat(r)))
            .unwrap_or_default();
        let params: Vec<String> = f.params.iter().map(|p| self.param_flat(p)).collect();
        let ret = f
            .ret
            .as_ref()
            .map(|r| format!(" -> {}", self.type_flat(r)))
            .unwrap_or_default();
        let flat = format!("fun {recv}{}({}){ret} {{", f.name, params.join(", "));
        if self.fits(&flat) || params.is_empty() {
            self.line(&flat);
        } else {
            // Overlong signature: one parameter per line inside the parens.
            self.line(&format!("fun {recv}{}(", f.name));
            self.level += 1;
            if let Some(first) = f.params.first() {
                self.finish(first.span.lo);
            }
            for p in &f.params {
                self.start(p.span.lo);
                let s = format!("{},", self.param_flat(p));
                self.line(&s);
                self.finish(p.span.hi);
            }
            self.level -= 1;
            self.line(&format!("){ret} {{"));
        }
        self.block_body(&f.body);
        self.line("}");
    }

    pub(crate) fn param_flat(&self, p: &Param) -> String {
        match &p.ty {
            Some(ty) => format!("{}: {}", p.name, self.type_flat(ty)),
            None => p.name.clone(),
        }
    }

    // ----- statements -----

    /// Emit the statements of a block. The caller prints the `{` and `}` lines;
    /// this indents one level and runs the comment bookkeeping between them.
    pub(crate) fn block_body(&mut self, b: &Block) {
        // Anchor just past the `{` so a same-line comment attaches to the
        // header line rather than moving into the body.
        self.finish(b.span.lo + 1);
        self.level += 1;
        for s in &b.stmts {
            self.start(s.span().lo);
            self.stmt(s);
            self.finish(s.span().hi);
        }
        self.flush_comments(b.span.hi);
        self.level -= 1;
    }

    pub(crate) fn stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Let {
                pat,
                ty,
                value,
                is_const,
                ..
            } => {
                let kw = if *is_const { "const" } else { "let" };
                let mut head = format!("{kw} {}", self.pattern_flat(pat));
                if let Some(t) = ty {
                    head.push_str(&format!(": {}", self.type_flat(t)));
                }
                match value {
                    None => self.line(&head),
                    Some(v) => {
                        head.push_str(" = ");
                        self.expr_lines(head, v, "", false);
                    }
                }
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let head = format!("{} {} ", self.flat_or_src(target, false), assign_sym(*op));
                self.expr_lines(head, value, "", false);
            }
            Stmt::Expr(e) => self.expr_lines(String::new(), e, "", false),
            Stmt::While { cond, body, .. } => {
                self.expr_lines("while ".to_string(), cond, " {", true);
                self.block_body(body);
                self.line("}");
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                let pat = self.pattern_flat(pat);
                self.expr_lines(format!("for {pat} in "), iter, " {", true);
                self.block_body(body);
                self.line("}");
            }
            Stmt::Return(v, _) => match v {
                None => self.line("return"),
                Some(e) => self.expr_lines("return ".to_string(), e, "", false),
            },
            Stmt::Break(_) => self.line("break"),
            Stmt::Continue(_) => self.line("continue"),
        }
    }
}

fn imported_name(n: &ImportedName) -> String {
    if n.local == n.remote {
        n.remote.clone()
    } else {
        format!("{} as {}", n.remote, n.local)
    }
}

fn member_span(m: &Member) -> (usize, usize) {
    match m {
        Member::Field(f) => (f.span.lo, f.span.hi),
        Member::Method(me) => (me.span.lo, me.span.hi),
    }
}

pub(crate) fn assign_sym(op: AssignOp) -> &'static str {
    match op {
        AssignOp::Eq => "=",
        AssignOp::Add => "+=",
        AssignOp::Sub => "-=",
        AssignOp::Mul => "*=",
        AssignOp::Div => "/=",
        AssignOp::Rem => "%=",
    }
}
