//! Qualified use of module imports: validate and mark `alias.name`
//! references from a bare `import a.b`.
//!
//! A module import brings no names by itself; the program refers to the
//! module's exports qualified by the path's last segment (`vec.dot(..)`,
//! `let v: vec.Vec2`, `vec.Vec2 { x: 1.0 }`). This pass validates each such
//! use against the target module's exports and rewrites it to a dotted
//! MARKER identifier (`Ident("vec.dot")` / `Named("vec.Vec2")`) -- a
//! spelling no source identifier can produce. Downstream resolution
//! recognizes the dot and resolves the marker through
//! `Program::module_aliases` (see `Program::resolve_marker`), so a marker
//! never collides with a braced import of the same bare name.
//!
//! A local binding shadows a qualifier: after `let vec = ..`, `vec.x` is a
//! field access on the binding, never a qualified reference. A qualifier that
//! collides with a declared or imported name is rejected up front -- the two
//! readings of `name.member` could not be told apart at use sites.

use std::collections::{HashMap, HashSet};

use prepoly_hir::LoadedModule;
use prepoly_parser::Span;
use prepoly_parser::ast::{
    Expr, Member, Pattern, Stmt, StrSeg, TopLevel, TypeBody, TypeExpr, Variant,
};

use crate::module::{ResolveError, collect_exports};

/// Rewrite every qualified use (`alias.name`) in `modules` to a dotted
/// marker identifier that downstream resolution can handle directly.
/// Returns the problems found: a shadowed or duplicated qualifier,
/// a qualified access to a private (`_`-prefixed) name, or a name
/// that is not exported by the target module.
pub fn resolve_qualified_uses(modules: &mut [LoadedModule]) -> Vec<ResolveError> {
    let exports = collect_exports(modules);
    let mut errors = Vec::new();
    for m in modules.iter_mut() {
        rewrite_module(m, &exports, &mut errors);
    }
    errors
}

fn rewrite_module(
    m: &mut LoadedModule,
    exports: &HashMap<String, HashSet<String>>,
    errors: &mut Vec<ResolveError>,
) {
    // Names that make a qualifier unusable in this module: names imported by
    // any import, and this module's own top-level declarations. A use site
    // could not distinguish `name.member` on these from a qualified access.
    let mut taken: HashSet<String> = m
        .ast
        .imports
        .iter()
        .flat_map(|i| i.names.iter().map(|n| n.local.clone()))
        .collect();
    for item in &m.ast.items {
        match item {
            TopLevel::Fun(f) => {
                taken.insert(f.name.clone());
            }
            TopLevel::Type(t) => {
                taken.insert(t.name.clone());
            }
            TopLevel::Stmt(Stmt::Let { pat, .. }) => collect_pattern_names(pat, &mut taken),
            TopLevel::Stmt(_) => {}
        }
    }

    let mut aliases: HashSet<String> = HashSet::new();
    let mut alias_paths: HashMap<String, String> = HashMap::new();
    for imp in &m.ast.imports {
        let Some(alias) = imp.alias.clone() else {
            continue;
        };
        if taken.contains(&alias) {
            errors.push(ResolveError {
                message: format!(
                    "the module qualifier `{alias}` (from `import {}`) collides with a \
                     declared or imported name; rename one of them",
                    imp.path.join(".")
                ),
                span: imp.span,
            });
            continue;
        }
        if aliases.contains(&alias) {
            errors.push(ResolveError {
                message: format!(
                    "two module imports share the qualifier `{alias}`; rename one with \
                     `import ... as <name>` or import names directly"
                ),
                span: imp.span,
            });
            continue;
        }
        alias_paths.insert(alias.clone(), imp.path.join("."));
        aliases.insert(alias);
    }
    if aliases.is_empty() {
        return;
    }

    let mut rw = Rewriter {
        aliases: &aliases,
        alias_paths: &alias_paths,
        exports,
        errors,
        scopes: vec![HashSet::new()],
    };
    for item in &mut m.ast.items {
        match item {
            TopLevel::Fun(f) => {
                for p in &mut f.params {
                    if let Some(t) = &mut p.ty {
                        rw.ty(t);
                    }
                }
                if let Some(r) = &mut f.ret {
                    rw.ty(r);
                }
                rw.push();
                for p in &f.params {
                    rw.bind(&p.name);
                }
                rw.block(&mut f.body);
                rw.pop();
            }
            TopLevel::Type(t) => rw.type_body(&mut t.body),
            TopLevel::Stmt(s) => rw.stmt(s),
        }
    }
}

pub(crate) fn collect_pattern_names(pat: &Pattern, out: &mut HashSet<String>) {
    match pat {
        Pattern::Binding(name, _) => {
            out.insert(name.clone());
        }
        Pattern::Array(pats, _) => {
            for p in pats {
                collect_pattern_names(p, out);
            }
        }
        Pattern::Record(_, fields, _) => {
            for f in fields {
                match &f.pat {
                    Some(p) => collect_pattern_names(p, out),
                    None => {
                        out.insert(f.name.clone());
                    }
                }
            }
        }
        Pattern::Wildcard(_) | Pattern::Literal(..) => {}
    }
}

struct Rewriter<'a> {
    aliases: &'a HashSet<String>,
    alias_paths: &'a HashMap<String, String>,
    exports: &'a HashMap<String, HashSet<String>>,
    errors: &'a mut Vec<ResolveError>,
    /// Lexical bindings in scope; a bound name shadows a qualifier.
    scopes: Vec<HashSet<String>>,
}

impl Rewriter<'_> {
    fn bound(&self, name: &str) -> bool {
        self.scopes.iter().any(|s| s.contains(name))
    }

    fn bind(&mut self, name: &str) {
        if let Some(top) = self.scopes.last_mut() {
            top.insert(name.to_string());
        }
    }

    fn push(&mut self) {
        self.scopes.push(HashSet::new());
    }

    fn pop(&mut self) {
        self.scopes.pop();
    }

    /// Validate a qualified use: `alias` names an unshadowed module import,
    /// `name` is public, and `name` is exported by the target module. Returns
    /// true when the use is valid; the caller rewrites the node to a marker
    /// identifier (`"alias.name"`).
    fn validate(&mut self, alias: &str, name: &str, span: Span) -> bool {
        if !self.aliases.contains(alias) {
            return false;
        }
        if self.bound(alias) {
            return false;
        }
        if name.starts_with('_') {
            self.errors.push(ResolveError {
                message: format!(
                    "cannot access private name `{name}` of module `{}`",
                    self.alias_paths[alias]
                ),
                span,
            });
            return false;
        }
        let module_path = &self.alias_paths[alias];
        if let Some(names) = self.exports.get(module_path)
            && !names.contains(name)
        {
            self.errors.push(ResolveError {
                message: format!("module `{module_path}` has no exported name `{name}`"),
                span,
            });
            return false;
        }
        true
    }

    fn block(&mut self, b: &mut prepoly_parser::ast::Block) {
        self.push();
        for s in &mut b.stmts {
            self.stmt(s);
        }
        self.pop();
    }

    fn stmt(&mut self, s: &mut Stmt) {
        match s {
            Stmt::Let { pat, ty, value, .. } => {
                if let Some(t) = ty {
                    self.ty(t);
                }
                if let Some(v) = value {
                    self.expr(v);
                }
                // The binding is visible only after its initializer.
                let mut names = HashSet::new();
                collect_pattern_names(pat, &mut names);
                for n in names {
                    self.bind(&n);
                }
            }
            Stmt::Assign { target, value, .. } => {
                self.expr(target);
                self.expr(value);
            }
            Stmt::Expr(e) => self.expr(e),
            Stmt::While { cond, body, .. } => {
                self.expr(cond);
                self.block(body);
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                self.expr(iter);
                self.push();
                for n in pat.bound_names() {
                    self.bind(n);
                }
                self.block(body);
                self.pop();
            }
            Stmt::Return(Some(e), _) => self.expr(e),
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }

    fn expr(&mut self, e: &mut Expr) {
        match e {
            // The qualified-use form itself: `alias.name` -> marker ident.
            Expr::Field(base, name, span) => {
                if let Expr::Ident(q, _) = base.as_ref() {
                    let (q, name, span) = (q.clone(), name.clone(), *span);
                    if self.validate(&q, &name, span) {
                        *e = Expr::Ident(format!("{q}.{name}"), span);
                        return;
                    }
                }
                self.expr(base);
            }
            // Qualified variant: `alias.Sum.Variant { .. }` — the parser
            // produces `VariantLit("alias.Sum", "Variant", ..)`.  Validate the
            // alias; the dotted ty is already the marker.
            //
            // `alias.Type { .. }` (no variant segment) parses as
            // `VariantLit(alias, Type, ..)` — qualified record literal;
            // rewrite to `TypeLit("alias.Type", ..)` with a marker name.
            Expr::VariantLit(ty, variant, fields, span) => {
                if let Some((q, sum)) = ty.split_once('.') {
                    // Already a dotted marker from the parser; just validate.
                    let at = *span;
                    self.validate(q, sum, at);
                    for (_, fe) in fields {
                        self.expr(fe);
                    }
                    return;
                }
                let (owner, name, at) = (ty.clone(), variant.clone(), *span);
                if !self.bound(&owner) && self.validate(&owner, &name, at) {
                    let moved = std::mem::take(fields);
                    *e = Expr::TypeLit(format!("{owner}.{name}"), moved, at);
                    let Expr::TypeLit(_, fields, _) = e else {
                        unreachable!("just assigned")
                    };
                    for (_, fe) in fields {
                        self.expr(fe);
                    }
                    return;
                }
                for (_, fe) in fields {
                    self.expr(fe);
                }
            }
            Expr::Unary(_, a, _) => self.expr(a),
            Expr::Binary(_, a, b, _) => {
                self.expr(a);
                self.expr(b);
            }
            Expr::Call(callee, args, _) => {
                self.expr(callee);
                for a in args {
                    self.expr(&mut a.expr);
                }
            }
            Expr::Index(a, i, _) => {
                self.expr(a);
                self.expr(i);
            }
            Expr::ErrorProp(a, _) => self.expr(a),
            Expr::Closure(params, body, _) => {
                for p in params.iter_mut() {
                    if let Some(t) = &mut p.ty {
                        self.ty(t);
                    }
                }
                self.push();
                for p in params.iter() {
                    self.bind(&p.name);
                }
                self.expr(body);
                self.pop();
            }
            Expr::Array(es, _) => {
                for x in es {
                    self.expr(x);
                }
            }
            Expr::Range(lo, hi, _) => {
                self.expr(lo);
                self.expr(hi);
            }
            Expr::TypeLit(_, fields, _) => {
                for (_, fe) in fields {
                    self.expr(fe);
                }
            }
            Expr::If(cond, then, els, _) => {
                self.expr(cond);
                self.block(then);
                if let Some(e) = els {
                    self.expr(e);
                }
            }
            Expr::IfLet(pat, scrut, then, els, _) => {
                self.expr(scrut);
                self.push();
                let mut names = HashSet::new();
                collect_pattern_names(pat, &mut names);
                for n in names {
                    self.bind(&n);
                }
                self.block(then);
                self.pop();
                if let Some(e) = els {
                    self.expr(e);
                }
            }
            Expr::Match(scrut, arms, _) => {
                self.expr(scrut);
                for arm in arms {
                    self.push();
                    let mut names = HashSet::new();
                    collect_pattern_names(&arm.pattern, &mut names);
                    for n in names {
                        self.bind(&n);
                    }
                    self.expr(&mut arm.body);
                    self.pop();
                }
            }
            Expr::Block(b, _) => self.block(b),
            Expr::Str(segs, _) => {
                for seg in segs {
                    if let StrSeg::Expr(e) = seg {
                        self.expr(e);
                    }
                }
            }
            Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(_)
            | Expr::Ident(..)
            | Expr::SelfExpr(_) => {}
        }
    }

    fn ty(&mut self, t: &mut TypeExpr) {
        match t {
            // The qualified type form: parsed as a dotted `Named`.
            TypeExpr::Named(name, span) => {
                if let Some((q, bare)) = name.split_once('.') {
                    // Already a dotted marker; validate the alias.
                    self.validate(q, bare, *span);
                }
            }
            TypeExpr::Array(inner, _, _)
            | TypeExpr::Nullable(inner, _)
            | TypeExpr::Fallible(inner, _)
            | TypeExpr::Mut(inner, _)
            | TypeExpr::Ref(inner, _) => self.ty(inner),
            TypeExpr::Fun(params, ret, _) => {
                for p in params {
                    self.ty(p);
                }
                self.ty(ret);
            }
            TypeExpr::Tuple(elems, _) => {
                for e in elems {
                    self.ty(e);
                }
            }
            TypeExpr::Anonymous(fields, _) => {
                for (_, ft) in fields {
                    self.ty(ft);
                }
            }
            TypeExpr::Refine(base, fields, _) => {
                self.ty(base);
                for (_, ft) in fields {
                    self.ty(ft);
                }
            }
            TypeExpr::TypeOf(e, _) => self.expr(e),
            TypeExpr::SelfField(..) | TypeExpr::TypeSlot(_) => {}
        }
    }

    fn type_body(&mut self, body: &mut TypeBody) {
        match body {
            TypeBody::Record(members) => self.members(members),
            TypeBody::Sum(variants) => {
                for Variant { members, .. } in variants {
                    self.members(members);
                }
            }
            TypeBody::Alias(t) => self.ty(t),
        }
    }

    fn members(&mut self, members: &mut [Member]) {
        for member in members {
            match member {
                Member::Field(f) => {
                    if let Some(t) = &mut f.ty {
                        self.ty(t);
                    }
                }
                Member::Method(method) => {
                    for p in &mut method.params {
                        if let Some(t) = &mut p.ty {
                            self.ty(t);
                        }
                    }
                    if let Some(r) = &mut method.ret {
                        self.ty(r);
                    }
                    if let Some(b) = &mut method.body {
                        self.push();
                        for p in &method.params {
                            self.bind(&p.name);
                        }
                        self.block(b);
                        self.pop();
                    }
                }
            }
        }
    }
}
