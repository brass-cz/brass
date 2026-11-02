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

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use brass_hir::LoadedModule;
use brass_parser::Span;
use brass_parser::ast::{
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

    let mut aliases: HashSet<String> = HashSet::default();
    let mut alias_paths: HashMap<String, String> = HashMap::default();
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
        scopes: vec![HashSet::default()],
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
        Pattern::Binding(name, None, _) => {
            out.insert(name.clone());
        }
        Pattern::Array(pats, _) => {
            for p in pats {
                collect_pattern_names(p, out);
            }
        }
        Pattern::Record(_, _, fields, _) => {
            for f in fields {
                match &f.pat {
                    Some(p) => collect_pattern_names(p, out),
                    None => {
                        out.insert(f.name.clone());
                    }
                }
            }
        }
        Pattern::Wildcard(_) | Pattern::Literal(..) | Pattern::Binding(_, Some(_), _) => {}
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
        self.scopes.push(HashSet::default());
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

    fn block(&mut self, b: &mut brass_parser::ast::Block) {
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
                self.pattern(pat);
                // The binding is visible only after its initializer.
                let mut names = HashSet::default();
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
                self.pattern(pat);
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
            Expr::TypeTest(subject, te, _, _) => {
                self.expr(subject);
                self.ty(te);
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
                self.pattern(pat);
                self.push();
                let mut names = HashSet::default();
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
                    self.pattern(&mut arm.pattern);
                    self.push();
                    let mut names = HashSet::default();
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

    /// Pattern type paths use the same dotted markers as variant literals.
    /// Validate before introducing bindings, which may shadow module aliases.
    fn pattern(&mut self, pat: &mut Pattern) {
        if let Pattern::Record(name, qualifier, _, span) = pat
            && let Some(q) = qualifier
            && self.aliases.contains(&q.ty)
        {
            let marker = format!("{}.{name}", q.ty);
            if self.bound(&q.ty) {
                self.errors.push(ResolveError {
                    message: format!("unknown type `{marker}`"),
                    span: q.span,
                });
            } else if self.validate(&q.ty, name, *span) {
                // Like a qualified record literal, the whole head names a
                // type. A dotted marker cannot collide with a variant name.
                *name = marker;
                *qualifier = None;
            }
        }
        match pat {
            Pattern::Binding(_, qualifier, _) | Pattern::Record(_, qualifier, _, _) => {
                if let Some(q) = qualifier
                    && let Some((alias, name)) = q.ty.split_once('.')
                {
                    if self.aliases.contains(alias) && self.bound(alias) {
                        self.errors.push(ResolveError {
                            message: format!("unknown type `{}`", q.ty),
                            span: q.span,
                        });
                    } else {
                        self.validate(alias, name, q.span);
                    }
                }
            }
            _ => {}
        }
        match pat {
            Pattern::Record(_, _, fields, _) => {
                for field in fields {
                    if let Some(pat) = &mut field.pat {
                        self.pattern(pat);
                    }
                }
            }
            Pattern::Array(patterns, _) => {
                for pat in patterns {
                    self.pattern(pat);
                }
            }
            _ => {}
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
                for (_, ft, _) in fields {
                    self.ty(ft);
                }
            }
            TypeExpr::Refine(base, fields, _) => {
                self.ty(base);
                for (_, ft, _) in fields {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn pattern_errors(body: &str) -> Vec<ResolveError> {
        let mut modules = vec![
            LoadedModule {
                source: None,
                is_prelude: false,
                path: vec!["shapes".into()],
                ast: brass_parser::parse("type Shape = X { v: int32 } | Y\ntype _Hidden = A | B\n")
                    .expect("library"),
            },
            LoadedModule {
                source: None,
                is_prelude: false,
                path: vec!["main".into()],
                ast: brass_parser::parse(&format!(
                    "import shapes as shapes\nfun f(x) {{ {body} }}\n"
                ))
                .expect("main"),
            },
        ];
        resolve_qualified_uses(&mut modules)
    }

    #[test]
    fn pattern_qualifiers_obey_module_visibility_and_shadowing() {
        // Patterns use the same exports and privacy rules as variant literals.
        for (ty, expected) in [
            (
                "shapes.Missing",
                "module `shapes` has no exported name `Missing`",
            ),
            (
                "shapes._Hidden",
                "cannot access private name `_Hidden` of module `shapes`",
            ),
        ] {
            let errors = pattern_errors(&format!("match x {{ {ty}.Y => 0, _ => 1 }}"));
            assert_eq!(errors.len(), 1, "{errors:?}");
            assert_eq!(errors[0].message, expected);
        }
        let errors = pattern_errors("let shapes = 0\nmatch x { shapes.Shape.Y => 0, _ => 1 }");
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert_eq!(errors[0].message, "unknown type `shapes.Shape`");
    }

    #[test]
    fn module_record_patterns_are_validated_and_normalized() {
        // The whole module-qualified head names a type, as in a record literal.
        // Preserve its dotted spelling and distinguish it from a sum qualifier.
        let mut modules = vec![
            LoadedModule {
                source: None,
                is_prelude: false,
                path: vec!["shapes".into()],
                ast: brass_parser::parse("type P = { x: int32 }\n").expect("library"),
            },
            LoadedModule {
                source: None,
                is_prelude: false,
                path: vec!["main".into()],
                ast: brass_parser::parse("import shapes as shapes\nlet shapes.P { x } = p\n")
                    .expect("main"),
            },
        ];
        let errors = resolve_qualified_uses(&mut modules);
        assert!(errors.is_empty(), "{errors:?}");
        let TopLevel::Stmt(Stmt::Let { pat, .. }) = &modules[1].ast.items[0] else {
            panic!("let pattern");
        };
        assert!(
            matches!(pat, Pattern::Record(name, None, _, _) if name == "shapes.P"),
            "{pat:?}"
        );
        for (body, expected) in [
            (
                "let shapes.Missing { x } = p",
                "module `shapes` has no exported name `Missing`",
            ),
            (
                "let shapes._Hidden { x } = p",
                "cannot access private name `_Hidden` of module `shapes`",
            ),
            (
                "let shapes = 0\nlet shapes.Shape { x } = p",
                "unknown type `shapes.Shape`",
            ),
        ] {
            let errors = pattern_errors(body);
            assert_eq!(errors.len(), 1, "{body}: {errors:?}");
            assert_eq!(errors[0].message, expected);
        }
    }

    #[test]
    fn pattern_qualifiers_are_visited_before_bindings_in_every_position() {
        // A field binding may shadow the module alias inside the body, but
        // cannot shadow the qualifier of the very pattern introducing it.
        assert!(
            pattern_errors("match x { shapes.Shape.X { v: shapes } => shapes, _ => 0 }").is_empty()
        );
        for body in [
            "let shapes.Missing.X { v } = x",
            "if let shapes.Missing.Y = x { 0 } else { 1 }",
            "for shapes.Missing.Y in x { 0 }",
            "match x { Box { item: shapes.Missing.Y } => 0, _ => 1 }",
        ] {
            let errors = pattern_errors(body);
            assert_eq!(errors.len(), 1, "{body}: {errors:?}");
            assert_eq!(
                errors[0].message,
                "module `shapes` has no exported name `Missing`"
            );
        }
    }
    #[test]
    fn pattern_qualifier_shadowing_is_lexical() {
        // Parameters and match bindings shadow inside their scope; leaving a
        // nested block restores the imported qualifier.
        for body in [
            "let f = (shapes) -> { match x { shapes.Shape.Y => 0, _ => 1 } }",
            "match x { shapes => match x { shapes.Shape.Y => 0, _ => 1 } }",
        ] {
            let errors = pattern_errors(body);
            assert_eq!(errors.len(), 1, "{body}: {errors:?}");
            assert_eq!(errors[0].message, "unknown type `shapes.Shape`");
        }
        let errors =
            pattern_errors("if true { let shapes = 0 }\nmatch x { shapes.Shape.Y => 0, _ => 1 }");
        assert!(errors.is_empty(), "{errors:?}");
    }
}
