//! Incremental analysis bookkeeping.
//!
//! The active document is split into top-level items (each function, each type,
//! and one bucket for module-level statements). For each item we record a hash
//! of its source text and the set of names it references. On an edit we compare
//! hashes to find the changed items, add every item that *uses* a changed name
//! (reverse dependencies), and re-check only that affected set plus the
//! definitions it depends on -- never the whole program. Diagnostics for the
//! untouched items are carried over from the previous version, their spans
//! shifted by the byte delta their (byte-identical) source moved.

use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use prepoly_lexer::Span;
use prepoly_parser::ast::{
    Arg, Block, Expr, FieldPat, Member, Module, Param, Pattern, Stmt, StrSeg, TopLevel, TypeBody,
    TypeDecl, TypeExpr,
};

/// A single diagnostic: a message and the global span it is reported at.
pub type Diag = (String, Span);

/// What kind of top-level construct an item is. The synthetic `Init` item
/// gathers every module-level statement into one unit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ItemKind {
    Fun,
    Type,
    Init,
}

/// One top-level item of the active document with the data the incremental
/// checker needs: its identity, source hash, referenced names, and -- once
/// checked -- its diagnostics in global span coordinates.
#[derive(Clone)]
pub struct Item {
    pub name: String,
    pub kind: ItemKind,
    /// Global span covering the whole item (parsed with the document's base).
    pub span: Span,
    /// Hash of the item's source text; equal iff the text is byte-identical.
    pub hash: u64,
    /// Names this item mentions (functions, types, methods/fields). An
    /// over-approximation -- extra names only cause extra re-checking.
    pub refs: HashSet<String>,
    /// Names this item *defines* at the top level. For a function or type this is
    /// just its own name; for the synthetic `<init>` item it is every module-level
    /// `let`/`const` global it declares. Dependency resolution matches an item's
    /// `refs` against these (not the item name), so a function that uses a global is
    /// pulled in together with the `<init>` item that declares it -- otherwise it is
    /// re-checked with the global out of scope and reports a spurious "unknown name".
    pub defines: HashSet<String>,
    /// Diagnostics attributed to this item, in global span coordinates.
    pub diags: Vec<Diag>,
}

/// The carried-over incremental state for one document.
#[derive(Clone, Default)]
pub struct ItemCache {
    pub items: Vec<Item>,
}

/// Split a parsed module into items, hashing each from `main_src` (the document
/// text; `base` is its global byte offset). The `diags` field starts empty.
pub fn split(module: &Module, main_src: &str, base: usize) -> Vec<Item> {
    let mut items = Vec::new();
    let mut init_stmts: Vec<&Stmt> = Vec::new();
    for top in &module.items {
        match top {
            TopLevel::Fun(f) => {
                let mut refs = HashSet::new();
                for p in &f.params {
                    refs_param(p, &mut refs);
                }
                if let Some(ret) = &f.ret {
                    refs_type(ret, &mut refs);
                }
                refs_block(&f.body, &mut refs);
                items.push(make_item(
                    f.name.clone(),
                    ItemKind::Fun,
                    f.span,
                    main_src,
                    base,
                    refs,
                ));
            }
            TopLevel::Type(t) => {
                let mut refs = HashSet::new();
                refs_type_decl(t, &mut refs);
                items.push(make_item(
                    t.name.clone(),
                    ItemKind::Type,
                    t.span,
                    main_src,
                    base,
                    refs,
                ));
            }
            TopLevel::Stmt(s) => init_stmts.push(s),
        }
    }
    if !init_stmts.is_empty() {
        let mut span = init_stmts[0].span();
        for s in &init_stmts[1..] {
            span = span.merge(s.span());
        }
        let mut refs = HashSet::new();
        let mut defines = HashSet::new();
        for s in &init_stmts {
            refs_stmt(s, &mut refs);
            collect_stmt_defines(s, &mut defines);
        }
        let mut item = make_item("<init>".into(), ItemKind::Init, span, main_src, base, refs);
        // The init item defines the module-level globals, not the synthetic name, so
        // a function that references a global resolves to (and pulls in) this item.
        item.defines = defines;
        items.push(item);
    }
    items
}

fn make_item(
    name: String,
    kind: ItemKind,
    span: Span,
    main_src: &str,
    base: usize,
    refs: HashSet<String>,
) -> Item {
    let lo = span.lo.saturating_sub(base);
    let hi = (span.hi.saturating_sub(base)).min(main_src.len());
    let text = main_src.get(lo..hi).unwrap_or("");
    let mut h = DefaultHasher::new();
    text.hash(&mut h);
    let mut defines = HashSet::new();
    defines.insert(name.clone());
    Item {
        name,
        kind,
        span,
        hash: h.finish(),
        refs,
        defines,
        diags: Vec::new(),
    }
}

/// The top-level names a module-level statement binds (`let`/`const` globals), so
/// the `<init>` item advertises them as its definitions.
fn collect_stmt_defines(stmt: &Stmt, out: &mut HashSet<String>) {
    if let Stmt::Let { pat, .. } = stmt {
        collect_pattern_defines(pat, out);
    }
}

fn collect_pattern_defines(pat: &Pattern, out: &mut HashSet<String>) {
    match pat {
        Pattern::Binding(name, _) => {
            out.insert(name.clone());
        }
        Pattern::Record(_, fields, _) => {
            for f in fields {
                match &f.pat {
                    Some(sub) => collect_pattern_defines(sub, out),
                    None => {
                        out.insert(f.name.clone());
                    }
                }
            }
        }
        Pattern::Array(pats, _) => pats.iter().for_each(|p| collect_pattern_defines(p, out)),
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
    }
}

/// The outcome of diffing new items against the previous cache: which items
/// must be re-checked, and which can keep shifted diagnostics.
pub struct Diff {
    /// `true` when a from-scratch check is required (no previous state, the set
    /// of top-level names changed, or names are not unique). Then every item is
    /// affected and the reduced set is the whole document.
    pub full: bool,
    /// Indices into the new item list that must be re-checked.
    pub affected: HashSet<usize>,
    /// Indices to re-check for context (affected plus their dependency closure);
    /// only `affected` diagnostics are kept, the rest provide resolution context.
    pub reduced: HashSet<usize>,
    /// For each carried-over item index, the byte delta to shift its previous
    /// diagnostics by (the previous item it corresponds to is byte-identical).
    pub carry: Vec<Carry>,
}

/// One carried-over item: its new index, the byte delta to shift its previous
/// diagnostics by, and those diagnostics.
pub type Carry = (usize, i64, Vec<Diag>);

/// Compute the incremental diff between `prev` (last cache) and `new_items`.
pub fn diff(prev: &ItemCache, new_items: &[Item]) -> Diff {
    let new_by_name = index_by_name(new_items);
    let names_unique = new_by_name.len() == new_items.len();
    let prev_by_name = index_by_name(&prev.items);

    let same_name_set = names_unique
        && prev_by_name.len() == prev.items.len()
        && new_by_name.len() == prev_by_name.len()
        && new_by_name.keys().all(|k| prev_by_name.contains_key(k));

    if prev.items.is_empty() || !same_name_set {
        // From-scratch check: everything is affected, the reduced set is all.
        let all: HashSet<usize> = (0..new_items.len()).collect();
        return Diff {
            full: true,
            affected: all.clone(),
            reduced: all,
            carry: Vec::new(),
        };
    }

    // Changed = source hash differs from the same-named previous item. Collect the
    // names those changed items *define* (an item's own name, or the globals of a
    // changed `<init>`), so a user of a changed global is re-checked too.
    let mut changed_names: HashSet<&str> = HashSet::new();
    let mut changed_defs: HashSet<&str> = HashSet::new();
    for (name, &i) in &new_by_name {
        let pi = prev_by_name[name];
        if new_items[i].hash != prev.items[pi].hash {
            changed_names.insert(name);
            for d in &new_items[i].defines {
                changed_defs.insert(d);
            }
        }
    }

    // Affected = changed items plus every item that references a name *defined* by a
    // changed item.
    let mut affected: HashSet<usize> = HashSet::new();
    for (name, &i) in &new_by_name {
        let is_changed = changed_names.contains(name.as_str());
        let uses_changed = new_items[i]
            .refs
            .iter()
            .any(|r| changed_defs.contains(r.as_str()));
        if is_changed || uses_changed {
            affected.insert(i);
        }
    }

    // Reduced = affected plus the forward dependency closure, resolved through
    // *defined* names so a referenced global pulls in the `<init>` item that
    // declares it -- otherwise the affected item is re-checked with the global out
    // of scope and reports a spurious "unknown name".
    let def_to_index = index_by_defines(new_items);
    let reduced = forward_closure(&affected, new_items, &def_to_index);

    // Carry = unaffected items keep last diagnostics, shifted by their byte move.
    let mut carry = Vec::new();
    for (name, &i) in &new_by_name {
        if affected.contains(&i) {
            continue;
        }
        let pi = prev_by_name[name];
        let delta = new_items[i].span.lo as i64 - prev.items[pi].span.lo as i64;
        carry.push((i, delta, prev.items[pi].diags.clone()));
    }

    Diff {
        full: false,
        affected,
        reduced,
        carry,
    }
}

/// Extend `seed` with every item referenced (transitively) by an item already
/// in the set, following `refs` that name another item in the document.
fn forward_closure(
    seed: &HashSet<usize>,
    items: &[Item],
    by_name: &HashMap<String, usize>,
) -> HashSet<usize> {
    let mut set = seed.clone();
    let mut work: Vec<usize> = seed.iter().copied().collect();
    while let Some(i) = work.pop() {
        for r in &items[i].refs {
            if let Some(&j) = by_name.get(r)
                && set.insert(j)
            {
                work.push(j);
            }
        }
    }
    set
}

fn index_by_name(items: &[Item]) -> HashMap<String, usize> {
    let mut map = HashMap::new();
    for (i, it) in items.iter().enumerate() {
        map.insert(it.name.clone(), i);
    }
    map
}

/// Map every *defined* name to its item index (a function/type name, or each global
/// the `<init>` item declares), for resolving an item's `refs` to the item that
/// provides the name.
fn index_by_defines(items: &[Item]) -> HashMap<String, usize> {
    let mut map = HashMap::new();
    for (i, it) in items.iter().enumerate() {
        for d in &it.defines {
            map.insert(d.clone(), i);
        }
    }
    map
}

// ===== reference collection =====
//
// These walk the AST gathering every name an item mentions. The set is an
// over-approximation: identifiers, type names, and field/method names all go in
// undistinguished, because a name shared between a field and a free function
// (UFCS) must still force a re-check of users when either changes.

fn refs_type_decl(t: &TypeDecl, out: &mut HashSet<String>) {
    for i in &t.interfaces {
        out.insert(i.clone());
    }
    let members = match &t.body {
        TypeBody::Record(members) => members.clone(),
        TypeBody::Sum(variants) => {
            for v in variants {
                for m in &v.members {
                    refs_member(m, out);
                }
            }
            return;
        }
        TypeBody::Alias(te) => {
            refs_type(te, out);
            return;
        }
    };
    for m in &members {
        refs_member(m, out);
    }
}

fn refs_member(m: &Member, out: &mut HashSet<String>) {
    match m {
        Member::Field(f) => {
            if let Some(ty) = &f.ty {
                refs_type(ty, out);
            }
        }
        Member::Method(method) => {
            for p in &method.params {
                refs_param(p, out);
            }
            if let Some(ret) = &method.ret {
                refs_type(ret, out);
            }
            if let Some(body) = &method.body {
                refs_block(body, out);
            }
        }
    }
}

fn refs_param(p: &Param, out: &mut HashSet<String>) {
    if let Some(ty) = &p.ty {
        refs_type(ty, out);
    }
}

fn refs_type(ty: &TypeExpr, out: &mut HashSet<String>) {
    match ty {
        TypeExpr::Named(name, _) => {
            out.insert(name.clone());
        }
        TypeExpr::Array(inner, _, _)
        | TypeExpr::Nullable(inner, _)
        | TypeExpr::Fallible(inner, _)
        | TypeExpr::Mut(inner, _)
        | TypeExpr::Ref(inner, _) => refs_type(inner, out),
        TypeExpr::Fun(params, ret, _) => {
            for p in params {
                refs_type(p, out);
            }
            refs_type(ret, out);
        }
        TypeExpr::Tuple(elems, _) => {
            for e in elems {
                refs_type(e, out);
            }
        }
        TypeExpr::Anonymous(fields, _) => {
            for (_, fty) in fields {
                refs_type(fty, out);
            }
        }
        // `typeof(e)` names no type by identifier; its type comes from `e`.
        TypeExpr::TypeOf(..) => {}
        // A refinement mentions its base type name and each pinned field's type.
        TypeExpr::Refine(base, fields, _) => {
            refs_type(base, out);
            for (_, fty) in fields {
                refs_type(fty, out);
            }
        }
        // `Self.field` / `type` slot name no external type by identifier.
        TypeExpr::SelfField(..) | TypeExpr::TypeSlot(..) => {}
    }
}

fn refs_block(b: &Block, out: &mut HashSet<String>) {
    for s in &b.stmts {
        refs_stmt(s, out);
    }
}

fn refs_stmt(s: &Stmt, out: &mut HashSet<String>) {
    match s {
        Stmt::Let { ty, value, .. } => {
            if let Some(ty) = ty {
                refs_type(ty, out);
            }
            if let Some(value) = value {
                refs_expr(value, out);
            }
        }
        Stmt::Assign { target, value, .. } => {
            refs_expr(target, out);
            refs_expr(value, out);
        }
        Stmt::Expr(e) => refs_expr(e, out),
        Stmt::While { cond, body, .. } => {
            refs_expr(cond, out);
            refs_block(body, out);
        }
        Stmt::For { iter, body, .. } => {
            refs_expr(iter, out);
            refs_block(body, out);
        }
        Stmt::Return(Some(e), _) => refs_expr(e, out),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

fn refs_expr(e: &Expr, out: &mut HashSet<String>) {
    match e {
        Expr::Ident(name, _) => {
            out.insert(name.clone());
        }
        Expr::Int(..) | Expr::Float(..) | Expr::Bool(..) | Expr::Null(_) | Expr::SelfExpr(_) => {}
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(e) = seg {
                    refs_expr(e, out);
                }
            }
        }
        Expr::Unary(_, e, _) | Expr::ErrorProp(e, _) => refs_expr(e, out),
        Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
            refs_expr(a, out);
            refs_expr(b, out);
        }
        Expr::Call(callee, args, _) => {
            refs_expr(callee, out);
            for Arg { expr } in args {
                refs_expr(expr, out);
            }
        }
        Expr::Field(recv, name, _) => {
            refs_expr(recv, out);
            // Method/field names participate in UFCS dispatch, so a free
            // function of the same name is a possible target: record it.
            out.insert(name.clone());
        }
        Expr::Closure(params, body, _) => {
            for p in params {
                refs_param(p, out);
            }
            refs_expr(body, out);
        }
        Expr::Array(elems, _) => {
            for e in elems {
                refs_expr(e, out);
            }
        }
        Expr::TypeLit(name, fields, _) => {
            out.insert(name.clone());
            for (_, v) in fields {
                refs_expr(v, out);
            }
        }
        Expr::VariantLit(ty, _, fields, _) => {
            out.insert(ty.clone());
            for (_, v) in fields {
                refs_expr(v, out);
            }
        }
        Expr::If(cond, then, els, _) => {
            refs_expr(cond, out);
            refs_block(then, out);
            if let Some(e) = els {
                refs_expr(e, out);
            }
        }
        Expr::IfLet(pat, scrut, then, els, _) => {
            refs_pattern(pat, out);
            refs_expr(scrut, out);
            refs_block(then, out);
            if let Some(e) = els {
                refs_expr(e, out);
            }
        }
        Expr::Match(scrut, arms, _) => {
            refs_expr(scrut, out);
            for arm in arms {
                refs_pattern(&arm.pattern, out);
                refs_expr(&arm.body, out);
            }
        }
        Expr::Block(b, _) => refs_block(b, out),
    }
}

fn refs_pattern(p: &Pattern, out: &mut HashSet<String>) {
    match p {
        Pattern::Wildcard(_) | Pattern::Binding(_, _) => {}
        Pattern::Literal(e, _) => refs_expr(e, out),
        Pattern::Record(name, fields, _) => {
            out.insert(name.clone());
            for FieldPat { pat, .. } in fields {
                if let Some(p) = pat {
                    refs_pattern(p, out);
                }
            }
        }
        Pattern::Array(pats, _) => {
            for p in pats {
                refs_pattern(p, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use prepoly_parser::parse;

    fn items_of(src: &str) -> Vec<Item> {
        split(&parse(src).expect("parse"), src, 0)
    }

    /// Editing a function that references a module-level global must pull the
    /// `<init>` item (which declares the global) into the reduced re-check set, so
    /// the function is not re-checked with the global out of scope -- which used to
    /// produce a spurious "unknown name" the full compiler never reports.
    #[test]
    fn editing_a_function_pulls_in_the_globals_it_uses() {
        let v1 = "const LIMIT = 100\nfun use_it() {\n    return LIMIT\n}\n";
        let v2 = "const LIMIT = 100\nfun use_it() {\n    return LIMIT + 0\n}\n";
        let prev = ItemCache {
            items: items_of(v1),
        };
        let new_items = items_of(v2);
        let d = diff(&prev, &new_items);
        assert!(
            !d.full,
            "a single-body edit is incremental, not from-scratch"
        );
        let init_idx = new_items
            .iter()
            .position(|it| it.kind == ItemKind::Init)
            .expect("an <init> item for the global");
        assert!(
            d.reduced.contains(&init_idx),
            "the <init> item declaring LIMIT must be re-checked in scope with its user"
        );
    }

    /// Changing a global's value must re-check the functions that use it (the global
    /// is one of `<init>`'s defined names), not carry over their stale diagnostics.
    #[test]
    fn editing_a_global_affects_its_users() {
        let v1 = "const LIMIT = 100\nfun use_it() {\n    return LIMIT\n}\n";
        let v2 = "const LIMIT = 200\nfun use_it() {\n    return LIMIT\n}\n";
        let prev = ItemCache {
            items: items_of(v1),
        };
        let new_items = items_of(v2);
        let d = diff(&prev, &new_items);
        let use_idx = new_items
            .iter()
            .position(|it| it.name == "use_it")
            .expect("use_it item");
        assert!(
            d.affected.contains(&use_idx),
            "a user of the changed global must be re-checked"
        );
    }
}
