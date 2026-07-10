//! Hover: show the type of the expression under the cursor, the signature of a
//! function, or the definition of a type.
//!
//! Function signatures render unannotated parameters and returns as numbered
//! `unknown_N` (see [`crate::render`]), which is the contract for displaying a
//! function type that inference has left partly open.

use std::collections::{BTreeMap, HashMap};

use prepoly_hir::{
    CallableSignature, NominalType, Substitution, Type, TypeInfo, TypeKind, TypeScheme,
    TypedExprKind, collapse_nullable, substitute_vars,
};
use prepoly_parser::Span;
use tower_lsp_server::ls_types::{
    Hover, HoverContents, MarkupContent, MarkupKind, Position, Range,
};

use crate::analysis::FullAnalysis;
use crate::document::Document;
use crate::features::nav;
use crate::render::{
    UnknownNamer, match_type_vars, render_signature_into, render_type, render_type_def_with,
};

/// Build the hover response for `pos` in `doc`, using the full analysis.
pub fn hover(doc: &Document, full: &FullAnalysis, pos: Position) -> Option<Hover> {
    let local = doc.offset_at(pos);
    let global = local + full.main_base;
    let module = vec!["main".to_string()];

    // The cursor on a method name in `recv.method(...)` shows the *method's* type
    // (its signature), not the call's result type. (A method called through UFCS is
    // a free function and is handled by the `resolve_function` path below.)
    if let Some(h) = method_hover(doc, full, local, global) {
        return Some(h);
    }

    // The tightest typed expression gives the precise inferred type of whatever
    // subexpression the cursor sits on.
    let expr = nav::smallest_typed_at(full, global);
    if let Some(expr) = expr {
        match &expr.kind {
            TypedExprKind::Ident(name) => {
                // A bare name resolving to a function (used as a value) shows its
                // signature, with no specific call's bindings; otherwise its type.
                if let Some(f) = full.program.resolve_function(&module, name) {
                    return Some(function_hover(
                        full,
                        f,
                        None,
                        local_range(doc, full, expr.span),
                    ));
                }
                return Some(value_hover(
                    full,
                    name,
                    &expr.ty,
                    local_range(doc, full, expr.span),
                ));
            }
            TypedExprKind::Field(name) => {
                let mut namer = UnknownNamer::default();
                let value = format!("{name}: {}", render_type(&expr.ty, &mut namer));
                return Some(markup(value, local_range(doc, full, expr.span)));
            }
            _ => {}
        }
    }

    // An identifier under the cursor: a local variable, a function (with the
    // bindings of the call it sits in, when any), or a type. A local shadows a
    // same-named symbol.
    if let Some((name, span)) = nav::ident_at(&doc.text, local) {
        if let Some(ty) = nav::local_var_type(full, global, &name) {
            return Some(value_hover(full, &name, &ty, Some(doc.range_of(span))));
        }
        if let Some(f) = full.program.resolve_function(&module, &name) {
            // When the cursor sits in a call expression, bind the function's
            // type variables to that specific call's argument types.
            let call_args = expr
                .filter(|e| matches!(e.kind, TypedExprKind::Call))
                .and_then(|e| nav::call_args_at_span(full, e.span));
            return Some(function_hover(full, f, call_args, Some(doc.range_of(span))));
        }
        if let Some(t) = full.program.resolve_type(&module, &name) {
            // The declaration view: no instance, so slots stay open and method
            // types resolve against the declaration itself (`Self.<slot>`).
            let empty = Substitution::empty();
            let resolved = typedef_method_signatures(full, t, &empty);
            return Some(markup_with_doc(
                render_type_def_with(t, &empty, &resolved),
                t.doc.as_deref(),
                Some(doc.range_of(span)),
            ));
        }
    }

    // A compound expression with nothing more specific under the cursor.
    if let Some(expr) = expr {
        let mut namer = UnknownNamer::default();
        return Some(markup(
            render_type(&expr.ty, &mut namer),
            local_range(doc, full, expr.span),
        ));
    }
    None
}

/// Hover for a value named `name` with resolved type `ty`. A record value shows
/// the type's full member list (slots, fields, and methods, `_`-prefixed ones
/// omitted) with this instance's types resolved -- so a `HashMap` shows the
/// `key`/`value` types it was constructed with. Any other value shows the
/// compact `name: type` form.
fn value_hover(full: &FullAnalysis, name: &str, ty: &Type, range: Option<Range>) -> Hover {
    let mut core = ty;
    while let Type::ConstOf(i) | Type::Mut(i) | Type::Ref(i) | Type::Nullable(i) = core {
        core = i;
    }
    if let Type::Record(n) = core
        && let Some(info) = full.program.type_by_id(n.id)
    {
        let resolved = typedef_method_signatures(full, info, &n.substitution);
        return markup_with_doc(
            render_type_def_with(info, &n.substitution, &resolved),
            info.doc.as_deref(),
            range,
        );
    }
    let mut namer = UnknownNamer::default();
    markup(format!("{name}: {}", render_type(ty, &mut namer)), range)
}

/// Hover for the method name in `recv.method(...)`: the method's signature (its
/// type). Returns `None` unless the cursor sits on an identifier immediately
/// preceded by `.` whose receiver resolves to a record type declaring that method,
/// so plain fields, UFCS free functions, and built-in methods fall through to the
/// general hover paths. The return slot is filled from the enclosing call's
/// inferred result type when present, so an unannotated method return shows its
/// concrete type rather than a bare `unknown_N`.
fn method_hover(doc: &Document, full: &FullAnalysis, local: usize, global: usize) -> Option<Hover> {
    let (name, span) = nav::ident_at(&doc.text, local)?;
    // A member access: a `.` immediately before the name. The receiver expression
    // ends exactly at that `.`.
    let bytes = doc.text.as_bytes();
    if span.lo == 0 || bytes.get(span.lo - 1) != Some(&b'.') {
        return None;
    }
    let recv_hi = full.main_base + (span.lo - 1);
    let recv_ty = receiver_type_at(full, recv_hi)?;
    let sig =
        record_method(full, &recv_ty, &name).or_else(|| primitive_method(full, &recv_ty, &name))?;
    // Resolve the signature against the receiver's instance via the type's scheme:
    // the scheme expresses each method over the type's inferred parameters (the
    // same variables the stored signature names), so matching the scheme's field
    // types to the receiver's resolved fields fixes them. A `HashMap<string,
    // string>` receiver shows `set : (self, string, string) -> void` and `get :
    // (self, key) -> string?` even with no call -- the return is resolved from the
    // instance, not left a bare `unknown_N`.
    let scheme_sig = scheme_resolved_signature(full, &recv_ty, &name, sig);
    // Specialize further to this call's argument types when the cursor is in a
    // call: the receiver is the call's first argument, aligned with `self`, so
    // `map.get(1)` can pin a parameter the scheme leaves open (a key compared with
    // `==` does not unify onto the scheme's parameter).
    let (call_span, ret) = enclosing_call(full, global)
        .map(|e| (Some(e.span), Some(e.ty.clone())))
        .unwrap_or((None, None));
    let call_args = call_span.and_then(|s| nav::call_args_at_span(full, s));
    let specialized = specialize_method_signature(&scheme_sig, call_args.as_deref(), ret.as_ref());
    // Show the inferred `ref`/`mut` passing mode of unannotated parameters
    // (including `self`): a parameter the method body mutates is a private `mut`
    // copy (or a `ref(mut(Self))` receiver), otherwise a `ref` borrow.
    let mutated: Option<Vec<bool>> = method_body(full, &recv_ty, &name).map(|body| {
        specialized
            .params
            .iter()
            .map(|p| prepoly_hir::mutates_root(body, &p.name))
            .collect()
    });
    let rendered = render_signature_into(
        &specialized,
        &[],
        specialized.ret_ty.as_ref(),
        mutated.as_deref(),
        &mut UnknownNamer::default(),
    );
    Some(markup_with_doc(
        rendered,
        method_doc(full, &recv_ty, &name),
        Some(doc.range_of(span)),
    ))
}

/// The doc comment of the method `name` on `recv_ty` -- from the `fun T.m`
/// declaration for a record/sum method, or the stdlib function declaration for
/// a primitive/array method.
fn method_doc<'a>(full: &'a FullAnalysis, recv_ty: &Type, name: &str) -> Option<&'a str> {
    let mut t = recv_ty;
    while let Type::Ref(i) | Type::Mut(i) | Type::ConstOf(i) | Type::Nullable(i) = t {
        t = i;
    }
    if let Type::Record(n) | Type::Sum(n) = t
        && let TypeKind::Record { methods, .. } = &full.program.type_by_id(n.id)?.kind
    {
        return methods.get(name).and_then(|m| m.decl.doc.as_deref());
    }
    let class = t.primitive_class()?;
    let symbol = full
        .program
        .primitive_methods
        .get(&(class.to_string(), name.to_string()))?;
    full.program
        .functions
        .get(symbol)
        .and_then(|f| f.decl.doc.as_deref())
}

/// Resolve `sig` against the receiver's instance using the type's scheme. The
/// scheme's parameters are the same inference variables the stored signature
/// names, so a map from those variables to the receiver's concrete field types
/// (built by matching the scheme's field types to the receiver's resolved field
/// substitution) substitutes directly into the parameters and return. The return
/// is taken from the scheme (the stored signature has none for an unannotated
/// method). Returns a clone of `sig` unchanged when the receiver is not a record
/// with a scheme that declares this method.
fn scheme_resolved_signature(
    full: &FullAnalysis,
    recv_ty: &Type,
    name: &str,
    sig: &CallableSignature,
) -> CallableSignature {
    let Some((nominal, scheme)) = receiver_scheme(full, recv_ty) else {
        return sig.clone();
    };
    let Some(method) = scheme.methods.get(name) else {
        return sig.clone();
    };
    let map = instance_param_map(scheme, nominal);
    let mut out = sig.clone();
    for p in &mut out.params {
        if let Some(t) = p.resolved_ty.as_ref() {
            p.resolved_ty = Some(substitute_vars(t, &map));
        }
    }
    out.ret_ty = Some(substitute_vars(&method.ret, &map));
    out
}

/// Pre-resolve each method's signature for the type-definition view (the
/// member list a type-name or record-value hover shows). Parameter and return
/// types come from the type's scheme -- the co-checked signatures expressed
/// over the type's inferred parameters -- with each scheme parameter mapped to
/// the concrete type the instance `substitution` pins, or, when open, to the
/// declaration's own slot variable so it renders as `Self.<slot>`. The type's
/// own nominal in a parameter or return shows as `Self`. A type without a
/// scheme (or a method the scheme does not know) keeps its stored signature.
fn typedef_method_signatures(
    full: &FullAnalysis,
    info: &TypeInfo,
    substitution: &Substitution,
) -> HashMap<String, CallableSignature> {
    let mut out = HashMap::new();
    let Some(scheme) = full.schemes.get(&info.name) else {
        return out;
    };
    let TypeKind::Record { fields, methods } = &info.kind else {
        return out;
    };
    // Scheme parameter -> display type, layered: the declaration pass aligns
    // each scheme parameter with the declared field position it generalizes (a
    // slot variable, or a declared type); the instance pass then replaces the
    // ones this value pins with their concrete types.
    let mut map: BTreeMap<u32, Type> = BTreeMap::new();
    for (fname, fty) in &scheme.fields {
        let declared = fields
            .iter()
            .find(|f| f.name == *fname)
            .and_then(|f| f.resolved_ty.as_ref());
        if let Some(declared) = declared {
            match_type_vars(fty, declared, &scheme.params, &mut map);
        }
    }
    for (fname, fty) in &scheme.fields {
        if let Some(actual) = substitution.get(fname) {
            match_type_vars(fty, actual, &scheme.params, &mut map);
        }
    }
    for (name, m) in methods {
        let Some(sm) = scheme.methods.get(name) else {
            continue;
        };
        let mut sig = m.signature.clone();
        // The scheme's parameters are positional with the signature's (both
        // carry a leading `self` for instance methods). `self` is left bare.
        // Instantiation can nest a nullable (`?`-wrapped return over a
        // variable pinned to a nullable type); collapse it for display.
        let instantiated =
            |t: &Type| self_ify(collapse_nullable(&substitute_vars(t, &map)), info.id);
        for (i, p) in sig.params.iter_mut().enumerate() {
            if p.name == "self" {
                continue;
            }
            if let Some((_, t)) = sm.params.get(i) {
                p.resolved_ty = Some(instantiated(t));
            }
        }
        sig.ret_ty = Some(instantiated(&sm.ret));
        out.insert(name.clone(), sig);
    }
    out
}

/// Show the type's own nominal as `Self` in its member signatures, seeing
/// through the wrappers a member position can carry.
fn self_ify(ty: Type, own_id: i32) -> Type {
    match ty {
        Type::Record(n) if n.id == own_id => Type::SelfType,
        Type::Nullable(i) => Type::Nullable(Box::new(self_ify(*i, own_id))),
        Type::Slice(i) => Type::Slice(Box::new(self_ify(*i, own_id))),
        Type::Array(i, n) => Type::Array(Box::new(self_ify(*i, own_id)), n),
        other => other,
    }
}

/// The receiver's record nominal and its type's scheme, seeing through
/// reference/mutability/const/nullable wrappers.
fn receiver_scheme<'a>(
    full: &'a FullAnalysis,
    recv_ty: &'a Type,
) -> Option<(&'a NominalType, &'a TypeScheme)> {
    let mut t = recv_ty;
    while let Type::Ref(i) | Type::Mut(i) | Type::ConstOf(i) | Type::Nullable(i) = t {
        t = i;
    }
    let nominal = match t {
        Type::Record(n) => n,
        _ => return None,
    };
    let info = full.program.type_by_id(nominal.id)?;
    full.schemes.get(&info.name).map(|s| (nominal, s))
}

/// Map each scheme parameter to the receiver instance's concrete type, by
/// matching the scheme's field types against the receiver's resolved field
/// substitution (`_entries : _Entry<K, V>[]` vs `_entries : _Entry<string,
/// string>[]` gives `K -> string`, `V -> string`).
fn instance_param_map(scheme: &TypeScheme, recv: &NominalType) -> BTreeMap<u32, Type> {
    let mut map = BTreeMap::new();
    for (fname, fty) in &scheme.fields {
        if let Some(actual) = recv.substitution.get(fname) {
            match_type_vars(fty, actual, &scheme.params, &mut map);
        }
    }
    map
}

/// A copy of `sig` with each unannotated (still-`unknown`) parameter resolved to
/// the corresponding call argument's type and the return to the call's inferred
/// result. `call_args` is positional with `sig.params` (the receiver is the
/// call's first argument, matching the `self` parameter); the `self` slot is left
/// unresolved so it still renders as a bare `self`. Only applied to instance
/// methods (a leading `self`), where the alignment holds.
fn specialize_method_signature(
    sig: &CallableSignature,
    call_args: Option<&[Type]>,
    ret: Option<&Type>,
) -> CallableSignature {
    let mut out = sig.clone();
    let is_instance = out.params.first().is_some_and(|p| p.name == "self");
    if let (true, Some(args)) = (is_instance, call_args) {
        for (i, p) in out.params.iter_mut().enumerate() {
            if p.name == "self" {
                continue;
            }
            let unresolved = p.resolved_ty.as_ref().is_none_or(Type::is_unknown);
            if unresolved && let Some(arg) = args.get(i) {
                p.resolved_ty = Some(arg.clone());
            }
        }
    }
    if let Some(r) = ret
        && out.ret_ty.as_ref().is_none_or(Type::is_unknown)
    {
        out.ret_ty = Some(r.clone());
    }
    out
}

/// The inferred type of the receiver expression ending at global offset `hi` (the
/// widest one, so `foo.bar.method` uses `foo.bar`). Mirrors completion's receiver
/// lookup.
fn receiver_type_at(full: &FullAnalysis, hi: usize) -> Option<Type> {
    full.typed
        .expressions
        .iter()
        .filter(|e| e.span.hi == hi)
        .min_by_key(|e| e.span.lo)
        .map(|e| e.ty.clone())
}

/// The signature of method `name` declared on the record type `recv_ty` resolves
/// to (seeing through reference/mutability/const/nullable wrappers), or `None` if
/// `recv_ty` is not a record or has no such method (e.g. `name` is a field).
fn record_method<'a>(
    full: &'a FullAnalysis,
    recv_ty: &Type,
    name: &str,
) -> Option<&'a CallableSignature> {
    let mut t = recv_ty;
    while let Type::Ref(i) | Type::Mut(i) | Type::ConstOf(i) | Type::Nullable(i) = t {
        t = i;
    }
    let id = match t {
        Type::Record(n) | Type::Sum(n) => n.id,
        _ => return None,
    };
    match &full.program.type_by_id(id)?.kind {
        TypeKind::Record { methods, .. } => methods.get(name).map(|m| &m.signature),
        _ => None,
    }
}

/// The body of the method `name` on `recv_ty` -- a record/sum method or a stdlib
/// primitive method -- used to infer each unannotated parameter's `ref`/`mut`
/// passing mode for display. `None` when the method or its body is not found (an
/// interface method has no body).
fn method_body<'a>(
    full: &'a FullAnalysis,
    recv_ty: &Type,
    name: &str,
) -> Option<&'a prepoly_parser::ast::Block> {
    let mut t = recv_ty;
    while let Type::Ref(i) | Type::Mut(i) | Type::ConstOf(i) | Type::Nullable(i) = t {
        t = i;
    }
    if let Type::Record(n) | Type::Sum(n) = t
        && let TypeKind::Record { methods, .. } = &full.program.type_by_id(n.id)?.kind
    {
        return methods.get(name).and_then(|m| m.decl.body.as_ref());
    }
    let class = t.primitive_class()?;
    let symbol = full
        .program
        .primitive_methods
        .get(&(class.to_string(), name.to_string()))?;
    full.program.functions.get(symbol).map(|f| &f.decl.body)
}

/// The signature of a stdlib method implemented on a primitive/array receiver
/// (`fun string.split`, `fun infer[].slice`), looked up by the receiver's class.
/// `None` when `recv_ty` is not a primitive/array or has no such method.
fn primitive_method<'a>(
    full: &'a FullAnalysis,
    recv_ty: &Type,
    name: &str,
) -> Option<&'a CallableSignature> {
    let mut t = recv_ty;
    while let Type::Ref(i) | Type::Mut(i) | Type::ConstOf(i) | Type::Nullable(i) = t {
        t = i;
    }
    let class = t.primitive_class()?;
    let symbol = full
        .program
        .primitive_methods
        .get(&(class.to_string(), name.to_string()))?;
    full.program.functions.get(symbol).map(|f| &f.signature)
}

/// The innermost call expression covering `global` (the method call the cursor
/// sits in): its span locates the call's arguments and its type is the method's
/// inferred return.
fn enclosing_call(full: &FullAnalysis, global: usize) -> Option<&prepoly_hir::TypedExpr> {
    full.typed
        .expressions
        .iter()
        .filter(|e| matches!(e.kind, TypedExprKind::Call) && nav::contains(e.span, global))
        .min_by_key(|e| e.span.hi - e.span.lo)
}

/// Hover for a free function: its generic signature plus, when the cursor is on
/// a call (`call_args` given), the `unknown_N` bindings that call instantiates
/// (see [`crate::features::signature`]).
fn function_hover(
    full: &FullAnalysis,
    f: &prepoly_hir::FunInfo,
    call_args: Option<Vec<prepoly_hir::Type>>,
    range: Option<Range>,
) -> Hover {
    Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: crate::features::signature::function_markdown(full, f, call_args.as_deref()),
        }),
        range,
    }
}

/// Map a global span back to a document-local range, when it lies in the active
/// file (it always does for an expression the cursor is on).
fn local_range(doc: &Document, full: &FullAnalysis, span: Span) -> Option<Range> {
    let base = full.main_base;
    if span.lo < base {
        return None;
    }
    let lo = span.lo - base;
    let hi = span.hi.saturating_sub(base);
    Some(doc.range_of(Span::new(lo, hi)))
}

/// Wrap rendered text in a Prepoly code block for the hover popup.
fn markup(code: String, range: Option<Range>) -> Hover {
    markup_with_doc(code, None, range)
}

/// Like [`markup`], with the declaration's doc comment (already markdown
/// prose) appended below the code block behind a separator.
fn markup_with_doc(code: String, doc: Option<&str>, range: Option<Range>) -> Hover {
    let mut value = format!("```prepoly\n{code}\n```");
    if let Some(doc) = doc {
        value.push_str(&format!("\n\n---\n\n{doc}"));
    }
    Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value,
        }),
        range,
    }
}
