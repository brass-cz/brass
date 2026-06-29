//! Hover: show the type of the expression under the cursor, the signature of a
//! function, or the definition of a type.
//!
//! Function signatures render unannotated parameters and returns as numbered
//! `unknown_N` (see [`crate::render`]), which is the contract for displaying a
//! function type that inference has left partly open.

use prepoly_hir::{CallableSignature, Type, TypeKind, TypedExprKind};
use prepoly_lexer::Span;
use tower_lsp_server::ls_types::{
    Hover, HoverContents, MarkupContent, MarkupKind, Position, Range,
};

use crate::analysis::FullAnalysis;
use crate::document::Document;
use crate::features::nav;
use crate::render::{UnknownNamer, render_signature_full, render_type, render_type_def};

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
                let mut namer = UnknownNamer::default();
                let value = format!("{name}: {}", render_type(&expr.ty, &mut namer));
                return Some(markup(value, local_range(doc, full, expr.span)));
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
            let mut namer = UnknownNamer::default();
            return Some(markup(
                format!("{name}: {}", render_type(&ty, &mut namer)),
                Some(doc.range_of(span)),
            ));
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
            return Some(markup(render_type_def(t), Some(doc.range_of(span))));
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
    let sig = record_method(full, &recv_ty, &name)?;
    let ret = enclosing_call_ty(full, global);
    let rendered = render_signature_full(sig, &[], ret.as_ref());
    Some(markup(rendered, Some(doc.range_of(span))))
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

/// The result type of the innermost call expression covering `global` (the method
/// call the cursor sits in), used as the method's inferred return type.
fn enclosing_call_ty(full: &FullAnalysis, global: usize) -> Option<Type> {
    full.typed
        .expressions
        .iter()
        .filter(|e| matches!(e.kind, TypedExprKind::Call) && nav::contains(e.span, global))
        .min_by_key(|e| e.span.hi - e.span.lo)
        .map(|e| e.ty.clone())
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
    Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```prepoly\n{code}\n```"),
        }),
        range,
    }
}
