//! Hover: show the type of the expression under the cursor, the signature of a
//! function, or the definition of a type.
//!
//! Function signatures render unannotated parameters and returns as numbered
//! `unknown_N` (see [`crate::render`]), which is the contract for displaying a
//! function type that inference has left partly open.

use prepoly_hir::TypedExprKind;
use prepoly_lexer::Span;
use tower_lsp_server::ls_types::{
    Hover, HoverContents, MarkupContent, MarkupKind, Position, Range,
};

use crate::analysis::FullAnalysis;
use crate::document::Document;
use crate::features::nav;
use crate::render::{UnknownNamer, render_signature_with, render_type, render_type_def};

/// Build the hover response for `pos` in `doc`, using the full analysis.
pub fn hover(doc: &Document, full: &FullAnalysis, pos: Position) -> Option<Hover> {
    let local = doc.offset_at(pos);
    let global = local + full.main_base;
    let module = vec!["main".to_string()];

    // Prefer the tightest typed expression: it gives the precise inferred type
    // of whatever subexpression the cursor sits on.
    if let Some(expr) = nav::smallest_typed_at(full, global) {
        match &expr.kind {
            TypedExprKind::Ident(name) => {
                // A bare name that resolves to a function is best shown as its
                // signature (with parameter names); otherwise show its type.
                if let Some(f) = full.program.resolve_function(&module, name) {
                    return Some(markup(
                        function_signature(full, f),
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
            _ => {
                // The tightest typed node is a compound expression (call, match,
                // if-let, block, ...). If the cursor is on an identifier within
                // it -- a callee, a constructor, or a pattern binding that has no
                // typed node of its own -- resolve that identifier; otherwise
                // show the whole expression's type.
                if let Some(h) = ident_hover(doc, full, local, global, &module) {
                    return Some(h);
                }
                let mut namer = UnknownNamer::default();
                return Some(markup(
                    render_type(&expr.ty, &mut namer),
                    local_range(doc, full, expr.span),
                ));
            }
        }
    }

    // No typed expression here: the cursor may be on a local binding's
    // declaration, a type annotation, or a declaration name.
    ident_hover(doc, full, local, global, &module)
}

/// Resolve the identifier under the cursor for hover: a local variable (its
/// `let`/parameter/loop/pattern binding has no typed node of its own) shows its
/// inferred type and shadows any same-named symbol; then a function shows its
/// signature, and a type its definition.
fn ident_hover(
    doc: &Document,
    full: &FullAnalysis,
    local: usize,
    global: usize,
    module: &[String],
) -> Option<Hover> {
    let (name, span) = nav::ident_at(&doc.text, local)?;
    if let Some(ty) = nav::local_var_type(full, global, &name) {
        let mut namer = UnknownNamer::default();
        return Some(markup(
            format!("{name}: {}", render_type(&ty, &mut namer)),
            Some(doc.range_of(span)),
        ));
    }
    if let Some(f) = full.program.resolve_function(module, &name) {
        return Some(markup(
            function_signature(full, f),
            Some(doc.range_of(span)),
        ));
    }
    if let Some(t) = full.program.resolve_type(module, &name) {
        return Some(markup(render_type_def(t), Some(doc.range_of(span))));
    }
    None
}

/// Render a free function's signature for hover, filling an unannotated return
/// type with the type inference recovered from its call sites.
fn function_signature(full: &FullAnalysis, f: &prepoly_hir::FunInfo) -> String {
    let inferred = if f.signature.ret_ty.is_none() {
        nav::inferred_return(full, &f.signature.name)
    } else {
        None
    };
    render_signature_with(&f.signature, inferred.as_ref())
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
