//! Convert the front end's message, span, and severity diagnostics into LSP
//! diagnostics ranged in the active document.

use tower_lsp_server::ls_types::{Diagnostic, DiagnosticSeverity};

use crate::analysis::items::{Diag, DiagSeverity};
use crate::document::Document;

/// Map document-local diagnostics to LSP `Diagnostic`s. Spans are already
/// document-local (see [`crate::analysis`]); only the line/column mapping
/// remains.
pub fn to_lsp(diags: &[Diag], doc: &Document) -> Vec<Diagnostic> {
    diags
        .iter()
        .map(|(message, span, severity)| Diagnostic {
            range: doc.range_of(*span),
            severity: Some(match severity {
                DiagSeverity::Error => DiagnosticSeverity::ERROR,
                DiagSeverity::Warning => DiagnosticSeverity::WARNING,
            }),
            source: Some("brass".to_string()),
            message: message.clone(),
            ..Default::default()
        })
        .collect()
}
