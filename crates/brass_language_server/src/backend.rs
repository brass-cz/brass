//! The LSP server: glue between the protocol and the analysis layer.
//!
//! One [`DocState`] per open document holds its text and its incremental
//! analyzer. Requests (`hover`, `definition`, `semantic_tokens`) read the
//! analysis; each handler does its synchronous analysis under the document's map
//! entry, then releases it before awaiting the client.
//!
//! Diagnostics are published on `did_open` and `did_save` (the full check) and on
//! `did_change` (SYNTAX ONLY). Type inference re-checks the whole module graph,
//! which is too much work to redo on every keystroke; parsing is cheap, and its
//! errors are the ones worth reporting mid-edit anyway.

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use dashmap::DashMap;
use dashmap::mapref::entry::Entry;
use tower_lsp_server::ls_types::{
    CompletionOptions, CompletionParams, CompletionResponse, Diagnostic,
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    DidSaveTextDocumentParams, DocumentDiagnosticParams, DocumentDiagnosticReport,
    DocumentDiagnosticReportResult, DocumentFormattingParams, FullDocumentDiagnosticReport,
    GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverParams, InitializeParams,
    InitializeResult, InitializedParams, MessageType, OneOf, Position, Range,
    RelatedFullDocumentDiagnosticReport, SemanticTokens, SemanticTokensFullOptions,
    SemanticTokensLegend, SemanticTokensOptions, SemanticTokensParams, SemanticTokensResult,
    SemanticTokensServerCapabilities, ServerCapabilities, ServerInfo, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextDocumentSyncOptions, TextDocumentSyncSaveOptions, TextEdit, Uri,
    WorkDoneProgressOptions,
};
// Advertised only on wasm, where the browser transport pulls diagnostics rather
// than receiving server-pushed ones.
#[cfg(target_family = "wasm")]
use tower_lsp_server::ls_types::{DiagnosticOptions, DiagnosticServerCapabilities};
use tower_lsp_server::{Client, LanguageServer, jsonrpc::Result};

use crate::analysis::DocAnalyzer;
use crate::document::Document;
use crate::features::{self, semantic_tokens};

/// The text and analyzer for one open document.
struct DocState {
    document: Document,
    analyzer: DocAnalyzer,
    /// Identifies one open/close lifetime independently of LSP versions, which
    /// clients may restart when a document is reopened.
    generation: u64,
}

impl DocState {
    fn new(uri: &Uri, text: String, version: i32, generation: u64) -> Self {
        DocState {
            document: Document::new(text, version),
            analyzer: DocAnalyzer::new(uri_to_path(uri)),
            generation,
        }
    }
}

pub struct Backend {
    client: Client,
    docs: DashMap<Uri, DocState>,
    /// Monotonic document-lifetime ids keep stale close/change handlers from
    /// mutating a later open of the same URI.
    next_generation: AtomicU64,
    /// Serializes diagnostic notifications. Document analysis remains
    /// concurrent; only publication is ordered so an older check cannot arrive
    /// after a newer version or after the document was closed.
    diagnostic_publish: tokio::sync::Mutex<()>,
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Backend {
            client,
            docs: DashMap::new(),
            next_generation: AtomicU64::new(1),
            diagnostic_publish: tokio::sync::Mutex::new(()),
        }
    }

    /// Install a freshly opened document and publish its full diagnostics.
    async fn open(&self, uri: Uri, text: String, version: i32) {
        let generation = self.next_generation.fetch_add(1, Ordering::Relaxed);
        let Some(diags) = open_document(&self.docs, &uri, text, version, generation, analyze)
        else {
            return;
        };
        self.publish_current(uri, diags, version, generation).await;
    }

    /// Store a document's new text and publish its syntax diagnostics. The
    /// analysis runs under the map entry; the entry is dropped before publish.
    async fn refresh(&self, uri: Uri, text: String, version: i32, generation: u64) {
        let Some(diags) = update_document(&self.docs, &uri, text, version, generation, |entry| {
            let raw = entry.analyzer.syntax_diagnostics(&entry.document.text);
            features::diagnostics::to_lsp(&raw, &entry.document)
        }) else {
            return;
        };
        self.publish_current(uri, diags, version, generation).await;
    }

    /// Re-publish the current document's full diagnostics, without a new text.
    /// The save notification carries no text under `TextDocumentSyncKind::FULL`.
    async fn recheck(&self, uri: Uri) {
        let Some(diags) = self.docs.get_mut(&uri).map(|mut entry| {
            let version = entry.document.version;
            let generation = entry.generation;
            (analyze(&mut entry), version, generation)
        }) else {
            return;
        };
        self.publish_current(uri, diags.0, diags.1, diags.2).await;
    }

    /// Diagnostics for an already-open document, for the pull
    /// (`textDocument/diagnostic`) path. Unknown documents report nothing.
    fn compute_diagnostics(&self, uri: &Uri) -> Vec<Diagnostic> {
        match self.docs.get_mut(uri) {
            Some(mut entry) => analyze(&mut entry),
            None => Vec::new(),
        }
    }

    async fn publish_current(
        &self,
        uri: Uri,
        diags: Vec<Diagnostic>,
        version: i32,
        generation: u64,
    ) {
        let _publish = self.diagnostic_publish.lock().await;
        if self
            .docs
            .get(&uri)
            .is_none_or(|entry| entry.generation != generation || entry.document.version != version)
        {
            return;
        }
        self.client
            .publish_diagnostics(uri, diags, Some(version))
            .await;
    }

    async fn clear_closed(&self, uri: Uri) {
        let _publish = self.diagnostic_publish.lock().await;
        // A rapid close/reopen may have installed a new document while the
        // close notification waited. Its diagnostics must not be cleared.
        if self.docs.contains_key(&uri) {
            return;
        }
        self.client.publish_diagnostics(uri, Vec::new(), None).await;
    }
}

impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                // `save` must be advertised for the client to send `did_save`, which
                // is when the type check runs (`did_change` only parses).
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(TextDocumentSyncKind::FULL),
                        save: Some(TextDocumentSyncSaveOptions::Supported(true)),
                        ..Default::default()
                    },
                )),
                hover_provider: Some(true.into()),
                definition_provider: Some(OneOf::Left(true)),
                document_formatting_provider: Some(OneOf::Left(true)),
                // `.` continues an import path (`import math.`) and member
                // access; `{` opens an import's name list. Identifier typing
                // triggers completion automatically without a trigger char.
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".to_string(), "{".to_string()]),
                    ..Default::default()
                }),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensOptions(
                        SemanticTokensOptions {
                            work_done_progress_options: WorkDoneProgressOptions::default(),
                            legend: SemanticTokensLegend {
                                token_types: semantic_tokens::TOKEN_TYPES.to_vec(),
                                token_modifiers: semantic_tokens::TOKEN_MODIFIERS.to_vec(),
                            },
                            range: Some(false),
                            full: Some(SemanticTokensFullOptions::Bool(true)),
                        },
                    ),
                ),
                // The browser's one-shot transport cannot receive the
                // server-pushed diagnostics that `did_open`/`did_change`
                // produce, so the wasm build also answers pull diagnostic
                // requests. Native clients keep using the push path.
                #[cfg(target_family = "wasm")]
                diagnostic_provider: Some(DiagnosticServerCapabilities::Options(
                    DiagnosticOptions {
                        identifier: None,
                        inter_file_dependencies: false,
                        workspace_diagnostics: false,
                        work_done_progress_options: WorkDoneProgressOptions::default(),
                    },
                )),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "czls".to_string(),
                version: Some(brass_metadata::version_string().to_string()),
            }),
            ..Default::default()
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "brass language server ready")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    /// Opening a file checks it in full: its type errors must be visible before
    /// the user has touched (and saved) anything.
    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let doc = params.text_document;
        self.open(doc.uri, doc.text, doc.version).await;
    }

    /// An edit re-parses only. The type diagnostics of the last checked version
    /// are cleared rather than left behind: their spans no longer describe this
    /// text, and a stale squiggle under the wrong code is worse than none.
    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        let Some(generation) = self.docs.get(&uri).map(|entry| entry.generation) else {
            return;
        };
        // FULL sync: the single content change carries the whole new text.
        let Some(change) = params.content_changes.into_iter().next() else {
            return;
        };
        self.refresh(uri, change.text, version, generation).await;
    }

    /// Saving runs the type check.
    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        self.recheck(params.text_document.uri).await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        let Some(generation) = self.docs.get(&uri).map(|entry| entry.generation) else {
            return;
        };
        if !close_document(&self.docs, &uri, generation) {
            return;
        }
        // Clear diagnostics for the closed file.
        self.clear_closed(uri).await;
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let pos = params.text_document_position_params.position;
        let uri = params.text_document_position_params.text_document.uri;
        let Some(entry) = self.docs.get(&uri) else {
            return Ok(None);
        };
        // The full analysis holds `Rc` data (`!Send`); it stays a local here and
        // is dropped before this handler ever awaits, so the future stays `Send`.
        let full = entry.analyzer.analyze_full(&entry.document.text);
        Ok(features::hover::hover(&entry.document, &full, pos))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let pos = params.text_document_position_params.position;
        let uri = params.text_document_position_params.text_document.uri;
        let Some(entry) = self.docs.get(&uri) else {
            return Ok(None);
        };
        let full = entry.analyzer.analyze_full(&entry.document.text);
        Ok(
            features::definition::definition(&entry.document, &full, pos)
                .map(GotoDefinitionResponse::Scalar),
        )
    }

    /// Pull diagnostics: the same analysis the push path runs, returned as a
    /// full report so a client that does not get pushed diagnostics (the
    /// browser) can request them.
    async fn diagnostic(
        &self,
        params: DocumentDiagnosticParams,
    ) -> Result<DocumentDiagnosticReportResult> {
        let items = self.compute_diagnostics(&params.text_document.uri);
        Ok(DocumentDiagnosticReportResult::Report(
            DocumentDiagnosticReport::Full(RelatedFullDocumentDiagnosticReport {
                related_documents: None,
                full_document_diagnostic_report: FullDocumentDiagnosticReport {
                    result_id: None,
                    items,
                },
            }),
        ))
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let pos = params.text_document_position.position;
        let uri = params.text_document_position.text_document.uri;
        let Some(entry) = self.docs.get(&uri) else {
            return Ok(None);
        };
        // Completion analyzes the document itself (and, for member access, a
        // probe-spliced variant), so the analyzer is passed in. Any `!Send`
        // analysis it produces stays inside that synchronous call and is dropped
        // before this handler awaits.
        let path = uri_to_path(&uri);
        let items = features::completion::completion(&entry.document, &entry.analyzer, &path, pos);
        Ok(Some(CompletionResponse::Array(items)))
    }

    /// Whole-document formatting. A document with syntax errors returns no
    /// edits (the formatter refuses to rewrite code it cannot fully parse; the
    /// user sees the syntax diagnostics instead), as does an already-formatted
    /// one. Otherwise the reply is a single edit replacing the full text --
    /// simpler than a diff and rendered atomically by clients.
    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let Some(entry) = self.docs.get(&params.text_document.uri) else {
            return Ok(None);
        };
        let text = &entry.document.text;
        let Ok(formatted) = brass_formatter::format_source(text) else {
            return Ok(None);
        };
        if formatted == *text {
            return Ok(Some(Vec::new()));
        }
        let range = Range {
            start: Position::new(0, 0),
            end: entry.document.position_at(text.len()),
        };
        Ok(Some(vec![TextEdit {
            range,
            new_text: formatted,
        }]))
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let uri = params.text_document.uri;
        let Some(entry) = self.docs.get(&uri) else {
            return Ok(None);
        };
        let data = semantic_tokens::tokens(&entry.document.text);
        Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
            result_id: None,
            data,
        })))
    }
}

/// Replace the document only when this open belongs to a newer lifetime. The
/// callback runs while the map entry is locked, so a change cannot observe a
/// half-installed analyzer/document pair.
fn open_document<R>(
    docs: &DashMap<Uri, DocState>,
    uri: &Uri,
    text: String,
    version: i32,
    generation: u64,
    use_state: impl FnOnce(&mut DocState) -> R,
) -> Option<R> {
    match docs.entry(uri.clone()) {
        Entry::Occupied(mut entry) => {
            if entry.get().generation >= generation {
                return None;
            }
            entry.insert(DocState::new(uri, text, version, generation));
            Some(use_state(entry.get_mut()))
        }
        Entry::Vacant(entry) => {
            let mut state = entry.insert(DocState::new(uri, text, version, generation));
            Some(use_state(&mut state))
        }
    }
}

/// Apply a change only to the lifetime it was received for and only when its
/// LSP version advances the installed text.
fn update_document<R>(
    docs: &DashMap<Uri, DocState>,
    uri: &Uri,
    text: String,
    version: i32,
    generation: u64,
    use_state: impl FnOnce(&mut DocState) -> R,
) -> Option<R> {
    let mut state = docs.get_mut(uri)?;
    if state.generation != generation || version <= state.document.version {
        return None;
    }
    state.document.update(text, version);
    Some(use_state(&mut state))
}

/// Remove only the open lifetime observed by the close handler. A reopen that
/// wins the race carries a different generation and remains installed.
fn close_document(docs: &DashMap<Uri, DocState>, uri: &Uri, generation: u64) -> bool {
    docs.remove_if(uri, |_, state| state.generation == generation)
        .is_some()
}

/// Run the incremental analyzer over a document's current text and lower the
/// raw diagnostics to LSP form. Shared by the push and pull diagnostic paths.
fn analyze(state: &mut DocState) -> Vec<Diagnostic> {
    let raw = state.analyzer.diagnostics(&state.document.text);
    features::diagnostics::to_lsp(&raw, &state.document)
}

/// Best-effort filesystem path for a document URI, used to resolve imports
/// relative to the document. A non-`file:` URI falls back to its raw string, so
/// analysis of that document still works (its imports just will not resolve).
fn uri_to_path(uri: &Uri) -> PathBuf {
    uri.to_file_path()
        .map(|p| p.into_owned())
        .unwrap_or_else(|| PathBuf::from(uri.as_str()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn uri() -> Uri {
        "file:///tmp/concurrent.cz".parse().expect("file URI")
    }

    /// Version and generation checks make deliberately reordered operations
    /// leave the newest open lifetime and its newest text installed.
    #[test]
    fn stale_document_operations_are_rejected() {
        let docs = DashMap::new();
        let uri = uri();
        assert!(open_document(&docs, &uri, "new".into(), 1, 2, |_| ()).is_some());
        assert!(open_document(&docs, &uri, "old open".into(), 8, 1, |_| ()).is_none());
        assert!(update_document(&docs, &uri, "version 3".into(), 3, 2, |_| ()).is_some());
        assert!(update_document(&docs, &uri, "version 2".into(), 2, 2, |_| ()).is_none());
        assert!(update_document(&docs, &uri, "old lifetime".into(), 99, 1, |_| ()).is_none());
        assert!(!close_document(&docs, &uri, 1));
        let state = docs.get(&uri).expect("new lifetime remains open");
        assert_eq!(state.document.text, "version 3");
        drop(state);
        assert!(close_document(&docs, &uri, 2));
    }
}
