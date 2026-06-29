//! The LSP server: glue between the protocol and the analysis layer.
//!
//! One [`DocState`] per open document holds its text and its incremental
//! analyzer. Notifications (`did_open`/`did_change`) re-run diagnostics and
//! publish them; requests (`hover`, `definition`, `semantic_tokens`) read the
//! cached analysis. Each handler does its synchronous analysis under the
//! document's map entry, then releases it before awaiting the client.

use std::path::PathBuf;

use dashmap::DashMap;
use tower_lsp_server::ls_types::{
    CompletionOptions, CompletionParams, CompletionResponse, Diagnostic,
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    DocumentDiagnosticParams, DocumentDiagnosticReport, DocumentDiagnosticReportResult,
    FullDocumentDiagnosticReport, GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverParams,
    InitializeParams, InitializeResult, InitializedParams, MessageType, OneOf,
    RelatedFullDocumentDiagnosticReport, SemanticTokens, SemanticTokensFullOptions,
    SemanticTokensLegend, SemanticTokensOptions, SemanticTokensParams, SemanticTokensResult,
    SemanticTokensServerCapabilities, ServerCapabilities, ServerInfo, TextDocumentSyncCapability,
    TextDocumentSyncKind, Uri, WorkDoneProgressOptions,
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
}

impl DocState {
    fn new(uri: &Uri, text: String, version: i32) -> Self {
        DocState {
            document: Document::new(text, version),
            analyzer: DocAnalyzer::new(uri_to_path(uri)),
        }
    }
}

pub struct Backend {
    client: Client,
    docs: DashMap<Uri, DocState>,
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Backend {
            client,
            docs: DashMap::new(),
        }
    }

    /// Re-analyze a document and publish its diagnostics. The analysis runs
    /// under the map entry; the entry is dropped before the async publish.
    async fn refresh(&self, uri: Uri, text: String, version: i32) {
        let diags = {
            let mut entry = self
                .docs
                .entry(uri.clone())
                .or_insert_with(|| DocState::new(&uri, String::new(), version));
            entry.document.update(text, version);
            analyze(&mut entry)
        };
        self.publish(uri, diags, version).await;
    }

    /// Diagnostics for an already-open document, for the pull
    /// (`textDocument/diagnostic`) path. Unknown documents report nothing.
    fn compute_diagnostics(&self, uri: &Uri) -> Vec<Diagnostic> {
        match self.docs.get_mut(uri) {
            Some(mut entry) => analyze(&mut entry),
            None => Vec::new(),
        }
    }

    async fn publish(&self, uri: Uri, diags: Vec<Diagnostic>, version: i32) {
        self.client
            .publish_diagnostics(uri, diags, Some(version))
            .await;
    }
}

impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(true.into()),
                definition_provider: Some(OneOf::Left(true)),
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
                name: "prepoly-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
            ..Default::default()
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "prepoly language server ready")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let doc = params.text_document;
        self.refresh(doc.uri, doc.text, doc.version).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        // FULL sync: the single content change carries the whole new text.
        let Some(change) = params.content_changes.into_iter().next() else {
            return;
        };
        self.refresh(uri, change.text, version).await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.docs.remove(&params.text_document.uri);
        // Clear diagnostics for the closed file.
        self.publish(params.text_document.uri.clone(), Vec::new(), 0)
            .await;
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let pos = params.text_document_position_params.position;
        let uri = params.text_document_position_params.text_document.uri;
        let Some(entry) = self.docs.get(&uri) else {
            return Ok(None);
        };
        // The full analysis holds `Rc` data (`!Send`); it stays a local here and
        // is dropped before this handler ever awaits, so the future stays `Send`.
        let Some(full) = entry.analyzer.analyze_full(&entry.document.text) else {
            return Ok(None);
        };
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
        let Some(full) = entry.analyzer.analyze_full(&entry.document.text) else {
            return Ok(None);
        };
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
        let items =
            features::completion::completion(&entry.document, &entry.analyzer, &path, pos);
        Ok(Some(CompletionResponse::Array(items)))
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
