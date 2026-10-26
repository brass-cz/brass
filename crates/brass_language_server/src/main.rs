//! The Brass language server.
//!
//! A stdio JSON-RPC LSP server that drives the Brass front end (lex, parse,
//! lower, resolve, type-check) to provide diagnostics, semantic-token
//! highlighting, hover, go-to-definition, completion and formatting. An edit
//! re-parses only; opening or saving a document type-checks it, and that check
//! is incremental: only changed items and their users are re-checked (see
//! [`analysis`]).

mod analysis;
mod backend;
mod document;
mod features;
mod render;
#[cfg(test)]
mod tests;
#[cfg(target_family = "wasm")]
mod wasm_serve;
#[cfg(target_family = "wasm")]
mod wasm_stdio;

use tower_lsp_server::{LspService, Server};

use backend::Backend;

// Async stdin/stdout for the transport. Native uses tokio's `io-std`; wasm,
// where that feature is unavailable, uses the blocking WASI adapters.
#[cfg(not(target_family = "wasm"))]
use tokio::io::{stdin, stdout};
#[cfg(target_family = "wasm")]
use wasm_stdio::{stdin, stdout};

// wasm has no threads, so the server runs on the current-thread runtime there;
// native keeps the default multi-threaded runtime.
#[cfg_attr(not(target_family = "wasm"), tokio::main)]
#[cfg_attr(target_family = "wasm", tokio::main(flavor = "current_thread"))]
async fn main() {
    // Logs go to stderr -- stdout is the LSP transport. Same BRASS_LOG /
    // BRASS_LOG_TYPE switches as the driver.
    brass_utils::init_tracing();
    let (service, socket) = LspService::new(Backend::new);
    let server = Server::new(stdin(), stdout(), socket);

    // The browser client feeds the whole batch (initialize, did_open, the
    // feature request, ...) up front rather than waiting for each reply, so the
    // lifecycle stays correct only if messages are handled strictly in order:
    // the service is serialized and the transport runs one message at a time. A
    // native client already serializes the handshake, so it keeps the default.
    #[cfg(target_family = "wasm")]
    {
        server
            .concurrency_level(1)
            .serve(wasm_serve::Sequential::new(service))
            .await;
    }
    #[cfg(not(target_family = "wasm"))]
    {
        server.serve(service).await;
    }
}
