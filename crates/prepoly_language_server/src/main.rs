//! The Prepoly language server.
//!
//! A stdio JSON-RPC LSP server that drives the Prepoly front end (lex, parse,
//! lower, resolve, type-check) to provide diagnostics, semantic-token
//! highlighting, hover types, and go-to-definition. The heavy path -- per-edit
//! diagnostics -- is incremental: only changed items and their users are
//! re-checked (see [`analysis`]).

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

use std::io;

use tower_lsp_server::{LspService, Server};

use backend::Backend;

// Async stdin/stdout for the transport. Native uses tokio's `io-std`; wasm,
// where that feature is unavailable, uses the blocking WASI adapters.
#[cfg(not(target_family = "wasm"))]
use tokio::io::{stdin, stdout};
#[cfg(target_family = "wasm")]
use wasm_stdio::{stdin, stdout};

/// Send the compiler/server's own logs to stderr; stdout is the LSP transport.
/// Controlled by `PREPOLY_LOG` (the same variable the driver uses), defaulting
/// to warnings only.
fn init_tracing() {
    use tracing_subscriber::filter::LevelFilter;
    let filter = tracing_subscriber::EnvFilter::builder()
        .with_default_directive(LevelFilter::WARN.into())
        .with_env_var("PREPOLY_LOG")
        .from_env_lossy();
    let _ = tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_writer(io::stderr)
        .without_time()
        .try_init();
}

// wasm has no threads, so the server runs on the current-thread runtime there;
// native keeps the default multi-threaded runtime.
#[cfg_attr(not(target_family = "wasm"), tokio::main)]
#[cfg_attr(target_family = "wasm", tokio::main(flavor = "current_thread"))]
async fn main() {
    init_tracing();
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
