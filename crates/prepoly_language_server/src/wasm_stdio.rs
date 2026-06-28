//! Blocking stdin/stdout adapters for the wasm build.
//!
//! tokio's async `io-std` (`tokio::io::stdin`/`stdout`) is unavailable on a wasm
//! target, so the JSON-RPC transport is backed by the standard library's
//! synchronous WASI stdio instead. Under the browser shim the host feeds the
//! whole request buffer up front and then signals EOF, so a "blocking" read
//! returns immediately -- there is nothing to await -- and a write goes straight
//! to the captured stdout. These adapters therefore satisfy tokio's async I/O
//! traits by performing the blocking call directly inside `poll_*`, which the
//! current-thread runtime drives to completion in a couple of polls.

use std::io::{Read, Write};
use std::pin::Pin;
use std::task::{Context, Poll};

use tokio::io::{AsyncRead, AsyncWrite, ReadBuf};

pub struct Stdin(std::io::Stdin);
pub struct Stdout(std::io::Stdout);

/// The process stdin as a tokio `AsyncRead`. Mirrors `tokio::io::stdin`.
pub fn stdin() -> Stdin {
    Stdin(std::io::stdin())
}

/// The process stdout as a tokio `AsyncWrite`. Mirrors `tokio::io::stdout`.
pub fn stdout() -> Stdout {
    Stdout(std::io::stdout())
}

impl AsyncRead for Stdin {
    fn poll_read(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<std::io::Result<()>> {
        // WASI stdin yields the available bytes, then 0 (EOF); a short read of 0
        // is how the framed-message stream terminates and the server exits.
        let n = match self.0.read(buf.initialize_unfilled()) {
            Ok(n) => n,
            Err(e) => return Poll::Ready(Err(e)),
        };
        buf.advance(n);
        Poll::Ready(Ok(()))
    }
}

impl AsyncWrite for Stdout {
    fn poll_write(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<std::io::Result<usize>> {
        Poll::Ready(self.0.write(buf))
    }

    fn poll_flush(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<std::io::Result<()>> {
        Poll::Ready(self.0.flush())
    }

    fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<std::io::Result<()>> {
        self.poll_flush(cx)
    }
}
