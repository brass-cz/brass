//! Sequential service wrapper for the wasm batch transport.
//!
//! In the browser the whole LSP exchange is one shot: the client writes the
//! lifecycle handshake, a `did_open`, and the feature request to stdin all at
//! once -- it cannot wait for the `initialize` reply before sending the rest,
//! the way a long-lived editor does. `Server::serve` reads that batch eagerly
//! and turns every message into a handler future up front, and tower-lsp's
//! lifecycle gate decides each request's fate from the server state *at the
//! moment `call` runs*. So without ordering, every message after `initialize`
//! is handled while the server still looks uninitialized and is rejected.
//!
//! [`Sequential`] restores the ordering a waiting client would provide: it
//! defers the inner `call` behind a mutex held across the await, so a message's
//! handler runs -- and reads the server state -- only after the previous
//! message's handler has fully completed. Paired with `concurrency_level(1)`,
//! `initialize` and `did_open` have taken effect before the requests that
//! depend on them.

use std::future::{Future, poll_fn};
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll};

use tokio::sync::Mutex;
use tower_service::Service;

pub struct Sequential<S> {
    inner: Arc<Mutex<S>>,
}

impl<S> Sequential<S> {
    pub fn new(inner: S) -> Self {
        Self {
            inner: Arc::new(Mutex::new(inner)),
        }
    }
}

impl<S, R> Service<R> for Sequential<S>
where
    S: Service<R> + Send + 'static,
    S::Future: Send,
    R: Send + 'static,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = Pin<Box<dyn Future<Output = Result<S::Response, S::Error>> + Send>>;

    /// Always ready: the transport may hand over the next message immediately.
    /// Ordering is enforced per call, under the lock.
    fn poll_ready(&mut self, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, req: R) -> Self::Future {
        let inner = self.inner.clone();
        Box::pin(async move {
            // Holding the guard across the inner await is what serializes the
            // batch: the next message blocks here until this one finishes.
            let mut service = inner.lock().await;
            poll_fn(|cx| service.poll_ready(cx)).await?;
            service.call(req).await
        })
    }
}
