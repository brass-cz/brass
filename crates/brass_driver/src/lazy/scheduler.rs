//! Checker parking, priority requests, and thread cleanup.

use super::LazyState;
use crate::AnalyzedProgram;

/// The checker-thread half of the streaming wiring: progress events flow out
/// over an unbounded channel (the checker never blocks on a slow consumer),
/// priority requests flow in and are drained between bodies.
pub(super) struct CheckerPause {
    pub(super) paused: std::sync::atomic::AtomicBool,
    pub(super) requests:
        tokio::sync::mpsc::UnboundedSender<Option<Vec<brass_typeck::stream::BodyRequest>>>,
}

impl CheckerPause {
    pub(super) fn request(&self, requests: Vec<brass_typeck::stream::BodyRequest>) {
        if !requests.is_empty() {
            let _ = self.requests.send(Some(requests));
        }
    }

    /// Release a checker parked on the request channel. `None` is a control
    /// wake and never enters the type checker's priority queue.
    pub(super) fn resume(&self) {
        if self
            .paused
            .swap(false, std::sync::atomic::Ordering::Relaxed)
        {
            let _ = self.requests.send(None);
        }
    }

    pub(super) fn is_paused(&self) -> bool {
        self.paused.load(std::sync::atomic::Ordering::Relaxed)
    }
}

/// Ensures every exit after checker startup requests termination and wakes a
/// checker that is waiting for another priority request.
pub(super) struct CheckerCleanup {
    pub(super) stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
    pub(super) paused: std::sync::Arc<CheckerPause>,
}

impl Drop for CheckerCleanup {
    fn drop(&mut self) {
        self.stop.store(true, std::sync::atomic::Ordering::Relaxed);
        self.paused.resume();
    }
}

pub(super) struct ThreadScheduler {
    /// Request context-pass metadata only for the automatic completion policy.
    pub(super) completion_observations: bool,
    pub(super) events: tokio::sync::mpsc::UnboundedSender<brass_typeck::stream::CheckEvent>,
    pub(super) requests:
        tokio::sync::mpsc::UnboundedReceiver<Option<Vec<brass_typeck::stream::BodyRequest>>>,
    /// Set by the driver when the program ends: the checker stops at the
    /// next body boundary instead of finishing code nothing will run.
    pub(super) stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
    /// Set while the driver is settling its entry (gate + start-up demands):
    /// the checker serves only requested bodies, so no demand ever waits for
    /// a definitional pass the queue happened to start first. Cleared when
    /// execution begins.
    pub(super) paused: std::sync::Arc<CheckerPause>,
    pub(super) requests_closed: bool,
}

impl brass_typeck::stream::Scheduler for ThreadScheduler {
    fn completion_observations(&self) -> bool {
        self.completion_observations
    }
    fn drain_requests(&mut self) -> Vec<brass_typeck::stream::BodyRequest> {
        let mut out = Vec::new();
        while let Ok(request) = self.requests.try_recv() {
            out.extend(request.into_iter().flatten());
        }
        out
    }

    fn wait_for_requests(&mut self) -> Vec<brass_typeck::stream::BodyRequest> {
        let mut out = Vec::new();
        match self.requests.blocking_recv() {
            Some(request) => out.extend(request.into_iter().flatten()),
            None => self.requests_closed = true,
        }
        out.extend(self.drain_requests());
        out
    }

    fn emit(&mut self, event: brass_typeck::stream::CheckEvent) {
        // A dropped receiver means the consumer stopped listening (it
        // aborted); checking still finishes for the thread's final result.
        let _ = self.events.send(event);
    }

    fn stopped(&self) -> bool {
        self.stop.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn paused(&self) -> bool {
        !self.requests_closed && self.paused.is_paused()
    }
}

/// Stop the checker and reclaim its thread. The stop flag is polled at body
/// boundaries, so the join is bounded by the body in flight; the drain runs
/// the event channel to close so the join never waits on a full buffer.
pub(super) fn stop_checker(
    rt: &tokio::runtime::Runtime,
    checker: tokio::task::JoinHandle<Result<AnalyzedProgram, Vec<String>>>,
    lazy: &mut LazyState,
) {
    lazy.stop.store(true, std::sync::atomic::Ordering::Relaxed);
    lazy.resume_background();
    while !lazy.closed {
        lazy.pump_blocking();
    }
    let _ = rt
        .block_on(checker)
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic.into_panic()));
}
