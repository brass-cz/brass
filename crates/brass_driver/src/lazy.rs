//! Lazy execution, checker coordination, and performance observations.

mod changed_inputs;
mod channels;
mod demand;
mod eager;
mod frontier;
mod policy;
mod region;
mod resolve;
mod run;
mod scheduler;
mod spawn;
mod state;
#[cfg(test)]
mod tests;
mod trace;
mod verdict;

use channels::MergedChannels;
use eager::finish_eagerly;
use resolve::resolve_deferred;
pub(crate) use run::run_lazy;
use scheduler::{CheckerCleanup, CheckerPause, ThreadScheduler, stop_checker};
use spawn::drain_targets_for_spawn;
use state::{LazyState, demand_loop_progress};
use verdict::{BodySpans, FatalVerdict, exit_if_fatal, judge_fatal};
