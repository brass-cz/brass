//! Priority-batch barriers, including requests overtaken by background work.

use super::{BodyId, BodyRequest, ChannelDelta, CheckEvent, Scheduler};
use crate::analyze_streaming;

#[derive(Default)]
struct Recorder {
    requests: Vec<BodyRequest>,
    after_a: Vec<BodyRequest>,
    events: Vec<CheckEvent>,
    paused: bool,
    stopped: bool,
    stop_after_a: bool,
    seals: usize,
    stop_after_seals: usize,
    waits: usize,
}

impl Scheduler for Recorder {
    fn drain_requests(&mut self) -> Vec<BodyRequest> {
        std::mem::take(&mut self.requests)
    }

    fn wait_for_requests(&mut self) -> Vec<BodyRequest> {
        self.waits += 1;
        self.stopped = true;
        self.drain_requests()
    }

    fn emit(&mut self, event: CheckEvent) {
        if matches!(&event, CheckEvent::BodyChecked(BodyId::Function(name), _) if name == "a") {
            self.requests.append(&mut self.after_a);
            self.stopped |= self.stop_after_a;
        }
        if delta(&event).is_some_and(|d| d.settles_batch.is_some()) {
            self.seals += 1;
            self.stopped |= self.seals == self.stop_after_seals;
        }
        self.events.push(event);
    }

    fn paused(&self) -> bool {
        self.paused
    }
    fn stopped(&self) -> bool {
        self.stopped
    }
}

fn delta(event: &CheckEvent) -> Option<&ChannelDelta> {
    match event {
        CheckEvent::StaticChecked(_) | CheckEvent::ContextChecked(_) => None,
        CheckEvent::ContextReady(d)
        | CheckEvent::BodyChecked(_, d)
        | CheckEvent::BatchSettled(d)
        | CheckEvent::Finished(d, _)
        | CheckEvent::KeyedReady(_, _, d) => Some(d),
    }
}

fn request(symbol: &str, batch: u64) -> BodyRequest {
    BodyRequest {
        symbol: symbol.into(),
        type_args: vec![],
        batch,
    }
}

fn run(rec: &mut Recorder) {
    let program = super::tests::lower(
        "let top = 1\nfun main() {}\nfun a() { return 1 }\nfun b() { return 2 }\nfun z() {}\n",
    );
    analyze_streaming(&program, None, rec);
    assert!(matches!(
        rec.events.first(),
        Some(CheckEvent::StaticChecked(_))
    ));
    let context = rec
        .events
        .iter()
        .position(|e| matches!(e, CheckEvent::ContextReady(_)))
        .unwrap();
    let init = rec
        .events
        .iter()
        .position(|e| matches!(e, CheckEvent::BodyChecked(BodyId::Init(0), _)))
        .unwrap();
    let body = rec
        .events
        .iter()
        .position(|e| matches!(e, CheckEvent::BodyChecked(BodyId::Function(_), _)))
        .unwrap();
    assert!(context < init && init < body);
    assert!(matches!(
        rec.events.last(),
        Some(CheckEvent::Finished(_, _))
    ));
}

fn seals(rec: &Recorder) -> Vec<u64> {
    rec.events
        .iter()
        .filter_map(delta)
        .filter_map(|d| d.settles_batch)
        .collect()
}

#[test]
fn seal_carries_all_members_effects_and_preserves_send_order() {
    let mut rec = Recorder {
        requests: vec![request("a", 10), request("b", 10)],
        // Arrives during the first batch; cannot overtake its seal. The
        // duplicate in that batch must not swallow its only final delta.
        after_a: vec![request("b", 11), request("a", 11), request("missing", 12)],
        paused: true,
        stop_after_seals: 3,
        ..Recorder::default()
    };
    run(&mut rec);
    assert_eq!(seals(&rec), [10, 11, 12]);
    let a = rec
        .events
        .iter()
        .find_map(|e| match e {
            CheckEvent::BodyChecked(BodyId::Function(name), d) if name == "a" => Some(d),
            _ => None,
        })
        .unwrap();
    assert!(
        a.is_empty(),
        "intermediate body cannot publish a partial batch"
    );
    let sealed = rec
        .events
        .iter()
        .filter_map(delta)
        .find(|d| d.settles_batch == Some(10))
        .unwrap();
    let mut names: Vec<_> = sealed
        .instance_returns
        .iter()
        .map(|(name, _, _)| name.as_str())
        .collect();
    names.sort_unstable();
    assert_eq!(names, ["a", "b"]);
    for id in [11, 12] {
        let mut d = rec
            .events
            .iter()
            .filter_map(delta)
            .find(|d| d.settles_batch == Some(id))
            .unwrap()
            .clone();
        assert!(!d.is_empty());
        d.settles_batch = None;
        assert!(d.is_empty(), "a stale-only seal needs no other content");
    }
    assert_eq!(rec.waits, 0, "pause must not interrupt a received batch");
}

#[test]
fn background_checked_member_still_gets_one_seal() {
    let mut rec = Recorder {
        // a finishes in the background before its request is received.
        after_a: vec![request("a", 20), request("b", 20), request("a", 21)],
        stop_after_seals: 2,
        ..Recorder::default()
    };
    run(&mut rec);
    assert_eq!(seals(&rec), [20, 21]);
    for symbol in ["a", "b"] {
        assert_eq!(
            rec.events
                .iter()
                .filter(|e| matches!(e,
            CheckEvent::BodyChecked(BodyId::Function(name), _) if name == symbol))
                .count(),
            1
        );
    }
}

#[test]
fn duplicate_final_member_publishes_the_cumulative_delta() {
    let mut rec = Recorder {
        requests: vec![request("a", 30), request("b", 30), request("a", 30)],
        paused: true,
        stop_after_seals: 1,
        ..Recorder::default()
    };
    run(&mut rec);
    assert_eq!(seals(&rec), [30]);
    assert!(rec.events.iter().any(|event| matches!(event,
        CheckEvent::BatchSettled(d) if d.settles_batch == Some(30) && d.instance_returns.len() == 2)));
}

#[test]
fn stop_mid_batch_finishes_received_requests_before_finished() {
    let mut rec = Recorder {
        requests: vec![request("a", 40), request("b", 40)],
        paused: true,
        stop_after_a: true,
        ..Recorder::default()
    };
    run(&mut rec);
    assert_eq!(seals(&rec), [40]);
    assert!(!rec.events.iter().any(|e| matches!(e,
        CheckEvent::BodyChecked(BodyId::Function(name), _) if name == "z")));
    assert_eq!(rec.waits, 0);
}

#[test]
fn a_paused_checker_finishes_after_all_background_entries_are_retired() {
    let mut rec = Recorder {
        requests: ["a", "b", "z", "main"]
            .map(|symbol| request(symbol, 50))
            .to_vec(),
        paused: true,
        ..Recorder::default()
    };
    run(&mut rec);
    assert_eq!(seals(&rec), [50]);
    assert_eq!(rec.waits, 0, "a completed background queue must not park");
    assert!(
        !rec.stopped,
        "Finished needs no stop request after the last body"
    );
}
