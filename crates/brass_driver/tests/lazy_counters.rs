//! Counter contracts on an empty entry and a chain crossing the depth cap.

#![cfg(feature = "jit")]

mod support;

use std::fs;
use std::path::PathBuf;
use std::process::Output;

struct Fixture(PathBuf);

impl Fixture {
    fn new(name: &str, source: &str) -> Self {
        let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("lazy-counters-{}-{name}", std::process::id()));
        fs::create_dir_all(&root).expect("create fixture");
        fs::write(root.join("main.cz"), source).expect("write fixture");
        Self(root)
    }

    fn run(&self, check: bool, traced: bool) -> Output {
        let mut command = support::brass_command(env!("CARGO_BIN_EXE_brass"));
        command
            .env_remove("BRASS_LOG_TYPE")
            .env_remove("BRASS_MEMO_CHECK")
            .env(
                "BRASS_LOG",
                if traced { "brass::perf=debug" } else { "off" },
            )
            .env("BRASS_JIT_CACHE", "off");
        if check {
            command.arg("check");
        }
        let output = command.arg(self.0.join("main.cz")).output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        output
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn count(line: &str, field: &str) -> u64 {
    line.split_whitespace()
        .find_map(|word| word.strip_prefix(&format!("{field}=")))
        .unwrap_or_else(|| panic!("missing {field}: {line}"))
        .parse()
        .unwrap()
}

fn assert_counts(line: &str, expected: &[(&str, u64)]) {
    for (field, value) in expected {
        assert_eq!(count(line, field), *value, "{field}: {line}");
    }
}

fn verify(fixture: &Fixture, chain: bool) {
    let completing = chain && std::env::var("BRASS_LAZY_COMPLETE").as_deref() != Ok("off");
    // The last checker summary belongs to the entry analysis, after the
    // separate context-only analysis of the implicit core library.
    let checked = fixture.run(true, true);
    let check_log = String::from_utf8_lossy(&checked.stderr);
    let summary = check_log
        .lines()
        .rfind(|line| line.contains("check: summary"))
        .expect("entry checker summary");
    assert_counts(
        summary,
        &[
            ("memo_hits", if chain { 69 } else { 0 }),
            ("memo_misses", if chain { 135 } else { 0 }),
            ("cap_hits", u64::from(chain)),
            ("co_walks", 0),
            ("co_hits", 0),
            ("co_misses", 0),
            ("elaborations", if chain { 134 } else { 0 }),
            // Core-only inputs use genuine complete context coverage.
            ("dedicated_passes", if chain { 72 } else { 1 }),
        ],
    );

    let traced = fixture.run(false, true);
    let quiet = fixture.run(false, false);
    assert_eq!(traced.status, quiet.status);
    assert_eq!(traced.stdout, quiet.stdout);
    assert_eq!(quiet.stdout, if chain { &b"1\n"[..] } else { &b""[..] });
    assert!(quiet.stderr.is_empty());
    let log = String::from_utf8_lossy(&traced.stderr);
    let summaries: Vec<_> = log
        .lines()
        .filter(|line| line.contains("lazy: summary"))
        .collect();
    assert_eq!(summaries.len(), 2, "{log}");
    assert!(summaries[0].contains("phase=\"startup\""));
    assert!(summaries[1].contains("phase=\"final\""));
    assert_counts(
        summaries[0],
        &[
            ("demand_batches", if chain { 3 } else { 1 }),
            ("demanded_bodies", if chain { 2 } else { 0 }),
            ("mono_passes", if chain { 5 } else { 3 }),
            ("channel_refreshes", if chain { 5 } else { 3 }),
            ("lowering_appends", if chain { 2 } else { 1 }),
            ("lowering_rebuilds", 1),
            ("runtime_resolves", 0),
        ],
    );
    // Completed contracts defer six more bodies until execution; all 72
    // bodies are still lowered exactly once. Background scheduling can
    // satisfy runtime demands before they send
    // requests. The actual mono, lowering and resolve counts remain fixed.
    assert_counts(
        summaries[1],
        &[
            (
                "demand_batches",
                if completing {
                    35
                } else if chain {
                    73
                } else {
                    1
                },
            ),
            (
                "mono_passes",
                if completing {
                    37
                } else if chain {
                    75
                } else {
                    3
                },
            ),
            (
                "channel_refreshes",
                if completing {
                    37
                } else if chain {
                    75
                } else {
                    3
                },
            ),
            ("lowering_appends", if chain { 72 } else { 1 }),
            ("lowering_rebuilds", 1),
            (
                "runtime_resolves",
                if completing {
                    32
                } else if chain {
                    70
                } else {
                    0
                },
            ),
        ],
    );
    if completing {
        assert!(
            log.contains("lazy: policy complete phase=\"runtime\" resolves=32 bodies=71"),
            "{log}"
        );
    } else {
        assert!(!log.contains("lazy: policy completing"), "{log}");
    }
}

#[test]
fn trivial_main_counters() {
    verify(&Fixture::new("trivial", "fun main() {}\n"), false);
}

#[test]
fn chain_beyond_depth_cap_counters() {
    let source = (0..70)
        .map(|i| format!("fun f{i}() {{ return f{}() }}\n", i + 1))
        .collect::<String>()
        + "fun f70() { return 1 }\nfun main() { println(f0()) }\n";
    verify(&Fixture::new("chain", &source), true);
}

#[test]
fn runtime_missing_bodies_share_one_batch() {
    // Closure callees cannot defer: the runtime root reports both missing
    // bodies in one mono stop. Settling them separately adds a fourth batch.
    let fixture = Fixture::new(
        "runtime-batch",
        "fun a() -> int32 { return 1 }\n\
         fun b() -> int32 { return 2 }\n\
         fun entry() -> int32 {\n\
             let f = () -> {\n\
                 let x = a()\n\
                 let y = b()\n\
                 return x + y\n\
             }\n\
             return f()\n\
         }\n\
         fun main() { println(entry()) }\n",
    );
    let traced = fixture.run(false, true);
    let quiet = fixture.run(false, false);
    assert_eq!(traced.status, quiet.status);
    assert_eq!(traced.stdout, b"3\n");
    assert_eq!(traced.stdout, quiet.stdout);
    assert!(quiet.stderr.is_empty());
    let log = String::from_utf8_lossy(&traced.stderr);
    let summaries: Vec<_> = log
        .lines()
        .filter(|line| line.contains("lazy: summary"))
        .collect();
    assert_eq!(summaries.len(), 2);
    assert_counts(
        summaries[0],
        &[
            ("demand_batches", 1),
            ("demanded_bodies", 0),
            ("mono_passes", 3),
            ("channel_refreshes", 3),
            ("lowering_appends", 1),
            ("lowering_rebuilds", 1),
            ("runtime_resolves", 0),
        ],
    );
    assert_counts(
        summaries[1],
        &[
            ("demand_batches", 3),
            ("mono_passes", 5),
            ("channel_refreshes", 5),
            ("lowering_appends", 4),
            ("lowering_rebuilds", 1),
            ("runtime_resolves", 1),
        ],
    );
}
