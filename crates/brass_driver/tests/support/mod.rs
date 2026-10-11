//! Driver subprocess configuration shared by integration tests.

use std::ffi::OsStr;
use std::path::Path;
use std::process::Command;

/// Keeps native object caching inside Cargo's test scratch directory, including
/// subprocesses launched by Brass programs. Tests may override this location
/// when they need to inspect a fresh store. The directory is shared by every
/// test process and run, so the store's size cap bounds it and later runs
/// exercise cache hits the way repeated user runs do. `NO_COLOR` keeps
/// `BRASS_LOG` output free of ANSI escapes (the log subscriber colors even a
/// pipe), so tests can match `field=value` text in any environment.
pub fn brass_command(binary: impl AsRef<OsStr>) -> Command {
    let mut command = Command::new(binary);
    command
        .env(
            "XDG_CACHE_HOME",
            Path::new(env!("CARGO_TARGET_TMPDIR")).join("jit-cache-tests"),
        )
        .env("NO_COLOR", "1");
    command
}
