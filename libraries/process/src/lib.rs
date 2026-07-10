//! Spawning and controlling OS processes, as a native Prepoly plugin.
//!
//! `libraries/process.pp` builds the `Command`/`Stdio`/`Child` surface on
//! these four primitives. A spawned child sits in a process-wide table keyed
//! by an `i64` handle; a piped standard stream leaves as a raw descriptor,
//! which the Prepoly side adopts as a `File` so the ordinary read/write/close
//! methods drive it.
//!
//! Stdio modes are the small integers `process.pp` translates its `Stdio`
//! variants to: 0 = inherit, 1 = pipe, 2 = null.

use std::collections::HashMap;
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Mutex, OnceLock};

use prepoly_plugin::{PrepolyLib, Registry, decl, export, prepoly_lib};

/// Live spawned children by handle. A child is removed on `wait`; its piped
/// streams are taken out (once each) by `take_stream`.
fn table() -> &'static Mutex<HashMap<i64, Child>> {
    static TABLE: OnceLock<Mutex<HashMap<i64, Child>>> = OnceLock::new();
    TABLE.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Translate a stdio mode integer (see the module comment) into the Rust
/// configuration; an unknown value is treated as inherit.
fn stdio(mode: i64) -> Stdio {
    match mode {
        1 => Stdio::piped(),
        2 => Stdio::null(),
        _ => Stdio::inherit(),
    }
}

/// The exit code for a process with no ordinary exit code (killed by a
/// signal): the negated signal number on Unix, or -1 elsewhere.
#[cfg(unix)]
fn signal_code(status: &std::process::ExitStatus) -> i32 {
    use std::os::unix::process::ExitStatusExt;
    status.signal().map(|s| -s).unwrap_or(-1)
}

#[cfg(not(unix))]
fn signal_code(_status: &std::process::ExitStatus) -> i32 {
    -1
}

export! {
    /// Spawn `program` (looked up on `PATH`) with `args`, connecting each
    /// standard stream by its mode (0 = inherit, 1 = pipe, 2 = null).
    /// Returns a handle to the running child.
    fn process_spawn(
        program: String,
        args: Vec<String>,
        stdin: i64,
        stdout: i64,
        stderr: i64,
    ) -> Result<i64, String> {
        let child = Command::new(&program)
            .args(&args)
            .stdin(stdio(stdin))
            .stdout(stdio(stdout))
            .stderr(stdio(stderr))
            .spawn()
            .map_err(|e| e.to_string())?;
        static NEXT: AtomicI64 = AtomicI64::new(1);
        let handle = NEXT.fetch_add(1, Ordering::Relaxed);
        table()
            .lock()
            .map_err(|_| "process table is poisoned".to_string())?
            .insert(handle, child);
        Ok(handle)
    }

    /// Take the child's piped standard stream `which` (0 = stdin, 1 = stdout,
    /// 2 = stderr) and return its raw descriptor. Available once, and only
    /// when that stream was configured as a pipe.
    fn process_stream(child: i64, which: i64) -> Result<i64, String> {
        let mut table = table()
            .lock()
            .map_err(|_| "process table is poisoned".to_string())?;
        let child = table
            .get_mut(&child)
            .ok_or("no such child process (already waited?)")?;
        let fd = match which {
            0 => child.stdin.take().map(into_fd),
            1 => child.stdout.take().map(into_fd),
            2 => child.stderr.take().map(into_fd),
            other => return Err(format!("no standard stream {other}")),
        };
        fd.ok_or_else(|| "stream is not piped or already taken".to_string())
    }

    /// Block until the child exits, returning its exit code (the signal
    /// number negated on a Unix signal death) and forgetting the child.
    fn process_wait(child: i64) -> Result<i64, String> {
        let removed = table()
            .lock()
            .map_err(|_| "process table is poisoned".to_string())?
            .remove(&child);
        let mut child = removed.ok_or("no such child process (already waited?)")?;
        let status = child.wait().map_err(|e| e.to_string())?;
        let code = status.code().unwrap_or_else(|| signal_code(&status));
        Ok(i64::from(code))
    }
}

/// A piped stream's descriptor, given up by the child. The Prepoly side owns
/// it from here (it adopts it as a `File`, whose `close` closes it).
#[cfg(unix)]
fn into_fd(stream: impl std::os::fd::IntoRawFd) -> i64 {
    i64::from(stream.into_raw_fd())
}

#[cfg(windows)]
fn into_fd(stream: impl std::os::windows::io::IntoRawHandle) -> i64 {
    stream.into_raw_handle() as i64
}

struct ProcessLib;

impl PrepolyLib for ProcessLib {
    fn entry(reg: &mut Registry) {
        reg.export(decl!(process_spawn));
        reg.export(decl!(process_stream));
        reg.export(decl!(process_wait));
    }
}

prepoly_lib!(ProcessLib);
