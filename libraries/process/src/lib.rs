//! Spawning and controlling OS processes, as a native Prepoly plugin.
//!
//! `libraries/process.pp` builds the `Command`/`Stdio`/`Child` surface on
//! these primitives. A spawned child sits in a process-wide table keyed by an
//! `i64` handle; a piped standard stream leaves as a raw descriptor, which the
//! Prepoly side adopts as a `File` so the ordinary read/write/close methods
//! drive it.
//!
//! Stdio modes are the small integers `process.pp` translates its `Stdio`
//! variants to: 0 = inherit, 1 = pipe, 2 = null. Stream selectors are
//! 0 = stdin, 1 = stdout, 2 = stderr.
//!
//! A child's entry outlives its `wait`: the exit status is cached, so waiting
//! twice is not an error, and streams stay takeable afterwards, because a pipe
//! still holds whatever the child wrote before it exited.

use std::collections::HashMap;
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, OnceLock};

use prepoly_plugin::{Bytes, PrepolyLib, Registry, decl, export, prepoly_lib};

/// One spawned child. `status` caches the exit code once waited for, and
/// `captured` holds the stdout/stderr buffers `process_wait_captured` drained.
#[derive(Default)]
struct Entry {
    child: Option<Child>,
    status: Option<i64>,
    /// Indexed by stream selector minus one: `[stdout, stderr]`.
    captured: [Option<Vec<u8>>; 2],
}

/// Live spawned children by handle. Each entry has its own lock, so a blocking
/// `wait` does not freeze unrelated process calls.
fn table() -> &'static Mutex<HashMap<i64, Arc<Mutex<Entry>>>> {
    static TABLE: OnceLock<Mutex<HashMap<i64, Arc<Mutex<Entry>>>>> = OnceLock::new();
    TABLE.get_or_init(|| Mutex::new(HashMap::new()))
}

fn poisoned() -> String {
    "process table is poisoned".to_string()
}

/// The entry for `handle`, with the table lock released: a caller may then
/// block on the child without holding up the whole table.
fn entry(handle: i64) -> Result<Arc<Mutex<Entry>>, String> {
    table()
        .lock()
        .map_err(|_| poisoned())?
        .get(&handle)
        .cloned()
        .ok_or_else(|| "no such child process".to_string())
}

fn lock(entry: &Arc<Mutex<Entry>>) -> Result<MutexGuard<'_, Entry>, String> {
    entry.lock().map_err(|_| poisoned())
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

fn exit_code(status: &std::process::ExitStatus) -> i64 {
    i64::from(status.code().unwrap_or_else(|| signal_code(status)))
}

/// Wait for the child in `e`, caching the code so a second wait sees it too.
fn wait_locked(e: &mut Entry) -> Result<i64, String> {
    if let Some(code) = e.status {
        return Ok(code);
    }
    let child = e.child.as_mut().ok_or(SPENT)?;
    let status = child.wait().map_err(|e| e.to_string())?;
    let code = exit_code(&status);
    e.status = Some(code);
    release_if_spent(e);
    Ok(code)
}

const SPENT: &str = "no such child process (it was waited for and its streams consumed)";

/// Drop the `Child` once nothing more can be asked of it: the exit status is
/// cached and every stream has been taken or was never piped. The entry itself
/// stays, so a repeated `wait` still answers from the cache; only the OS handle
/// and the pipe descriptors go. Entries are never removed from the table --
/// removing one would make a repeated `wait` an error.
fn release_if_spent(e: &mut Entry) {
    let spent = e.status.is_some()
        && e.captured.iter().all(Option::is_none)
        && e.child
            .as_ref()
            .is_some_and(|c| c.stdin.is_none() && c.stdout.is_none() && c.stderr.is_none());
    if spent {
        e.child = None;
    }
}

export! {
    /// Spawn `program` (looked up on `PATH`) with `args`, connecting each
    /// standard stream by its mode (0 = inherit, 1 = pipe, 2 = null).
    /// Returns a handle to the running child.
    ///
    /// `env` is a flat `[name, value, name, value, ...]` run of environment
    /// overrides (the ABI carries arrays, not maps): each is SET on top of the
    /// environment this process passes on, so a child sees the parent's
    /// variables plus these. A name repeated in the run takes its last value,
    /// as an assignment would. An odd-length run is a bug in the wrapper that
    /// built it, so it is reported rather than silently dropping the last name.
    fn process_spawn(
        program: String,
        args: Vec<String>,
        env: Vec<String>,
        stdin: i64,
        stdout: i64,
        stderr: i64,
    ) -> Result<i64, String> {
        if !env.len().is_multiple_of(2) {
            return Err(format!(
                "environment overrides must be name/value pairs, got {} entries",
                env.len()
            ));
        }
        let mut command = Command::new(&program);
        command
            .args(&args)
            .stdin(stdio(stdin))
            .stdout(stdio(stdout))
            .stderr(stdio(stderr));
        for pair in env.chunks_exact(2) {
            command.env(&pair[0], &pair[1]);
        }
        let child = command.spawn().map_err(|e| e.to_string())?;
        static NEXT: AtomicI64 = AtomicI64::new(1);
        let handle = NEXT.fetch_add(1, Ordering::Relaxed);
        let entry = Entry { child: Some(child), ..Entry::default() };
        table()
            .lock()
            .map_err(|_| poisoned())?
            .insert(handle, Arc::new(Mutex::new(entry)));
        Ok(handle)
    }

    /// Take the child's piped standard stream `which` (0 = stdin, 1 = stdout,
    /// 2 = stderr) and return its raw descriptor. Available once, and only
    /// when that stream was configured as a pipe -- but also after `wait`,
    /// because the pipe still holds what the child wrote before exiting.
    fn process_stream(child: i64, which: i64) -> Result<i64, String> {
        let entry = entry(child)?;
        let mut e = lock(&entry)?;
        let fd = {
            let child = e.child.as_mut().ok_or(SPENT)?;
            match which {
                0 => child.stdin.take().map(into_fd),
                1 => child.stdout.take().map(into_fd),
                2 => child.stderr.take().map(into_fd),
                other => return Err(format!("no standard stream {other}")),
            }
        };
        release_if_spent(&mut e);
        fd.ok_or_else(|| "stream is not piped or already taken".to_string())
    }

    /// Block until the child exits, returning its exit code (the signal
    /// number negated on a Unix signal death). Waiting again returns the same
    /// code, and the child's piped streams stay takeable.
    ///
    /// A child writing more than a pipe buffer holds to a pipe nobody reads
    /// will never exit; use `process_wait_captured` instead.
    fn process_wait(child: i64) -> Result<i64, String> {
        let entry = entry(child)?;
        // The table lock is already released, so this blocks only this child.
        let mut e = lock(&entry)?;
        wait_locked(&mut e)
    }

    /// Drain the child's piped stdout and stderr concurrently, then wait,
    /// returning the exit code. The buffers are stored on the child and taken
    /// with `process_take_captured`.
    ///
    /// This is the call that cannot deadlock: a child filling the pipe buffer
    /// blocks until someone reads, and `process_wait` is not that someone.
    fn process_wait_captured(child: i64) -> Result<i64, String> {
        let entry = entry(child)?;
        let mut e = lock(&entry)?;
        if e.status.is_some() {
            return wait_locked(&mut e);
        }
        // `wait_with_output` consumes the child, so drain by hand: a reader
        // thread per still-piped stream, then wait, then join.
        let (out, err) = {
            let child = e.child.as_mut().ok_or(SPENT)?;
            // A piped stdin the caller never took would keep the child waiting
            // on input it will not get; close it before blocking on exit.
            child.stdin.take();
            (
                child.stdout.take().map(reader_thread),
                child.stderr.take().map(reader_thread),
            )
        };
        let code = wait_locked(&mut e)?;
        e.captured[0] = out.map(join_reader).transpose()?;
        e.captured[1] = err.map(join_reader).transpose()?;
        Ok(code)
    }

    /// Take the buffer `process_wait_captured` collected for stream `which`
    /// (1 = stdout, 2 = stderr). Empty when that stream was not piped, and
    /// empty again on a second take.
    fn process_take_captured(child: i64, which: i64) -> Result<Bytes, String> {
        let slot = match which {
            1 | 2 => (which - 1) as usize,
            other => return Err(format!("no captured stream {other}")),
        };
        let entry = entry(child)?;
        let mut e = lock(&entry)?;
        let taken = e.captured[slot].take().unwrap_or_default();
        release_if_spent(&mut e);
        Ok(Bytes(taken))
    }
}

type Reader = std::thread::JoinHandle<std::io::Result<Vec<u8>>>;

/// Read `stream` to EOF on its own thread. Both pipes must drain at once: a
/// child that fills stderr while the parent reads stdout would otherwise block
/// forever.
fn reader_thread(mut stream: impl std::io::Read + Send + 'static) -> Reader {
    std::thread::spawn(move || {
        let mut buf = Vec::new();
        std::io::Read::read_to_end(&mut stream, &mut buf)?;
        Ok(buf)
    })
}

fn join_reader(handle: Reader) -> Result<Vec<u8>, String> {
    handle
        .join()
        .map_err(|_| "a stream reader panicked".to_string())?
        .map_err(|e| e.to_string())
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
        reg.export(decl!(process_wait_captured));
        reg.export(decl!(process_take_captured));
    }
}

prepoly_lib!(ProcessLib);
