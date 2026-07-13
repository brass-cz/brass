// Spawning and controlling child processes. The `Command` builder, the
// `Stdio` mode, and the `Child` handle are written in prepoly on top of the
// native plugin (`libprocess`, built from `process/`); a piped standard
// stream is a `File`, so it is read and written with the ordinary file
// methods.
//
// This is a library rather than part of `std`: spawning processes needs
// native code, which arrives as a plugin instead of a runtime builtin. Point
// `PREPOLY_INCLUDE` at this directory and import it:
//
//     PREPOLY_INCLUDE=/path/to/libraries
//     import process.{ Command, Stdio }
//
// Build the plugin once with `libraries/build.sh`.

import fs.{ File }
import libprocess.{
    process_spawn,
    process_stream,
    process_wait,
    process_wait_captured,
    process_take_captured,
}

/**
 * How a child's standard stream is connected:
 * - `Inherit` shares this process's own stream (the default);
 * - `Pipe` opens a pipe reachable through the `Child`'s stream accessors;
 * - `Null` discards it (`/dev/null`).
 */
type Stdio =
    | Inherit
    | Pipe
    | Null

// The mode integer the plugin expects (see `process/src/lib.rs`).
fun _stdio_mode(s: Stdio) -> int64 {
    match s {
        Stdio.Inherit => { return 0 }
        Stdio.Pipe => { return 1 }
        Stdio.Null => { return 2 }
    }
}

// The stream selectors the plugin expects: 0 = stdin, 1 = stdout, 2 = stderr.

/**
 * A builder for an OS process. Construct with `Command.new`, then chain the
 * configuration methods -- each mutates the command and returns it -- and
 * finish with `spawn`:
 *
 *     const child = Command.new("git")
 *         .args(["init"])
 *         .stdout(Stdio.Pipe)
 *         .spawn()!
 */
type Command = {
    _program: string
    _args: string[]
    // Environment overrides as a flat [name, value, name, value, ...] run: the
    // plugin ABI carries arrays, not maps, and the child's environment is built
    // by SETTING each pair on top of this process's own.
    _env: string[]
    _stdin: Stdio
    _stdout: Stdio
    _stderr: Stdio
}

/**
 * A command that runs `program` (looked up on `PATH`) with no arguments,
 * inherited streams, and this process's environment.
 */
fun Command.new(program: string) -> Command {
    let args: string[] = []
    let env: string[] = []
    return Self {
        _program: program,
        _args: args,
        _env: env,
        _stdin: Stdio.Inherit,
        _stdout: Stdio.Inherit,
        _stderr: Stdio.Inherit,
    }
}

/** Append one argument. */
fun Command.arg(self, value: string) -> Command {
    self._args.push(value)
    return self
}

/** Append several arguments in order. */
fun Command.args(self, values: string[]) -> Command {
    for v in values {
        self._args.push(v)
    }
    return self
}

/**
 * Set the environment variable `name` to `value` in the child.
 *
 * The child otherwise INHERITS this process's environment, so this adds to it
 * (or overrides one entry of it) rather than replacing it; setting the same
 * name twice keeps the last value, as an assignment would. There is no way to
 * unset an inherited variable or to start from an empty environment -- neither
 * has been needed, and both would be new plugin calls.
 *
 *     const child = Command.new("printenv")
 *         .arg("GREETING")
 *         .env("GREETING", "hello")
 *         .stdout(Stdio.Pipe)
 *         .spawn()!
 */
fun Command.env(self, name: string, value: string) -> Command {
    self._env.push(name)
    self._env.push(value)
    return self
}

/** Set how the child's standard input is connected. */
fun Command.stdin(self, mode: Stdio) -> Command {
    self._stdin = mode
    return self
}

/** Set how the child's standard output is connected. */
fun Command.stdout(self, mode: Stdio) -> Command {
    self._stdout = mode
    return self
}

/** Set how the child's standard error is connected. */
fun Command.stderr(self, mode: Stdio) -> Command {
    self._stderr = mode
    return self
}

/** Spawn the process, returning a handle to the running `Child`. */
fun Command.spawn(self) -> Child! {
    let handle = process_spawn(
        self._program,
        self._args,
        self._env,
        _stdio_mode(self._stdin),
        _stdio_mode(self._stdout),
        _stdio_mode(self._stderr),
    )!
    return Child {
        _handle: handle,
        _stdin_f: null,
        _stdout_f: null,
        _stderr_f: null,
    }
}

/**
 * A running (or finished) child process. A stream configured as `Stdio.Pipe`
 * is reachable through the matching accessor as a `File`: read the child's
 * output, or write to its input. Call `wait` to block for exit and get the
 * exit code, or `output` to collect the piped streams and the exit code at
 * once.
 */
type Child = {
    _handle: int64
    // The adopted `File` per stream, once an accessor has taken it from the
    // plugin. The plugin gives each descriptor up exactly once, so the
    // accessors have to hand back the same `File` on every later call.
    _stdin_f: File?
    _stdout_f: File?
    _stderr_f: File?
}

/**
 * A finished child's exit code together with everything it wrote to the
 * streams that were piped (empty for a stream that was not).
 */
type Output = {
    code: int32
    stdout: uint8[]
    stderr: uint8[]
}

// The plugin hands back the piped stream's raw descriptor; adopting it as a
// `File` is what makes the ordinary read/write/close methods drive it.
fun Child._stream(self, which: int64) -> File! {
    return File.from_fd(process_stream(self._handle, which)!)
}

/** The child's standard input pipe, to write to it (requires `Stdio.Pipe`). */
fun Child.stdin(self) -> File! {
    if let f = self._stdin_f {
        return f
    }
    const f = self._stream(0)!
    self._stdin_f = f
    return f
}

/** The child's standard output pipe, to read from it (requires `Stdio.Pipe`). */
fun Child.stdout(self) -> File! {
    if let f = self._stdout_f {
        return f
    }
    const f = self._stream(1)!
    self._stdout_f = f
    return f
}

/** The child's standard error pipe, to read from it (requires `Stdio.Pipe`). */
fun Child.stderr(self) -> File! {
    if let f = self._stderr_f {
        return f
    }
    const f = self._stream(2)!
    self._stderr_f = f
    return f
}

/**
 * Block until the child exits and return its exit code. Waiting again returns
 * the same code, and the piped streams stay readable afterwards.
 *
 * A child that writes more than a pipe buffer holds (about 64KiB on Linux) to
 * a pipe nobody is reading blocks forever, and so does this call. Drain the
 * piped streams first, or use `output`, which drains them for you.
 */
// The plugin's exit code is an `int64`; the narrowing is checked, and cannot
// fail for a real exit status.
fun Child.wait(self) -> int32! {
    return int32.from(process_wait(self._handle)!)!
}

/**
 * Drain the child's piped output, wait for it to exit, and return both. Unlike
 * `wait` this cannot deadlock on a chatty child: the streams are read while
 * the child is still running.
 *
 * A stream already taken through `stdin`/`stdout`/`stderr` belongs to the
 * caller, so it is not captured and its buffer comes back empty.
 */
fun Child.output(self) -> Output! {
    const code = int32.from(process_wait_captured(self._handle)!)!
    const out = process_take_captured(self._handle, 1)!
    const err = process_take_captured(self._handle, 2)!
    return Output { code: code, stdout: out, stderr: err }
}
