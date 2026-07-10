// Spawning and controlling child processes. The `Command` builder, the
// `Stdio` mode, and the `Child` handle are written in prepoly on top of the
// native `process` plugin (see `process/`); a piped standard stream is a
// `File`, so it is read and written with the ordinary file methods.
//
// This is a library rather than part of `std`: spawning processes needs
// native code, which arrives as a plugin instead of a runtime builtin. Point
// `PREPOLY_PACKAGES` at this directory and import it:
//
//     PREPOLY_PACKAGES=process=/path/to/libraries
//     import process.{ Command, Stdio }
//
// Build the plugin once with `libraries/build.sh`.

import process.process.{ process_spawn, process_stream, process_wait }

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

// The stream selector the plugin expects.
fun _stream_stdin() -> int64 {
    return 0
}

fun _stream_stdout() -> int64 {
    return 1
}

fun _stream_stderr() -> int64 {
    return 2
}

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
    _stdin: Stdio
    _stdout: Stdio
    _stderr: Stdio
}

/** A command that runs `program` (looked up on `PATH`) with no arguments and inherited streams. */
fun Command.new(program: string) -> Command {
    let args: string[] = []
    return Self {
        _program: program,
        _args: args,
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
        _stdio_mode(self._stdin),
        _stdio_mode(self._stdout),
        _stdio_mode(self._stderr),
    )!
    return Child { _handle: handle }
}

/**
 * A running (or finished) child process. A stream configured as `Stdio.Pipe`
 * is reachable through the matching accessor as a `File`: read the child's
 * output, or write to its input. Call `wait` to block for exit and get the
 * exit code.
 */
type Child = {
    _handle: int64
}

// The plugin hands back the piped stream's raw descriptor; adopting it as a
// `File` is what makes the ordinary read/write/close methods drive it.
fun Child._stream(self, which: int64) -> File! {
    return _file_from_fd(process_stream(self._handle, which)!)
}

/** The child's standard input pipe, to write to it (requires `Stdio.Pipe`). */
fun Child.stdin(self) -> File! {
    return self._stream(_stream_stdin())!
}

/** The child's standard output pipe, to read from it (requires `Stdio.Pipe`). */
fun Child.stdout(self) -> File! {
    return self._stream(_stream_stdout())!
}

/** The child's standard error pipe, to read from it (requires `Stdio.Pipe`). */
fun Child.stderr(self) -> File! {
    return self._stream(_stream_stderr())!
}

/** Block until the child exits and return its exit code. */
// The plugin's exit code is an `int64`; the narrowing is checked, and cannot
// fail for a real exit status.
fun Child.wait(self) -> int32! {
    return int32.from(process_wait(self._handle)!)!
}
