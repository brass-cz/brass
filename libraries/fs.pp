// File handles and byte I/O. A `File` holds an OS file descriptor privately;
// `File.open` produces one from a path, and other libraries adopt descriptors
// they obtained elsewhere (a child's pipe, a socket) through `File.from_fd`, so
// the ordinary read/write/close methods drive any byte stream.
//
// This is a library rather than part of `std`: asking the operating system to
// open and move bytes needs native code, which arrives as a plugin instead of
// a runtime builtin. Point `PREPOLY_INCLUDE` at this directory and import it:
//
//     PREPOLY_INCLUDE=/path/to/libraries
//     import fs.{ File, read_file, write_file }
//
// Build the plugin once with `libraries/build.sh`. Sizes are the path
// library's business (a size needs no open file, only a name), so `size`
// works exactly for files opened by path.

import libfs.{
    fd_open,
    fd_read,
    fd_write,
    fd_seek,
    fd_close,
    file_remove,
    file_copy,
    file_move,
    dir_create,
    dir_remove,
    dir_copy,
    dir_move,
}
import path.{ Path }

/**
 * An open file (or any adopted byte stream): read, write, seek, close. The
 * descriptor and the path it was opened under (empty for adopted descriptors
 * and the standard streams) are private; every capability is a method.
 */
type File = {
    _fd: int64
    _path: string
}

/**
 * Adopt an already-open descriptor as a `File`, so the ordinary
 * read/write/close methods drive it. Where the descriptor came from -- a pipe
 * handed back by a spawned child, a socket -- is the caller's business. The
 * `File` owns the descriptor from here: closing the `File` closes it.
 */
fun File.from_fd(fd: int64) -> File {
    return File { _fd: fd, _path: "" }
}

/**
 * Open the file at `path`, which is a string or a `Path`. Modes: `"r"` read,
 * `"w"` truncate+create write, `"a"` append+create.
 */
fun File.open(path, mode: string) -> File! {
    // The text is kept as well as the descriptor: `size` stats by name (see
    // below), so the `File` has to remember the name it was opened under.
    const text = _as_text(path)!
    return File { _fd: fd_open(text, mode)!, _path: text }
}

/** Standard input as a `File` (never closed by `close`). */
fun File.stdin() -> File {
    return File { _fd: 0, _path: "" }
}

/** Standard output as a `File` (never closed by `close`). */
fun File.stdout() -> File {
    return File { _fd: 1, _path: "" }
}

/** Standard error as a `File` (never closed by `close`). */
fun File.stderr() -> File {
    return File { _fd: 2, _path: "" }
}

/** Block for data and read up to `max` bytes (fewer on a short read; empty at end-of-file). */
fun File.read(self, max: int64) -> uint8[]! {
    return fd_read(self._fd, max)!
}

/** Write all of `data`, returning the byte count written. */
fun File.write(self, data: uint8[]) -> int64! {
    return fd_write(self._fd, data)!
}

/** Move the read/write cursor to absolute byte offset `pos` from the start. Fallible. */
fun File.seek(self, pos: int64) {
    fd_seek(self._fd, pos)!
}

/**
 * The file's length in bytes. Answered by the path library (a stat by name,
 * which needs no open descriptor), so it works exactly for files opened by
 * path -- an adopted descriptor or standard stream has no path to ask about.
 */
fun File.size(self) -> int64! {
    if self._path == "" {
        error("this file was not opened by path; its size is unknown")!
    }
    return Path.parse(self._path).file_size()!
}

/**
 * Close the file. The standard streams are left open, and the stored
 * descriptor is forgotten on close so a second `close()` cannot re-close a
 * descriptor the OS may have reassigned to a later `open` (it is a no-op),
 * and reads/writes after close fail instead of hitting an unrelated file.
 */
fun File.close(self) {
    if self._fd > 2 {
        fd_close(self._fd)!
        self._fd = -1
    }
}

/**
 * Read the whole file at `path` (a string or a `Path`) as text. Fails when the
 * file cannot be opened or does not hold valid UTF-8.
 */
fun read_file(path) {
    let f = File.open(path, "r")!
    let size = f.size()!
    let bytes = f.read(size)!
    f.close()!
    return to_text(bytes)!
}

/**
 * Write `content` to the file at `path` (a string or a `Path`), truncating it
 * -- creating the file when it is not there, but NOT its parent directories
 * (`create_dir` does that). Fallible: returns a `Result`.
 */
fun write_file(path, content: string) {
    let f = File.open(path, "w")!
    f.write(to_bytes(content))!
    f.close()!
}

/**
 * Delete the file at `path` (a string or a `Path`).
 *
 * A symbolic link is removed as the LINK -- what it points at is untouched. A
 * `path` that is a directory is an error (`remove_dir` takes a tree), and so is
 * one that is not there: a typo in a destructive call must not read as "done".
 */
fun remove_file(path) {
    file_remove(_as_text(path)!)!
}

/**
 * Copy the file at `source` onto `target`, contents and permissions, REPLACING
 * `target` when it already exists. Each path is a string or a `Path`.
 *
 * `target`'s parent directory must exist -- `create_dir` makes one -- and a
 * directory as either side is an error.
 */
fun copy_file(source, target) {
    file_copy(_as_text(source)!, _as_text(target)!)!
}

/**
 * Move the file at `source` to `target`, REPLACING `target` when it already
 * exists. Each path is a string or a `Path`.
 *
 * Within one filesystem this is a rename: atomic, and the file's contents are
 * never read. Across filesystems -- and a temporary directory very often IS
 * another filesystem, which is exactly where "move the file I just built into
 * place" happens -- a rename cannot work, so the move falls back to a copy
 * followed by a delete. That fallback is not atomic, and `source` survives if
 * the delete fails (the error says so).
 *
 * `source` must be a file: moving a directory would succeed on one filesystem
 * and fail on another, so it is refused rather than left to chance.
 */
fun move_file(source, target) {
    file_move(_as_text(source)!, _as_text(target)!)!
}

/**
 * Copy the directory tree at `source` to `target`, recursively. Each path is a
 * string or a `Path`.
 *
 * `target` must NOT already exist. This is where the directory forms part ways
 * with `copy_file`, which replaces its target: replacing a TREE would mean
 * deleting files the copy never mentioned, which is not something a copy should
 * do behind the caller's back. Remove the old tree with `remove_dir` first if
 * that is what you want.
 *
 * A symbolic link inside the tree is recreated as a LINK rather than followed,
 * as `cp -R` does -- which is also what keeps the walk finite when a link points
 * back at an ancestor. `target` may not lie inside `source`, for the same
 * reason.
 */
fun copy_dir(source, target) {
    dir_copy(_as_text(source)!, _as_text(target)!)!
}

/**
 * Move the directory tree at `source` to `target`. Each path is a string or a
 * `Path`, and `target` must NOT already exist (see `copy_dir`).
 *
 * Within one filesystem this is a rename: atomic, and nothing in the tree is
 * read. Across filesystems it falls back to copying the tree and then removing
 * the original -- not atomic, and `source` survives if the removal fails (the
 * error says so).
 */
fun move_dir(source, target) {
    dir_move(_as_text(source)!, _as_text(target)!)!
}

/**
 * Copy `source` to `target`, whichever it is: a directory is copied as a tree
 * (`copy_dir`), anything else as a file (`copy_file`). Each path is a string or
 * a `Path`.
 *
 * The two halves keep their own rules about an existing `target` -- a file is
 * REPLACED, a tree is REFUSED (see `copy_dir` on why) -- so reach for the
 * specific call when it matters which one you are doing.
 */
fun copy(source, target) {
    if _is_dir(source)! {
        copy_dir(source, target)!
    } else {
        copy_file(source, target)!
    }
}

/**
 * Move `source` to `target`, whichever it is: a directory moves as a tree
 * (`move_dir`), anything else as a file (`move_file`). Each path is a string or
 * a `Path`.
 *
 * As with `copy`, the two halves keep their own rules about an existing
 * `target`: a file is replaced, a tree is refused.
 */
fun move(source, target) {
    if _is_dir(source)! {
        move_dir(source, target)!
    } else {
        move_file(source, target)!
    }
}

// Whether `path` names a directory. A `source` that is not there at all answers
// false, so the call goes to the file half -- whose error names the missing file
// rather than talking about directories.
fun _is_dir(path) -> bool! {
    return Path.parse(_as_text(path)!).is_dir()
}

/**
 * Create the directory at `path`, and every missing parent along the way -- as
 * `mkdir -p` does, so a nested directory needs one call. `path` is a string or
 * a `Path`.
 *
 * A directory that already exists is NOT an error: the state the call asks for
 * already holds. A `path` that exists as something else (a file, a symbolic
 * link) is.
 */
fun create_dir(path) {
    dir_create(_as_text(path)!)!
}

/**
 * Remove the directory at `path` and everything under it, recursively -- as
 * `rm -r` does. `path` is a string or a `Path`.
 *
 * A symbolic link inside the tree is removed as a LINK: the walk does not
 * follow it, so whatever it points at is untouched. `path` itself must BE a
 * directory (a symbolic link to one is not removed through here), and a `path`
 * that does not exist is an error rather than a silent success -- a typo in a
 * destructive call must not read as "done".
 */
fun remove_dir(path) {
    dir_remove(_as_text(path)!)!
}

// A string or a `Path` as text, so one function takes either. Every path-taking
// function in this module goes through here, so the two forms are accepted
// everywhere a path is.
//
// `Path.from(path)` is the `Path` test: a structural conversion accepts an
// argument of any type and answers null when it cannot build the record -- a
// string has none of `Path`'s fields, so it lands in the failure path rather
// than being a type error.
//
// The string case still needs its own guard: `Path.from` decides at RUN time,
// so the code after it is live for both types, and `return path` would be
// checked against the `string` return with `path` still a `Path`. `chars` is a
// member a `Path` does not have, and an uncalled member is a compile-time
// presence test, so for a `Path` argument that arm is statically dead -- never
// checked, never emitted.
//
// The trailing error is a backstop: an argument that is neither (an `int32`)
// has no `chars` member either, and is already rejected at compile time by the
// presence test itself.
fun _as_text(path) -> string! {
    if let p = Path.from(path) {
        return p.to_string()
    }
    if path.chars {
        return path
    }
    return error("expected a string or a `Path`, found `{typeof(path)}`")
}
