//! Standard-stream runtime primitives.
//!
//! File I/O lives in the fs library (a plugin over raw descriptors); the
//! runtime keeps only what the import-free prelude needs -- writing a string
//! to stdout (`pp_print_str`/`pp_println_str` in `crate::alloc`) and reading
//! bytes from stdin for `input()`.

use std::fs::File;
use std::io::Read;
use std::mem::ManuallyDrop;
use std::os::fd::FromRawFd;

use crate::alloc::{pp_arr_new, pp_str_const, typed_result, typed_result_err};
use crate::rt::Header;

/// `_flush()`: push whatever the program has written but not yet handed to the
/// operating system out to it.
///
/// Standard output is buffered by line, so a `println` is already on its way
/// out but a `print` with no trailing newline is not. That only matters when
/// something other than a normal return ends the program (`process.exit`) or
/// reads the terminal next (a prompt printed without a newline), which is why
/// this exists rather than flushing on every write: those callers flush, and a
/// print-heavy loop keeps its batching.
pub extern "C-unwind" fn pp_flush() {
    use std::io::Write;
    let _ = std::io::stdout().flush();
    let _ = std::io::stderr().flush();
}

/// `_argv() -> string[]`: the program's argument vector -- the program file
/// as written on the driver's command line, then everything after it -- as
/// published by the driver through `prepoly_utils::set_program_argv`. Empty
/// when none was published (an interactive REPL session, or an embedder).
/// The primitive behind the env library's `args()`.
pub extern "C-unwind" fn pp_argv() -> *mut Header {
    let argv = prepoly_utils::program_argv();
    unsafe {
        // A string[]: one pointer-sized slot per element.
        let arr = pp_arr_new(8, argv.len() as i64);
        let data = *((arr as *mut u8).offset(32) as *mut *mut *mut Header);
        for (i, a) in argv.iter().enumerate() {
            *data.add(i) = pp_str_const(a.as_ptr(), a.len() as i64);
        }
        arr
    }
}

/// `_stdin_read(n) -> uint8[]!`: up to `n` bytes from standard input (fewer
/// at end-of-input). The primitive behind the prelude's `input()`, so reading
/// a line needs no `File` value.
pub extern "C-unwind" fn pp_stdin_read(n: i64) -> *mut Header {
    unsafe {
        // Borrow descriptor 0 without taking ownership, so the borrow ending
        // does not close it.
        let mut stdin = ManuallyDrop::new(File::from_raw_fd(0));
        let mut buf = vec![0u8; n.max(0) as usize];
        match stdin.read(&mut buf) {
            Ok(got) => {
                let arr = pp_arr_new(1, got as i64);
                let data = *((arr as *mut u8).offset(32) as *mut *mut u8);
                std::ptr::copy_nonoverlapping(buf.as_ptr(), data, got);
                typed_result(true, |p| *(p as *mut *mut Header) = arr)
            }
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}
