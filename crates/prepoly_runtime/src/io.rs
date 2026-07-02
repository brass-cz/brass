//! File I/O runtime primitives.
//!
//! A `File` is a typed record object `{ header16 | fd@16 (i64) }` holding an OS
//! file descriptor. These primitives operate on that descriptor and return typed
//! `Result`s shaped exactly as the type checker's contracts for `open`/`File.*`
//! (`open -> File!`, `read -> uint8[]!`, `write`/`size -> int64!`, `close ->
//! void!`), so the typed back end calls them directly. The descriptor is borrowed
//! without ownership for reads/writes (so an operation does not close it); `close`
//! takes ownership and closes it.

use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::mem::ManuallyDrop;
use std::os::fd::{FromRawFd, IntoRawFd, RawFd};

use crate::alloc::pp_typed_alloc;
use crate::alloc::{pp_arr_new, typed_result, typed_result_err, typed_str};
use crate::rt::Header;

/// Build a `File` object holding descriptor `fd`.
unsafe fn make_file(fd: RawFd) -> *mut Header {
    unsafe {
        let h = pp_typed_alloc(24);
        *((h as *mut u8).offset(16) as *mut i64) = fd as i64;
        h
    }
}

/// The descriptor a `File` object holds.
unsafe fn file_fd(file: *mut Header) -> RawFd {
    unsafe { *((file as *mut u8).offset(16) as *mut i64) as RawFd }
}

/// Run `op` on the `File` for `fd` without taking ownership, so the borrow ending
/// does not close the descriptor.
unsafe fn borrow_fd<R>(fd: RawFd, op: impl FnOnce(&mut File) -> R) -> R {
    unsafe {
        let mut file = ManuallyDrop::new(File::from_raw_fd(fd));
        op(&mut file)
    }
}

/// `open(path, mode) -> File!`. Modes: `r` read, `w` truncate+create write, `a`
/// append+create.
///
/// # Safety
/// `path` and `mode` must be string objects.
pub unsafe extern "C-unwind" fn pp_file_open(path: *mut Header, mode: *mut Header) -> *mut Header {
    unsafe {
        let path = typed_str(path);
        let mut opts = OpenOptions::new();
        match typed_str(mode) {
            "r" => opts.read(true),
            "w" => opts.write(true).create(true).truncate(true),
            "a" => opts.append(true).create(true),
            other => return typed_result_err(&format!("invalid open mode `{other}`")),
        };
        match opts.open(path) {
            Ok(f) => {
                let file = make_file(f.into_raw_fd());
                typed_result(true, |p| *(p as *mut *mut Header) = file)
            }
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}

/// `File.stdin()` -- descriptor 0. (Static methods; never closed by `close`.)
pub extern "C-unwind" fn pp_file_stdin() -> *mut Header {
    unsafe { make_file(0) }
}

/// `File.stdout()` -- descriptor 1.
pub extern "C-unwind" fn pp_file_stdout() -> *mut Header {
    unsafe { make_file(1) }
}

/// `File.stderr()` -- descriptor 2.
pub extern "C-unwind" fn pp_file_stderr() -> *mut Header {
    unsafe { make_file(2) }
}

/// `file.read(n) -> uint8[]!`: up to `n` bytes (fewer at end-of-file).
///
/// # Safety
/// `file` must be a `File` object.
pub unsafe extern "C-unwind" fn pp_file_read(file: *mut Header, n: i64) -> *mut Header {
    unsafe {
        let fd = file_fd(file);
        let mut buf = vec![0u8; n.max(0) as usize];
        match borrow_fd(fd, |f| f.read(&mut buf)) {
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

/// `file.write(bytes) -> int64!`: writes the whole `uint8[]`, returning its length.
///
/// # Safety
/// `file` must be a `File` object and `bytes` a `uint8[]` object.
pub unsafe extern "C-unwind" fn pp_file_write(
    file: *mut Header,
    bytes: *mut Header,
) -> *mut Header {
    unsafe {
        let fd = file_fd(file);
        let len = *((bytes as *mut u8).offset(16) as *mut i64) as usize;
        let data = *((bytes as *mut u8).offset(32) as *const *const u8);
        let slice = std::slice::from_raw_parts(data, len);
        match borrow_fd(fd, |f| f.write_all(slice)) {
            Ok(()) => typed_result(true, |p| *(p as *mut i64) = len as i64),
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}

/// `file.size() -> int64!`: the file's length in bytes.
///
/// # Safety
/// `file` must be a `File` object.
pub unsafe extern "C-unwind" fn pp_file_size(file: *mut Header) -> *mut Header {
    unsafe {
        let fd = file_fd(file);
        match borrow_fd(fd, |f| f.metadata().map(|m| m.len())) {
            Ok(sz) => typed_result(true, |p| *(p as *mut i64) = sz as i64),
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}

/// `file.seek(pos) -> void!`: move the read/write cursor to absolute byte offset
/// `pos` from the start of the file.
///
/// # Safety
/// `file` must be a `File` object.
pub unsafe extern "C-unwind" fn pp_file_seek(file: *mut Header, pos: i64) -> *mut Header {
    unsafe {
        let fd = file_fd(file);
        match borrow_fd(fd, |f| f.seek(SeekFrom::Start(pos.max(0) as u64))) {
            Ok(_) => typed_result(true, |p| *(p as *mut i64) = 0),
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}

/// `file.close() -> void!`: closes the descriptor (the standard streams 0/1/2 are
/// left open, as closing them would break the process).
///
/// # Safety
/// `file` must be a `File` object.
pub unsafe extern "C-unwind" fn pp_file_close(file: *mut Header) -> *mut Header {
    unsafe {
        let fd = file_fd(file);
        if fd > 2 {
            drop(File::from_raw_fd(fd));
            // Invalidate the stored descriptor so a second `close()` cannot
            // re-close a descriptor the OS may have reassigned to a later `open`,
            // and so reads/writes after close fail (EBADF) instead of hitting an
            // unrelated file.
            *((file as *mut u8).offset(16) as *mut i64) = -1;
        }
        typed_result(true, |p| *(p as *mut i64) = 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alloc::pp_str_const;
    use std::sync::MutexGuard;

    /// These tests allocate strings/arrays/Results through the shared counted
    /// heap. Hold the crate's heap-test lock so the tests elsewhere that assert
    /// on `pp_live_blocks` (gc, conc) never observe these allocations mid-flight.
    fn serial_io() -> MutexGuard<'static, ()> {
        crate::serial_heap_test()
    }

    unsafe fn str_obj(s: &str) -> *mut Header {
        unsafe { pp_str_const(s.as_ptr(), s.len() as i64) }
    }

    unsafe fn result_is_ok(r: *mut Header) -> bool {
        unsafe { *((r as *mut u8).offset(16) as *mut i32) == 0 }
    }

    unsafe fn result_payload(r: *mut Header) -> *mut Header {
        unsafe { *((r as *mut u8).offset(24) as *mut *mut Header) }
    }

    // A write-then-read round trip through the real descriptor path: open for
    // write, write bytes, close, reopen for read, read them back, and confirm the
    // bytes and the reported size match what was written.
    #[test]
    fn write_then_read_round_trip() {
        let _serial = serial_io();
        unsafe {
            let path = format!(
                "{}/prepoly_io_test_{}.txt",
                std::env::temp_dir().display(),
                std::process::id()
            );
            let content = b"hello file io";

            // Build a uint8[] of the content and write it.
            let bytes = pp_arr_new(1, content.len() as i64);
            let data = *((bytes as *mut u8).offset(32) as *mut *mut u8);
            std::ptr::copy_nonoverlapping(content.as_ptr(), data, content.len());

            let wf = pp_file_open(str_obj(&path), str_obj("w"));
            assert!(result_is_ok(wf), "open for write");
            let file = result_payload(wf);
            let wr = pp_file_write(file, bytes);
            assert!(result_is_ok(wr), "write");
            assert!(result_is_ok(pp_file_close(file)), "close");

            let rf = pp_file_open(str_obj(&path), str_obj("r"));
            assert!(result_is_ok(rf), "open for read");
            let file = result_payload(rf);
            let sz = pp_file_size(file);
            assert!(result_is_ok(sz));
            let sz_val = *((sz as *mut u8).offset(24) as *mut i64);
            assert_eq!(
                sz_val as usize,
                content.len(),
                "size matches written length"
            );
            let rd = pp_file_read(file, content.len() as i64);
            assert!(result_is_ok(rd), "read");
            let arr = result_payload(rd);
            let got_len = *((arr as *mut u8).offset(16) as *mut i64) as usize;
            let got_data = *((arr as *mut u8).offset(32) as *const *const u8);
            let got = std::slice::from_raw_parts(got_data, got_len);
            assert_eq!(got, content, "read back the written bytes");
            let _ = pp_file_close(file);
            let _ = std::fs::remove_file(&path);
        }
    }

    // Seeking back to the start lets a second read re-read from the beginning.
    #[test]
    fn seek_repositions_the_cursor() {
        let _serial = serial_io();
        unsafe {
            let path = format!(
                "{}/prepoly_seek_test_{}.txt",
                std::env::temp_dir().display(),
                std::process::id()
            );
            let content = b"0123456789";
            let bytes = pp_arr_new(1, content.len() as i64);
            let data = *((bytes as *mut u8).offset(32) as *mut *mut u8);
            std::ptr::copy_nonoverlapping(content.as_ptr(), data, content.len());

            let wf = pp_file_open(str_obj(&path), str_obj("w"));
            let file = result_payload(wf);
            let _ = pp_file_write(file, bytes);
            let _ = pp_file_close(file);

            let rf = pp_file_open(str_obj(&path), str_obj("r"));
            let file = result_payload(rf);
            // Read 4 bytes, then seek back to offset 2 and read 3: expect "234".
            let _ = pp_file_read(file, 4);
            assert!(result_is_ok(pp_file_seek(file, 2)), "seek ok");
            let rd = pp_file_read(file, 3);
            let arr = result_payload(rd);
            let got_len = *((arr as *mut u8).offset(16) as *mut i64) as usize;
            let got_data = *((arr as *mut u8).offset(32) as *const *const u8);
            let got = std::slice::from_raw_parts(got_data, got_len);
            assert_eq!(got, b"234", "read resumes from the sought offset");
            let _ = pp_file_close(file);
            let _ = std::fs::remove_file(&path);
        }
    }

    // An invalid mode is reported as an error Result, not a crash.
    #[test]
    fn invalid_mode_is_an_error() {
        let _serial = serial_io();
        unsafe {
            let r = pp_file_open(str_obj("/tmp/whatever"), str_obj("zzz"));
            assert!(!result_is_ok(r), "invalid mode yields Err");
        }
    }
}
