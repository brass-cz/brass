//! Network runtime primitives.
//!
//! A socket is a `File` -- the same fd-holding record file I/O uses (see
//! `crate::io`) -- so `read`/`write`/`close` apply to connected sockets
//! unchanged. These primitives cover only what byte I/O cannot express:
//! establishing sockets (connect/bind/listen/accept), datagram addressing,
//! socket addresses, and timeouts. Every function returns a typed `Result`
//! shaped exactly as the checker's contracts (`_tcp_connect -> File!`,
//! `_udp_recv_from -> uint8[]!`, ...).
//!
//! The std wrappers live in `std/net.pp` (`import std.net`).

use std::mem::ManuallyDrop;
use std::net::{TcpListener, TcpStream, UdpSocket};
use std::os::fd::{FromRawFd, IntoRawFd, RawFd};
use std::time::Duration;

use crate::alloc::{pp_arr_new, pp_str_const, typed_result, typed_result_err, typed_str};
use crate::io::{file_fd, make_file};
use crate::rt::Header;

/// A typed `Result.Ok` holding a fresh `File` for `fd`.
unsafe fn file_ok(fd: RawFd) -> *mut Header {
    unsafe {
        let file = make_file(fd);
        typed_result(true, |p| *(p as *mut *mut Header) = file)
    }
}

/// A typed `Result.Ok` holding a string.
unsafe fn str_ok(s: &str) -> *mut Header {
    unsafe {
        let obj = pp_str_const(s.as_ptr(), s.len() as i64);
        typed_result(true, |p| *(p as *mut *mut Header) = obj)
    }
}

/// Validate a port operand into `u16` range.
fn valid_port(port: i64) -> Result<u16, String> {
    u16::try_from(port).map_err(|_| format!("port {port} is out of range (0..=65535)"))
}

/// Run `op` on the socket type `S` borrowed from `fd` without taking
/// ownership, so the borrow ending does not close the descriptor. The socket
/// std types are fd wrappers, and the syscalls behind the operations used
/// here (`getsockname`, `getpeername`, `setsockopt`, `accept`, `sendto`,
/// `recvfrom`) act on the descriptor itself, so borrowing an fd as a
/// different socket family than created it is well-defined at this layer;
/// the OS reports a mismatch as an ordinary error.
unsafe fn borrow_socket<S: FromRawFd, R>(fd: RawFd, op: impl FnOnce(&S) -> R) -> R {
    unsafe {
        let sock = ManuallyDrop::new(S::from_raw_fd(fd));
        op(&sock)
    }
}

/// The (len, data) view of a `uint8[]` object (layout as in `crate::io`).
unsafe fn bytes_view(bytes: *mut Header) -> &'static [u8] {
    unsafe {
        let len = *((bytes as *mut u8).offset(16) as *mut i64) as usize;
        let data = *((bytes as *mut u8).offset(32) as *const *const u8);
        std::slice::from_raw_parts(data, len)
    }
}

/// `_tcp_connect(host, port) -> File!`: open a TCP connection. `host` is an
/// IP literal or a name (resolved through the system resolver).
///
/// # Safety
/// `host` must be a string object.
pub unsafe extern "C-unwind" fn pp_tcp_connect(host: *mut Header, port: i64) -> *mut Header {
    unsafe {
        let host = typed_str(host);
        let port = match valid_port(port) {
            Ok(p) => p,
            Err(e) => return typed_result_err(&e),
        };
        match TcpStream::connect((host, port)) {
            Ok(s) => file_ok(s.into_raw_fd()),
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}

/// `_tcp_listen(host, port) -> File!`: bind and listen. Port 0 asks the OS
/// for an ephemeral port (read it back with `_socket_addr`).
///
/// # Safety
/// `host` must be a string object.
pub unsafe extern "C-unwind" fn pp_tcp_listen(host: *mut Header, port: i64) -> *mut Header {
    unsafe {
        let host = typed_str(host);
        let port = match valid_port(port) {
            Ok(p) => p,
            Err(e) => return typed_result_err(&e),
        };
        match TcpListener::bind((host, port)) {
            Ok(l) => file_ok(l.into_raw_fd()),
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}

/// `_tcp_accept(listener) -> File!`: block until a connection arrives and
/// return it.
///
/// # Safety
/// `listener` must be a `File` holding a listening TCP socket.
pub unsafe extern "C-unwind" fn pp_tcp_accept(listener: *mut Header) -> *mut Header {
    unsafe {
        let fd = file_fd(listener);
        match borrow_socket::<TcpListener, _>(fd, |l| l.accept()) {
            Ok((stream, _)) => file_ok(stream.into_raw_fd()),
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}

/// `_udp_bind(host, port) -> File!`: bind a UDP socket. Port 0 asks the OS
/// for an ephemeral port.
///
/// # Safety
/// `host` must be a string object.
pub unsafe extern "C-unwind" fn pp_udp_bind(host: *mut Header, port: i64) -> *mut Header {
    unsafe {
        let host = typed_str(host);
        let port = match valid_port(port) {
            Ok(p) => p,
            Err(e) => return typed_result_err(&e),
        };
        match UdpSocket::bind((host, port)) {
            Ok(s) => file_ok(s.into_raw_fd()),
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}

/// `_udp_send_to(sock, bytes, host, port) -> int64!`: send one datagram,
/// returning the byte count sent.
///
/// # Safety
/// `sock` must be a `File` holding a UDP socket, `bytes` a `uint8[]` object,
/// and `host` a string object.
pub unsafe extern "C-unwind" fn pp_udp_send_to(
    sock: *mut Header,
    bytes: *mut Header,
    host: *mut Header,
    port: i64,
) -> *mut Header {
    unsafe {
        let fd = file_fd(sock);
        let data = bytes_view(bytes);
        let host = typed_str(host);
        let port = match valid_port(port) {
            Ok(p) => p,
            Err(e) => return typed_result_err(&e),
        };
        match borrow_socket::<UdpSocket, _>(fd, |s| s.send_to(data, (host, port))) {
            Ok(sent) => typed_result(true, |p| *(p as *mut i64) = sent as i64),
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}

/// `_udp_recv_from(sock, max) -> uint8[]!`: receive one datagram of up to
/// `max` bytes. The returned array is `[addr_len: u8][addr utf8][payload]` --
/// a length-prefixed sender address followed by the payload -- because a
/// primitive returns one object; `std/net.pp` splits it into a `Datagram`
/// record. An "ip:port" rendering is always shorter than 256 bytes, so one
/// length byte suffices.
///
/// # Safety
/// `sock` must be a `File` holding a UDP socket.
pub unsafe extern "C-unwind" fn pp_udp_recv_from(sock: *mut Header, max: i64) -> *mut Header {
    unsafe {
        let fd = file_fd(sock);
        let mut buf = vec![0u8; max.max(0) as usize];
        match borrow_socket::<UdpSocket, _>(fd, |s| s.recv_from(&mut buf)) {
            Ok((got, peer)) => {
                let addr = peer.to_string();
                let total = 1 + addr.len() + got;
                let arr = pp_arr_new(1, total as i64);
                let data = *((arr as *mut u8).offset(32) as *mut *mut u8);
                *data = addr.len() as u8;
                std::ptr::copy_nonoverlapping(addr.as_ptr(), data.add(1), addr.len());
                std::ptr::copy_nonoverlapping(buf.as_ptr(), data.add(1 + addr.len()), got);
                typed_result(true, |p| *(p as *mut *mut Header) = arr)
            }
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}

/// `_socket_addr(sock, which) -> string!`: the socket's address as
/// `"ip:port"`; `which` 0 is the local address (`getsockname`), anything else
/// the connected peer (`getpeername`). Works for TCP and UDP sockets alike
/// (the syscalls are fd-generic; the borrow type only shapes the call).
///
/// # Safety
/// `sock` must be a `File` holding a socket.
pub unsafe extern "C-unwind" fn pp_socket_addr(sock: *mut Header, which: i64) -> *mut Header {
    unsafe {
        let fd = file_fd(sock);
        let addr = borrow_socket::<TcpStream, _>(fd, |s| {
            if which == 0 {
                s.local_addr()
            } else {
                s.peer_addr()
            }
        });
        match addr {
            Ok(a) => str_ok(&a.to_string()),
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}

/// `_socket_set_timeout(sock, ms) -> void!`: set the read and write timeouts
/// to `ms` milliseconds; `ms <= 0` clears them (blocking forever). A read or
/// write past the deadline fails with a timeout error Result.
///
/// # Safety
/// `sock` must be a `File` holding a socket.
pub unsafe extern "C-unwind" fn pp_socket_set_timeout(sock: *mut Header, ms: i64) -> *mut Header {
    unsafe {
        let fd = file_fd(sock);
        let dur = if ms > 0 {
            Some(Duration::from_millis(ms as u64))
        } else {
            None
        };
        let set = borrow_socket::<TcpStream, _>(fd, |s| {
            s.set_read_timeout(dur)
                .and_then(|_| s.set_write_timeout(dur))
        });
        match set {
            Ok(()) => typed_result(true, |p| *(p as *mut i64) = 0),
            Err(e) => typed_result_err(&e.to_string()),
        }
    }
}
