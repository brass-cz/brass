//! TCP/UDP sockets and TLS client connections, as a native Brass plugin.
//!
//! `std/net.cz` builds the `Tcp`/`TcpListener`/`Udp`/`TlsStream`
//! surface on these primitives. A plain socket crosses the boundary as its
//! raw descriptor (an `i64`), which the Brass side adopts as a `File` --
//! so connected sockets are read and written with the ordinary file methods,
//! and only what byte I/O cannot express lives here: establishing sockets
//! (connect/bind/listen/accept), datagram addressing, socket addresses, and
//! timeouts.
//!
//! A TLS connection is NOT a descriptor: it is a rustls session plus its TCP
//! socket, so it lives in a process-wide handle table and the `tls_*`
//! functions take an `i64` handle. Certificate verification is rustls'
//! default against the Mozilla root set (webpki-roots), with the server name
//! taken from `host`; no knobs are exposed.

use std::collections::HashMap;
use std::io::{Read, Write};
use std::mem::ManuallyDrop;
use std::net::{TcpListener, TcpStream, UdpSocket};
use std::os::fd::{FromRawFd, IntoRawFd, RawFd};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::Duration;

use brass_plugin::{BrassLib, Bytes, Registry, brass_lib, decl, export};

use rustls::pki_types::ServerName;
use rustls::{ClientConfig, ClientConnection, RootCertStore, StreamOwned};

/// Validate a port operand into `u16` range.
fn valid_port(port: i64) -> Result<u16, String> {
    u16::try_from(port).map_err(|_| format!("port {port} is out of range (0..=65535)"))
}

/// Reject a negative descriptor (a closed socket record stores -1) before
/// it can hit `from_raw_fd`'s assertion; the caller sees an ordinary error.
fn live(fd: i64) -> Result<RawFd, String> {
    if fd < 0 {
        return Err("socket is closed".to_string());
    }
    RawFd::try_from(fd).map_err(|_| format!("socket descriptor {fd} is out of range"))
}

fn byte_count(value: i64) -> Result<usize, String> {
    usize::try_from(value).map_err(|_| format!("byte count {value} must be non-negative"))
}

/// Run `op` on the socket type `S` borrowed from `fd` without taking
/// ownership, so the borrow ending does not close the descriptor. The socket
/// std types are fd wrappers, and the syscalls behind the operations used
/// here (`getsockname`, `getpeername`, `setsockopt`, `accept`, `sendto`,
/// `recvfrom`) act on the descriptor itself, so borrowing an fd as a
/// different socket family than created it is well-defined at this layer;
/// the OS reports a mismatch as an ordinary error.
fn borrow_socket<S: FromRawFd, R>(fd: RawFd, op: impl FnOnce(&S) -> R) -> R {
    let sock = ManuallyDrop::new(unsafe { S::from_raw_fd(fd) });
    op(&sock)
}

export! {
    /// Open a TCP connection to `host`:`port` and give up its descriptor.
    /// `host` is an IP literal or a name (resolved through the system
    /// resolver). The Brass side owns the descriptor from here.
    fn tcp_connect(host: String, port: i64) -> Result<i64, String> {
        let port = valid_port(port)?;
        match TcpStream::connect((host.as_str(), port)) {
            Ok(s) => Ok(i64::from(s.into_raw_fd())),
            Err(e) => Err(e.to_string()),
        }
    }

    /// Bind `host`:`port`, listen for TCP connections, and give up the
    /// listening descriptor. Port 0 asks the OS for an ephemeral port (read
    /// it back with `socket_addr`).
    fn tcp_listen(host: String, port: i64) -> Result<i64, String> {
        let port = valid_port(port)?;
        match TcpListener::bind((host.as_str(), port)) {
            Ok(l) => Ok(i64::from(l.into_raw_fd())),
            Err(e) => Err(e.to_string()),
        }
    }

    /// Block until a connection arrives on listening descriptor `fd` and
    /// give up the accepted connection's descriptor.
    fn tcp_accept(fd: i64) -> Result<i64, String> {
        let fd = live(fd)?;
        match borrow_socket::<TcpListener, _>(fd, |l| l.accept()) {
            Ok((stream, _)) => Ok(i64::from(stream.into_raw_fd())),
            Err(e) => Err(e.to_string()),
        }
    }

    /// Bind a UDP socket on `host`:`port` and give up its descriptor. Port 0
    /// asks the OS for an ephemeral port.
    fn udp_bind(host: String, port: i64) -> Result<i64, String> {
        let port = valid_port(port)?;
        match UdpSocket::bind((host.as_str(), port)) {
            Ok(s) => Ok(i64::from(s.into_raw_fd())),
            Err(e) => Err(e.to_string()),
        }
    }

    /// Send `data` as one datagram from UDP descriptor `fd` to `host`:`port`,
    /// returning the byte count sent.
    fn udp_send_to(fd: i64, data: Bytes, host: String, port: i64) -> Result<i64, String> {
        let fd = live(fd)?;
        let port = valid_port(port)?;
        match borrow_socket::<UdpSocket, _>(fd, |s| s.send_to(&data.0, (host.as_str(), port))) {
            Ok(sent) => Ok(sent as i64),
            Err(e) => Err(e.to_string()),
        }
    }

    /// Receive one datagram of up to `max` bytes on UDP descriptor `fd`. The
    /// returned bytes are `[addr_len: u8][addr utf8][payload]` -- a
    /// length-prefixed sender address followed by the payload -- because one
    /// call returns one value; `net.cz` splits it into a `Datagram` record.
    /// An "ip:port" rendering is always shorter than 256 bytes, so one
    /// length byte suffices.
    fn udp_recv_from(fd: i64, max: i64) -> Result<Bytes, String> {
        let fd = live(fd)?;
        let mut buf = vec![0u8; byte_count(max)?];
        match borrow_socket::<UdpSocket, _>(fd, |s| s.recv_from(&mut buf)) {
            Ok((got, peer)) => {
                let addr = peer.to_string();
                let mut out = Vec::with_capacity(1 + addr.len() + got);
                out.push(addr.len() as u8);
                out.extend_from_slice(addr.as_bytes());
                out.extend_from_slice(&buf[..got]);
                Ok(Bytes(out))
            }
            Err(e) => Err(e.to_string()),
        }
    }

    /// The socket's address as `"ip:port"`; `which` 0 is the local address
    /// (`getsockname`), anything else the connected peer (`getpeername`).
    /// Works for TCP and UDP sockets alike (the syscalls are fd-generic; the
    /// borrow type only shapes the call).
    fn socket_addr(fd: i64, which: i64) -> Result<String, String> {
        let fd = live(fd)?;
        let addr = borrow_socket::<TcpStream, _>(fd, |s| {
            if which == 0 { s.local_addr() } else { s.peer_addr() }
        });
        match addr {
            Ok(a) => Ok(a.to_string()),
            Err(e) => Err(e.to_string()),
        }
    }

    /// Set the socket's read and write timeouts to `ms` milliseconds;
    /// `ms <= 0` clears them (blocking forever). A read or write past the
    /// deadline fails with a timeout error Result.
    fn socket_set_timeout(fd: i64, ms: i64) -> Result<(), String> {
        let fd = live(fd)?;
        let dur = (ms > 0).then(|| Duration::from_millis(ms as u64));
        borrow_socket::<TcpStream, _>(fd, |s| {
            s.set_read_timeout(dur).and_then(|_| s.set_write_timeout(dur))
        })
        .map_err(|e| e.to_string())
    }

    /// Open a TCP connection to `host`:`port`, complete the TLS handshake
    /// (verifying the certificate against `host`), and return the connection
    /// handle. Failing at connect time -- rather than on the first read --
    /// is what surfaces certificate errors to the caller.
    fn tls_connect(host: String, port: i64) -> Result<i64, String> {
        let port = valid_port(port)?;
        let server = ServerName::try_from(host.clone())
            .map_err(|_| format!("invalid server name `{host}`"))?;
        let sock = TcpStream::connect((host.as_str(), port)).map_err(|e| e.to_string())?;
        let session =
            ClientConnection::new(client_config().clone(), server).map_err(|e| e.to_string())?;
        let mut stream = StreamOwned::new(session, sock);
        while stream.conn.is_handshaking() {
            if let Err(e) = stream.conn.complete_io(&mut stream.sock) {
                return Err(format!("TLS handshake failed: {e}"));
            }
        }
        static NEXT: AtomicI64 = AtomicI64::new(1);
        let handle = NEXT.fetch_add(1, Ordering::Relaxed);
        table().lock().map_err(|_| poisoned())?.insert(handle, Arc::new(Mutex::new(stream)));
        Ok(handle)
    }

    /// Up to `max` plaintext bytes from TLS connection `handle` (fewer on a
    /// short read; empty at a clean end-of-stream).
    fn tls_read(handle: i64, max: i64) -> Result<Bytes, String> {
        let c = conn(handle)?;
        let mut buf = vec![0u8; byte_count(max)?];
        let got = c.lock().map_err(|_| poisoned())?.read(&mut buf).map_err(|e| e.to_string())?;
        buf.truncate(got);
        Ok(Bytes(buf))
    }

    /// Encrypt and send all of `data` on TLS connection `handle`, returning
    /// its length.
    fn tls_write(handle: i64, data: Bytes) -> Result<i64, String> {
        let c = conn(handle)?;
        let mut stream = c.lock().map_err(|_| poisoned())?;
        stream
            .write_all(&data.0)
            .and_then(|_| stream.flush())
            .map_err(|e| e.to_string())?;
        Ok(data.0.len() as i64)
    }

    /// Send close_notify (best effort) and drop TLS connection `handle`.
    /// Closing an already-closed handle is an error Result, mirroring
    /// double-close on a `File`.
    fn tls_close(handle: i64) -> Result<(), String> {
        let removed = table().lock().map_err(|_| poisoned())?.remove(&handle);
        match removed {
            Some(c) => {
                if let Ok(mut stream) = c.lock() {
                    stream.conn.send_close_notify();
                    let _ = stream.flush();
                }
                Ok(())
            }
            None => Err("TLS connection is closed".to_string()),
        }
    }
}

type Conn = StreamOwned<ClientConnection, TcpStream>;

/// Live TLS connections by handle. Each connection sits behind its own lock
/// so a blocking read on one never stalls another; the outer map lock is
/// held only for lookup/insert/remove.
fn table() -> &'static Mutex<HashMap<i64, Arc<Mutex<Conn>>>> {
    static TABLE: OnceLock<Mutex<HashMap<i64, Arc<Mutex<Conn>>>>> = OnceLock::new();
    TABLE.get_or_init(|| Mutex::new(HashMap::new()))
}

fn conn(handle: i64) -> Result<Arc<Mutex<Conn>>, String> {
    table()
        .lock()
        .map_err(|_| poisoned())?
        .get(&handle)
        .cloned()
        .ok_or_else(|| "TLS connection is closed".to_string())
}

fn poisoned() -> String {
    "TLS connection table is poisoned".to_string()
}

/// The one client configuration: rustls defaults, Mozilla roots, no client
/// auth.
fn client_config() -> &'static Arc<ClientConfig> {
    static CFG: OnceLock<Arc<ClientConfig>> = OnceLock::new();
    CFG.get_or_init(|| {
        // Only the ring provider is compiled in, but install it explicitly so
        // `ClientConfig::builder()` never depends on ambient state.
        let _ = rustls::crypto::ring::default_provider().install_default();
        let mut roots = RootCertStore::empty();
        roots.extend(webpki_roots::TLS_SERVER_ROOTS.iter().cloned());
        Arc::new(
            ClientConfig::builder()
                .with_root_certificates(roots)
                .with_no_client_auth(),
        )
    })
}

struct NetLib;

impl BrassLib for NetLib {
    fn entry(reg: &mut Registry) {
        reg.export(decl!(tcp_connect));
        reg.export(decl!(tcp_listen));
        reg.export(decl!(tcp_accept));
        reg.export(decl!(udp_bind));
        reg.export(decl!(udp_send_to));
        reg.export(decl!(udp_recv_from));
        reg.export(decl!(socket_addr));
        reg.export(decl!(socket_set_timeout));
        reg.export(decl!(tls_connect));
        reg.export(decl!(tls_read));
        reg.export(decl!(tls_write));
        reg.export(decl!(tls_close));
    }
}

brass_lib!(NetLib);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn descriptor_and_buffer_ranges_are_checked() {
        // Plugin integers must not truncate into a different OS descriptor,
        // and a negative receive size is a caller error rather than EOF.
        assert!(live(i64::from(i32::MAX) + 1).is_err());
        assert!(byte_count(-1).is_err());
    }
}
