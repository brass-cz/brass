//! TLS (client) runtime primitives, backed by rustls.
//!
//! A TLS connection is NOT a `File`: it is a rustls session plus its TCP
//! socket, so it lives in a process-wide handle table and the primitives take
//! an `int64` handle (`std/net/tls.pp` wraps it in the `TlsStream` record).
//! Certificate verification is rustls' default against the Mozilla root set
//! (webpki-roots), with the server name taken from `host`; no knobs are
//! exposed. Every function returns a typed `Result` shaped exactly as the
//! checker's contracts (`_tls_connect -> int64!`, `_tls_read -> uint8[]!`,
//! ...).
//!
//! Built without the `tls` cargo feature -- or for a wasm target, where
//! rustls does not build -- the same symbols exist but return an error
//! Result, so the language surface is identical and only the capability is
//! missing.

#[cfg(all(feature = "tls", not(target_family = "wasm")))]
mod real {
    use std::collections::HashMap;
    use std::io::{Read, Write};
    use std::net::TcpStream;
    use std::sync::atomic::{AtomicI64, Ordering};
    use std::sync::{Arc, Mutex, OnceLock};

    use rustls::pki_types::ServerName;
    use rustls::{ClientConfig, ClientConnection, RootCertStore, StreamOwned};

    use crate::alloc::{pp_arr_new, typed_result, typed_result_err, typed_str};
    use crate::rt::Header;

    type Conn = StreamOwned<ClientConnection, TcpStream>;

    /// Live connections by handle. Each connection sits behind its own lock so
    /// a blocking read on one never stalls another; the outer map lock is held
    /// only for lookup/insert/remove.
    fn table() -> &'static Mutex<HashMap<i64, Arc<Mutex<Conn>>>> {
        static TABLE: OnceLock<Mutex<HashMap<i64, Arc<Mutex<Conn>>>>> = OnceLock::new();
        TABLE.get_or_init(|| Mutex::new(HashMap::new()))
    }

    fn conn(handle: i64) -> Option<Arc<Mutex<Conn>>> {
        table().lock().ok()?.get(&handle).cloned()
    }

    /// The one client configuration: rustls defaults, Mozilla roots, no
    /// client auth.
    fn client_config() -> &'static Arc<ClientConfig> {
        static CFG: OnceLock<Arc<ClientConfig>> = OnceLock::new();
        CFG.get_or_init(|| {
            // Only the ring provider is compiled in, but install it explicitly
            // so `ClientConfig::builder()` never depends on ambient state.
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

    /// `_tls_connect(host, port) -> int64!`: open a TCP connection, complete
    /// the TLS handshake (verifying the certificate against `host`), and
    /// return the connection handle. Failing at connect time -- rather than on
    /// the first read -- is what surfaces certificate errors to the caller.
    ///
    /// # Safety
    /// `host` must be a string object.
    pub unsafe extern "C-unwind" fn pp_tls_connect(host: *mut Header, port: i64) -> *mut Header {
        unsafe {
            let host = typed_str(host);
            let port = match u16::try_from(port) {
                Ok(p) => p,
                Err(_) => {
                    return typed_result_err(&format!("port {port} is out of range (0..=65535)"));
                }
            };
            let server = match ServerName::try_from(host.to_string()) {
                Ok(s) => s,
                Err(_) => return typed_result_err(&format!("invalid server name `{host}`")),
            };
            let sock = match TcpStream::connect((host, port)) {
                Ok(s) => s,
                Err(e) => return typed_result_err(&e.to_string()),
            };
            let session = match ClientConnection::new(client_config().clone(), server) {
                Ok(c) => c,
                Err(e) => return typed_result_err(&e.to_string()),
            };
            let mut stream = StreamOwned::new(session, sock);
            while stream.conn.is_handshaking() {
                if let Err(e) = stream.conn.complete_io(&mut stream.sock) {
                    return typed_result_err(&format!("TLS handshake failed: {e}"));
                }
            }
            static NEXT: AtomicI64 = AtomicI64::new(1);
            let handle = NEXT.fetch_add(1, Ordering::Relaxed);
            if let Ok(mut t) = table().lock() {
                t.insert(handle, Arc::new(Mutex::new(stream)));
            }
            typed_result(true, |p| *(p as *mut i64) = handle)
        }
    }

    /// `_tls_read(handle, max) -> uint8[]!`: up to `max` plaintext bytes
    /// (fewer on a short read; empty at a clean end-of-stream).
    ///
    /// # Safety
    /// Callable from any state; an unknown `handle` yields an error Result.
    /// Unsafe only for C-ABI symmetry with the other runtime primitives.
    pub unsafe extern "C-unwind" fn pp_tls_read(handle: i64, max: i64) -> *mut Header {
        unsafe {
            let Some(c) = conn(handle) else {
                return typed_result_err("TLS connection is closed");
            };
            let mut buf = vec![0u8; max.max(0) as usize];
            let got = {
                let mut stream = match c.lock() {
                    Ok(s) => s,
                    Err(_) => return typed_result_err("TLS connection is poisoned"),
                };
                match stream.read(&mut buf) {
                    Ok(n) => n,
                    Err(e) => return typed_result_err(&e.to_string()),
                }
            };
            let arr = pp_arr_new(1, got as i64);
            let data = *((arr as *mut u8).offset(32) as *mut *mut u8);
            std::ptr::copy_nonoverlapping(buf.as_ptr(), data, got);
            typed_result(true, |p| *(p as *mut *mut Header) = arr)
        }
    }

    /// `_tls_write(handle, bytes) -> int64!`: encrypt and send the whole
    /// `uint8[]`, returning its length.
    ///
    /// # Safety
    /// `bytes` must be a `uint8[]` object.
    pub unsafe extern "C-unwind" fn pp_tls_write(handle: i64, bytes: *mut Header) -> *mut Header {
        unsafe {
            let Some(c) = conn(handle) else {
                return typed_result_err("TLS connection is closed");
            };
            let len = *((bytes as *mut u8).offset(16) as *mut i64) as usize;
            let data = *((bytes as *mut u8).offset(32) as *const *const u8);
            let slice = std::slice::from_raw_parts(data, len);
            let mut stream = match c.lock() {
                Ok(s) => s,
                Err(_) => return typed_result_err("TLS connection is poisoned"),
            };
            match stream.write_all(slice).and_then(|_| stream.flush()) {
                Ok(()) => typed_result(true, |p| *(p as *mut i64) = len as i64),
                Err(e) => typed_result_err(&e.to_string()),
            }
        }
    }

    /// `_tls_close(handle) -> void!`: send close_notify (best effort) and
    /// drop the connection. Closing an already-closed handle is an error
    /// Result, mirroring double-close on a `File`.
    ///
    /// # Safety
    /// Callable from any state; an unknown `handle` yields an error Result.
    /// Unsafe only for C-ABI symmetry with the other runtime primitives.
    pub unsafe extern "C-unwind" fn pp_tls_close(handle: i64) -> *mut Header {
        unsafe {
            let removed = table().lock().ok().and_then(|mut t| t.remove(&handle));
            match removed {
                Some(c) => {
                    if let Ok(mut stream) = c.lock() {
                        stream.conn.send_close_notify();
                        let _ = stream.flush();
                    }
                    typed_result(true, |p| *(p as *mut i64) = 0)
                }
                None => typed_result_err("TLS connection is closed"),
            }
        }
    }
}

#[cfg(all(feature = "tls", not(target_family = "wasm")))]
pub use real::{pp_tls_close, pp_tls_connect, pp_tls_read, pp_tls_write};

#[cfg(any(not(feature = "tls"), target_family = "wasm"))]
mod stub {
    use crate::alloc::typed_result_err;
    use crate::rt::Header;

    fn unsupported() -> *mut Header {
        unsafe { typed_result_err("TLS support is not built into this binary") }
    }

    pub unsafe extern "C-unwind" fn pp_tls_connect(_host: *mut Header, _port: i64) -> *mut Header {
        unsupported()
    }
    pub unsafe extern "C-unwind" fn pp_tls_read(_handle: i64, _max: i64) -> *mut Header {
        unsupported()
    }
    pub unsafe extern "C-unwind" fn pp_tls_write(_handle: i64, _bytes: *mut Header) -> *mut Header {
        unsupported()
    }
    pub unsafe extern "C-unwind" fn pp_tls_close(_handle: i64) -> *mut Header {
        unsupported()
    }
}

#[cfg(any(not(feature = "tls"), target_family = "wasm"))]
pub use stub::{pp_tls_close, pp_tls_connect, pp_tls_read, pp_tls_write};
