// TLS client connections, backed by the runtime's rustls-based primitives.
// A TLS connection is an opaque runtime handle (not a File): the `TlsStream`
// record below is its only surface. Certificate verification uses the
// bundled Mozilla root set with the server name taken from `host`; there are
// no configuration knobs. Import explicitly:
//
//     import std.net.tls.{ TlsStream }
//
// Like the rest of networking this runs on the native runtime only, and only
// when the driver is built with TLS support (the default).

/**
 * An encrypted TLS connection to a server, opened with `TlsStream.connect`.
 * The API mirrors `Tcp`: `read`/`write`/`close`, with the same byte-stream
 * semantics (one `read` may return less than what the peer wrote).
 */
type TlsStream = {
    _handle: int64
}

/**
 * Connect to `host`:`port` and complete the TLS handshake, verifying the
 * server's certificate against `host`. Fails on connection, name, or
 * certificate errors.
 */
fun TlsStream.connect(host: string, port: int64) -> TlsStream! {
    return Self { _handle: _tls_connect(host, port)! }
}

/** Block for incoming data and read up to `max` decrypted bytes (fewer on a short read; empty at end-of-stream). */
fun TlsStream.read(self, max: int64) -> uint8[]! {
    return _tls_read(self._handle, max)!
}

/** Encrypt and send all of `data`, returning the byte count written. */
fun TlsStream.write(self, data: uint8[]) -> int64! {
    return _tls_write(self._handle, data)!
}

/** Close the connection (sends the TLS close notification). */
fun TlsStream.close(self) {
    _tls_close(self._handle)!
}
