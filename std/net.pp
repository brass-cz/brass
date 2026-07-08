// Networking built on the runtime socket primitives. A socket is a `File`
// (an OS file descriptor) held privately by the `Tcp`/`TcpListener`/`Udp`
// records below, which expose only the operations that make sense for each
// socket kind (a listener cannot be read; a connection cannot accept). Part
// of the standard library but NOT in the implicit prelude -- import it
// explicitly:
//
//     import std.net.{ Tcp, TcpListener }
//
// Networking runs on the native runtime only; the REPL back end rejects it,
// like file I/O.

/**
 * A TCP connection: a bidirectional byte stream. Obtain one with
 * `Tcp.connect` (client side) or `TcpListener.accept` (server side). TCP
 * carries no message boundaries: one `read` may return less than what the
 * peer wrote, so frame messages or read in a loop.
 */
type Tcp = {
    _sock: File
}

/**
 * Open a TCP connection to `host`:`port`. `host` is an IP literal or a name
 * (resolved through the system resolver).
 */
fun Tcp.connect(host: string, port: int64) -> Tcp! {
    return Self { _sock: _tcp_connect(host, port)! }
}

/** Block for incoming data and read up to `max` bytes (fewer on a short read; empty at end-of-stream). */
fun Tcp.read(self, max: int64) -> uint8[]! {
    return self._sock.read(max)!
}

/** Write all of `data`, returning the byte count written. */
fun Tcp.write(self, data: uint8[]) -> int64! {
    return self._sock.write(data)!
}

/** Close the connection. */
fun Tcp.close(self) {
    self._sock.close()!
}

/** The socket's own `"ip:port"` address. */
fun Tcp.local_addr(self) -> string! {
    return _socket_addr(self._sock, 0)!
}

/** The connected peer's `"ip:port"` address. */
fun Tcp.peer_addr(self) -> string! {
    return _socket_addr(self._sock, 1)!
}

/**
 * Give the connection a read/write timeout of `ms` milliseconds; 0 clears
 * it (block forever). A read or write that exceeds the deadline returns an
 * error Result instead of blocking.
 */
fun Tcp.set_timeout(self, ms: int64) {
    _socket_set_timeout(self._sock, ms)!
}

/**
 * A listening TCP socket producing `Tcp` connections. Obtain one with
 * `TcpListener.bind`, then call `accept` per connection.
 */
type TcpListener = {
    _sock: File
}

/**
 * Bind `host`:`port` and listen for TCP connections. Port 0 asks the OS for
 * an ephemeral port; read it back with `local_addr`.
 */
fun TcpListener.bind(host: string, port: int64) -> TcpListener! {
    return Self { _sock: _tcp_listen(host, port)! }
}

/** Block until a connection arrives and return it. */
fun TcpListener.accept(self) -> Tcp! {
    return Tcp { _sock: _tcp_accept(self._sock)! }
}

/** The listener's own `"ip:port"` address (for a port the OS picked, see `bind`). */
fun TcpListener.local_addr(self) -> string! {
    return _socket_addr(self._sock, 0)!
}

/** Stop listening and release the socket. */
fun TcpListener.close(self) {
    self._sock.close()!
}

/**
 * A UDP socket. Obtain one with `Udp.bind` (port 0 for an ephemeral port),
 * then exchange datagrams with `send_to`/`recv_from`.
 */
type Udp = {
    _sock: File
}

/** Bind a UDP socket on `host`:`port` (port 0 for an ephemeral port). */
fun Udp.bind(host: string, port: int64) -> Udp! {
    return Self { _sock: _udp_bind(host, port)! }
}

/** Send `data` as one datagram to `host`:`port`, returning the bytes sent. */
fun Udp.send_to(self, data: uint8[], host: string, port: int64) -> int64! {
    return _udp_send_to(self._sock, data, host, port)!
}

/** One received datagram: the payload and the sender's `"ip:port"` address. */
type Datagram = {
    data: uint8[]
    addr: string
}

/**
 * Block until a datagram of up to `max` bytes arrives. A datagram longer
 * than `max` is truncated (UDP semantics).
 */
fun Udp.recv_from(self, max: int64) -> Datagram! {
    // The primitive returns one byte array shaped
    // [addr_len: u8][addr utf8][payload]; split it here.
    let raw = _udp_recv_from(self._sock, max)!
    let alen: int64 = raw[0]
    let addr = _string_from_bytes(raw.slice(1, 1 + alen))!
    return Datagram { data: raw.slice(1 + alen, len(raw)), addr: addr }
}

/** The socket's own `"ip:port"` address. */
fun Udp.local_addr(self) -> string! {
    return _socket_addr(self._sock, 0)!
}

/**
 * Give the socket a receive/send timeout of `ms` milliseconds; 0 clears it.
 */
fun Udp.set_timeout(self, ms: int64) {
    _socket_set_timeout(self._sock, ms)!
}

/** Close the socket. */
fun Udp.close(self) {
    self._sock.close()!
}

/** The UTF-8 bytes of `s`, ready to `write`/`send_to`. */
fun to_bytes(s: string) -> uint8[] {
    return _string_bytes(s)
}

/** Decode received bytes as UTF-8 text. Fails on invalid UTF-8. */
fun to_text(bytes: uint8[]) -> string! {
    return _string_from_bytes(bytes)!
}
