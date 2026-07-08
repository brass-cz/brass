// Networking built on the runtime socket primitives. A socket is a `File`
// (an OS file descriptor), so a connection is read, written, and closed with
// the same `read`/`write`/`close` methods file I/O uses; this module adds
// what byte I/O cannot express: establishing sockets, datagram addressing,
// socket addresses, and timeouts. Part of the standard library but NOT in
// the implicit prelude -- import it explicitly:
//
//     import std.net.{ tcp_connect, tcp_listen, tcp_accept }
//
// Networking runs on the native runtime only; the REPL back end rejects it,
// like file I/O.

/**
 * Open a TCP connection to `host`:`port`. `host` is an IP literal or a name
 * (resolved through the system resolver). The connection is a `File`: use
 * `read`/`write`/`close` on it.
 */
fun tcp_connect(host: string, port: int64) -> File! {
    return _tcp_connect(host, port)!
}

/**
 * Bind `host`:`port` and listen for TCP connections. Port 0 asks the OS for
 * an ephemeral port; read it back with `socket_local_addr`. The listener is
 * a `File` usable only with `tcp_accept` and `close`.
 */
fun tcp_listen(host: string, port: int64) -> File! {
    return _tcp_listen(host, port)!
}

/** Block until a connection arrives on `listener` and return it. */
fun tcp_accept(listener: File) -> File! {
    return _tcp_accept(listener)!
}

/**
 * Bind a UDP socket on `host`:`port` (port 0 for an ephemeral port). Use
 * `udp_send_to`/`udp_recv_from` on the result, and `close` when done.
 */
fun udp_bind(host: string, port: int64) -> File! {
    return _udp_bind(host, port)!
}

/** Send `data` as one datagram to `host`:`port`, returning the bytes sent. */
fun udp_send_to(sock: File, data: uint8[], host: string, port: int64) -> int64! {
    return _udp_send_to(sock, data, host, port)!
}

/** One received datagram: the payload and the sender's `"ip:port"` address. */
type Datagram = {
    data: uint8[]
    addr: string
}

/**
 * Block until a datagram of up to `max` bytes arrives on `sock`. A datagram
 * longer than `max` is truncated (UDP semantics).
 */
fun udp_recv_from(sock: File, max: int64) -> Datagram! {
    // The primitive returns one byte array shaped
    // [addr_len: u8][addr utf8][payload]; split it here.
    let raw = _udp_recv_from(sock, max)!
    let alen: int64 = raw[0]
    let addr = _string_from_bytes(raw.slice(1, 1 + alen))!
    return Datagram { data: raw.slice(1 + alen, len(raw)), addr: addr }
}

/** The socket's own `"ip:port"` address (for a port the OS picked, see `tcp_listen`). */
fun socket_local_addr(sock: File) -> string! {
    return _socket_addr(sock, 0)!
}

/** The connected peer's `"ip:port"` address. Fails on an unconnected socket. */
fun socket_peer_addr(sock: File) -> string! {
    return _socket_addr(sock, 1)!
}

/**
 * Give `sock` a read/write timeout of `ms` milliseconds; 0 clears it (block
 * forever). A read or write that exceeds the deadline returns an error
 * Result instead of blocking.
 */
fun socket_set_timeout(sock: File, ms: int64) {
    _socket_set_timeout(sock, ms)!
}

/** The UTF-8 bytes of `s`, ready to `write` to a socket. */
fun to_bytes(s: string) -> uint8[] {
    return _string_bytes(s)
}

/** Decode bytes `read` from a socket as UTF-8 text. Fails on invalid UTF-8. */
fun to_text(bytes: uint8[]) -> string! {
    return _string_from_bytes(bytes)!
}
