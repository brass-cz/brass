// TLS failures surface as ordinary error Results. Loopback port 1 has no
// listener, so the connect fails deterministically (before any handshake or
// network access), which keeps this case offline-safe; certificate and
// handshake failures come back through the same Err path.
import std.net.tls.{ TlsStream }

match TlsStream.connect("127.0.0.1", 1) {
    Ok { value } => println("unexpected ok"),
    Err { error } => println("connect failed"),
}
