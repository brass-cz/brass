// A spawned thread as the TCP client, the main thread as the server. The
// closure captures only the port (a copied scalar): sharing the listener
// itself would auto-guard it with a cown lock that the blocking accept would
// then hold, tripping the deadlock watchdog. Match-based error handling
// keeps the closure non-fallible (a `!` inside a closure is unsupported).
import std.net.{ tcp_listen, tcp_connect, tcp_accept, socket_local_addr }

fun run_client(port: int64) {
    match tcp_connect("127.0.0.1", port) {
        Ok { value } => {
            let conn = value
            let w = conn.write(_string_bytes("hi"))
            match conn.read(64) {
                Ok { value } => {
                    match _string_from_bytes(value) {
                        Ok { value } => println("client got: {value}"),
                        Err { error } => println("client decode failed: {error}")
                    }
                }
                Err { error } => println("client read failed: {error}")
            }
            let closed = conn.close()
        }
        Err { error } => println("connect failed: {error}")
    }
}

fun main() {
    let listener = tcp_listen("127.0.0.1", 0)!
    let port = int64.parse(socket_local_addr(listener)!.split(":")[1])!
    spawn(() -> {
        run_client(port)
    })
    let conn = tcp_accept(listener)!
    let req = conn.read(64)!
    // One write, so the client's single read sees the whole reply.
    conn.write(_string_bytes("echo: " + _string_from_bytes(req)!))!
    conn.close()!
    sync()
    println("server done")
}
