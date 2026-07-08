// A spawned thread as the TCP client, the main thread as the server. The
// closure captures only the port (a copied scalar): sharing the listener
// itself would auto-guard it with a cown lock that the blocking accept would
// then hold, tripping the deadlock watchdog. Match-based error handling
// keeps the closure non-fallible (a `!` inside a closure is unsupported).
import std.net.{ Tcp, TcpListener, to_bytes, to_text }

fun run_client(port: int64) {
    match Tcp.connect("127.0.0.1", port) {
        Ok { value } => {
            let conn = value
            let w = conn.write(to_bytes("hi"))
            match conn.read(64) {
                Ok { value } => {
                    match to_text(value) {
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
    let listener = TcpListener.bind("127.0.0.1", 0)!
    let port = int64.parse(listener.local_addr()!.split(":")[1])!
    spawn(() -> {
        run_client(port)
    })
    let conn = listener.accept()!
    let req = conn.read(64)!
    // One write, so the client's single read sees the whole reply.
    conn.write(to_bytes("echo: " + to_text(req)!))!
    conn.close()!
    sync()
    println("server done")
}
