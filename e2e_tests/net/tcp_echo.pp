// Single-threaded TCP over loopback: on Linux a connect to a listening
// socket completes in the kernel backlog before accept runs, so one thread
// can drive both ends deterministically. Port 0 requests an ephemeral port,
// read back through socket_local_addr, so parallel test runs never collide.
import std.net.{ tcp_listen, tcp_connect, tcp_accept, socket_local_addr, socket_peer_addr, socket_set_timeout }

let listener = tcp_listen("127.0.0.1", 0)!
let addr = socket_local_addr(listener)!
let port = int64.parse(addr.split(":")[1])!

let client = tcp_connect("127.0.0.1", port)!
let server = tcp_accept(listener)!

client.write(_string_bytes("hello server"))!
let got = server.read(64)!
println(_string_from_bytes(got)!)

server.write(_string_bytes("hello client"))!
let echo = client.read(64)!
println(_string_from_bytes(echo)!)

// The accepted socket's peer is the client's local address.
println(socket_peer_addr(server)! == socket_local_addr(client)!)

// A read with nothing pending fails once the timeout elapses instead of
// blocking forever. The OS error text varies, so only the branch is printed.
socket_set_timeout(client, 50)!
match client.read(1) {
    Ok { value } => println("unexpected data"),
    Err { error } => println("timed out"),
}

client.close()!
server.close()!
listener.close()!
