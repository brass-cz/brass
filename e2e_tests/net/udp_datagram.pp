// UDP datagrams between two loopback sockets on ephemeral ports: the
// Datagram record carries both the payload and the sender's address, so the
// receiver can verify who sent it.
import std.net.{ Udp, to_bytes, to_text }

let a = Udp.bind("127.0.0.1", 0)!
let b = Udp.bind("127.0.0.1", 0)!
let b_port = int64.parse(b.local_addr()!.split(":")[1])!

let sent = a.send_to(to_bytes("ping over udp"), "127.0.0.1", b_port)!
println(sent)

let d = b.recv_from(64)!
println(to_text(d.data)!)
println(d.addr == a.local_addr()!)

a.close()!
b.close()!
