// UDP datagrams between two loopback sockets on ephemeral ports: the
// Datagram record carries both the payload and the sender's address, so the
// receiver can verify who sent it.
import std.net.{ udp_bind, udp_send_to, udp_recv_from, socket_local_addr }

let a = udp_bind("127.0.0.1", 0)!
let b = udp_bind("127.0.0.1", 0)!
let b_port = int64.parse(socket_local_addr(b)!.split(":")[1])!

let sent = udp_send_to(a, _string_bytes("ping over udp"), "127.0.0.1", b_port)!
println(sent)

let d = udp_recv_from(b, 64)!
println(_string_from_bytes(d.data)!)
println(d.addr == socket_local_addr(a)!)

a.close()!
b.close()!
