// The store barrier is symmetric: a reference that escapes a `with` region
// through an external container stops counting once the container's slot is
// overwritten, so the region closes cleanly at scope exit.
type Node = { v: int32 }
type Box = { node: Node? }
type Keep = { n: Node? }

fun main() {
    let b = Box { node: null }
    let k = Keep { n: null }
    with(b, (h) -> {
        h.node = Node { v: 5 }
        if let n = h.node {
            k.n = n
            k.n = null
        }
    })
    if let n = b.node {
        println(n.v)
    }
}
