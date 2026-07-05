// A reference created inside a `with` region must not escape it: storing a
// region member into a module-level global raises the region's external
// reference count, so leaving the `with` scope fails the closedness check
// instead of silently letting the reference leak out.
type Node = { v: int32 }
type Box = { node: Node? }

let leaked = Node { v: 0 }

fun main() {
    let b = Box { node: null }
    with(b, (h) -> {
        h.node = Node { v: 1 }
        if let n = h.node {
            leaked = n
            println("stored")
        }
    })
    println(leaked.v)
}
