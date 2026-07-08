// A witness-free map whose value type is pinned to int64 by the first store.
// A later `set` with a bare integer literal (which would default to int32) is
// checked against the receiver's pinned value type via the type's scheme, so
// the literal takes int64; an int32 variable widens at the call boundary. Both
// store correctly rather than being rejected as an int32/int64 mismatch.

import std.collections.{ HashMap }

fun main() {
    let m = HashMap.new()
    let base: int64 = 100
    m.set("a", base)
    m.set("b", 20)          // bare literal -> int64 (the map's value type)
    let w: int32 = 3
    m.set("c", w)           // int32 -> widens to int64
    println(m.get("a"))
    println(m.get("b"))
    println(m.get("c"))
}
