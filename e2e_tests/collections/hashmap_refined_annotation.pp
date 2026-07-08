// A binding annotated with a refinement alias pins the map's key/value types up
// front. The witness-free constructor's inferred slot array is seeded from the
// annotation (so it is a concrete `_Entry<string, int64>` array, not an open
// one that would read as `never`), and later stores type against the pinned
// value: an int64 variable, an int32 variable (widened), and a bare integer
// literal (which would default to int32) all store as int64.

import std.collections.{ HashMap }

type Scores = HashMap {
    key: string,
    value: int64,
}

fun main() {
    let m: Scores = HashMap.new()
    let a: int64 = 100
    m.set("a", a)
    let b: int32 = 20
    m.set("b", b)
    m.set("c", 3)
    println(m.get("a"))
    println(m.get("b"))
    println(m.get("c"))
    println(m.size())
}
