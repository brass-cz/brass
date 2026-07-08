import std.collections.{ HashMap }

// A HashMap's value type is fixed by use: `set("a", "b")` makes this a
// `string -> string` map. Setting a later value of a different type (`int32`) is a
// type error, caught at the call site rather than silently miscompiling the
// unboxed slot and crashing at runtime.
fun main() {
    let map = HashMap.new()
    map.set("a", "b")
    map.set("a", 1)
}
