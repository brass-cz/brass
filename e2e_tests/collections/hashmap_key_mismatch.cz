// A HashMap's key/value types are fixed by use: `set("a", "b")` makes this a
// `string -> string` map. Using it inconsistently -- `get` with an `int32` key --
// is a type error, reported at the call site in this file, not at a span inside
// the stdlib implementation that re-elaborating `get`'s body would otherwise
// surface.
fun main() {
    let map = HashMap.new()
    map.set("a", "b")
    map.get(1)
}
