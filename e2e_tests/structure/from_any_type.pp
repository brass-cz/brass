// `T.from(v)` is a structural conversion that accepts an argument of ANY type
// and answers `T?`: the record when the concrete argument carries every field
// `T` declares, null otherwise -- including when the argument is not a record at
// all. That is what lets one function branch on "is this a T?" for a value whose
// type differs per call site (`fs.create_dir` takes a string or a `Path` this
// way); rejecting a non-record argument at compile time, as the checker once
// did, made the idiom impossible to write.
type Point = {
    x: int32
    y: int32
}

fun describe(v) -> string {
    if let p = Point.from(v) {
        return "Point({p.x}, {p.y})"
    }
    return "not a Point"
}

fun main() {
    // A record with the fields, nominal or anonymous.
    println(describe(Point { x: 1, y: 2 }))
    println(describe({ x: 3, y: 4 }))
    // A record missing a field.
    println(describe({ x: 5 }))
    // Values that are not records at all: each is null, not an error.
    println(describe("hello"))
    println(describe(42))
    println(describe(1.5))
    println(describe(true))
    println(describe([1, 2]))
    // The conversion's result is a plain nullable, so it compares to null.
    println(Point.from("hello") == null)
}
