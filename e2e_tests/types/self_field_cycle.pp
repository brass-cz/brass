// Field types are resolved like Hindley-Milner inference: each field gets a type
// variable and `Self.field` resolves to it. A field whose type refers back to
// itself through the `Self.field` chain is a circular unification (an
// occurs-check failure) and is rejected rather than expanded forever.

type Loop = {
    a: Self.b
    b: Self.a
    n: int64
}

fun main() {
    println(1)
}
