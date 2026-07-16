// A child variant's annotated field must match the parent's annotation
// invariantly (fields are mutable storage).
type P =
    | A {
        x: int32
    }

type C: P =
    | A {
        x: string
    }

fun main() {
    println(1)
}
