// A `type Result` shadows the prelude's for the fallibility sugar, so its
// shape is validated at the declaration even when the module never uses the
// sugar.
type Result =
    | Good { v: int32 }
    | Bad

fun main() {
    println(1)
}
