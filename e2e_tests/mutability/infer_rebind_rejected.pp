// An `infer` parameter is read-only as a BINDING too: rebinding the name is
// rejected like member mutation, not silently applied to the private copy.
fun f(a: infer) {
    a = 3
    println(a)
}

fun main() {
    f(1)
}
