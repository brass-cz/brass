// A declared sum subtype may not add variants the parent lacks: the parent
// could not represent such a value at a coercion site.
type MyResult: Result =
    | Ok {
        value
    }
    | Err {
        error
    }
    | Pending

fun main() {
    println(1)
}
