// A declared sum subtype must cover every parent variant.
type MyResult: Result =
    | Ok {
        value
    }

fun main() {
    println(1)
}
