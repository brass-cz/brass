// Mixed int+float arithmetic converts to the common float type regardless of
// which side is the literal: a bare float literal next to an int-typed operand
// keeps its own class instead of being pinned to the int kind.
fun main() {
    let a: int32 = 3
    println(a + 0.5)
    println(0.5 + a)
    println(1 + 0.5)
    if a < 3.5 {
        println("lt ok")
    }
}
