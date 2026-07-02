// input() reads one line fallibly (string!): the bare value binds after `!`.
// With no stdin attached the line is empty, which is still an Ok result.
fun main() {
    let line = input()!
    println("[{line}]")
}
