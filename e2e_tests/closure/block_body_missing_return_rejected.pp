// Binding the call result of a block-bodied closure with no `return` is a
// compile error: the block's trailing expression is not its value.
fun main() {
    let g = (x: int32) -> {
        x + 1
    }
    let y = g(1)
    println(y)
}
