// A block-bodied closure yields what it RETURNS; the trailing expression is
// not the value. The explicit-return form produces the value on both back
// ends, and binding the no-return form's (void) call result is a compile
// error rather than an opaque back-end rejection.
fun main() {
    let g = (x: int32) -> {
        return x + 1
    }
    let y = g(1)
    println(y)
}
