// Numeric conversions: a conversion that may exceed the destination range
// returns a Result and must be unwrapped or matched.


fun bounded_byte(fail: bool) {
    if fail {
        return error("byte unavailable")
    }
    return uint8.from(7)!
}

fun main() {
    let small: uint8 = uint8.from(42)!
    println("uint8 ok = {small}")

    let too_big = uint8.from(300)
    match too_big {
        Ok { value } => println("unexpected ok {value}"),
        Err { error } => println("uint8 err = {error}"),
    }

    let parsed = int32.parse("2147483648")
    match parsed {
        Ok { value } => println("unexpected parse {value}"),
        Err { error } => println("parse err = {error}"),
    }

    let truncated = int32.from(3.9)!
    let widened = float64.from(truncated) + 0.5
    println("truncated+widened = {widened}")

    let exact: uint8 = bounded_byte(false)!
    println("bounded byte = {exact}")
}
