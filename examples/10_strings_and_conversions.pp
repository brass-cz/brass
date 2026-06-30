// String utilities (prelude) and explicit numeric conversions. Numeric operators
// implicitly convert mixed numeric operands to a common type; use `from`/`parse`
// when the conversion itself is the operation you want to spell out.

fun main() {
    let csv = "alice,bob,carol"
    let names = csv.split(",")
    println("count = {len(names)}")
    println("joined = {names.join(" | ")}")
    let upper = to_upper("hello")
    println("upper = {upper}")
    println("trimmed = '{trim("   spaced   ")}'")
    println("starts = {starts_with("prepoly", "pre")}")
    println("replace = {replace("a-b-c", "-", "+")}")

    // Conversions: parse returns a Result, `from` converts between numbers.
    let n = int32.parse("123")!
    let f = float64.from(n) + 0.5
    println("n = {n}, f = {f}")
    println("string.from = {string.from(42)} and {string.from(true)}")
}
