// An unannotated array literal containing `null` infers as a nullable-element
// sequence, not a tuple: null unifies with any element type (`[4, null]` is
// `int32?`-elemented). A `const` binding is a fixed-length array (`int32?[4]`);
// a `let` binding is a growable slice (`int32?[]`).
const fixed = [4, 1, null, 65]

fun main() {
    println(fixed)
    let third = fixed[3]
    if third {
        println("present: {third}")
    }
    // The let form grows, accepting both null and plain pushes.
    let grow = [7, null, 9]
    grow.push(null)
    grow.push(2)
    println(grow)
    let second = grow[1]
    if second {
        println("second present")
    } else {
        println("second absent")
    }
    // A plain literal is unaffected; ununifiable elements still form a tuple.
    let plain = [1, 2, 3]
    plain.push(4)
    println(plain)
    let hetero = [1, "s"]
    println(hetero[1])
}
