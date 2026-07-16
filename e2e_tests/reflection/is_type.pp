type P = {
    x: int32
}

// Each primitive class implements only its own `is_<type>` method, so one
// generic body dispatches per concrete type through member presence; a
// record has none of them and falls through. The call itself returns true.
fun kind(v) -> string {
    if v.is_string {
        return "string {v.is_string()}"
    } else if v.is_int32 {
        return "int32"
    } else if v.is_int64 {
        return "int64"
    } else if v.is_uint8 {
        return "uint8"
    } else if v.is_bool {
        return "bool"
    } else if v.is_float64 {
        return "float64"
    } else if v.is_array {
        return "array"
    }
    return "other"
}

fun main() {
    println(kind("hi"))
    println(kind(3))
    let big: int64 = 3
    println(kind(big))
    let byte: uint8 = 7
    println(kind(byte))
    println(kind(true))
    println(kind(1.5))
    println(kind([1, 2]))
    println(kind(P { x: 1 }))
    // A concrete receiver folds the same way.
    if "".is_string {
        println("literal")
    }
}
