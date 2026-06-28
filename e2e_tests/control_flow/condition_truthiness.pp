// A condition may be of any type. A nullable tests non-null (unchanged), while a
// non-nullable, non-bool value is unconditionally truthy -- here a zero integer
// still takes the `then` arm rather than being treated as false.
fun describe(n: int32?) -> string {
    if n {
        return "present"
    } else {
        return "absent"
    }
}

fun main() {
    let present: int32? = 5
    let absent: int32? = null
    println("{describe(present)}")
    println("{describe(absent)}")

    let zero: int32 = 0
    if zero {
        println("int-truthy")
    } else {
        println("int-falsy")
    }
}
