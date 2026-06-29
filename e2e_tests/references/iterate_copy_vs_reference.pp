// Iterating binds each element by reference of the array's kind, so reassigning
// the loop variable writes back into the array (`e *= 2` doubles in place).
fun double_ref(a: ref(mut(infer))) {
    for e in a {
        e *= 2
    }
    println(a)
}

// A plain `infer` parameter (no ref/mut) is passed by deep copy, so the loop
// mutates only the callee's copy and the caller's array is unchanged.
fun double(a: infer) {
    for e in a {
        e *= 2
    }
    println(a)
}

let b = [1, 2, 3]

double(b)     // the copy is doubled -> [2, 4, 6]
println(b)    // b is unchanged       -> [1, 2, 3]
double_ref(b) // b is doubled in place -> [2, 4, 6]
println(b)    // b stays doubled       -> [2, 4, 6]
