// A `ref(mut(T))` parameter is a mutable reference: the callee mutates the
// caller's array in place. A plain (non-reference) array parameter -- annotated
// `int32[]` -- is passed by deep copy instead, so `snapshot` cannot change `a`.
fun append(xs: ref(mut(int32[])), v: int32) {
    xs.push(v)
}

fun snapshot(xs: int32[]) {
    xs.push(99)
    println(xs)
}

let a = [1, 2]
append(a, 3)
snapshot(a)
println(a)
