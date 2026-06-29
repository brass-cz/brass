fun copy(a: infer[]) {
    a.push(2)
    println(a) // should [1, 2]
}

fun reference(a: ref(mut(infer[]))) {
    a.push(3)
    println(a) // should [1, 3]
}

let a = [1]

copy(a)
println(a) // should [1]

reference(a)
println(a) // should [1, 3]
