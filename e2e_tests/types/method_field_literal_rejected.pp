type P = {
    x: int32
}

fun P.get(self) -> int32 {
    return self.x
}

fun main() {
    let a = P { x: 1, get: 9 }
    println(a.get())
}
