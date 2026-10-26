type A = {
    func:(int32)->int32
}
fun main(){
    const f = (x)->2*x
    println(f(8))  //OK
    const a = A{func:(x)->x-2}
    println(a.func(4)) //error: `A` has no method `func`
    const g = a.func
    println(g(4))      //error: program uses constructs outside the typed (Value-free) subset
}
