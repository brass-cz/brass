// Regression case: `prepoly check` accepts a method call that neither runtime
// can run.
//
// `if a { .. }` narrows `a` from `A?` to `A`, and the checker resolves
// `a.show()` against that. Both back ends then look the method up on the
// unnarrowed `A?` and give up:
//
//   $ prepoly check check_accepts_method_on_nullable_record.pp
//   ok
//   $ prepoly repl check_accepts_method_on_nullable_record.pp
//   error: program uses constructs outside the REPL runtime's supported subset:
//   no method `show` for `A<x=int32>?`
//   $ prepoly check_accepts_method_on_nullable_record.pp
//   error: program uses constructs outside the typed (Value-free) subset:
//   no method `show` for `A<x=int32>?`
//
// Field access on the same narrowed value (`a.x`) works, and so does a method
// call on a freshly built `A`, so it is method dispatch alone that ignores the
// narrowing. Passing the narrowed value to a function taking a plain `A` does
// not help either: the parameter keeps the nullable representation.
//
// Either the checker should reject this, or the runtimes should honour the
// narrowing -- honouring it is what makes `T?` usable for record types.

type A = { x: int32 }
type Box = { a: A? }

fun A.show(self) -> string {
    return "x={self.x}"
}

fun main() {
    let box = Box { a: A { x: 5 } }

    let a = box.a
    if a { assert(a.show() == "x=5", "method call on a narrowed nullable record") }
    println("ok")
}
