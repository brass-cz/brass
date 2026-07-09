// Regression case: storing a reassigned nullable record into a record field
// corrupts the heap on the JIT.
//
// `a` starts as null and is then reassigned a record. Storing it into `B.a`
// makes the program free the same allocation twice. The typechecker accepts the
// file and the interpreter runs it, so only the LLVM back end is wrong:
//
//   $ prepoly check jit_double_free_nullable_record_field.pp
//   ok
//   $ prepoly repl jit_double_free_nullable_record_field.pp
//   ok
//   $ prepoly jit_double_free_nullable_record_field.pp
//   ok
//   double free or corruption (fasttop)      <- glibc aborts; the exact
//   [SIGABRT]                                   diagnosis varies between runs,
//                                               and SIGSEGV also shows up
//
// Three things are needed together: the nullable local, the reassignment, and
// the store into a record field. Assigning at the declaration
// (`let a: A? = A { x: 1 }`), or building the field directly
// (`B { a: A { x: 1 } }`), both lower correctly.

type A = { x: int32 }
type B = { a: A? }

fun main() {
    let a: A? = null
    a = A { x: 1 }
    let b = B { a: a }

    let stored = b.a
    if stored { assert(stored.x == 1, "the record survives the store") }
    println("ok")
}
