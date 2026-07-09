// Regression case: indexing an array with a narrowed nullable panics the JIT.
//
// `string.find` returns `int64?`. After `if !i { return }` the checker narrows
// `i` to `int64` -- `prepoly check` accepts this file, and `prepoly repl` runs
// it and prints `b` twice. The LLVM back end, though, still hands the array
// index the nullable's pointer representation:
//
//   $ prepoly check jit_panic_index_narrowed_nullable.pp
//   ok
//   $ prepoly repl jit_panic_index_narrowed_nullable.pp
//   b
//   b
//   $ prepoly jit_panic_index_narrowed_nullable.pp
//   thread 'prepoly-main' panicked at crates/prepoly_jit_llvm/src/codegen.rs:3735:36:
//   Found PointerValue(..) but expected the IntValue variant
//
// Annotating the binding (`let j: int64 = i`) sidesteps it, so only the
// narrowed-but-uninferred path reaches the bad branch. Arithmetic on the same
// narrowed value (`i + 1`) already lowers correctly; it is the index operand
// that does not.

fun main() {
    let cs = "abc".chars()

    let i = "abc".find("b")
    if !i { return }
    assert(cs[i] == "b", "index by a narrowed nullable")

    // Same value copied into a fresh binding, still without an annotation.
    let j = i
    assert(cs[j] == "b", "index by a copy of a narrowed nullable")

    println("ok")
}
