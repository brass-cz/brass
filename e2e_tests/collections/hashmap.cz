// HashMap end-to-end: insert/update/get/delete, growth across the load-factor
// resize, and a hashed key reused across operations (the string-alias path).
// Output is kept order-independent (lookups and counts, not key order).

fun main() {
    // string -> int32: count words, reusing each loop key in get_or + set.
    let counts = HashMap.new()
    let words = ["a", "b", "a", "c", "a", "b"]
    for w in words {
        counts.set(w, counts.get_or(w, 0) + 1)
    }
    println("a={counts.get("a")} b={counts.get("b")} c={counts.get("c")} d={counts.get("d")}")
    println("size={counts.size()} has_a={counts.contains_key("a")}")
    println("deleted_a={counts.delete("a")} has_a={counts.contains_key("a")} size={counts.size()}")

    // int32 -> int32 with enough entries to force several resizes.
    let big = HashMap.new()
    let k = 0
    while k < 50 {
        big.set(k, k * k)
        k += 1
    }
    big.set(7, 777)
    println("big_size={big.size()} sq49={big.get(49)} k7={big.get(7)} k50={big.get_or(50, -1)}")
    big.clear()
    println("cleared_empty={big.is_empty()} size={big.size()}")
}
