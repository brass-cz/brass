// Deletion leaves tombstones that probing passes through and insertion reuses;
// growth drops them. Delete-then-reinsert must find the reinserted key, keys
// deleted before a grow must stay deleted after it, and size bookkeeping must
// survive the churn.
fun main() {
    let m = HashMap.new()
    let i = 0
    while i < 6 {
        m.set(i, i * 10)
        i += 1
    }
    // Delete half, creating tombstones in the probe chains.
    println(m.delete(0))
    println(m.delete(2))
    println(m.delete(4))
    println("size={m.size()}")
    // Reinsert one deleted key (reuses a tombstone) and add fresh keys to
    // push count+tombs over the load factor, forcing a grow.
    m.set(2, 222)
    let j = 100
    while j < 110 {
        m.set(j, j)
        j += 1
    }
    println("size={m.size()}")
    println("k2={m.get(2)} k0={m.get_or(0, -1)} k4={m.get_or(4, -1)}")
    println("k1={m.get(1)} k105={m.get(105)}")
    println(m.contains_key(0))
    println(m.contains_key(2))
}
