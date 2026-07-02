// A scalar-element array shared with a spawned task is a SINGLE cown (its
// object header carries the lock): both sides' element writes are guarded, and
// pushes (whose realloc keeps the header) stay safe. Element-locking the raw
// int32 values as if they were cown pointers used to crash here.
fun main() {
    let box = [0]
    let log = ["seed"]
    spawn(() -> {
        let i = 0
        while i < 10000 {
            box[0] += 1
            log.push("x")
            i += 1
        }
    })
    let j = 0
    while j < 10000 {
        box[0] += 1
        log.push("y")
        j += 1
    }
    sync()
    println(box[0])
    println(log.len() - 1)
}
