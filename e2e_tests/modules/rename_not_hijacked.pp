// A renamed import (`norm as dist`) must resolve to the origin's `norm`,
// NOT to hijacklib's `dist`, which happens to be unique program-wide and is
// loaded transitively -- this module never imports it.
import renamelib.{ norm as dist }

fun main() {
    println(dist())
}
