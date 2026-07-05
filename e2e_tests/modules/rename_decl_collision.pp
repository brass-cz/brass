// A rename whose local name is also declared in this module is rejected:
// the rename takes resolution precedence, so it would silently shadow `g`.
import veclib.{ dot as g }

fun g() -> int32 { return 1 }

fun main() {
    println(g())
}
