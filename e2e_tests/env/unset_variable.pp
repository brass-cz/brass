// An unset environment variable is an error, not an empty string; unhandled
// in `main`, it aborts with the variable's name in the message.
import env.{ var }

fun main() {
    let v = var("PREPOLY_E2E_SURELY_UNSET_VARIABLE")!
    println(v)
}
