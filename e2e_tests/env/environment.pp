// The env library: a variable read singly, the bulk map, and the working
// directory. Only environment-independent answers are printed: the harness
// always sets PREPOLY_INCLUDE, so its presence (never its value) is the
// stable signal, and the two ways of reading it must agree.
import env.{ var, vars, current_dir }

fun main() {
    let include = var("PREPOLY_INCLUDE")!
    println(len(include) > 0)
    let all = vars()
    println(all.get_or("PREPOLY_INCLUDE", "<unset>") == include)
    println(all.size() > 0)
    println(current_dir()!.is_absolute())
}
