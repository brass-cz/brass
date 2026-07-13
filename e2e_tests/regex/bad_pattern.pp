// A pattern the engine rejects is reported by `Regex.new`, so every method on a
// compiled `Regex` is infallible. Unhandled in `main`, the compile error aborts.
//
// This engine has no backreferences and no lookaround (neither is expressible
// in a finite automaton), so a pattern using one fails to compile here rather
// than quietly meaning something else -- which is what this case pins.
import regex.{ Regex }

fun main() {
    match Regex.new("(unclosed") {
        Ok { value } => println("BUG: an unbalanced group compiled"),
        Err { error } => println("unbalanced group rejected"),
    }
    match Regex.new("(a)\\1") {
        Ok { value } => println("BUG: a backreference compiled"),
        Err { error } => println("backreference rejected"),
    }
    const lookahead = Regex.new("foo(?=bar)")!
    println("BUG: a lookahead compiled: {lookahead.pattern}")
}
