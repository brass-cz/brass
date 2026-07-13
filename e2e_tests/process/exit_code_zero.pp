// `exit(code)` ends THIS process with the code given: nothing after it runs.
//
// The text before it is printed WITHOUT a trailing newline. Standard output is
// buffered by line, so that text is still sitting in the buffer when `exit` is
// called -- it reaches the terminal only because `exit` flushes first. Printing
// it here is what pins that: were the flush dropped, this case would produce
// nothing at all.
import process.{ exit }

fun main() {
    println("work done")
    print("no trailing newline")
    exit(0)
    println("MUST NOT PRINT: exit does not return")
}
