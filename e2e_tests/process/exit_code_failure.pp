// A non-zero `exit` reports failure to whatever ran the program, and the
// diagnostic written to standard error before it is flushed on the way out
// (stderr is unbuffered here, but `exit` flushes both streams regardless).
import process.{ exit }
import fs.{ File }

fun main() {
    let err = File.stderr()
    err.write(to_bytes("giving up: nothing to do\n"))!
    exit(3)
    println("MUST NOT PRINT")
}
