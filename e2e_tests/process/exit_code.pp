// A non-zero exit code and a failed spawn both come back as ordinary values:
// `false` exits 1, and a missing program is an Err.
import process.{ Command }

const child = Command.new("false").spawn()!
println("false exit: {child.wait()!}")

match Command.new("prepoly-no-such-program-xyz").spawn() {
    Ok { value } => println("unexpected ok"),
    Err { error } => println("spawn failed"),
}
