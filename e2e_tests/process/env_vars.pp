// `env(name, value)` sets a variable in the child. The child otherwise INHERITS
// this process's environment, so `env` adds to it (or overrides one entry)
// rather than replacing it -- which is what the PATH check below pins, since a
// replaced environment would leave `sh` unable to find anything.
import process.{ Command, Stdio }

// Run `sh -c script` with the given overrides applied, and answer what it wrote.
fun output_of(cmd) -> string! {
    const child = cmd.stdout(Stdio.Pipe).spawn()!
    const done = child.output()!
    return to_text(done.stdout)!.trim()
}

fun main() {
    // One variable, reaching the child.
    println(output_of(
        Command.new("sh")
            .args(["-c", "echo $GREETING"])
            .env("GREETING", "hello")
    )!)

    // Several, chained. A name set twice keeps the LAST value, as an assignment
    // would.
    println(output_of(
        Command.new("sh")
            .args(["-c", "echo $A-$B"])
            .env("A", "first")
            .env("B", "two")
            .env("A", "one")
    )!)

    // The parent's environment is still there: PATH was never set here.
    println(output_of(
        Command.new("sh")
            .args(["-c", "test -n \"$PATH\" && echo inherited"])
    )!)

    // An inherited variable can be overridden.
    println(output_of(
        Command.new("sh")
            .args(["-c", "echo $HOME"])
            .env("HOME", "/nowhere")
    )!)

    // A command with no overrides at all still runs.
    println(output_of(Command.new("echo").arg("no overrides"))!)
}
