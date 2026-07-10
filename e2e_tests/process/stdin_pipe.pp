// A duplex pipe: write to `cat`'s stdin, read the same bytes from its stdout.
import process.{ Command, Stdio }
import std.net.{ to_bytes, to_text }

const child = Command.new("cat")
    .stdin(Stdio.Pipe)
    .stdout(Stdio.Pipe)
    .spawn()!

const sink = child.stdin()!
sink.write(to_bytes("round trip\n"))!
sink.close()!

const out = child.stdout()!
print(to_text(out.read(256)!)!)
println("exit: {child.wait()!}")
