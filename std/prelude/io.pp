// Standard input/output, written in Prepoly on the runtime File primitives
//. Part of the implicit prelude.

/**
 * Write a value's text to standard output, without a trailing newline.
 * Values are combined with string interpolation (`"{a} {b}"`), so a single
 * argument is the idiomatic form.
 */
fun print(value) -> void {
    let out = File.stdout()
    out.write(_string_bytes(string.from(value)))
}

/** Like `print`, followed by a newline. */
fun println(value) -> void {
    let out = File.stdout()
    out.write(_string_bytes(string.from(value)))
    out.write(_string_bytes("\n"))
}

/** Read one line from standard input, without the trailing newline. */
fun input() {
    let stdin = File.stdin()
    let buf = []
    while true {
        let byte = stdin.read(1)!
        if len(byte) == 0 {
            break
        }
        if byte[0] == 10 {
            break
        }
        buf.push(byte[0])
    }
    return _string_from_bytes(buf)!
}

/** Read the whole file at `path` as text. Fallible: returns a `Result`. */
fun read_file(path: string) {
    let f = open(path, "r")!
    let size = f.size()!
    let bytes = f.read(size)!
    f.close()!
    return _string_from_bytes(bytes)!
}

/** Write `content` to the file at `path`, truncating it. Fallible: returns a `Result`. */
fun write_file(path: string, content: string) {
    let f = open(path, "w")!
    f.write(_string_bytes(content))!
    f.close()!
}
