// The error-handling core of the prelude.
//
// `Result` is the type behind the language's fallibility sugar: a `-> T!`
// return type is `Result<T, E>`, `error(x)` constructs `Result.Err`, a bare
// return from a fallible function is wrapped in `Result.Ok`, and `!`
// propagates `Err` to the caller. The compiler resolves those constructs to
// this declaration; the sum itself is an ordinary two-variant nominal with
// no special runtime shape (tag 0 = Ok, tag 1 = Err).
type Result =
    | Ok {
        value
    }
    | Err {
        error
    }

// A source position. A function whose LAST parameter is annotated `Location`
// receives its caller's position automatically when the call omits it: the
// compiler fills the argument with the call site. `error(..)` and
// `Result.context(..)` use this to build error traces.
type Location = {
    file: string
    line: int32
    col: int32
}

fun Location.display(self) -> string {
    return "{self.file}:{self.line}:{self.col}"
}

// One step of an error trace: the message `Result.context` attached, at the
// position of the `context` call.
type Frame = {
    message: string
    location: Location
}

// What `error(..)` wraps its payload in: the payload itself, the position
// the error was raised at, and the trace frames `Result.context` attached
// on the way up (oldest first).
type Error = {
    value
    location: Location
    frames: Frame[]
}

// The rendered trace: the newest context first, one indent level per frame,
// the original error last. The unhandled-`!` abort prints this verbatim.
fun Error.display(self) -> string {
    let out = ""
    let indent = ""
    let i = self.frames.len() - 1
    while i >= 0 {
        let f = self.frames[i]
        out = out + indent + "[" + f.location.display() + "] unhandled error: " + f.message + "\n"
        indent = indent + "    "
        i = i - 1
    }
    return out + indent + "[" + self.location.display() + "] unhandled error: {self.value}"
}

// Raise an error: wrap the payload with the caller's position. The `loc`
// parameter is the implicit caller-location -- calls omit it.
fun error(value, loc: Location) -> infer! {
    // The annotation types the empty literal for the back end.
    let frames: Frame[] = []
    return Result.Err { error: Error { value: value, location: loc, frames: frames } }
}

// Attach a context message to a failed Result, keeping a success untouched.
// An `Error` payload gains a trace frame at the caller's position; any other
// payload is wrapped into an `Error` first (its base position is the
// `context` call, the nearest position known).
fun Result.context(self, ctx: string, loc: Location) {
    return match self {
        Err { error } => {
            if error.frames {
                error.frames.push(Frame { message: ctx, location: loc })
                self
            } else {
                Result.Err {
                    error: Error {
                        value: error,
                        location: loc,
                        frames: [Frame { message: ctx, location: loc }]
                    }
                }
            }
        }
        Ok { value } => self
    }
}

// The unhandled-`!` abort renders its Err payload through this: a payload
// carrying a trace (an `Error`) renders itself, anything else keeps the
// plain prefix form. The `frames` presence test dispatches statically per
// payload type.
fun _render_unhandled(e) -> string {
    if e.frames {
        return e.display()
    }
    return "unhandled error: {e}"
}
