---
title: "Standard library"
description: "Every standard-library module and builtin, with signatures."
---

The standard library has two layers:

- **The implicit prelude** — the modules under `std/prelude/` (`io`, `array`,
  `string`, `math`, `conv`, `assert`) plus the runtime builtins. Their public
  names are in scope in every program with no import.
- **Import-only modules** — everything else under `std/`
  (`std.collections`): imported explicitly, e.g.
  `import std.collections.{ HashMap }`, and loaded on demand.

Most of the library is written in prepoly itself, on top of a small set of
runtime primitives. Identifiers beginning with `_` (e.g. `_string_bytes`,
`_panic`) are those internals — do not call them directly.

Reserved builtin names that cannot be redefined: `len`, `spawn`, `with`,
`sync`, `error`, `fields`, `typeof`.

## Builtins

| Function                           | Signature                    | Notes                                                   |
| ---------------------------------- | ---------------------------- | ------------------------------------------------------- |
| `len(x)`                           | `(array or string) -> int64` | element count / byte length; also callable as `x.len()` |
| `error(x)`                         | constructs `Result.Err`      | see [Result](/references/types/#result)                 |
| `fields(x)`, `typeof(x)`           | compile-time                 | see [Reflection](/references/reflection/)               |
| `spawn(f)`, `with(c, f)`, `sync()` | concurrency                  | see [Concurrency](/references/concurrency/)             |

Growable arrays (`T[]`) have these built-in methods (all rejected on
fixed-length `T[n]`):

| Method             | Signature                             |
| ------------------ | ------------------------------------- |
| `arr.push(v)`      | `(T) -> void`                         |
| `arr.pop()`        | `() -> T?` — `null` when empty        |
| `arr.insert(i, v)` | `(int64, T) -> void`                  |
| `arr.remove(i)`    | `(int64) -> T`                        |
| `arr.len()`        | `() -> int64` (both `T[]` and `T[n]`) |

Indexing is bounds-checked at runtime on both array kinds.

## `std.io`

| Function         | Signature       | Behavior                                                            |
| ---------------- | --------------- | ------------------------------------------------------------------- |
| `print(value)`   | `(any) -> void` | write the value's text to stdout; combine values with interpolation |
| `println(value)` | `(any) -> void` | `print` plus a newline                                              |
| `input()`        | `() -> string!` | one line from stdin, without the trailing newline                   |

Files live in the [`fs` library](#fs-a-library-not-std), not the prelude:
opening and moving bytes needs native code, so it ships as a plugin like
`process` and `path`.

## `std.array`

Methods on any array (`fun infer[].m`), so `arr.map(f)` works with no import:

| Method              | Behavior                                         |
| ------------------- | ------------------------------------------------ |
| `map(f)`            | new array of `f(item)`                           |
| `filter(pred)`      | elements where `pred(item)` is true              |
| `fold(init, f)`     | left fold with accumulator                       |
| `each(f)`           | run `f` for side effects                         |
| `slice(start, end)` | copy of the half-open range; indices are `int64` |
| `reverse()`         | reversed copy                                    |
| `contains(x)`       | membership by `==`                               |
| `sort()`            | ascending copy (orders with `<`/`>`)             |

These return new arrays; only the builtin `push`/`pop`/`insert`/`remove`
mutate in place.

## `std.string`

String positions are UTF-8 **byte** offsets throughout: `len`, `find`, and
slicing agree on byte positions; the per-character helpers advance by each
character's byte length.

| Method                                | Signature                     | Behavior                                                   |
| ------------------------------------- | ----------------------------- | ---------------------------------------------------------- |
| `s.split(sep)`                        | `(string) -> string[]`        | one field per separator boundary; empty `sep` yields `[s]` |
| `s.trim()`                            | `() -> string`                | strip leading/trailing ASCII whitespace                    |
| `s.starts_with(p)` / `s.ends_with(p)` | `(string) -> bool`            |                                                            |
| `s.find(sub)`                         | `(string) -> int64?`          | byte offset of first occurrence, else `null`               |
| `s.replace(old, new)`                 | `(string, string) -> string`  | replace every occurrence; empty `old` is a no-op           |
| `s.chars()`                           | `() -> string[]`              | one-character strings, multibyte-safe                      |
| `s.to_upper()` / `s.to_lower()`       | `() -> string`                | ASCII case change                                          |
| `parts.join(sep)`                     | `string[].(string) -> string` | join a _string array_ with `sep`                           |
| `s.len()`                             | `() -> int64`                 | byte length                                                |

There is no public substring-slicing method and no direct `s[i]` indexing; use
`chars`, `split`, `find`, `replace`.

## `std.math`

`abs(x)`, `min(a, b)`, `max(a, b)` are polymorphic free functions (any type
supporting `<` and, for `abs`, `-`). The float routines take and return
`float64`: `sqrt(x)`, `floor(x)`, `ceil(x)`, `pow(base, exp)`.

## `std.conv`

Constants: `INT32_MAX`, `INT32_MIN`, `INT64_MAX`, `INT64_MIN`.

Byte/string conversion: `to_bytes(s) -> uint8[]` is the UTF-8 bytes of a
string, ready to `write`/`send_to`; `to_text(bytes) -> string!` decodes bytes
as UTF-8 text and fails on invalid input.

Free-function aliases of the conversion methods: `int32_from(x) -> int32!`,
`int32_parse(s) -> int32!`, `float64_from(x) -> float64`,
`float64_parse(s) -> float64!`, `string_from(x) -> string`. The method forms
(`T.from`, `T.parse`) are described in the
[type system](/references/types/#explicit-conversions).

## `std.assert`

`assert(cond: bool, msg: string?)` aborts the program when `cond` is false.
`msg` is a trailing nullable parameter, so `assert(cond)` works and prints a
generic message.

## `process` (a library, not `std`)

```prepoly norun
import process.{ Command, Stdio }
```

Spawn and control child processes. Unlike the modules above this is not part
of `std`: its native half is a Rust plugin (a `cdylib` built against the
`prepoly_plugin` crate) rather than a runtime builtin, so it ships as a
library under `libraries/`. A distributed toolchain finds `libraries/`
beside its binary automatically; when running from a repo checkout, build
the plugin once with `libraries/build.sh` and point `PREPOLY_INCLUDE` at
that directory (one entry serves every library that lives there):

```
PREPOLY_INCLUDE=/path/to/prepoly/libraries
```

`Command` is a builder — each method mutates the command and returns it, so
calls chain — and `spawn` starts the process. A standard stream configured as
`Stdio.Pipe` is reachable through the `Child` as a `File`
(`read`/`write`/`close`); `Inherit` (the default) shares this process's stream
and `Null` discards it.

| Method / function              | Signature                     | Behavior                                     |
| ------------------------------ | ----------------------------- | -------------------------------------------- |
| `Command.new(program)`         | `(string) -> Command`         | `program` is looked up on `PATH`             |
| `cmd.arg(value)`               | `(string) -> Command`         | append one argument                          |
| `cmd.args(values)`             | `(string[]) -> Command`       | append several arguments                     |
| `cmd.env(name, value)`         | `(string, string) -> Command` | set a variable in the child                  |
| `cmd.stdin/stdout/stderr(mode)`| `(Stdio) -> Command`          | connect a stream (`Inherit`/`Pipe`/`Null`)   |
| `cmd.spawn()`                  | `() -> Child!`                | start the process                            |
| `child.stdin/stdout/stderr()`  | `() -> File!`                 | a piped stream (requires `Stdio.Pipe`)       |
| `child.wait()`                 | `() -> int32!`                | block for exit; returns the exit code        |
| `child.output()`               | `() -> Output!`               | drain the piped streams, then wait           |

`Stdio` is `| Inherit | Pipe | Null`. Piped streams are `File`s, so the
prelude byte helpers `to_bytes`/`to_text` convert their contents. The
accessors may be called repeatedly: each hands back the same `File`.

The child **inherits this process's environment**, and `env` adds to it (or
overrides one entry of it) rather than replacing it; setting the same name
twice keeps the last value. There is no way to unset an inherited variable or
to start from an empty environment.

```prepoly norun
const child = Command.new("sh")
    .args(["-c", "echo $GREETING"])
    .env("GREETING", "hello")
    .stdout(Stdio.Pipe)
    .spawn()!
```

`wait` blocks for exit and nothing else, so a child writing more to a pipe
than the OS buffers (about 64KiB on Linux) blocks on the full pipe while
`wait` blocks on the child. Read the piped streams before waiting, or use
`output`, which reads them while the child runs and cannot deadlock:

```prepoly norun
import process.{ Command, Stdio }

let child = Command.new("git")
    .args(["log", "--oneline"])
    .stdout(Stdio.Pipe)
    .spawn()!

// `Output` is `{ code: int32, stdout: uint8[], stderr: uint8[] }`; a stream
// that was not piped (or was taken through its accessor) comes back empty.
let result = child.output()!
print(to_text(result.stdout)!)
println("exit: {result.code}")
```

Waiting is idempotent: a second `wait` returns the same code, and a piped
stream stays readable afterwards, since the pipe still holds what the child
wrote before it exited.

Everything here runs on either back end: a piped stream is an `fs` `File`,
and the fs plugin executes natively under the interpreter too.

## `path` (a library, not `std`)

```prepoly norun
import path.{ Path }
```

Filesystem paths. Like `process` this is a library, not `std`: asking the
operating system what exists needs native code, so its other half is a plugin
built by `libraries/build.sh`.

```
PREPOLY_INCLUDE=/path/to/prepoly/libraries
```

A `Path` is a sequence of components, absolute exactly when its first component
is the root `/`. Empty and repeated separators are dropped when a path is
parsed, so `/usr//lib/` and `/usr/lib` are the same path. Every method that
answers with a path builds a new one, so a `Path` may be shared freely.

| Method / function            | Signature                  | Behavior                                        |
| ---------------------------- | -------------------------- | ----------------------------------------------- |
| `Path.parse(s)`              | `(string) -> Path`         | absolute when `s` starts with `/`               |
| `Path.current_dir()`         | `() -> Path!`              | the working directory                           |
| `Path.home()` / `temp_dir()` | `() -> Path!`              | the home / temporary directory                  |
| `p.to_string()`              | `() -> string`             | `.` for the empty path                          |
| `p.components()`             | `() -> string[]`           | a copy, the root included as `/`                |
| `p.depth()`                  | `() -> int64`              | component count (`len` is a reserved builtin)   |
| `p.is_absolute()` / `is_root()` | `() -> bool`            | shape of the path, not what is on disk          |
| `p.parent()` / `basename()`  | `() -> Path`               | the root is its own parent                      |
| `p.join(s)`                  | `(string \| string[] \| Path) -> Path` | absolute `s` replaces `p`           |
| `p.stem()` / `extension()`   | `() -> string` / `string?` | `.gitignore` is all stem                        |
| `p.with_extension(ext)`      | `(string) -> Path`         | empty `ext` removes it                          |
| `p.normalize()`              | `() -> Path`               | drops `.`, resolves `..`, no filesystem access  |
| `p.to_absolute()`            | `() -> Path!`              | against the working directory; links unresolved |
| `p.to_relative(base)`        | `(Path) -> Path!`          | so that `base.join(result)` is `p` again        |
| `p.starts_with(base)` / `equals(other)` | `(Path) -> bool` | component-wise                                  |
| `p.exists()` / `is_dir()` / `is_file()` | `() -> bool`    | false for a path that is not there              |
| `p.is_sym_link()`            | `() -> bool`               | about the link itself, not its target           |
| `p.canonicalize()`           | `() -> Path!`              | resolves links; the path must exist             |
| `p.read_link()`              | `() -> Path!`              | where a symbolic link points                    |
| `p.entries()`                | `() -> Path[]!`            | a directory's entries                           |
| `p.file_size()`              | `() -> int64!`             | size in bytes                                   |

`join` takes a string, an array of components, or another `Path` through one
parameter. It is not overloading: the argument's members decide which arm of
the body survives compilation, as described under
[member presence](/references/reflection/#member-presence-xm-without-a-call).

A file's own location is not a method here. Every module is loaded with a
private `_PATH` constant holding its absolute source path, so the path of the
file you are writing is `Path.parse(_PATH)` — and an imported module reads its
own, not yours.

```prepoly norun
import path.{ Path }

const here = Path.parse(_PATH).parent()
for entry in here.join("assets").entries()! {
    // `extension` is a `string?`: a name without one has no extension to test.
    if let ext = entry.extension() {
        if ext == "png" {
            println(entry.basename().to_string())
        }
    }
}
```

## `fs` (a library, not `std`)

```prepoly norun
import fs.{ File, read_file, write_file, create_dir, remove_dir }
```

File handles, byte I/O, and directories. Like the other libraries this is a
plugin under `libraries/`, with the same setup — automatic for a distributed
toolchain, `libraries/build.sh` + `PREPOLY_INCLUDE` from a repo checkout.

| Function / method           | Signature                   | Behavior                                          |
| --------------------------- | --------------------------- | -------------------------------------------------- |
| `File.open(path, mode)`     | `(string or Path, string) -> File!` | `"r"` read, `"w"` truncate+create, `"a"` append |
| `read_file(path)`           | `(string or Path) -> string!` | whole file as text                               |
| `write_file(path, content)` | `(string or Path, string) -> void!` | write text, truncating                     |
| `create_dir(path)`          | `(string or Path) -> void!` | recursive, like `mkdir -p`                         |
| `remove_dir(path)`          | `(string or Path) -> void!` | recursive, like `rm -r`                            |
| `f.read(n)`                 | `(int64) -> uint8[]!`       | up to `n` bytes; fewer at end-of-file              |
| `f.write(bytes)`            | `(uint8[]) -> int64!`       | write all of `bytes`                               |
| `f.seek(pos)`               | `(int64) -> void!`          | absolute reposition                                |
| `f.size()`                  | `() -> int64!`              | by path (see below)                                |
| `f.close()`                 | `() -> void!`               | idempotent; standard streams are never closed      |
| `File.from_fd(fd)`          | `(int64) -> File`           | adopt an open descriptor (a pipe, a socket)        |
| `File.stdin/stdout/stderr()`| `() -> File`                | the standard streams                               |

`size()` is answered by the `path` library — a stat by name needs no open
descriptor — so it works exactly for files opened by path; an adopted
descriptor or standard stream has no path to ask about and reports an error.
`File.from_fd` is how the `process` and `net` libraries hand their pipes and
sockets to the ordinary read/write/close methods.

**Every path a function in this library takes may be a string or a `Path`** —
`File.open`, `read_file`, `write_file`, `create_dir`, `remove_dir` — so a path
built with the `path` library needs no `to_string()` on the way in. (The arm
that fits the argument is the only one compiled, so neither form costs the
other anything.)

`create_dir` and `remove_dir` are both recursive: `create_dir` makes every missing parent
and treats an existing directory as success, while `remove_dir` takes the whole
tree, removing a symbolic link inside it as a link rather than following it. A
directory that is not there is an **error** for `remove_dir`, not a silent
success — a typo in a destructive call must not read as "done".

File I/O runs on both back ends: the plugin executes natively whether the
program is JIT-compiled or interpreted, so the old "the REPL refuses file
I/O" rule is gone (only `spawn` remains JIT-only). The playground has no
filesystem, so the examples here are not runnable in it.

## `env` (a library, not `std`)

```prepoly norun
import env.{ args, var, vars, current_dir }
```

The process environment: command-line arguments, environment variables, and
the working directory. A plugin under `libraries/`, with the same setup as
the others — automatic for a distributed toolchain, `libraries/build.sh` +
`PREPOLY_INCLUDE` from a repo checkout. Not runnable in the playground.

| Function        | Signature          | Behavior                                          |
| --------------- | ------------------ | ------------------------------------------------- |
| `args()`        | `() -> string[]`   | the program file, then everything written after it |
| `var(name)`     | `(string) -> string!` | an unset variable is an error, not `""`        |
| `vars()`        | `() -> HashMap`    | every variable, as a `string -> string` map       |
| `current_dir()` | `() -> Path!`      | the working directory, as a `path` `Path`         |

Everything after the program file on the command line belongs to the
program, verbatim — flags included, no separator needed:

```sh
prepoly main.pp --verbose input.txt
```

gives `args() == ["main.pp", "--verbose", "input.txt"]` — the program file
as written, then the arguments (index `0` is the program, as in C's `argv`).
The same holds for `prepoly repl main.pp ...`. In an interactive REPL
session, or under an embedder that passes no arguments, `args()` is empty.

## `hash` (a library, not `std`)

```prepoly norun
import hash.{ sha256, hmac_sha256, hex, equal, Hasher }
```

Message digests (MD5, SHA-1, SHA-2) and HMAC. A plugin under `libraries/`
wrapping the RustCrypto implementations — these algorithms are built from
wrapping 32/64-bit arithmetic, which prepoly does not have, so a prepoly
implementation would be a hand-masked emulation whose failure mode is a
silently wrong digest.

A digest is a `uint8[]`: the algorithm's raw bytes. Hash text by its UTF-8
bytes with the prelude's `to_bytes`, and render the result with `hex`:

```prepoly norun
println(hex(sha256(to_bytes("abc"))))
// ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
```

| Function                       | Signature                            | Digest size |
| ------------------------------ | ------------------------------------ | ----------- |
| `md5(data)`                    | `(uint8[]) -> uint8[]`               | 16 bytes    |
| `sha1(data)`                   | `(uint8[]) -> uint8[]`               | 20 bytes    |
| `sha224` / `sha256`            | `(uint8[]) -> uint8[]`               | 28 / 32     |
| `sha384` / `sha512`            | `(uint8[]) -> uint8[]`               | 48 / 64     |
| `hmac_sha1/sha256/sha512(k,d)` | `(uint8[], uint8[]) -> uint8[]`      | 20 / 32 / 64 |
| `hex(bytes)`                   | `(uint8[]) -> string`                | lowercase   |
| `unhex(text)`                  | `(string) -> uint8[]!`               | inverse of `hex` |
| `equal(a, b)`                  | `(uint8[], uint8[]) -> bool`         | constant-time |

For input that is not in memory at once (a file read in chunks, a socket
stream), `Hasher` is the incremental form. `finalize` **consumes** the hasher
— a digest cannot be resumed once taken, so a second call is an error rather
than a meaningless second answer:

```prepoly norun
let h = Hasher.sha256()!      // also .md5() .sha1() .sha224() .sha384() .sha512()
h.update(chunk)!
h.update(next)!
println(hex(h.finalize()!))
```

**Security.** `md5` and `sha1` are broken against collision attacks: use them
only to interoperate with something that already speaks them (a published MD5
checksum, a git object id), never to decide whether two inputs are "the same".
Prefer `sha256`/`sha512`. Authenticate a message with `hmac_sha256`, not
`sha256(key + data)` (which is forgeable by length extension). Compare a
digest or MAC against an attacker-supplied one with `equal`, not `==`: an
early-exit comparison leaks how many leading bytes of a forgery were right.
All of these are **fast** hashes — storing a password needs a purpose-built
slow KDF (argon2, scrypt, bcrypt), which this library deliberately does not
offer, so that a fast hash cannot be mistaken for one.

## `regex` (a library, not `std`)

```prepoly norun
import regex.{ Regex, escape }
```

Regular expressions, on Rust's `regex` engine: a finite automaton, so matching
is **linear** in the subject's length however the pattern is written — a regex
over untrusted input cannot blow up the way a backtracking engine does. The
price is that **backreferences (`\1`) and lookaround (`(?=..)`, `(?<=..)`) do
not exist**; a pattern using one fails to compile rather than quietly meaning
something else. Everything else is the usual syntax: classes (`\d`, `\w`,
`\p{Greek}`), repetition (`*`, `+`, `?`, `{m,n}`, each with a lazy `?` form),
alternation, anchors (`^`, `$`, `\b`), groups (`(..)`, `(?:..)`,
`(?<name>..)`), and inline flags (`(?i)`, `(?m)`, `(?s)`, `(?x)`).

### Writing a pattern

A prepoly string literal is **not raw**: it interprets `\` and it interpolates
`{expr}`. A pattern therefore needs two escapes, and the second one bites
silently:

- a backslash doubles — `\\d`, `\\w`, `\\b`;
- an opening brace is escaped `\{` — `"\\d{4}"` does **not** mean "four
  digits": the `{4}` interpolates to the text `4`, so the pattern compiles as
  `\d4` (a digit, then the character `4`). Write `"\\d\{4}"`. A closing brace
  needs nothing, and a quantifier with a comma (`{2,3}`) is a syntax error
  rather than a silent change.

In a replacement string, prefer `$name` and `$1` over the braced `${name}`
form for the same reason.

```prepoly norun
const date = Regex.new("(?<year>\\d\{4})-(\\d\{2})-(\\d\{2})")!
if let m = date.find("due 2026-07-13, ok") {
    println(m.text)                                   // 2026-07-13
    println("{m.start}..{m.end}")                     // 4..14
    if let y = m.named("year") { println(y.text) }    // 2026
}
println(date.replace_all("2026-07-13", "$year/$2"))   // 2026/07
```

### API

`Regex.new(pattern) -> Regex!` is where a bad pattern is reported; every method
below is infallible.

| Method                            | Signature                        | Behavior                                    |
| --------------------------------- | -------------------------------- | ------------------------------------------- |
| `re.is_match(text)`               | `(string) -> bool`               | cheapest — no groups recorded               |
| `re.find(text)`                   | `(string) -> Match?`             | leftmost match, `null` when none            |
| `re.find_from(text, from)`        | `(string, int64) -> Match?`      | search starts at a byte offset              |
| `re.find_all(text)`               | `(string) -> Match[]`            | every non-overlapping match                 |
| `re.replace(text, rep)`           | `(string, string) -> string`     | first match only                            |
| `re.replace_all(text, rep)`       | `(string, string) -> string`     | `$1` / `$name` / `$$` expand in `rep`       |
| `re.split(text)`                  | `(string) -> string[]`           | one more field than there were matches      |
| `re.group_count()`                | `() -> int64`                    | counts group 0, so no groups answers 1      |
| `escape(text)`                    | `(string) -> string`             | a pattern matching `text` literally         |

A `Match` carries `text`, `start`, `end` (byte offsets into the subject) and
`groups: Group?[]`, where `groups[0]` is the whole match. Reach a group by
number with `m.group(i)` or by name with `m.named("year")`; both answer `null`
when the group did not participate (the `(a)` of `(a)|(b)` against `"b"`) or
the pattern has no such group. A `Group` is `{ text, start, end }`.

A compiled `Regex` is never released (the language has no destructors), so
compile a pattern **once** and keep it — compiling inside a loop grows the
process. That is the right way to use any regex engine: compilation costs far
more than matching.

## `semver` (a library, not `std`)

```prepoly norun
import semver.{ Version, sort }
```

[Semantic Versioning 2.0.0](https://semver.org): parse a version, render it
back, and order two of them. Pure prepoly on top of `regex` — it has no native
half of its own — and it parses with the **official pattern from semver.org
verbatim**, so what it accepts is exactly what the spec defines: no leading
zeros, an optional dot-separated pre-release, optional build metadata, and
nothing else in the string (`v1.0.0` and `1.0` are rejected).

```prepoly norun
const v = Version.parse("1.4.2-rc.1+build.5")!
println("{v.major}.{v.minor}.{v.patch}")        // 1.4.2
println(v.prerelease)                           // rc.1  (null when absent)
println(v.compare(Version.parse("1.4.2")!))     // -1: a pre-release is LOWER
```

`Version` is `{ major, minor, patch: int64, prerelease, build: string? }` —
the optional components are `null` when absent, which the grammar keeps
distinct from empty.

| Method / function                | Signature                     | Behavior                                       |
| -------------------------------- | ----------------------------- | ---------------------------------------------- |
| `Version.parse(text)`            | `(string) -> Version!`        | the whole string must be a version             |
| `Version.new(major, minor, patch)` | `(int64, int64, int64) -> Version` | no pre-release, no build             |
| `v.to_string()`                  | `() -> string`                | parsing the result yields an equal version     |
| `v.compare(other)`               | `(Version) -> int64`          | `-1` / `0` / `1` by precedence                 |
| `v.equals` / `less_than` / `greater_than` | `(Version) -> bool`  | in terms of `compare`                          |
| `v.is_prerelease()`              | `() -> bool`                  |                                                |
| `v.prerelease_ids()`             | `() -> string[]`              | `"rc.1"` → `["rc", "1"]`                       |
| `sort(versions)`                 | `(Version[]) -> Version[]`    | a new array, ascending                         |

**Precedence** follows §11: major/minor/patch numerically, then a version with
a pre-release *precedes* the same version without one (`1.0.0-rc.1 < 1.0.0`).
Pre-release identifiers compare left to right — numeric ones numerically (so
`beta.2 < beta.11`, not lexically) and before alphanumeric ones, which compare
in ASCII order; if all shared identifiers are equal, the shorter list precedes.
**Build metadata is ignored** (§10), so `1.0.0+a` and `1.0.0+b` compare equal —
compare `to_string()` if textual identity is what you want.

## `net` (a library, not `std`)

```prepoly norun
import net.{ Tcp, TcpListener, Udp, TlsStream }
```

TCP and UDP sockets plus TLS client connections. Like `process` and `path`
this is a library: talking to the operating system's sockets needs native
code, which arrives as a plugin under `libraries/`, and the setup is the
same — automatic for a distributed toolchain, `libraries/build.sh` +
`PREPOLY_INCLUDE` from a repo checkout. Networking does not run in the
playground.

Under the hood a plain socket is a `File` (an OS file descriptor) held
privately by each record — a connection cannot `accept` and a listener
cannot `read`.

**`Tcp`** — a bidirectional byte-stream connection:

| Method                     | Signature                  | Behavior                                             |
| -------------------------- | -------------------------- | ----------------------------------------------------- |
| `Tcp.connect(host, port)`  | `(string, int64) -> Tcp!`  | open a connection; `host` is an IP or a DNS name     |
| `conn.read(max)`           | `(int64) -> uint8[]!`      | up to `max` bytes; fewer on a short read              |
| `conn.write(data)`         | `(uint8[]) -> int64!`      | write all of `data`                                   |
| `conn.local_addr()` / `conn.peer_addr()` | `() -> string!` | the `"ip:port"` of each end                          |
| `conn.set_timeout(ms)`     | `(int64) -> void!`         | read/write timeout; 0 clears it                       |
| `conn.close()`             | `() -> void!`              |                                                       |

**`TcpListener`** — produces `Tcp` connections:

| Method                          | Signature                          | Behavior                                        |
| ------------------------------- | ---------------------------------- | ------------------------------------------------ |
| `TcpListener.bind(host, port)`  | `(string, int64) -> TcpListener!`  | bind and listen; port 0 picks an ephemeral port |
| `listener.accept()`             | `() -> Tcp!`                       | block until a connection arrives                 |
| `listener.local_addr()`         | `() -> string!`                    | reads back an OS-picked port                     |
| `listener.close()`              | `() -> void!`                      |                                                  |

**`Udp`** — a datagram socket:

| Method                              | Signature                              | Behavior                                    |
| ----------------------------------- | -------------------------------------- | -------------------------------------------- |
| `Udp.bind(host, port)`              | `(string, int64) -> Udp!`              | port 0 picks an ephemeral port              |
| `sock.send_to(data, host, port)`    | `(uint8[], string, int64) -> int64!`   | send one datagram                            |
| `sock.recv_from(max)`               | `(int64) -> Datagram!`                 | block for one datagram of up to `max` bytes |
| `sock.local_addr()`                 | `() -> string!`                        |                                              |
| `sock.set_timeout(ms)`              | `(int64) -> void!`                     |                                              |
| `sock.close()`                      | `() -> void!`                          |                                              |

`Datagram` is `{ data: uint8[], addr: string }` — one received datagram with
its sender's address. The prelude helpers `to_bytes(s) -> uint8[]` and
`to_text(bytes) -> string!` convert between strings and socket bytes.

```prepoly norun
import net.{ Tcp, TcpListener }

let listener = TcpListener.bind("127.0.0.1", 0)!
let port = int64.parse(listener.local_addr()!.split(":")[1])!

let client = Tcp.connect("127.0.0.1", port)!
let server = listener.accept()!
client.write(to_bytes("hello"))!
println(to_text(server.read(64)!)!)   // hello
```

Two practical notes for concurrent servers: a spawned closure should capture
the **port** (a copied scalar), not the listener — a shared listener is
auto-guarded by a cown lock that a blocking `accept` would then hold — and
TCP is a byte stream: one `read` may return less than what the peer wrote,
so frame messages or read in a loop.

**`TlsStream`** — TLS **client** connections, backed by rustls inside the
plugin. Certificate verification uses the bundled Mozilla root set with the
server name taken from `host`; there are no configuration knobs (no custom
CAs, no server side yet). `TlsStream` mirrors `Tcp`, so code written against
`read`/`write` structurally accepts either:

| Method                          | Signature                        | Behavior                                              |
| ------------------------------- | -------------------------------- | ------------------------------------------------------ |
| `TlsStream.connect(host, port)` | `(string, int64) -> TlsStream!`  | TCP connect + full handshake; certificate errors fail here |
| `conn.read(max)`                | `(int64) -> uint8[]!`            | up to `max` decrypted bytes; empty at end-of-stream    |
| `conn.write(data)`              | `(uint8[]) -> int64!`            | encrypt and send all of `data`                         |
| `conn.close()`                  | `() -> void!`                    | sends the TLS close notification                       |

```prepoly norun
import net.{ TlsStream }

let conn = TlsStream.connect("example.com", 443)!
conn.write(to_bytes("GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"))!
println(to_text(conn.read(16)!)!)   // HTTP/1.1 200 OK
conn.close()!
```

Back ends: everything here runs on either back end — sockets are `fs`
`File`s and the plugins execute natively under the interpreter too.

## `std.collections`

```prepoly
import std.collections.{ HashMap }
```

An open-addressing (linear-probing) hash map. Keys may be of any type that
renders to a stable string and compares with `==` (integers, strings,
records, ...); values may be of any type. `HashMap.new()` takes **no
arguments** — the key/value types are inferred from the first `set` or
`from_pairs`, so `let m = HashMap.new(); m.set("a", 1)` is a
`string -> int32` map with no annotations.

| Method                      | Signature               | Behavior                        |
| --------------------------- | ----------------------- | ------------------------------- |
| `HashMap.new()`             | `() -> HashMap`         | empty map                       |
| `HashMap.from_pairs(pairs)` | `([[K, V]]) -> HashMap` | build from `[key, value]` pairs |
| `m.set(k, v)`               | insert or overwrite     |                                 |
| `m.get(k)`                  | `-> V?`                 | `null` when absent              |
| `m.get_or(k, dflt)`         | `-> V`                  | non-nullable                    |
| `m.contains_key(k)`         | `-> bool`               |                                 |
| `m.delete(k)`               | `-> bool`               | whether the key was present     |
| `m.size()`                  | `-> int64`              | live pair count                 |
| `m.is_empty()`              | `-> bool`               |                                 |
| `m.keys()` / `m.values()`   | `-> K[]` / `-> V[]`     | unspecified (slot) order        |
| `m.pairs()`                 | `-> [K, V][]`           | same order as `keys`            |
| `m.clear()`                 | remove every pair       | keeps capacity and types        |

## `data.json` (a library, not `std`)

```prepoly norun
import data.json.{ JsonValue }
```

A JSON value tree, parser, accessors, serializer, and a reflective decoder.
The whole surface hangs off `JsonValue`, so the type is the only name to import.
A pure-prepoly library (no plugin) under `libraries/`, with the same setup
as the others — automatic for a distributed toolchain, `PREPOLY_INCLUDE`
from a repo checkout.

```prepoly norun
type JsonValue =
    | Null
    | Bool { value: bool }
    | Number { value: float64 }
    | String { value: string }
    | Array { value: JsonValue[] }
    | Object { values: _JsonObject }   // a string -> JsonValue HashMap
```

An `Object` keeps its members in a `HashMap` (a refinement pinning the key
to `string` and the value to `JsonValue`), so `get` is a hash lookup. One
consequence: `stringify` renders object members in the map's slot order,
not the source document's ordering (stable for a given input).

| Function / method                                 | Signature                           | Behavior                                                                                                             |
| ------------------------------------------------- | ----------------------------------- | -------------------------------------------------------------------------------------------------------------------- |
| `JsonValue.parse(text)`                           | `(string) -> JsonValue!`            | whole input must be one JSON value                                                                                   |
| `j.stringify()`                                   | `-> string`                         | serialize back to JSON text                                                                                          |
| `j.as_bool()` / `j.as_number()` / `j.as_string()` | `-> bool!` / `float64!` / `string!` | payload, or a decode error naming the expected kind                                                                  |
| `j.is_null()`                                     | `-> bool`                           |                                                                                                                      |
| `j.get(key)`                                      | `(string) -> JsonValue!`            | object field, or an error naming the missing field                                                                   |
| `j.at(index)`                                     | `(int64) -> JsonValue!`             | array element, range-checked                                                                                         |
| `j.into()`                                        | `-> infer!`                         | decode into the type the call site expects — see [Reflection](/references/reflection/#generic-decoders-with---infer) |

Decoding a whole document into a typed structure combines `parse` and `into`:

```prepoly norun
import data.json.{ JsonValue }

type Address = { city: string, zip: int64 }
type User = { name: string, age: int64, address: Address }

const src = "\{\"name\": \"Aki\", \"age\": 30, \"address\": \{\"city\": \"Tokyo\", \"zip\": 100\}\}"
const u: User = JsonValue.parse(src)!.into()!
println("{u.name} {u.age} {u.address.city}")   // Aki 30 Tokyo
```
