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
| `cmd.stdin/stdout/stderr(mode)`| `(Stdio) -> Command`          | connect a stream (`Inherit`/`Pipe`/`Null`)   |
| `cmd.spawn()`                  | `() -> Child!`                | start the process                            |
| `child.stdin/stdout/stderr()`  | `() -> File!`                 | a piped stream (requires `Stdio.Pipe`)       |
| `child.wait()`                 | `() -> int32!`                | block for exit; returns the exit code        |
| `child.output()`               | `() -> Output!`               | drain the piped streams, then wait           |

`Stdio` is `| Inherit | Pipe | Null`. Piped streams are `File`s, so the
prelude byte helpers `to_bytes`/`to_text` convert their contents. The
accessors may be called repeatedly: each hands back the same `File`.

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
import fs.{ File, open, read_file, write_file }
```

File handles and byte I/O. Like the other libraries this is a plugin under
`libraries/`, with the same setup — automatic for a distributed toolchain,
`libraries/build.sh` + `PREPOLY_INCLUDE` from a repo checkout.

| Function / method           | Signature                   | Behavior                                          |
| --------------------------- | --------------------------- | -------------------------------------------------- |
| `open(path, mode)`          | `(string, string) -> File!` | `"r"` read, `"w"` truncate+create, `"a"` append   |
| `read_file(path)`           | `(string) -> string!`       | whole file as text                                 |
| `write_file(path, content)` | `(string, string) -> void!` | write text, truncating                             |
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
import data.json.{ JsonValue, parse, stringify }
```

A JSON value tree, parser, accessors, serializer, and a reflective decoder.
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
| `parse(text)`                                     | `(string) -> JsonValue!`            | whole input must be one JSON value                                                                                   |
| `stringify(j)`                                    | `(JsonValue) -> string`             | serialize back to JSON text (a free function)                                                                        |
| `j.as_bool()` / `j.as_number()` / `j.as_string()` | `-> bool!` / `float64!` / `string!` | payload, or a decode error naming the expected kind                                                                  |
| `j.is_null()`                                     | `-> bool`                           |                                                                                                                      |
| `j.get(key)`                                      | `(string) -> JsonValue!`            | object field, or an error naming the missing field                                                                   |
| `j.at(index)`                                     | `(int64) -> JsonValue!`             | array element, range-checked                                                                                         |
| `j.into()`                                        | `-> infer!`                         | decode into the type the call site expects — see [Reflection](/references/reflection/#generic-decoders-with---infer) |

Decoding a whole document into a typed structure combines `parse` and `into`:

```prepoly norun
import data.json.{ JsonValue, parse }

type Address = { city: string, zip: int64 }
type User = { name: string, age: int64, address: Address }

const src = "\{\"name\": \"Aki\", \"age\": 30, \"address\": \{\"city\": \"Tokyo\", \"zip\": 100\}\}"
const u: User = parse(src)!.into()!
println("{u.name} {u.age} {u.address.city}")   // Aki 30 Tokyo
```
