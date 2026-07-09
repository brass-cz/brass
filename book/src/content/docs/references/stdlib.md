---
title: "Standard library"
description: "Every standard-library module and builtin, with signatures."
---

The standard library has two layers:

- **The implicit prelude** — the modules under `std/prelude/` (`io`, `array`,
  `string`, `math`, `conv`, `assert`) plus the runtime builtins. Their public
  names are in scope in every program with no import.
- **Import-only modules** — everything else under `std/` (`std.net`,
  `std.collections`, `std.data.json`): imported explicitly, e.g.
  `import std.collections.{ HashMap }`, and loaded on demand.

Most of the library is written in prepoly itself, on top of a small set of
runtime primitives. Identifiers beginning with `_` (e.g. `_string_bytes`,
`_panic`) are those internals — do not call them directly.

Reserved builtin names that cannot be redefined: `len`, `open`, `spawn`,
`with`, `sync`, `error`, `fields`, `typeof`.

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

| Function                    | Signature                   | Behavior                                                            |
| --------------------------- | --------------------------- | ------------------------------------------------------------------- |
| `print(value)`              | `(any) -> void`             | write the value's text to stdout; combine values with interpolation |
| `println(value)`            | `(any) -> void`             | `print` plus a newline                                              |
| `input()`                   | `() -> string!`             | one line from stdin, without the trailing newline                   |
| `read_file(path)`           | `(string) -> string!`       | whole file as text                                                  |
| `write_file(path, content)` | `(string, string) -> void!` | write text, truncating                                              |

### Files

`open(path, mode) -> File!` opens a file (`mode` as in C: `"r"`, `"w"`, ...).
`File` methods, all Results:

| Method                                             | Signature             |
| -------------------------------------------------- | --------------------- |
| `f.read(n)`                                        | `(int64) -> uint8[]!` |
| `f.write(bytes)`                                   | `(uint8[]) -> int64!` |
| `f.seek(pos)`                                      | `-> void!`            |
| `f.size()`                                         | `() -> int64!`        |
| `f.close()`                                        | `() -> void!`         |
| `File.stdin()` / `File.stdout()` / `File.stderr()` | static constructors   |

File I/O requires the native runtime; the REPL interpreter refuses it (see
[Execution model](/references/execution/)).

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

Free-function aliases of the conversion methods: `int32_from(x) -> int32!`,
`int32_parse(s) -> int32!`, `float64_from(x) -> float64`,
`float64_parse(s) -> float64!`, `string_from(x) -> string`. The method forms
(`T.from`, `T.parse`) are described in the
[type system](/references/types/#explicit-conversions).

## `std.assert`

`assert(cond: bool, msg: string?)` aborts the program when `cond` is false.
`msg` is a trailing nullable parameter, so `assert(cond)` works and prints a
generic message.

## `std.net`

```prepoly norun
import std.net.{ Tcp, TcpListener, Udp }
```

TCP and UDP sockets, as three record types — a connection cannot `accept`
and a listener cannot `read`. Under the hood a socket is a `File` (an OS
file descriptor) held privately by each record. Not in the prelude: import
it explicitly.

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
its sender's address. The free functions `to_bytes(s) -> uint8[]` and
`to_text(bytes) -> string!` convert between strings and socket bytes.

```prepoly norun
import std.net.{ Tcp, TcpListener, to_bytes, to_text }

let listener = TcpListener.bind("127.0.0.1", 0)!
let port = int64.parse(listener.local_addr()!.split(":")[1])!

let client = Tcp.connect("127.0.0.1", port)!
let server = listener.accept()!
client.write(to_bytes("hello"))!
println(to_text(server.read(64)!)!)   // hello
```

Networking requires the native runtime; the REPL interpreter refuses it, like
file I/O. Two practical notes for concurrent servers: a spawned closure
should capture the **port** (a copied scalar), not the listener — a shared
listener is auto-guarded by a cown lock that a blocking `accept` would then
hold — and TCP is a byte stream: one `read` may return less than what the
peer wrote, so frame messages or read in a loop.

## `std.net.tls`

```prepoly norun
import std.net.tls.{ TlsStream }
```

TLS **client** connections, backed by rustls built into the runtime.
Certificate verification uses the bundled Mozilla root set with the server
name taken from `host`; there are no configuration knobs (no custom CAs, no
server side yet). `TlsStream` mirrors `Tcp`, so code written against
`read`/`write` structurally accepts either:

| Method                          | Signature                        | Behavior                                              |
| ------------------------------- | -------------------------------- | ------------------------------------------------------ |
| `TlsStream.connect(host, port)` | `(string, int64) -> TlsStream!`  | TCP connect + full handshake; certificate errors fail here |
| `conn.read(max)`                | `(int64) -> uint8[]!`            | up to `max` decrypted bytes; empty at end-of-stream    |
| `conn.write(data)`              | `(uint8[]) -> int64!`            | encrypt and send all of `data`                         |
| `conn.close()`                  | `() -> void!`                    | sends the TLS close notification                       |

```prepoly norun
import std.net.tls.{ TlsStream }
import std.net.{ to_bytes, to_text }

let conn = TlsStream.connect("example.com", 443)!
conn.write(to_bytes("GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"))!
println(to_text(conn.read(16)!)!)   // HTTP/1.1 200 OK
conn.close()!
```

A driver built without the `tls` cargo feature (and the wasm interpreter)
keeps the same API but every call returns an error Result.

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

## `std.data.json`

```prepoly
import std.data.json.{ JsonValue, parse, stringify }
```

A JSON value tree, parser, accessors, serializer, and a reflective decoder.

```prepoly
type JsonValue =
    | Null
    | Bool { value: bool }
    | Number { value: float64 }
    | String { value: string }
    | Array { value: JsonValue[] }
    | Object { keys: string[], vals: JsonValue[] }   // members as parallel arrays
```

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

```prepoly
import std.data.json.{ JsonValue, parse }

type Address = { city: string, zip: int64 }
type User = { name: string, age: int64, address: Address }

const src = "\{\"name\": \"Aki\", \"age\": 30, \"address\": \{\"city\": \"Tokyo\", \"zip\": 100\}\}"
const u: User = parse(src)!.into()!
println("{u.name} {u.age} {u.address.city}")   // Aki 30 Tokyo
```
