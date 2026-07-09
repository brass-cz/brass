// Importing one name from a nested std module must not leak the module's
// other public names into bare scope: only the prelude is import-free.
// `to_bytes` lives in std.net and is not imported here, so calling it is an
// error naming the module that has it.
import std.net.{ Tcp }

println(to_bytes("nope"))
