// The anonymous literal satisfies Person, which this module imports under
// the local name P. The rename still counts as naming the type here, so
// structural method dispatch adopts it.
import personlib.{ Person as P }

{ name: "hello" }.display()
