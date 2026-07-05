import personlib.{ map }

// The literal satisfies Person structurally, but this module never
// imported Person, so the method must not dispatch to it.
{ name: "hello" }.display() // error: the type Person is not imported

if let person = map().get(0) {
    person.display() // no error: person's type flows from the imported map()
}
