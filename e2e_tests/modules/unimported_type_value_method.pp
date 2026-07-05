import personlib.{ map }

// Person itself is not imported here, but the value's type is resolved
// from the imported map()'s return type, so the method dispatches by
// that type without naming it in this module.
if let person = map().get(0) {
    person.display()
}
