// The `Default` protocol type behind the method model (see the book's
// syntax-sugar reference): a type satisfies `Default` when it provides a
// `default() -> Self` method producing its default value. The built-in
// zero-value types -- the numeric widths, bool, and string -- satisfy it
// through `T.default()`.
//
// A method declaration `fun T.m(self) ...` is, semantically, a field on `T`
// whose type satisfies `Default`, with `default()` producing the declared
// function. That is what lets the member be absent from every constructed
// value and still be read (`value.m`) or called. The compiler erases the
// model: method calls compile to direct calls and the field has no storage.
// Only method declarations get this treatment -- a user-declared field is
// required at construction and in structural subtyping regardless of its
// type.
type Default = {
    default() -> Self
}
