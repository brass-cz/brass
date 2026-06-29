// A `T!` return makes a bare `return v` unify with `Result.Ok { value: v }`, even
// when the body raises no error; combined with open structural fields, a generic
// fallible consumer degrades to its fallback when the value does not fit.
fun get_name(person) -> string! {
    if person.name {
        return person.name
    } else {
        return "no name"
    }
}

println(get_name({ name: "Asimov" }))
println(get_name({ age: 20 }))
println(get_name({ name: 1 }))
