// Accessing a field a structure does not have, or that does not fit the use, is
// not a type error: the guarding `if` is statically false (the then-branch is
// pruned) so the function degrades to its fallback.
fun get_name(person) -> string {
    if person.name {
        return person.name
    } else {
        return "no name"
    }
}

println(get_name({ name: "Asimov" }))
println(get_name({ age: 20 }))
println(get_name({ name: 1 }))
