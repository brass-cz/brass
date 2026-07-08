import std.collections.{ HashMap }

// Reflective deserialization: a struct is populated field by field from a
// name-keyed map, using `fields()` to drive the field walk and `v[field]` to
// store into each slot. `typeof` labels errors and output with the target's
// name. This is the shape a JSON-object decoder takes once the object has been
// parsed into a name->value map.

type Config = {
    width: int64,
    height: int64,
    depth: int64,
}

// Fill an uninitialized `Config` from `source`, reading each declared field by
// its own name. Because the loop visits every field of the target, the binding
// is definitely assigned; a missing key is a decode error naming the field and
// the target type.
fun from_map(source: HashMap) -> Config! {
    let ret: Config
    for field in fields(ret) {
        if let value = source.get(field) {
            ret[field] = value
        } else {
            return error("{typeof(ret)}: missing field '{field}'")
        }
    }
    return ret
}

fun main() {
    const source = HashMap.new()
    source.set("width", 1920)
    source.set("height", 1080)
    source.set("depth", 24)

    match from_map(source) {
        Ok { value } => {
            println("decoded {typeof(value)}:")
            for field in fields(value) {
                println("  {field} = {value[field]}")
            }
        }
        Err { error } => { println("error: {error}") }
    }

    // A missing key is reported by name.
    const partial = HashMap.new()
    partial.set("width", 800)
    partial.set("height", 600)
    match from_map(partial) {
        Ok { value } => { println("depth = {value.depth}") }
        Err { error } => { println("error: {error}") }
    }
}
