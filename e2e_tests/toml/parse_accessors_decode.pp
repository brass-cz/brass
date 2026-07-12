import data.toml.{ TomlValue, parse, stringify, as_array }

type Server = { host: string, port: int64 }
type Config = { title: string, retries: int64, server: Server }

fun main() {
    // Scalars: strings, integers (dec/hex), floats, booleans, and a date-time
    // kept verbatim.
    const doc = "title = \"demo\"\nretries = 3\nmask = 0xff\nratio = 1.5\nok = true\nwhen = 1979-05-27T07:32:00Z\nnums = [10, 20, 30]\n\n[server]\nhost = \"localhost\"\nport = 5432\n\n[[items]]\nid = 1\n\n[[items]]\nid = 2\n"
    const t = parse(doc)!
    println(t.get("mask")!.as_integer()!)
    println(t.get("ratio")!.as_float()!)
    println(t.get("ok")!.as_bool()!)
    println(t.get("when")!.as_datetime()!)
    println(t.get("nums")!.at(2)!.as_integer()!)

    // Nested table and array of tables.
    println(t.get("server")!.get("port")!.as_integer()!)
    const items = as_array(t.get("items")!)!
    println(items[1].get("id")!.as_integer()!)

    // Reflective decode into a typed struct (a nested record included).
    const cfg: Config = parse(doc)!.into()!
    println("{cfg.title} {cfg.retries} {cfg.server.host} {cfg.server.port}")

    // Round-trip a single value through the serializer.
    const rt = parse(stringify(t.get("server")!))!
    println(rt.get("host")!.as_string()!)

    // A missing key is an error.
    match t.get("nope") {
        Ok { value } => { println("unexpected") }
        Err { error } => { println("error: {error}") }
    }
}
