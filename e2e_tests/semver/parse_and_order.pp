// Semantic Versioning 2.0.0, end to end: what the official pattern accepts and
// rejects, the round trip through `to_string`, and the precedence rules -- the
// spec's own §11 ordering example is the real test, because it is where a
// lexical comparison (`beta.11` < `beta.2`) or a mishandled pre-release
// (`1.0.0-rc.1` > `1.0.0`) would show.
import semver.{ Version, sort }

fun show(text: string) {
    match Version.parse(text) {
        Ok { value } => println("{text} -> {value.to_string()}"),
        Err { error } => println("{text} -> rejected"),
    }
}

fun main() {
    // Accepted: the forms the spec's own examples use.
    show("0.0.4")
    show("1.4.2")
    show("1.0.0-alpha")
    show("1.0.0-0.3.7")
    show("1.0.0-x.7.z.92")
    show("1.0.0-alpha+001")
    show("1.0.0+20130313144700")
    show("1.0.0-beta+exp.sha.5114f85")

    // Rejected: the pattern is anchored and forbids leading zeros, so a `v`
    // prefix, a missing field, a leading zero, an empty pre-release, and
    // trailing text are all not versions.
    show("v1.0.0")
    show("1.0")
    show("01.0.0")
    show("1.0.0-")
    show("1.0.0 ")
    show("")

    // The components, and the absence of the optional ones.
    const full = Version.parse("1.4.2-rc.1+build.5")!
    println("{full.major} {full.minor} {full.patch}")
    println("{full.prerelease} {full.build}")
    println(full.prerelease_ids())
    println(full.is_prerelease())
    const plain = Version.parse("1.4.2")!
    println("{plain.prerelease} {plain.build}")
    println(plain.is_prerelease())
    println(Version.new(2, 3, 4).to_string())

    // Precedence (§11), the spec's example, sorted back from reverse order.
    const order = [
        "1.0.0-alpha",
        "1.0.0-alpha.1",
        "1.0.0-alpha.beta",
        "1.0.0-beta",
        "1.0.0-beta.2",
        "1.0.0-beta.11",
        "1.0.0-rc.1",
        "1.0.0",
    ]
    let parsed: Version[] = []
    for text in order {
        parsed.push(Version.parse(text)!)
    }
    let rendered: string[] = []
    for v in sort(parsed.reverse()) {
        rendered.push(v.to_string())
    }
    println(rendered.join(" < "))

    // Build metadata is IGNORED by precedence (§10): same version, different
    // build.
    const a = Version.parse("1.0.0+a")!
    const b = Version.parse("1.0.0+b")!
    println(a.compare(b))
    println(a.equals(b))

    println(Version.parse("1.0.0-rc.1")!.less_than(Version.parse("1.0.0")!))
    println(Version.parse("1.0.1")!.greater_than(Version.parse("1.0.0")!))

    // A numeric pre-release identifier too large for an int64 still orders
    // correctly: identifiers are compared by width then digits, never parsed.
    const huge = Version.parse("1.0.0-99999999999999999999")!
    println(huge.greater_than(Version.parse("1.0.0-2")!))
}
