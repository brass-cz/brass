// The regex library end to end: compilation, the match/group/name surface, the
// byte offsets a match reports, and the replace/split/escape operations.
//
// NOTE the pattern escaping: a prepoly string interpolates `{expr}`, so a
// repetition brace must be written `\{4}` -- `"\\d{4}"` would compile as `\d4`.
import regex.{ Regex, escape }

fun main() {
    const date = Regex.new("(?<year>\\d\{4})-(\\d\{2})-(\\d\{2})")!
    println(date.is_match("due 2026-07-13"))
    println(date.is_match("no date here"))
    // Group 0 (the whole match) is counted: three `(..)` groups answer 4.
    println(date.group_count())

    if let m = date.find("due 2026-07-13, ok") {
        // The span is a byte span into the subject: "due " is four bytes.
        println("{m.text} [{m.start}..{m.end}]")
        if let year = m.named("year") { println("year={year.text}@{year.start}") }
        if let day = m.group(3) { println("day={day.text}") }
        // A name the pattern does not have, and an out-of-range number, are
        // null rather than an error.
        println(m.named("month") == null)
        println(m.group(9) == null)
    }

    // A group that did not participate is null -- not an empty group.
    if let m = Regex.new("(a)|(b)")!.find("b") {
        println(m.group(1) == null)
        if let g = m.group(2) { println("arm={g.text}") }
    }

    // Every non-overlapping match, leftmost-first.
    const word = Regex.new("\\w+")!
    for m in word.find_all("a bb ccc") {
        println("{m.text}@{m.start}")
    }
    println(len(word.find_all("...")))
    println(word.find("...") == null)

    // The search offset moves where the search starts, and the reported offsets
    // stay absolute.
    if let m = word.find_from("a bb ccc", 2) { println("from2={m.text}@{m.start}") }

    // Offsets are UTF-8 byte offsets: `é` is two bytes, so `ll` starts at 3.
    if let m = Regex.new("l+")!.find("héllo") { println("{m.text} {m.start} {m.end}") }

    // `$name`/`$1` expand in a replacement; `replace` takes only the first match.
    println(date.replace_all("2026-07-13 and 1999-01-02", "$year/$2"))
    println(date.replace("2026-07-13 and 1999-01-02", "X"))

    // Splitting yields one more field than there were matches.
    println(Regex.new(",\\s*")!.split("a,b, c"))

    // An escaped pattern matches its text literally.
    println(escape("a.b*c"))
    println(Regex.new(escape("a.b*c"))!.is_match("a.b*c"))
    println(Regex.new(escape("a.b*c"))!.is_match("axbxc"))
}
