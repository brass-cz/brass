// `URI.resolve` is what turns a redirect's `Location` header into the URL to
// request next, so it is pinned against the normative examples of RFC 3986
// section 5.4 -- both the normal ones and the abnormal `..`-past-the-root cases,
// where a wrong answer would let a redirect escape its authority.
import url.{ URI }

fun _show(base: URI, reference: string) {
    const target = base.resolve(reference)!
    const text = target.to_string()
    println("{reference} -> {text}")
}

fun main() {
    const base = URI.parse("http://a/b/c/d;p?q")!
    // 5.4.1 normal examples.
    _show(base, "g:h")
    _show(base, "g")
    _show(base, "./g")
    _show(base, "g/")
    _show(base, "/g")
    _show(base, "//g")
    _show(base, "?y")
    _show(base, "g?y")
    _show(base, "#s")
    _show(base, "g#s")
    _show(base, "")
    _show(base, ".")
    _show(base, "./")
    _show(base, "..")
    _show(base, "../")
    _show(base, "../g")
    _show(base, "../..")
    _show(base, "../../g")
    // 5.4.2 abnormal examples: a `..` that would climb above the root is dropped.
    _show(base, "../../../g")
    _show(base, "/./g")
    _show(base, "/../g")
    _show(base, "g.")
    _show(base, "./g/.")
    _show(base, "g/./h")
    _show(base, "g/../h")

    // A redirect may cross scheme and host, and a relative one is read against
    // the path it came from.
    const page = URI.parse("https://example.com/docs/intro/index.html?v=2")!
    _show(page, "http://other.example/x")
    _show(page, "/top")
    _show(page, "../guide/")
    _show(page, "next.html")
}
