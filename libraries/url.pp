// A URI parser following RFC 3986.
//
//   URI-reference = URI / relative-ref
//   URI           = scheme ":" hier-part [ "?" query ] [ "#" fragment ]
//   hier-part     = "//" authority path-abempty / path-absolute
//                 / path-rootless / path-empty

import url.text.{ substr, index_of }
import url.charset.{ is_alpha, is_scheme_char }
import url.validate.{ validate, CharClass }
import url.authority.Authority
import url.query.QueryPair
import url.percent

/**
 * A parsed URI reference.
 *
 * Components keep their percent-encoding, as RFC 3986 asks: decoding before the
 * delimiters are known would erase the difference between `/a%2Fb` and `/a/b`.
 * Use `path_segments` and `query_pairs` for the decoded forms.
 *
 * A null component is one that was absent, which is not the same as one that
 * was empty: `http://h/p` has a null query, `http://h/p?` has an empty one.
 * `scheme` is null only for a relative reference, and `authority` is null when
 * the reference carried no `//` part. `scheme` is lowercased, being
 * case-insensitive.
 */
type URI = {
    scheme: string?
    authority: Authority?
    path: string
    query: string?
    fragment: string?
}

/** Parses an absolute URI. Fails when `s` carries no scheme. */
fun URI.parse(s: string) -> URI! {
    let uri = URI.parse_reference(s)!
    if !uri.scheme { return error("URI has no scheme: {s}") }
    return uri
}

/** Parses a URI reference, i.e. a URI or a relative reference such as `../a`. */
fun URI.parse_reference(s: string) -> URI! {
    let cs = s.chars()
    let n = len(cs)

    // A fragment runs to the end, so it is cut off first; the query is then cut
    // off at the first "?" that survives.
    let fragment: string? = null
    let end = n
    let hash = index_of(cs, "#", 0, n)
    if hash {
        fragment = substr(cs, hash + 1, n)
        end = hash
    }

    let query: string? = null
    let hier_end = end
    let question = index_of(cs, "?", 0, end)
    if question {
        query = substr(cs, question + 1, end)
        hier_end = question
    }

    // A ":" only introduces a scheme while no "/" has been seen; that is what
    // separates `mailto:a@b` from the relative reference `a/b:c`.
    let scheme: string? = null
    let pos: int64 = 0
    let colon = index_of(cs, ":", 0, hier_end)
    if colon {
        let slash = index_of(cs, "/", 0, colon)
        if !slash && _is_scheme(cs, colon) {
            scheme = substr(cs, 0, colon).to_lower()
            pos = colon + 1
        }
    }

    // An authority is introduced by "//" and runs to the next "/".
    let has_authority = pos + 1 < hier_end && cs[pos] == "/" && cs[pos + 1] == "/"
    let authority_text = ""
    let path = ""
    if has_authority {
        let auth_start = pos + 2
        let auth_end = hier_end
        let slash = index_of(cs, "/", auth_start, hier_end)
        if slash { auth_end = slash }
        authority_text = substr(cs, auth_start, auth_end)
        // path-abempty: empty, or rooted at the "/" that ended the authority.
        path = substr(cs, auth_end, hier_end)
    } else {
        path = substr(cs, pos, hier_end)
    }

    validate(path, CharClass.Path)!
    if !has_authority && !scheme && _first_segment_has_colon(path) {
        // path-noscheme: such a colon would read back as a scheme.
        return error("first path segment of a relative reference may not contain `:`: {s}")
    }

    let q = query
    if q { query = validate(q, CharClass.Query)! }
    let f = fragment
    if f { fragment = validate(f, CharClass.Fragment)! }

    // The authority is built straight into the field rather than through a
    // nullable local: the typed back end miscompiles `let a: T? = null; a = T
    // { .. }` once `a` is stored into a record.
    if has_authority {
        return Self {
            scheme: scheme,
            authority: Authority.parse(authority_text)!,
            path: path,
            query: query,
            fragment: fragment,
        }
    }
    return Self {
        scheme: scheme,
        authority: null,
        path: path,
        query: query,
        fragment: fragment,
    }
}

/** The authority written back as text, or null when the reference has none. */
fun URI.authority_string(self) -> string? {
    let a = self.authority
    if a {
        // The typed back end cannot dispatch a method on a nullable record even
        // once it is narrowed, so the value is rebuilt as a plain Authority.
        let authority = Authority { userinfo: a.userinfo, host: a.host, port: a.port }
        return authority.to_string()
    }
    return null
}

/** Reassembles the reference; parsing the result yields an equal URI. */
fun URI.to_string(self) -> string {
    let out = ""
    let scheme = self.scheme
    if scheme { out += "{scheme}:" }
    let authority = self.authority_string()
    if authority { out += "//{authority}" }
    out += self.path
    let query = self.query
    if query { out += "?{query}" }
    let fragment = self.fragment
    if fragment { out += "#{fragment}" }
    return out
}

/**
 * The percent-decoded path segments, without the empty segment that a leading
 * `/` would produce. A trailing `/` still yields a final empty segment, since
 * `/a/` and `/a` name different resources.
 */
fun URI.path_segments(self) -> string[]! {
    let path = self.path
    if path.starts_with("/") {
        let cs = path.chars()
        path = substr(cs, 1, len(cs))
    }
    let out: string[] = []
    if len(path) == 0 { return out }
    for segment in path.split("/") {
        out.push(percent.decode(segment)!)
    }
    return out
}

/** The decoded query pairs, or an empty array when there is no query. */
fun URI.query_pairs(self) -> QueryPair[]! {
    let none: QueryPair[] = []
    let query = self.query
    if !query { return none }
    return QueryPair.parse_all(query)!
}

fun _is_scheme(cs: string[], colon: int64) -> bool {
    if colon == 0 { return false }
    if !is_alpha(cs[0]) { return false }
    let i: int64 = 1
    while i < colon {
        if !is_scheme_char(cs[i]) { return false }
        i += 1
    }
    return true
}

fun _first_segment_has_colon(path: string) -> bool {
    let cs = path.chars()
    let end = len(cs)
    let slash = index_of(cs, "/", 0, end)
    if slash { end = slash }
    return index_of(cs, ":", 0, end) != null
}
