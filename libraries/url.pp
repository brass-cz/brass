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
 * Resolves `reference` against `self`, per RFC 3986 section 5.2.
 *
 * This is what turns a `Location:` header into the URL to request next: a
 * redirect may answer with an absolute URI, an absolute path (`/next`), or a
 * relative one (`../next`), and only the base says what the last two mean. The
 * base must be absolute -- a relative one has no scheme to lend.
 */
fun URI.resolve(self, reference: string) -> URI! {
    let base_scheme = self.scheme
    if !base_scheme { return error("cannot resolve against a relative base") }
    let r = URI.parse_reference(reference)!

    // A reference with its own scheme is already absolute; only its path is
    // normalized. One with an authority but no scheme borrows only the scheme.
    let r_scheme = r.scheme
    if r_scheme {
        return URI {
            scheme: r_scheme,
            authority: r.authority,
            path: _remove_dot_segments(r.path),
            query: r.query,
            fragment: r.fragment,
        }
    }
    let r_authority = r.authority
    if r_authority {
        return URI {
            scheme: base_scheme,
            authority: r_authority,
            path: _remove_dot_segments(r.path),
            query: r.query,
            fragment: r.fragment,
        }
    }

    // No authority: the reference's path decides. An empty path names the base's
    // resource, so it keeps the base's path -- and its query too, unless the
    // reference wrote one (a bare `#fragment` must not drop the base's query).
    let path = self.path
    let query = r.query
    if len(r.path) == 0 {
        if !query { query = self.query }
    } else if r.path.starts_with("/") {
        path = _remove_dot_segments(r.path)
    } else {
        path = _remove_dot_segments(_merge_path(self, r.path))
    }
    return URI {
        scheme: base_scheme,
        authority: self.authority,
        path: path,
        query: query,
        fragment: r.fragment,
    }
}

// RFC 3986 section 5.2.3: a relative path is merged onto the base's, replacing
// everything after the base's last `/`. A base that has an authority but an empty
// path stands in for one whose path is `/`.
fun _merge_path(base: URI, path: string) -> string {
    let base_path = base.path
    if len(base_path) == 0 {
        let authority = base.authority
        if authority { return "/{path}" }
        return path
    }
    let cs = base_path.chars()
    let cut = _last_slash(cs)
    if cut < 0 { return path }
    let head = substr(cs, 0, cut + 1)
    return "{head}{path}"
}

// RFC 3986 section 5.2.4: interpret the `.` and `..` segments of a path. A `..`
// that would climb above the root is dropped, as the RFC requires -- the result
// of a resolution is never allowed to escape the authority.
fun _remove_dot_segments(path: string) -> string {
    if len(path) == 0 { return path }
    let absolute = path.starts_with("/")
    let parts = path.split("/")
    let kept: string[] = []
    // A path ending in `/`, `.` or `..` names a directory, so it keeps a trailing
    // slash even though the segment itself contributes nothing.
    let directory = false
    let i: int64 = 0
    while i < len(parts) {
        let segment = parts[i]
        i += 1
        if segment == "." {
            directory = true
        } else if segment == ".." {
            if len(kept) > 0 { kept = kept.slice(0, len(kept) - 1) }
            directory = true
        } else if len(segment) > 0 {
            kept.push(segment)
            directory = false
        } else if i == len(parts) {
            // The empty segment a trailing `/` leaves behind. (A leading one --
            // the `/` of an absolute path -- is carried by `absolute` instead.)
            directory = true
        }
    }
    let joined = kept.join("/")
    let out = joined
    if absolute { out = "/{joined}" }
    if directory && len(kept) > 0 { out = "{out}/" }
    return out
}

// The index of the last `/` in `cs`, or -1.
fun _last_slash(cs: string[]) -> int64 {
    let i = len(cs) - 1
    while i >= 0 {
        if cs[i] == "/" { return i }
        i -= 1
    }
    let missing: int64 = -1
    return missing
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
