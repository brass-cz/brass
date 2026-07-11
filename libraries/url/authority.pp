// The authority component: [ userinfo "@" ] host [ ":" port ]

import text.{ substr, index_of }
import charset.{ is_digit }
import validate.{ validate, CharClass }

/**
 * A parsed authority.
 *
 * `userinfo` keeps its percent-encoding; decode it with `percent.decode` when
 * you want the raw bytes. `host` is stored as written, so an IPv6 address keeps
 * its brackets (`[::1]`); a reg-name host is lowercased, host names being
 * case-insensitive. `port` is null both when no colon was written and when the
 * colon carried no digits (`host:`), which RFC 3986 treats alike.
 */
type Authority = {
    userinfo: string?
    host: string
    port: uint16?
}

/** Parses the text between `//` and the start of the path. */
fun Authority.parse(s: string) -> Authority! {
    let cs = s.chars()
    let n = len(cs)
    // A literal "@" is not allowed inside userinfo, so the first one delimits it.
    let at = index_of(cs, "@", 0, n)
    if at {
        let authority = _parse_host_port(substr(cs, at + 1, n))!
        authority.userinfo = validate(substr(cs, 0, at), CharClass.Userinfo)!
        return authority
    }
    return _parse_host_port(s)!
}

/** Whether the host is a bracketed IPv6 or IPvFuture literal. */
fun Authority.is_ip_literal(self) -> bool {
    return self.host.starts_with("[")
}

fun Authority.to_string(self) -> string {
    let out = ""
    let userinfo = self.userinfo
    if userinfo { out += "{userinfo}@" }
    out += self.host
    let port = self.port
    if port { out += ":{port}" }
    return out
}

fun _parse_host_port(s: string) -> Authority! {
    let cs = s.chars()
    let n = len(cs)
    if n > 0 && cs[0] == "[" { return _parse_ip_literal(cs, n)! }

    // Neither a reg-name nor an IPv4 address may hold a colon, so the first one
    // starts the port.
    let colon = index_of(cs, ":", 0, n)
    if colon {
        let host = validate(substr(cs, 0, colon), CharClass.RegName)!
        return Authority {
            userinfo: null,
            host: host.to_lower(),
            port: _parse_port(substr(cs, colon + 1, n))!,
        }
    }
    return Authority { userinfo: null, host: validate(s, CharClass.RegName)!.to_lower(), port: null }
}

fun _parse_ip_literal(cs: string[], n: int64) -> Authority! {
    let found = index_of(cs, "]", 0, n)
    if !found { return error("unterminated IP literal in authority: {substr(cs, 0, n)}") }
    let close: int64 = found
    // IP-literal = "[" ( IPv6address / IPvFuture ) "]", so "[]" is not one.
    if close == 1 { return error("empty IP literal in authority") }
    validate(substr(cs, 1, close), CharClass.IpLiteral)!
    let host = substr(cs, 0, close + 1)
    let next: int64 = close + 1
    if next == n { return Authority { userinfo: null, host: host, port: null } }
    if cs[next] != ":" {
        return error("expected `:` after the IP literal in authority: {substr(cs, 0, n)}")
    }
    return Authority { userinfo: null, host: host, port: _parse_port(substr(cs, next + 1, n))! }
}

/** Parses the digits after the port colon; no digits at all means "no port". */
fun _parse_port(s: string) -> uint16?! {
    if len(s) == 0 { return null }
    for c in s.chars() {
        if !is_digit(c) { return error("port is not a number: {s}") }
    }
    return uint16.parse(s)!
}
