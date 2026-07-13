import net.{ Tcp, TlsStream }
import url.{ URI }

type Header = {
    name: string
    value: string
}

type HttpRequest = {
    method: string
    path: string
    version: string
    headers: Header[]
    body: uint8[]
}

type HttpResponse = {
    version: string
    status: int32
    reason: string
    headers: Header[]
    body: uint8[]
}

// --- internal helpers ---

fun _split_once(s: string, delim: string) {
    let parts = s.split(delim)
    if len(parts) < 2 { error("delimiter not found")! }
    return [parts[0], parts.slice(1, len(parts)).join(delim)]
}

// \r\n\r\n (13,10,13,10) in byte array
fun _find_header_end(data: uint8[]) -> int64? {
    if len(data) < 4 { return null }
    for i in [0..len(data) - 3] {
        if data[i] == 13 && data[i + 1] == 10 &&
           data[i + 2] == 13 && data[i + 3] == 10 {
            return i
        }
    }
    return null
}

fun _find_header(headers: Header[], name: string) -> string? {
    let lower = name.to_lower()
    for h in headers {
        if h.name.to_lower() == lower { return h.value }
    }
    return null
}

fun _require_header(headers: Header[], name: string) {
    let lower = name.to_lower()
    for h in headers {
        if h.name.to_lower() == lower { return h.value }
    }
    error("missing header: {name}")!
}

fun _parse_header_lines(text: string) {
    let headers: Header[] = []
    for line in text.split("\r\n") {
        if len(line.trim()) > 0 {
            let [name, val] = _split_once(line, ":")!
            headers.push(Header { name: name.trim(), value: val.trim() })
        }
    }
    return headers
}

// --- HttpRequest ---

/** Parses a raw HTTP/1.x request string. */
fun HttpRequest.parse(raw: string) {
    let [head, body_text] = _split_once(raw, "\r\n\r\n")!
    let lines = head.split("\r\n")
    if len(lines) == 0 { error("empty request")! }

    let parts = lines[0].split(" ")
    if len(parts) < 3 { error("invalid request line")! }

    let header_text = lines.slice(1, len(lines)).join("\r\n")
    let headers = _parse_header_lines(header_text)!

    return Self {
        method: parts[0],
        path: parts[1],
        version: parts[2],
        headers: headers,
        body: to_bytes(body_text),
    }
}

/** Serializes this request into raw bytes for sending over TCP. */
fun HttpRequest.serialize(self) -> uint8[] {
    let text = "{self.method} {self.path} {self.version}\r\n"
    for h in self.headers {
        text = "{text}{h.name}: {h.value}\r\n"
    }
    text = "{text}\r\n"
    let bytes = to_bytes(text)
    for b in self.body { bytes.push(b) }
    return bytes
}

// --- HttpResponse ---

/** Parses a raw HTTP/1.x response string. */
fun HttpResponse.parse(raw: string) {
    let [head, body_text] = _split_once(raw, "\r\n\r\n")!
    let lines = head.split("\r\n")
    if len(lines) == 0 { error("empty response")! }

    let parts = lines[0].split(" ")
    if len(parts) < 2 { error("invalid status line")! }

    let status = int32.parse(parts[1])!
    let reason = ""
    if len(parts) >= 3 {
        reason = parts.slice(2, len(parts)).join(" ")
    }

    let header_text = lines.slice(1, len(lines)).join("\r\n")
    let headers = _parse_header_lines(header_text)!

    return Self {
        version: parts[0],
        status: status,
        reason: reason,
        headers: headers,
        body: to_bytes(body_text),
    }
}

/**
 * Serializes this response into raw bytes, as a server writes them onto the
 * connection: the status line, the headers, a blank line, then the body.
 *
 * The headers are written exactly as they stand -- nothing is added, so a
 * `Content-Length` (or a `Transfer-Encoding`) is the caller's business, as it
 * is for `HttpRequest.serialize`. Parsing the result yields an equal response.
 *
 * The status line keeps the space before the reason phrase even when the reason
 * is empty (`HTTP/1.1 204 `): the grammar asks for it, and it is what lets
 * `parse` read the line back.
 */
fun HttpResponse.serialize(self) -> uint8[] {
    let text = "{self.version} {self.status} {self.reason}\r\n"
    for h in self.headers {
        text = "{text}{h.name}: {h.value}\r\n"
    }
    text = "{text}\r\n"
    let bytes = to_bytes(text)
    for b in self.body { bytes.push(b) }
    return bytes
}

/** Returns the response body decoded as a UTF-8 string. */
fun HttpResponse.body_text(self) {
    return to_text(self.body)
}

// --- HttpClient ---

// _connect is unannotated: accepts any () -> conn! closure.
// Tcp and TlsStream are structurally compatible (read/write/close),
// so a single type handles both protocols.
type HttpClient = {
    host: string
    port: int32
    _default_port: int32
    _connect
}

fun HttpClient.http(host: string, port: int32) {
    return Self {
        host: host,
        port: port,
        _default_port: 80,
        _connect: () -> { return Tcp.connect(host, port) },
    }
}

fun HttpClient.https(host: string, port: int32) {
    return Self {
        host: host,
        port: port,
        _default_port: 443,
        _connect: () -> { return TlsStream.connect(host, port) },
    }
}

// conn is structurally typed: works with both Tcp and TlsStream
fun _read_response(conn, req: HttpRequest) {
    conn.write(req.serialize())!

    let data: uint8[] = []
    let header_end: int64 = -1

    while header_end < 0 {
        let chunk = conn.read(4096)!
        if len(chunk) == 0 { error("connection closed before headers complete")! }
        for b in chunk { data.push(b) }
        let pos = _find_header_end(data)
        if pos { header_end = pos }
    }

    let header_bytes = data.slice(0, header_end)
    let header_text = to_text(header_bytes)!
    let lines = header_text.split("\r\n")
    if len(lines) == 0 { error("empty response")! }

    let status_parts = lines[0].split(" ")
    if len(status_parts) < 2 { error("invalid status line")! }

    let version = status_parts[0]
    let status = int32.parse(status_parts[1])!
    let reason = ""
    if len(status_parts) >= 3 {
        reason = status_parts.slice(2, len(status_parts)).join(" ")
    }

    let remaining = lines.slice(1, len(lines)).join("\r\n")
    let headers = _parse_header_lines(remaining)!

    let body_start = header_end + 4
    let content_length: int64 = -1
    for h in headers {
        if h.name.to_lower() == "content-length" {
            content_length = int64.parse(h.value.trim())!
        }
    }

    if content_length >= 0 {
        while len(data) - body_start < content_length {
            let chunk = conn.read(4096)!
            if len(chunk) == 0 { error("connection closed before body complete")! }
            for b in chunk { data.push(b) }
        }
    } else {
        let reading = true
        while reading {
            let read_result = conn.read(4096)
            if let Ok { value } = read_result {
                if len(value) == 0 { reading = false }
                else { for b in value { data.push(b) } }
            } else {
                reading = false
            }
        }
    }

    conn.close()

    return HttpResponse {
        version: version,
        status: status,
        reason: reason,
        headers: headers,
        body: data.slice(body_start, len(data)),
    }
}

fun HttpClient.request(self, req: HttpRequest) {
    let conn = self._connect()!
    return _read_response(conn, req)
}

fun HttpClient.fetch(self, path: string) {
    let host_str = self.host
    if self.port != self._default_port {
        host_str = "{self.host}:{self.port}"
    }
    let req = HttpRequest {
        method: "GET",
        path: path,
        version: "HTTP/1.1",
        headers: [Header { name: "Host", value: host_str }],
        body: [],
    }
    return self.request(req)
}

// --- convenience functions ---

/** Sends the request via plain HTTP. Requires a Host header. */
fun request(req: HttpRequest) {
    let host_value = _require_header(req.headers, "Host")!
    let host_parts = host_value.trim().split(":")
    let host = host_parts[0].trim()
    let port = 80
    if len(host_parts) == 2 {
        if let Ok { value } = int32.parse(host_parts[1].trim()) {
            port = value
        }
    }
    let client = HttpClient.http(host, port)
    return client.request(req)
}

/** How many redirects `fetch` follows before it gives up. */
const MAX_REDIRECTS = 10

/**
 * GETs the given URL (http:// or https://), following redirects, and returns the
 * response.
 *
 * A 3xx carrying a `Location` is followed, up to `MAX_REDIRECTS` hops; the header
 * is resolved against the URL it came from, so a relative `Location` (`/next`,
 * `../next`) works as well as an absolute one, and a hop may cross schemes or
 * hosts. The chain stays a GET: `fetch` sends no body, so the method rewrite RFC
 * 9110 prescribes for 301/302/303 is a no-op here, and 307/308 preserve the
 * method anyway.
 *
 * A 3xx with NO `Location` is returned as it stands rather than treated as a
 * failure -- a 304 (not modified) or a 300 (multiple choices) is an answer, not
 * a hop.
 */
fun fetch(url_str: string) {
    let uri = URI.parse(url_str)!
    let hops = 0
    while hops <= MAX_REDIRECTS {
        let response = _fetch_uri(uri)!
        if !_is_redirect(response.status) {
            return response
        }
        if let location = _find_header(response.headers, "Location") {
            uri = uri.resolve(location)!
            hops += 1
        } else {
            return response
        }
    }
    error("too many redirects ({MAX_REDIRECTS}) following {url_str}")!
}

// The redirects that name a new target in `Location`. 300 and 304 are 3xx too,
// but neither is a hop, so they are deliberately absent.
fun _is_redirect(status: int32) -> bool {
    return status == 301 || status == 302 || status == 303 ||
           status == 307 || status == 308
}

// One GET of an already-parsed URL. The scheme picks the transport and the
// default port; an explicit port overrides it.
fun _fetch_uri(uri: URI) {
    let is_https = false
    let s = uri.scheme
    if s { is_https = s == "https" }

    let path = uri.path
    if len(path) == 0 { path = "/" }
    let q = uri.query
    if q { path = "{path}?{q}" }

    let auth = uri.authority
    if auth {
        let host = auth.host
        let port = 80
        if is_https { port = 443 }
        let p = auth.port
        if p { port = int32.from(p)! }

        if is_https {
            let client = HttpClient.https(host, port)
            return client.fetch(path)
        }
        let client = HttpClient.http(host, port)
        return client.fetch(path)
    }
    let url_str = uri.to_string()
    error("URL has no authority: {url_str}")!
}
