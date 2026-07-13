// `HttpResponse.serialize` writes a response as a server puts it on the wire --
// the mirror of `HttpRequest.serialize`, and the piece a program needs to ANSWER
// a request rather than only make one.
//
// The line endings are what a case like this is for: HTTP separates its lines
// with CRLF, and a lone LF would be read as part of the header value by a strict
// peer. The output is printed with the CRLFs marked, so a regression shows up as
// changed text rather than as invisible whitespace.
import http.{ HttpRequest, HttpResponse, Header }

fun show(bytes: uint8[]) -> string! {
    return to_text(bytes)!.replace("\r\n", "<CRLF>")
}

fun main() {
    const body = "hi"
    const response = HttpResponse {
        version: "HTTP/1.1",
        status: 200,
        reason: "OK",
        headers: [
            Header { name: "Content-Type", value: "text/plain" },
            Header { name: "Content-Length", value: "{len(body)}" },
        ],
        body: to_bytes(body),
    }
    println(show(response.serialize())!)

    // Parsing the serialized form yields an equal response.
    const back = HttpResponse.parse(to_text(response.serialize())!)!
    println("{back.version} {back.status} {back.reason}")
    println("{len(back.headers)} {back.body_text()!}")

    // An empty reason phrase keeps the space before it: the status line's
    // grammar asks for that space, and it is what lets `parse` read the line
    // back (as the round trip below shows).
    const empty = HttpResponse {
        version: "HTTP/1.1",
        status: 204,
        reason: "",
        headers: [],
        body: [],
    }
    println(show(empty.serialize())!)
    const back2 = HttpResponse.parse(to_text(empty.serialize())!)!
    println("{back2.status} [{back2.reason}] {len(back2.headers)} {len(back2.body)}")

    // The request side serializes to the same shape, which is the point of
    // having both.
    const request = HttpRequest {
        method: "GET",
        path: "/",
        version: "HTTP/1.1",
        headers: [Header { name: "Host", value: "example.test" }],
        body: [],
    }
    println(show(request.serialize())!)
}
