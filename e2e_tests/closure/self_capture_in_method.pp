// A closure inside a METHOD body that reads `self`. The free-variable walk
// collected `Ident` reads only, and `self` is its own expression form -- so the
// closure never CAPTURED it: the body's `self` resolved to nothing, and both back
// ends refused the value ("cannot infer the type of an expression temporary").
type Req = {
    path: string
}
type Resp = {
    status: int32
}
type Handler = {
    handler: (Req) -> Resp
}
type Server = {
    _handlers: Handler[]
}

fun Server._handler_pass(self, req: Req) {
    for h in self._handlers {
        return h.handler(req)
    }
    return Resp { status: 404 }
}

/**
 * Register a handler. The closure is never CALLED here, only stored: its call
 * contract is the field's declared function type, one call boundary away from
 * the caller -- the probe follows the store.
 */
fun Server.register(self, handler: (Req) -> Resp) {
    self._handlers.push(Handler { handler: handler })
}

fun Server.dispatch_via_closure(self, req: Req) {
    // The closure reads `self` (a method call on it), so it must capture it.
    const c = () -> {
        return self._handler_pass(req)
    }
    return c()
}

fun main() {
    let s = Server { _handlers: [] }
    // An UNANNOTATED closure registered through the method: its parameter type
    // comes from the stored field's annotation.
    s.register(
        (r) -> {
            if r.path == "/abc" {
                return Resp { status: 200 }
            }
            return Resp { status: 404 }
        },
    )
    const resp = s.dispatch_via_closure(Req { path: "/abc" })
    println(resp.status)
}
