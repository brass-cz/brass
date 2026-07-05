// Library defining `dist` -- the same name rename_not_hijacked.pp binds
// locally via `import ... as dist`. That use must NOT resolve here.
fun dist() -> int32 { return 2 }

fun helper() -> int32 { return 40 }
