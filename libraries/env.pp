// The process environment: the program's command-line arguments, environment
// variables singly and in bulk, and the working directory.
//
// This is a library rather than part of `std`: asking the operating system
// needs native code, which arrives as a plugin instead of a runtime builtin.
// Point `PREPOLY_INCLUDE` at this directory and import it:
//
//     PREPOLY_INCLUDE=/path/to/libraries
//     import env.{ args, var, vars, current_dir }
//
// Build the plugin once with `libraries/build.sh`.

import libenv.{ env_var, env_vars }
import path.{ Path }
import std.collections.HashMap

/**
 * The program's argument vector: the program file as it was given to the
 * driver, then everything after it -- so `prepoly main.pp a b` gives
 * `["main.pp", "a", "b"]`. Empty in an interactive REPL session, or when
 * the embedder published no arguments.
 */
fun args() -> string[] {
    return _argv()
}

/**
 * The value of environment variable `name`. An unset variable is an error
 * rather than an empty string, so "unset" and "set to empty" stay
 * distinguishable.
 */
fun var(name: string) -> string! {
    return env_var(name)!
}

/**
 * Every environment variable, as a name -> value `HashMap`. Variables whose
 * name or value is not valid UTF-8 are omitted.
 */
fun vars() {
    let flat = env_vars()
    let m = HashMap.new()
    let i = 0
    while i < len(flat) {
        m.set(flat[i], flat[i + 1])
        i += 2
    }
    return m
}

/** The process's current working directory. */
fun current_dir() -> Path! {
    return Path.current_dir()!
}
