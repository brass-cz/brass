//! Process-environment queries, as a native Brass plugin.
//!
//! `std/env.cz` owns the user-facing API (`args`, `var`, `vars`,
//! `current_dir`) and calls in here for what needs the operating system --
//! except `args`, which is the `_argv` runtime builtin (the argument vector
//! lives in the driver process, not the environment). The plugin ABI carries
//! strings and arrays but not maps, so `env_vars` answers with a flat
//! name/value sequence the wrapper folds into a `HashMap`.

use brass_plugin::{BrassLib, Registry, brass_lib, decl, export};

export! {
    /// The value of environment variable `name`. Unset (or a value that is not
    /// valid UTF-8) is an error, so "unset" and "set to the empty string" stay
    /// distinguishable.
    fn env_var(name: String) -> Result<String, String> {
        std::env::var(&name).map_err(|e| format!("{name}: {e}"))
    }

    /// Every environment variable, as a flat `[name, value, name, value, ..]`
    /// sequence. Variables whose name or value is not valid UTF-8 are skipped:
    /// Brass strings are UTF-8, and a bulk listing should not fail over one
    /// foreign entry (ask for it by name with `env_var` to see the error).
    fn env_vars() -> Vec<String> {
        let mut flat = Vec::new();
        for (name, value) in std::env::vars_os() {
            if let (Ok(name), Ok(value)) = (name.into_string(), value.into_string()) {
                flat.push(name);
                flat.push(value);
            }
        }
        flat
    }

    /// The separator between entries in an environment path list: `:` on
    /// Unix-family platforms and `;` on Windows.
    fn env_path_separator() -> String {
        if cfg!(windows) { ";" } else { ":" }.to_string()
    }
}

struct EnvLib;

impl BrassLib for EnvLib {
    fn entry(reg: &mut Registry) {
        reg.export(decl!(env_var));
        reg.export(decl!(env_vars));
        reg.export(decl!(env_path_separator));
    }
}

brass_lib!(EnvLib);
