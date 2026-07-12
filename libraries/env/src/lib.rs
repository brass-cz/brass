//! Process-environment queries, as a native prepoly plugin.
//!
//! `libraries/env.pp` owns the user-facing API (`args`, `var`, `vars`,
//! `current_dir`) and calls in here for what needs the operating system --
//! except `args`, which is the `_argv` runtime builtin (the argument vector
//! lives in the driver process, not the environment). The plugin ABI carries
//! strings and arrays but not maps, so `env_vars` answers with a flat
//! name/value sequence the wrapper folds into a `HashMap`.

use prepoly_plugin::{PrepolyLib, Registry, decl, export, prepoly_lib};

export! {
    /// The value of environment variable `name`. Unset (or a value that is not
    /// valid UTF-8) is an error, so "unset" and "set to the empty string" stay
    /// distinguishable.
    fn env_var(name: String) -> Result<String, String> {
        std::env::var(&name).map_err(|e| format!("{name}: {e}"))
    }

    /// Every environment variable, as a flat `[name, value, name, value, ..]`
    /// sequence. Variables whose name or value is not valid UTF-8 are skipped:
    /// prepoly strings are UTF-8, and a bulk listing should not fail over one
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
}

struct EnvLib;

impl PrepolyLib for EnvLib {
    fn entry(reg: &mut Registry) {
        reg.export(decl!(env_var));
        reg.export(decl!(env_vars));
    }
}

prepoly_lib!(EnvLib);
