//! Cross-crate utilities: the tracing initialization every prepoly binary
//! (driver, language server) uses, and the program argument vector shared
//! between the driver and both back ends' `_argv` builtin.

use std::sync::OnceLock;

/// The running program's argument vector: the program file as it was written
/// on the driver's command line, then everything after it. Set once by the
/// driver before the program runs; both back ends' `_argv` builtin reads it.
static PROGRAM_ARGV: OnceLock<Vec<String>> = OnceLock::new();

/// Publish the program's argument vector (see [`program_argv`]). Later calls
/// are ignored: the vector describes this process's one program invocation.
pub fn set_program_argv(argv: Vec<String>) {
    let _ = PROGRAM_ARGV.set(argv);
}

/// The program's argument vector, or empty when none was published -- an
/// interactive REPL session, or an embedder that never set one.
pub fn program_argv() -> &'static [String] {
    PROGRAM_ARGV.get().map(Vec::as_slice).unwrap_or(&[])
}

/// Initialize the tracing subscriber for a prepoly binary.
///
/// Two environment variables control the output (both default to warnings
/// only):
///
/// - `PREPOLY_LOG` -- a full `tracing_subscriber::EnvFilter` directive string
///   (`PREPOLY_LOG=debug`, `PREPOLY_LOG=prepoly_typeck=debug,prepoly_solver=trace`)
///   for anyone comfortable with filter syntax.
/// - `PREPOLY_LOG_TYPE` -- a comma-separated list of log TYPE names, the
///   friendlier switch for "show me this one output". Each type `t` enables
///   both the named-output target `prepoly::t` at TRACE (e.g. `mir` and `ir`
///   are the MIR / LLVM-module dumps the back end emits under
///   `tracing::trace!(target: "prepoly::mir", ...)`) and the crate target
///   `prepoly_t` at DEBUG (so `PREPOLY_LOG_TYPE=typeck,solver` reads naturally).
///
/// Logs go to stderr (program output owns stdout; for the language server
/// stdout is the LSP transport) without timestamps, which keeps them readable
/// as a compile trace and avoids a clock call on the wasm build. `try_init` so
/// a second call (e.g. from a test harness) is a no-op rather than a panic.
pub fn init_tracing() {
    use tracing_subscriber::filter::LevelFilter;
    let mut filter = tracing_subscriber::EnvFilter::builder()
        .with_default_directive(LevelFilter::WARN.into())
        .with_env_var("PREPOLY_LOG")
        .from_env_lossy();
    if let Ok(types) = std::env::var("PREPOLY_LOG_TYPE") {
        for ty in types.split(',').map(str::trim).filter(|t| !t.is_empty()) {
            for directive in [
                format!("prepoly::{ty}=trace"),
                format!("prepoly_{ty}=debug"),
            ] {
                match directive.parse() {
                    Ok(d) => filter = filter.add_directive(d),
                    // A malformed type name must not silently vanish: the user
                    // asked for that output and would otherwise stare at silence.
                    Err(e) => eprintln!("warning: ignoring PREPOLY_LOG_TYPE entry `{ty}`: {e}"),
                }
            }
        }
    }
    let _ = tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_writer(std::io::stderr)
        .without_time()
        .try_init();
}
