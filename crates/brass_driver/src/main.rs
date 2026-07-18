//! Brass command-line driver.
//!
//! Pipeline: resolve the module graph, parse, lower to HIR, check
//! (resolve + typeck), then run the checked program. The standard library is an
//! embedded prelude.
//!
//! Two execution back ends share the same front end. When the JIT back end is
//! available, `brass <file>` compiles and runs through the LLVM JIT
//! (`brass_jit_llvm`); otherwise the default runtime is the REPL interpreter
//! (`brass_repl`). The JIT is available when the default `jit` feature is on AND
//! the target is not wasm (LLVM cannot link for wasm), so a wasm build
//! automatically disables it and falls back to the interpreter -- this is the
//! `jit_backend` cfg from `build.rs`. `brass repl [file]` always uses the
//! interpreter: with a file it runs the file, with none it starts an interactive
//! session. Argument parsing is `clap`'s derive interface.

use std::collections::{HashMap, HashSet};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};

use brass_hir::{LoadedModule, Program, lower};
use brass_parser::ast::{Stmt, TopLevel};
use brass_parser::parse;
use brass_parser::{Span, line_col};

/// The Brass toolchain driver.
///
/// The program file is a bare positional argument (`brass file.cz`) rather than
/// a `run` subcommand. A leading `check`/`repl` parses as the subcommand; any
/// other first argument is taken as the file, and everything after the file
/// is the program's, untouched (see [`parse_cli`]).
#[derive(Parser)]
#[command(
    name = "brass",
    version = brass_metadata::version_string(),
    about = "The Brass compiler and REPL"
)]
struct Cli {
    /// A program file to type-check and run with the default runtime (the LLVM JIT
    /// when it is available -- the `jit` feature on a non-wasm target -- otherwise
    /// the REPL interpreter). With neither a file nor a subcommand, the
    /// interactive REPL starts instead.
    file: Option<String>,
    /// Everything after the program file, passed through to the program
    /// VERBATIM -- driver-flag lookalikes (`--eager`, `--help`), subcommand
    /// words, and `--` included: the env library's `args()` returns the
    /// program file followed by these. Filled by [`parse_cli`], which splits
    /// the command line at the file before clap parses it; clap alone would
    /// intercept its own flags anywhere on the line.
    args: Vec<String>,
    /// Type-check the whole program before running it (what `brass check`
    /// does), instead of the default lazy check that runs type inference on a
    /// separate thread. Must precede the program file: everything after the
    /// file belongs to the program.
    #[arg(long)]
    eager: bool,
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand)]
enum Command {
    /// Type-check a program without running it.
    Check { file: String },
    /// Start the interactive REPL, or run a file through the REPL interpreter.
    Repl {
        file: Option<String>,
        /// Everything after the program file, passed through to the program
        /// verbatim (see the env library's `args()` and [`parse_cli`]).
        args: Vec<String>,
    },
}

/// Which back end / phase `drive` runs after the front end produces a checked
/// program.
enum Mode {
    /// Type-check and run. `eager` (the `--eager` flag) forces the whole
    /// check to finish on the calling thread before execution; the default
    /// for a JIT run is the lazy path, which moves type inference to a
    /// dedicated checker thread.
    Run {
        eager: bool,
    },
    Check,
    Repl,
}

/// Host stack for the worker thread `main` delegates to. The REPL interpreter
/// recurses natively once per Brass call (plus expression nesting inside each
/// body), so its call-depth guard (`brass_repl`'s 8000-call limit) is only
/// reachable when the stack holds that many interpreter activation records; the
/// default 8 MiB main stack overflows first and aborts the process instead of
/// surfacing the guard's clean error. The reservation is virtual memory — pages
/// are committed only as the stack actually grows.
#[cfg(not(target_family = "wasm"))]
const MAIN_STACK_BYTES: usize = 256 * 1024 * 1024;

fn main() -> ExitCode {
    // Shared across the Brass binaries: BRASS_LOG (EnvFilter syntax) and
    // BRASS_LOG_TYPE (comma-separated named log types) select the output.
    brass_utils::init_tracing();
    #[cfg(not(target_family = "wasm"))]
    {
        std::thread::Builder::new()
            .name("brass-main".into())
            .stack_size(MAIN_STACK_BYTES)
            .spawn(run_cli)
            .expect("failed to start the driver thread")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    }
    // WebAssembly has no threads; run on the embedder's stack.
    #[cfg(target_family = "wasm")]
    run_cli()
}

fn run_cli() -> ExitCode {
    let cli = parse_cli();
    match cli.command {
        // A bare file argument is type-checked and run; with neither a file nor a
        // subcommand, start an interactive REPL session.
        None => match cli.file {
            Some(file) => {
                set_program_args(Some(&file), &cli.args);
                exit_code(drive(Mode::Run { eager: cli.eager }, &file))
            }
            None => {
                set_program_args(None, &cli.args);
                repl_interactive()
            }
        },
        Some(Command::Check { file }) => exit_code(drive(Mode::Check, &file)),
        Some(Command::Repl { file: None, args }) => {
            set_program_args(None, &args);
            repl_interactive()
        }
        Some(Command::Repl {
            file: Some(file),
            args,
        }) => {
            set_program_args(Some(&file), &args);
            exit_code(drive(Mode::Repl, &file))
        }
    }
}

/// Parse the command line with the program-argument boundary applied BEFORE
/// clap sees it: everything after the program file belongs to the program,
/// verbatim -- tokens that look like driver flags (`--eager`), the driver's
/// own `--help`/`--version`, subcommand words, and `--` included. Clap alone
/// cannot express that (its defined flags and subcommands match anywhere on
/// the line), so the argv is split at the file and only the head is parsed.
///
/// The file is the first token that does not start with `-` -- directly for
/// the bare-file form, after `repl` for the interpreter form. `check` and
/// `help` take no program arguments, so their lines stay fully clap's.
fn parse_cli() -> Cli {
    let argv: Vec<std::ffi::OsString> = std::env::args_os().collect();
    let file_at = program_file_index(&argv);
    let split = file_at.map_or(argv.len(), |i| i + 1);
    let mut cli = Cli::parse_from(argv[..split].iter().cloned());
    let rest: Vec<String> = argv[split..]
        .iter()
        .map(|a| a.to_string_lossy().into_owned())
        .collect();
    if !rest.is_empty() {
        match &mut cli.command {
            Some(Command::Repl { args, .. }) => *args = rest,
            _ => cli.args = rest,
        }
    }
    cli
}

/// Locate the positional program file before splitting its trailing arguments
/// away from clap. Root flags may precede a subcommand; `--` ends flag and
/// subcommand recognition, so a following `check` or `repl` is a file name.
fn program_file_index(argv: &[std::ffi::OsString]) -> Option<usize> {
    let mut index = 1;
    let mut positional_only = false;
    while index < argv.len() {
        let token = argv[index].to_string_lossy();
        if !positional_only && token == "--" {
            positional_only = true;
            index += 1;
            continue;
        }
        if !positional_only && token.starts_with('-') {
            index += 1;
            continue;
        }
        if !positional_only && (token == "check" || token == "help") {
            return None;
        }
        if !positional_only && token == "repl" {
            index += 1;
            while index < argv.len() {
                let token = argv[index].to_string_lossy();
                if token == "--" {
                    positional_only = true;
                    index += 1;
                    continue;
                }
                if positional_only || !token.starts_with('-') {
                    return Some(index);
                }
                index += 1;
            }
            return None;
        }
        return Some(index);
    }
    None
}

/// Publish the program's argument vector -- the program file as written on
/// the command line, then everything after it -- for the `_argv` builtin
/// (behind the env library's `args()`) to answer with. Empty for an
/// interactive REPL session.
fn set_program_args(file: Option<&str>, args: &[String]) {
    let argv = file
        .iter()
        .map(|f| f.to_string())
        .chain(args.iter().cloned())
        .collect();
    brass_utils::set_program_argv(argv);
}

fn exit_code(r: Result<(), u8>) -> ExitCode {
    match r {
        Ok(()) => ExitCode::SUCCESS,
        Err(code) => ExitCode::from(code),
    }
}

/// Apply the spawn auto-acquire transform to every function and
/// method body in each module, before lowering. This rewrites a `spawn` closure
/// that mutates a captured cown to acquire it with `with` (or the `_with_all`
/// group form), so the source needs no ownership annotations yet concurrent
/// mutation is serialized by the cown lock. Interprocedural spawn-capture
/// summaries are computed first over all modules, so a caller handing a local to
/// a helper that spawns is promoted and guarded too. Returns the compile errors
/// for `spawn` arguments the analysis cannot see through (each such spawn would
/// otherwise share state with no guard at all).
#[cfg(jit_backend)]
fn auto_acquire_modules(modules: &mut [LoadedModule]) -> Vec<(String, Span)> {
    use brass_jit_llvm::ownership::{auto_acquire, spawn_capture_summaries};
    use brass_parser::ast::{Block, Member, TypeBody};

    let names = |params: &[brass_parser::ast::Param]| -> HashSet<String> {
        params.iter().map(|p| p.name.clone()).collect()
    };
    let name_list = |params: &[brass_parser::ast::Param]| -> Vec<String> {
        params.iter().map(|p| p.name.clone()).collect()
    };

    // Interprocedural pass: which parameters of which function/method are
    // captured by a spawn reachable inside it (methods contribute their explicit
    // `self` at index 0, matching a method call's receiver position).
    let summaries = {
        let mut fns: Vec<(String, Vec<String>, &Block)> = Vec::new();
        for m in modules.iter() {
            for item in &m.ast.items {
                match item {
                    TopLevel::Fun(f) => fns.push((f.name.clone(), name_list(&f.params), &f.body)),
                    TopLevel::Type(t) => {
                        let members = match &t.body {
                            TypeBody::Record(members) => members,
                            TypeBody::Sum(_) | TypeBody::Alias(_) => continue,
                        };
                        for member in members {
                            if let Member::Method(method) = member
                                && let Some(body) = &method.body
                            {
                                fns.push((method.name.clone(), name_list(&method.params), body));
                            }
                        }
                    }
                    TopLevel::Stmt(_) => {}
                }
            }
        }
        spawn_capture_summaries(&fns)
    };

    // Module globals written anywhere in the program: a spawned task touching
    // one would race the writer with no binding to promote to a cown, so
    // `pre_spawn_errors` rejects such captures (never-written globals are
    // shareable and stay allowed).
    let mutated_globals = {
        use brass_jit_llvm::ownership::mutates;
        use brass_parser::ast::{Pattern, Stmt};

        fn pattern_names(pat: &Pattern, out: &mut HashSet<String>) {
            match pat {
                Pattern::Binding(name, _) => {
                    out.insert(name.clone());
                }
                Pattern::Array(pats, _) => {
                    for p in pats {
                        pattern_names(p, out);
                    }
                }
                _ => {}
            }
        }

        let mut globals: HashSet<String> = HashSet::new();
        for m in modules.iter() {
            for item in &m.ast.items {
                if let TopLevel::Stmt(Stmt::Let { pat, .. }) = item {
                    pattern_names(pat, &mut globals);
                }
            }
        }
        let mut bodies: Vec<Block> = Vec::new();
        for m in modules.iter() {
            let mut top = Vec::new();
            for item in &m.ast.items {
                match item {
                    TopLevel::Fun(f) => bodies.push(f.body.clone()),
                    TopLevel::Type(t) => {
                        if let TypeBody::Record(members) = &t.body {
                            for member in members {
                                if let Member::Method(method) = member
                                    && let Some(body) = &method.body
                                {
                                    bodies.push(body.clone());
                                }
                            }
                        }
                    }
                    TopLevel::Stmt(s) => top.push(s.clone()),
                }
            }
            bodies.push(Block {
                stmts: top,
                span: brass_parser::Span::new(0, 0),
            });
        }
        let mut mutated: HashSet<String> = HashSet::new();
        for g in &globals {
            if bodies.iter().any(|b| mutates(b, g)) {
                mutated.insert(g.clone());
            }
        }
        mutated
    };

    let mut errors: Vec<(String, Span)> = Vec::new();
    let mut push_errors = |errs: Vec<brass_jit_llvm::ownership::SpawnError>| {
        errors.extend(errs.into_iter().map(|e| (e.message, e.span)));
    };
    for m in modules {
        // Init code never runs through the ownership pass, so a module-top-level
        // spawn would get no promotion or guarding at all: reject it.
        let top_stmts: Vec<brass_parser::ast::Stmt> = m
            .ast
            .items
            .iter()
            .filter_map(|item| match item {
                TopLevel::Stmt(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        push_errors(
            brass_jit_llvm::ownership::all_spawn_spans(&top_stmts)
                .into_iter()
                .map(|span| brass_jit_llvm::ownership::SpawnError {
                    message: "`spawn` at module top level is not supported; spawn inside a \
                              function"
                        .to_string(),
                    span,
                })
                .collect(),
        );
        for item in &mut m.ast.items {
            match item {
                TopLevel::Fun(f) => {
                    let params = names(&f.params);
                    push_errors(brass_jit_llvm::ownership::pre_spawn_errors(
                        &f.body.stmts,
                        &params,
                        &mutated_globals,
                    ));
                    push_errors(auto_acquire(&mut f.body.stmts, &params, &summaries));
                }
                TopLevel::Type(t) => {
                    let members = match &mut t.body {
                        TypeBody::Record(members) => members,
                        TypeBody::Sum(_) | TypeBody::Alias(_) => continue,
                    };
                    for member in members {
                        if let Member::Method(method) = member
                            && let Some(body) = &mut method.body
                        {
                            let params = names(&method.params);
                            push_errors(brass_jit_llvm::ownership::pre_spawn_errors(
                                &body.stmts,
                                &params,
                                &mutated_globals,
                            ));
                            push_errors(auto_acquire(&mut body.stmts, &params, &summaries));
                        }
                    }
                }
                TopLevel::Stmt(_) => {}
            }
        }
    }
    errors
}

/// Emit a warning for every `spawn` capture the compiler auto-cowns. The shared ownership analysis (`brass_jit_llvm::ownership`) decides
/// move/freeze/cown from liveness and mutation; a `Cown` decision means the capture
/// is mutated and still live, so the compiler wraps it for safe concurrent access.
///
/// Runs on the original module ASTs *before* `auto_acquire_modules` rewrites the
/// mutated captures into explicit `with` scopes: the warning must reflect what
/// auto-acquire is about to do, so it has to see the pre-transform source.
#[cfg(jit_backend)]
fn report_spawn_ownership(modules: &[LoadedModule]) -> Vec<String> {
    use brass_jit_llvm::ownership::{CaptureDecision, Ownership, analyze_spawns_stmts};
    use brass_parser::ast::{Member, TypeBody};

    fn warn(out: &mut Vec<String>, decisions: Vec<CaptureDecision>, ctx: &str) {
        for d in decisions {
            if d.ownership == Ownership::Cown {
                out.push(format!(
                    "warning: variable '{}' is shared with a spawned task; every \
                     access to it is auto-guarded by its cown lock{ctx}\n  = note: for \
                     finer-grained concurrency, acquire it explicitly with 'with(cown, \
                     (c) -> {{ ... }})'",
                    d.var
                ));
            }
        }
    }

    fn param_names(params: &[brass_parser::ast::Param]) -> HashSet<String> {
        params.iter().map(|p| p.name.clone()).collect()
    }

    let mut out = Vec::new();
    for m in modules {
        let mut init_stmts: Vec<Stmt> = Vec::new();
        for item in &m.ast.items {
            match item {
                TopLevel::Fun(f) => warn(
                    &mut out,
                    analyze_spawns_stmts(&f.body.stmts, &param_names(&f.params)),
                    &format!(" in `{}`", f.name),
                ),
                TopLevel::Type(t) => {
                    let members = match &t.body {
                        TypeBody::Record(members) => members,
                        TypeBody::Sum(_) | TypeBody::Alias(_) => continue,
                    };
                    for member in members {
                        if let Member::Method(method) = member
                            && let Some(body) = &method.body
                        {
                            warn(
                                &mut out,
                                analyze_spawns_stmts(&body.stmts, &param_names(&method.params)),
                                &format!(" in `{}.{}`", t.name, method.name),
                            );
                        }
                    }
                }
                TopLevel::Stmt(s) => init_stmts.push(s.clone()),
            }
        }
        if !init_stmts.is_empty() {
            warn(
                &mut out,
                analyze_spawns_stmts(&init_stmts, &HashSet::new()),
                &format!(" in module `{}`", m.path.join(".")),
            );
        }
    }
    out
}

/// Make any Rust panic abort the process instead of unwinding. JIT-compiled
/// frames carry no unwind tables, so a panic in a runtime function called from
/// JIT code that unwinds into them is undefined behavior. Aborting in the panic
/// hook -- before unwinding begins -- keeps such a failure well-defined (a clean
/// abort with the panic message). Installed once, only on the JIT execution path;
/// the interpreter is pure Rust and unwinds normally, and the in-process JIT
/// tests call `brass_jit_llvm::run` directly without going through here.
#[cfg(jit_backend)]
fn install_jit_panic_guard() {
    use std::sync::Once;
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        let default = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            default(info);
            std::process::abort();
        }));
    });
}

/// Run a checked program through the default runtime: the LLVM JIT, used when the
/// JIT back end is available (the `jit` feature on a non-wasm target).
#[cfg(jit_backend)]
#[allow(clippy::too_many_arguments)] // mirrors the checker's channel outputs
fn execute(
    program: &Program,
    expr_types: &HashMap<Span, brass_hir::Type>,
    view_args: &HashSet<Span>,
    sum_views: &HashMap<Span, brass_hir::Type>,
    call_locations: &HashMap<Span, (String, u32, u32)>,
    lift_errs: &HashSet<Span>,
    fields_loops: &HashMap<Span, Vec<String>>,
    type_names: &HashMap<Span, String>,
    typeof_types: &HashMap<Span, brass_hir::Type>,
    null_props: &HashSet<Span>,
    lazy: bool,
) -> Result<(), String> {
    install_jit_panic_guard();
    if lazy {
        return brass_jit_llvm::run_lazy(
            program,
            &brass_mir::CheckerChannels {
                expr_types,
                view_args,
                sum_views,
                call_locations,
                lift_errs,
                fields_loops,
                type_names,
                typeof_types,
                null_props,
            },
        );
    }
    brass_jit_llvm::run(
        program,
        expr_types,
        view_args,
        sum_views,
        call_locations,
        lift_errs,
        fields_loops,
        type_names,
        typeof_types,
        null_props,
    )
}

/// Run a checked program through the default runtime: the REPL interpreter, used
/// when the JIT back end is unavailable (no `jit` feature, or a wasm target).
#[cfg(not(jit_backend))]
#[allow(clippy::too_many_arguments)] // mirrors the checker's channel outputs
fn execute(
    program: &Program,
    expr_types: &HashMap<Span, brass_hir::Type>,
    view_args: &HashSet<Span>,
    sum_views: &HashMap<Span, brass_hir::Type>,
    call_locations: &HashMap<Span, (String, u32, u32)>,
    lift_errs: &HashSet<Span>,
    fields_loops: &HashMap<Span, Vec<String>>,
    type_names: &HashMap<Span, String>,
    typeof_types: &HashMap<Span, brass_hir::Type>,
    null_props: &HashSet<Span>,
    _lazy: bool,
) -> Result<(), String> {
    brass_repl::run(
        program,
        expr_types,
        view_args,
        sum_views,
        call_locations,
        lift_errs,
        fields_loops,
        type_names,
        typeof_types,
        null_props,
        &mut io::stdout(),
    )
}

/// Run a checked program through the REPL interpreter (the `repl` subcommand),
/// regardless of the `jit` feature.
#[allow(clippy::too_many_arguments)] // mirrors the checker's channel outputs
fn execute_repl(
    program: &Program,
    expr_types: &HashMap<Span, brass_hir::Type>,
    view_args: &HashSet<Span>,
    sum_views: &HashMap<Span, brass_hir::Type>,
    call_locations: &HashMap<Span, (String, u32, u32)>,
    lift_errs: &HashSet<Span>,
    fields_loops: &HashMap<Span, Vec<String>>,
    type_names: &HashMap<Span, String>,
    typeof_types: &HashMap<Span, brass_hir::Type>,
    null_props: &HashSet<Span>,
) -> Result<(), String> {
    brass_repl::run(
        program,
        expr_types,
        view_args,
        sum_views,
        call_locations,
        lift_errs,
        fields_loops,
        type_names,
        typeof_types,
        null_props,
        &mut io::stdout(),
    )
}

/// A program that passed every front-end check, ready to run.
struct Checked {
    program: Program,
    /// Checker-resolved instance types of aggregate-producing expressions, keyed
    /// by span; the back-end seeding channel (see
    /// `brass_typeck::stream::aggregate_result_types`).
    expr_types: HashMap<Span, brass_hir::Type>,
    /// Spans of anonymous structural arguments the checker approved for view
    /// conversion; MIR lowering wraps exactly these in `Rvalue::RecordView`.
    view_args: HashSet<Span>,
    /// Value expressions the checker accepted as a declared sum subtype at a
    /// flow site (span -> parent sum symbol); MIR lowering rebuilds them.
    sum_views: HashMap<Span, brass_hir::Type>,
    /// Every call expression's source position (label, line, col), keyed by
    /// the call's span. MIR lowering fills a callee's implicit trailing
    /// `Location` parameter from this map.
    call_locations: HashMap<Span, (String, u32, u32)>,
    /// `expr!` sites whose propagated Err payload is re-raised wrapped into
    /// the prelude `Error`; MIR's propagation arm rebuilds the value.
    lift_errs: HashSet<Span>,
    /// Field lists of checker-approved fields-loops, keyed by loop-statement
    /// span; MIR lowering unrolls them (see `brass_hir::expand`).
    fields_loops: HashMap<Span, Vec<String>>,
    /// Resolved `typeof(x)` strings, keyed by call span.
    type_names: HashMap<Span, String>,
    /// Resolved binding types of `typeof`-bearing local annotations.
    typeof_types: HashMap<Span, brass_hir::Type>,
    /// Spans of `expr!` operators with a nullable operand (null propagates as
    /// `Result.Null`); MIR lowering emits the presence-test shape for these.
    null_props: HashSet<Span>,
}

/// Drive the front end on a source file, then act per `mode`. Front-end
/// diagnostics are printed to stderr; an error returns a non-zero exit code.
fn drive(mode: Mode, file: &str) -> Result<(), u8> {
    let main_path = PathBuf::from(file);
    let main_src = std::fs::read_to_string(&main_path).map_err(|e| {
        eprintln!("error: cannot read `{file}`: {e}");
        1u8
    })?;
    let root = main_path.parent().unwrap_or(Path::new(".")).to_path_buf();

    // A default JIT run checks lazily: type inference runs on a dedicated
    // checker thread while this thread compiles and executes the program,
    // demand-first (see [`run_lazy`]). `check`, `repl`, `--eager`, and the
    // interpreter-only builds (including wasm, which cannot spawn threads)
    // check eagerly on this thread. A cache hit skips checking but keeps the
    // entry-rooted JIT, so a warm run does not compile unrelated roots.
    let lazy = cfg!(jit_backend) && matches!(mode, Mode::Run { eager: false });
    let checked = if lazy {
        match load_cached(file, &root) {
            Some(checked) => checked,
            None => return run_lazy(file.to_string(), main_src, root),
        }
    } else {
        match analyze(file, &main_src, &root) {
            Ok(c) => c,
            Err(diagnostics) => return Err(print_diags(diagnostics)),
        }
    };

    match mode {
        // Silence on success, as a checker in a pipeline should be: the exit code
        // carries the answer, and anything on stdout is noise an editor or a script
        // has to filter out.
        Mode::Check => Ok(()),
        Mode::Run { .. } => execute(
            &checked.program,
            &checked.expr_types,
            &checked.view_args,
            &checked.sum_views,
            &checked.call_locations,
            &checked.lift_errs,
            &checked.fields_loops,
            &checked.type_names,
            &checked.typeof_types,
            &checked.null_props,
            lazy,
        )
        .map_err(|e| {
            report_runtime_error(&e);
            1
        }),
        Mode::Repl => execute_repl(
            &checked.program,
            &checked.expr_types,
            &checked.view_args,
            &checked.sum_views,
            &checked.call_locations,
            &checked.lift_errs,
            &checked.fields_loops,
            &checked.type_names,
            &checked.typeof_types,
            &checked.null_props,
        )
        .map_err(|e| {
            report_runtime_error(&e);
            1
        }),
    }
}

/// The front-end flavor stamped into cache tags: a JIT driver rewrites spawn
/// bodies (auto-acquire) before caching ASTs; a REPL-only build does not, so
/// the two must never accept each other's caches.
#[cfg(jit_backend)]
const CACHE_FLAVOR: &str = "jit";
/// The PARTIAL cache's flavor (a stopped lazy run's settled state): its own
/// tag, so the full-cache loader can never mistake it for a complete
/// analysis and vice versa.
#[cfg(jit_backend)]
const PARTIAL_CACHE_FLAVOR: &str = "jit-partial";
#[cfg(not(jit_backend))]
const CACHE_FLAVOR: &str = "repl";

/// Re-anchor each cached module's `_PATH` constant to where the module lives
/// NOW. The cache's stamps are deliberately location-independent (a moved
/// project still hits), but `_PATH` is precisely the module's location, so a
/// hit must refresh it rather than replay the analysis machine's paths.
fn reanchor_module_paths(
    modules: &mut [LoadedModule],
    entry: &Path,
    root: &Path,
    search: &brass_resolve::SearchPaths,
) {
    for m in modules {
        // Embedded modules (prelude, nested std) have no location to refresh,
        // and a plugin wrapper's `_PATH` is its label -- its library is pinned
        // by an Absolute stamp, so a hit means it did not move.
        if m.is_prelude || m.path.first().is_some_and(|s| s == "core") {
            continue;
        }
        if matches!(m.path.as_slice(), [p] if p == "main") {
            let loc = std::fs::canonicalize(entry)
                .unwrap_or_else(|_| entry.to_path_buf())
                .display()
                .to_string();
            brass_resolve::reinject_module_path(&mut m.ast, &loc);
            continue;
        }
        if let Some(brass_resolve::ModuleFile::Source(file)) =
            brass_resolve::resolve_module_file(root, search, &m.path)
        {
            let loc = std::fs::canonicalize(&file)
                .unwrap_or(file)
                .display()
                .to_string();
            brass_resolve::reinject_module_path(&mut m.ast, &loc);
        }
    }
}

/// The context seed for `ctx` (every module except the entry): from the
/// shared on-disk store under `key` when caching is enabled, else built by a
/// context-only run and stored back. `None` when the context itself has
/// diagnostics -- the unseeded full run then reports them as before.
fn cached_context_seed(
    key: &Option<[u8; 20]>,
    ctx: &[LoadedModule],
    module_hashes: Option<&[(String, [u8; 20])]>,
    phase_name: &'static str,
) -> Option<brass_typeck::ContextTables> {
    if let Some(key) = key
        && brass_cache::enabled()
        && let Some(seed) = brass_cache::load_context(key)
    {
        tracing::debug!(target: "brass::perf", "context seed loaded from disk");
        return Some(seed);
    }
    let t = std::time::Instant::now();
    let (ctx_program, ctx_errors) = lower(ctx);
    let seed = if ctx_errors.is_empty() {
        // An exact-key miss usually means an EDIT somewhere in the context.
        // The incremental sidecar of the previous build of this same context
        // (same module-path list) tells which modules changed: everything
        // else's tables are retained as a partial seed and only the changed
        // modules -- plus their transitive importers, which may observe the
        // change -- re-infer.
        let incremental = module_hashes.and_then(|hashes| {
            if !brass_cache::enabled() {
                return None;
            }
            let id = context_identity(CACHE_FLAVOR, hashes);
            let prior = brass_cache::load_context_bundle(&id)?;
            let keep = clean_context_modules(ctx, hashes, &prior.module_hashes);
            if keep.is_empty() {
                return None;
            }
            tracing::debug!(
                target: "brass::perf",
                kept = keep.len(),
                total = ctx.len(),
                "incremental context rebuild"
            );
            let mut partial = prior.seed;
            if !partial.retain_modules(&ctx_program, &keep) {
                tracing::debug!(
                    target: "brass::perf",
                    "incremental context rebuild rejected changed HIR identity"
                );
                return None;
            }
            brass_typeck::context_seed_with(&ctx_program, Some(&partial))
        });
        match incremental {
            Some(seed) => Some(seed),
            None => brass_typeck::context_seed(&ctx_program),
        }
    } else {
        None
    };
    brass_utils::perf_phase(phase_name, t.elapsed());
    if let (Some(key), Some(seed), true) = (key, &seed, brass_cache::enabled()) {
        brass_cache::save_context(key, seed);
        if let Some(hashes) = module_hashes {
            brass_cache::save_context_bundle(
                &context_identity(CACHE_FLAVOR, hashes),
                &brass_cache::ContextBundle {
                    module_hashes: hashes.to_vec(),
                    seed: seed.clone(),
                },
            );
        }
    }
    seed
}

/// The context's IDENTITY: the frontend flavor and its module-path list,
/// contents excluded, so an edited context still finds its own previous
/// build's sidecar without crossing into a frontend with different rewrites.
fn context_identity(flavor: &str, module_hashes: &[(String, [u8; 20])]) -> [u8; 20] {
    let mut paths: Vec<&str> = module_hashes.iter().map(|(p, _)| p.as_str()).collect();
    paths.sort_unstable();
    let mut buf = flavor.as_bytes().to_vec();
    buf.push(0);
    for p in paths {
        buf.extend_from_slice(p.as_bytes());
        buf.push(0);
    }
    brass_cache::content_hash(&buf)
}

/// The source-map base encoded by the `_PATH` declaration injected at the
/// start of every loaded module.
fn module_source_base(module: &LoadedModule) -> Option<usize> {
    match module.ast.items.first()? {
        TopLevel::Stmt(Stmt::Let {
            pat: brass_parser::ast::Pattern::Binding(name, span),
            is_const: true,
            ..
        }) if name == brass_resolve::MODULE_PATH_CONST => Some(span.lo),
        _ => None,
    }
}

/// Hash each module's own source by its injected source base. Source entries
/// are discovered before recursive imports while modules are appended after
/// them, so their vector positions are deliberately unrelated.
fn context_module_hashes(
    modules: &[LoadedModule],
    sources: &brass_resolve::SourceMap,
) -> Option<Vec<(String, [u8; 20])>> {
    modules
        .iter()
        .map(|module| {
            let base = module_source_base(module)?;
            let source = sources.locate(base)?.src;
            Some((
                module.path.join("."),
                brass_cache::content_hash(source.as_bytes()),
            ))
        })
        .collect()
}

/// Find the loaded module that owns `offset`, independent of module graph
/// order. Generated rewrites retain the injected source base.
fn module_path_at(
    modules: &[LoadedModule],
    sources: &brass_resolve::SourceMap,
    offset: usize,
) -> Option<Vec<String>> {
    let located = sources.locate(offset)?;
    let base = offset.checked_sub(located.local)?;
    modules
        .iter()
        .find(|module| module_source_base(module) == Some(base))
        .map(|module| module.path.clone())
}

/// The context modules whose retained tables are still valid: source hash
/// unchanged since `prior`, and no (transitive) import of a changed module.
/// The import edges are matched conservatively by PATH TEXT -- an import's
/// written path may be package-relative, so a dirty module counts as a
/// target whenever its dotted path could resolve the import -- and a dirty
/// implicit-prelude module dirties everything (it is visible with no
/// import). Over-matching only re-infers more than strictly needed.
fn clean_context_modules(
    ctx: &[LoadedModule],
    now: &[(String, [u8; 20])],
    prior: &[(String, [u8; 20])],
) -> HashSet<Vec<String>> {
    let prior_map: HashMap<&str, &[u8; 20]> = prior.iter().map(|(p, h)| (p.as_str(), h)).collect();
    let mut dirty: HashSet<String> = now
        .iter()
        .filter(|(p, h)| prior_map.get(p.as_str()) != Some(&h))
        .map(|(p, _)| p.clone())
        .collect();
    if dirty.is_empty() {
        // Identical context under a missed exact key (e.g. the entry list
        // changed): everything is reusable.
        return ctx.iter().map(|m| m.path.clone()).collect();
    }
    if ctx
        .iter()
        .any(|m| m.is_prelude && dirty.contains(&m.path.join(".")))
    {
        return HashSet::new();
    }
    // A written import path may name a dirty module in several shapes:
    // absolute (`std.package_manager.manifest`), package-relative
    // (`manifest` from a sibling), or with a trailing item name
    // (`manifest.Manifest`). Match on segment-boundary suffixes both ways.
    let may_target = |written: &str, dirty_path: &str| {
        let strip = |whole: &str, suffix: &str| {
            whole == suffix
                || (whole.len() > suffix.len()
                    && whole.ends_with(suffix)
                    && whole.as_bytes()[whole.len() - suffix.len() - 1] == b'.')
        };
        strip(dirty_path, written)
            || strip(written, dirty_path)
            || match written.rsplit_once('.') {
                Some((module_part, _item)) => strip(dirty_path, module_part),
                None => false,
            }
    };
    loop {
        let mut changed = false;
        for m in ctx {
            let mp = m.path.join(".");
            if dirty.contains(&mp) {
                continue;
            }
            let imports_dirty = m.ast.imports.iter().any(|imp| {
                let written = imp.path.join(".");
                dirty.iter().any(|d| may_target(&written, d))
            });
            if imports_dirty {
                dirty.insert(mp);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    ctx.iter()
        .filter(|m| !dirty.contains(&m.path.join(".")))
        .map(|m| m.path.clone())
        .collect()
}

/// A finished front-end analysis in thread-transportable form: the final
/// module graph (post-resolution, post-rewrite, post-keyed-specialization)
/// plus the checker's span-keyed channels. HIR holds `Rc`, so a checked
/// `Program` cannot cross the checker-thread boundary; the receiver rebuilds
/// it from the modules with [`assemble_checked`]. A cache hit reproduces the
/// same shape from disk (`brass_cache::Payload` stores exactly these parts).
struct AnalyzedProgram {
    modules: Vec<LoadedModule>,
    channels: brass_cache::Channels,
}

/// Re-lower an analysis result into an executable [`Checked`] program.
/// Lowering is deterministic, so the rebuilt HIR carries the same spans and
/// type ids the channels are keyed by. A clean analysis re-lowers cleanly; an
/// error here means a stale cache or a driver bug, and the caller decides
/// whether to fall back or report.
fn assemble_checked(analyzed: AnalyzedProgram) -> Result<Checked, Vec<String>> {
    let (program, lower_errors) = lower(&analyzed.modules);
    if !lower_errors.is_empty() {
        return Err(lower_errors
            .into_iter()
            .map(|e| format!("error: {}", e.message))
            .collect());
    }
    let c = analyzed.channels;
    Ok(Checked {
        program,
        expr_types: c.expr_types.into_iter().collect(),
        view_args: c.view_args.into_iter().collect(),
        sum_views: c.sum_views.into_iter().collect(),
        call_locations: c.call_locations.into_iter().collect(),
        lift_errs: c.lift_errs.into_iter().collect(),
        fields_loops: c.fields_loops.into_iter().collect(),
        type_names: c.type_names.into_iter().collect(),
        typeof_types: c.typeof_types.into_iter().collect(),
        null_props: c.null_props.into_iter().collect(),
    })
}

/// The analysis-cache probe: on a valid `.czcache` (same compiler, same
/// resolution environment, every recorded source unchanged) the final module
/// ASTs are re-lowered -- deterministic and cheap -- and the cached checker
/// channels are used as-is, skipping type checking entirely. Only an
/// error-free analysis is ever cached, so a hit implies a clean program; a
/// re-lowering that nonetheless reports an error treats the cache as stale
/// (`None`, and the caller runs the full pipeline).
fn load_cached(main_label: &str, root: &Path) -> Option<Checked> {
    let entry_path = PathBuf::from(main_label);
    let search = brass_resolve::SearchPaths::from_env();
    if !brass_cache::enabled() {
        return None;
    }
    let mut payload = brass_cache::load(&entry_path, CACHE_FLAVOR, &search)?;
    let t = std::time::Instant::now();
    reanchor_module_paths(&mut payload.modules, &entry_path, root, &search);
    match assemble_checked(AnalyzedProgram {
        modules: payload.modules,
        channels: payload.channels,
    }) {
        Ok(checked) => {
            // The full pipeline's clean-program warnings replay so warm runs
            // are not silently quieter than cold ones.
            for w in &payload.warnings {
                eprintln!("{w}");
            }
            brass_utils::perf_phase("front/cache-hit", t.elapsed());
            Some(checked)
        }
        Err(_) => {
            tracing::debug!(target: "brass::perf", "cache: re-lowering failed, falling back");
            None
        }
    }
}

/// Parse, resolve the module graph, lower, and statically check `main_src` (a
/// program whose label is `main_label`, imports resolved relative to `root`):
/// the cached fast path when it is valid, the full pipeline otherwise, on the
/// calling thread. Returns the checked program or the rendered diagnostics.
/// Shared by eager file execution and the interactive REPL, so both report
/// identical errors.
fn analyze(main_label: &str, main_src: &str, root: &Path) -> Result<Checked, Vec<String>> {
    if let Some(checked) = load_cached(main_label, root) {
        return Ok(checked);
    }
    assemble_checked(analyze_fresh(main_label, main_src, root, None)?)
}

/// The checker-thread half of the streaming wiring: progress events flow out
/// over an unbounded channel (the checker never blocks on a slow consumer),
/// priority requests flow in and are drained non-blockingly between bodies.
#[cfg(jit_backend)]
struct ThreadScheduler {
    events: tokio::sync::mpsc::UnboundedSender<brass_typeck::stream::CheckEvent>,
    requests: tokio::sync::mpsc::UnboundedReceiver<brass_typeck::stream::BodyRequest>,
    /// Set by the driver when the program ends: the checker stops at the
    /// next body boundary instead of finishing code nothing will run.
    stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
    /// Whether the stop actually interrupted the queue (an `Interrupted`
    /// event passed through): a completed analysis stays cacheable as full
    /// even when the stop arrived moments later.
    interrupted: std::cell::Cell<bool>,
    /// Set while the driver is settling its entry (gate + start-up demands):
    /// the checker serves only requested bodies, so no demand ever waits for
    /// a definitional pass the queue happened to start first. Cleared when
    /// execution begins.
    paused: std::sync::Arc<std::sync::atomic::AtomicBool>,
}

#[cfg(jit_backend)]
impl brass_typeck::stream::Scheduler for ThreadScheduler {
    fn drain_requests(&mut self) -> Vec<brass_typeck::stream::BodyRequest> {
        let mut out = Vec::new();
        while let Ok(request) = self.requests.try_recv() {
            out.push(request);
        }
        out
    }

    fn emit(&mut self, event: brass_typeck::stream::CheckEvent) {
        if matches!(event, brass_typeck::stream::CheckEvent::Interrupted(_)) {
            self.interrupted.set(true);
        }
        // A dropped receiver means the consumer stopped listening (it
        // aborted); checking still finishes for the thread's final result.
        let _ = self.events.send(event);
    }

    fn stopped(&self) -> bool {
        self.stop.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn interrupted(&self) -> bool {
        self.interrupted.get()
    }

    fn paused(&self) -> bool {
        self.paused.load(std::sync::atomic::Ordering::Relaxed)
    }
}

/// The main-thread accumulation of the checker thread's event stream: the
/// same span-keyed maps [`Checked`] carries, built by replaying channel
/// deltas as they arrive (removals first -- a delta never removes and
/// re-adds one span). A `Restarted` event (the keyed-specialization re-pass
/// rewrote the program, moving spans) drops everything accumulated.
#[cfg(jit_backend)]
#[derive(Default)]
struct MergedChannels {
    expr_types: HashMap<Span, brass_hir::Type>,
    view_args: HashSet<Span>,
    sum_views: HashMap<Span, brass_hir::Type>,
    lift_errs: HashSet<Span>,
    fields_loops: HashMap<Span, Vec<String>>,
    type_names: HashMap<Span, String>,
    typeof_types: HashMap<Span, brass_hir::Type>,
    null_props: HashSet<Span>,
}

#[cfg(jit_backend)]
impl MergedChannels {
    fn apply(&mut self, event: brass_typeck::stream::CheckEvent) {
        use brass_typeck::stream::CheckEvent;
        match event {
            // Error verdicts ride the thread's final result in this pipeline;
            // the event copy gates execution once the JIT consumes the stream
            // mid-run.
            CheckEvent::StaticChecked(_) => {}
            CheckEvent::ContextReady(d)
            | CheckEvent::BodyChecked(_, d)
            | CheckEvent::Finished(d, _) => self.apply_delta(d),
            CheckEvent::Restarted => *self = Self::default(),
            // The stop-snapshot is bookkeeping for the partial cache, not
            // channel data (everything in it was already applied as deltas).
            CheckEvent::Interrupted(_) => {}
        }
    }

    /// The prior run's delivered state, verbatim: what its deltas had
    /// built up by the time it stopped.
    fn from_snapshot(snap: &brass_typeck::stream::StreamSnapshot) -> Self {
        MergedChannels {
            expr_types: snap
                .expr_flushed
                .iter()
                .map(|(s, t)| (*s, t.clone()))
                .collect(),
            view_args: snap.view_args.iter().copied().collect(),
            sum_views: snap
                .sum_views
                .iter()
                .map(|(s, t)| (*s, t.clone()))
                .collect(),
            lift_errs: snap.lift_errs.iter().copied().collect(),
            fields_loops: snap
                .fields_loops
                .iter()
                .map(|(s, f)| (*s, f.clone()))
                .collect(),
            type_names: snap
                .type_names
                .iter()
                .map(|(s, t)| (*s, t.clone()))
                .collect(),
            typeof_types: snap
                .typeof_types
                .iter()
                .map(|(s, t)| (*s, t.clone()))
                .collect(),
            null_props: snap.null_props.iter().copied().collect(),
        }
    }

    fn apply_delta(&mut self, d: brass_typeck::stream::ChannelDelta) {
        for s in &d.expr_types_removed {
            self.expr_types.remove(s);
        }
        for s in &d.typeof_types_removed {
            self.typeof_types.remove(s);
        }
        self.expr_types.extend(d.expr_types);
        self.view_args.extend(d.view_args);
        self.sum_views.extend(d.sum_views);
        self.lift_errs.extend(d.lift_errs);
        self.fields_loops.extend(d.fields_loops);
        self.type_names.extend(d.type_names);
        self.typeof_types.extend(d.typeof_types);
        self.null_props.extend(d.null_props);
    }
}

/// Render diagnostics to stderr and yield the front end's failure exit code.
fn print_diags(diags: Vec<String>) -> u8 {
    for d in diags {
        eprintln!("{d}");
    }
    1
}

/// Every function and method body's span range, for attributing a
/// diagnostic to the body containing it. Lazy checking HOLDS an error whose
/// span lies inside a body execution never needs; an error inside a needed
/// body -- or outside any body at all (top-level code, declarations,
/// signatures) -- is fatal at the next gate. Methods use keys no demand ever
/// names, so their errors surface through the mono-failure path instead.
#[cfg(jit_backend)]
struct BodySpans {
    ranges: Vec<(String, usize, usize)>,
}

#[cfg(jit_backend)]
impl BodySpans {
    fn new(program: &Program) -> Self {
        // The WHOLE declaration's range, not just the body block: a
        // signature-level diagnostic (a return-path error points at the
        // return annotation) about a function nothing runs is as ignorable
        // as one inside its body.
        let mut ranges = Vec::new();
        for (symbol, f) in &program.functions {
            let span = f.decl.span;
            ranges.push((symbol.clone(), span.lo, span.hi));
        }
        for info in program.types.values() {
            let mut methods: Vec<&brass_hir::MethodInfo> = Vec::new();
            match &info.kind {
                brass_hir::TypeKind::Record { methods: ms, .. } => methods.extend(ms.values()),
                brass_hir::TypeKind::Sum { variants } => {
                    for v in variants {
                        methods.extend(v.methods.values());
                    }
                }
            }
            for m in methods {
                if m.decl.body.is_some() {
                    let span = m.decl.span;
                    ranges.push((format!("{}.{}", info.name, m.decl.name), span.lo, span.hi));
                }
            }
        }
        BodySpans { ranges }
    }

    /// The body whose range contains `span`, if any.
    fn owner(&self, span: Span) -> Option<&str> {
        tracing::trace!(target: "brass::lazy", lo = span.lo, ranges = ?self.ranges, "owner probe");
        self.ranges
            .iter()
            .find(|(_, lo, hi)| *lo <= span.lo && span.lo < *hi)
            .map(|(symbol, _, _)| symbol.as_str())
    }
}

/// What a gate should do about the held diagnostics.
#[cfg(jit_backend)]
enum FatalVerdict {
    /// Nothing on the needed path: proceed.
    Clean,
    /// Fatal diagnostics were printed: abort with this code.
    Fatal(u8),
    /// The confirmation wait saw a keyed-specialization restart: the
    /// diagnostics were the first pass's provisional artifacts, not a
    /// verdict -- fall back to the whole-analysis path.
    Restarted,
}

/// Judge the held diagnostics at a gate. A fatal candidate is CONFIRMED
/// before it aborts anything: a keyed (`-> infer!`) program's first pass
/// records provisional errors that its specialization re-pass may clear, so
/// the gate waits for the checker's verdict (its terminal event, a restart,
/// or hang-up) once -- and only once something looked fatal; clean programs
/// never wait here. Confirmed diagnostics print sorted and deduplicated,
/// rendered like the eager pipeline.
#[cfg(jit_backend)]
fn judge_fatal(
    lazy: &mut LazyState,
    bodies: &BodySpans,
    sources: &brass_resolve::SourceMap,
) -> FatalVerdict {
    if lazy.fatal(bodies).is_empty() {
        return FatalVerdict::Clean;
    }
    // Wait for the checker's hang-up (or a restart), NOT its terminal
    // event: a keyed program's first pass emits `Finished` before the
    // specialization re-pass announces itself with `Restarted`. The wait is
    // on the checker's own progress, so its queue must be running.
    lazy.resume_background();
    while !lazy.closed && !lazy.restarted {
        lazy.pump_blocking();
    }
    if lazy.restarted {
        return FatalVerdict::Restarted;
    }
    let fatal = lazy.fatal(bodies);
    if fatal.is_empty() {
        return FatalVerdict::Clean;
    }
    for line in render_errors(&fatal, sources) {
        eprintln!("{line}");
    }
    FatalVerdict::Fatal(1)
}

/// The execution side of the lazy pipeline: replays the checker thread's
/// events into the merged channel state, tracks which bodies are settled,
/// and sends the priority requests -- the demanded function's path plus the
/// concrete argument types of the call that needs it -- that pull bodies to
/// the front of the checking order.
#[cfg(jit_backend)]
struct LazyState {
    events: tokio::sync::mpsc::UnboundedReceiver<brass_typeck::stream::CheckEvent>,
    requests: tokio::sync::mpsc::UnboundedSender<brass_typeck::stream::BodyRequest>,
    merged: MergedChannels,
    checked_fns: HashSet<String>,
    inits_checked: usize,
    /// Every diagnostic reported so far, HELD: lazy checking ignores an
    /// error unless execution needs the body it lives in (see
    /// [`LazyState::fatal`] and [`BodySpans`]).
    held: Vec<brass_typeck::TypeError>,
    /// The bodies execution needs: `main`, plus every demanded function.
    /// (Top-level code needs no entry here -- its spans lie outside every
    /// body, which is always fatal.) Grows at each demand; held errors are
    /// re-judged against it at every gate.
    needed: HashSet<String>,
    /// Tell the checker to stop at the next body boundary (the program
    /// ended; what it never executed no longer needs checking).
    stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
    /// While set, the checker serves only demanded bodies and holds its
    /// background queue (see `Scheduler::paused`). Cleared when execution
    /// begins -- and before any wait that needs the checker to make progress
    /// of its own (a fatal confirmation, a transient-failure retry), which
    /// would otherwise wait forever on a held queue.
    paused: std::sync::Arc<std::sync::atomic::AtomicBool>,
    /// The keyed-specialization re-pass restarted the analysis: spans moved,
    /// so everything merged is unusable and the run falls back likewise.
    restarted: bool,
    /// The event channel closed (the checker finished and hung up).
    closed: bool,
    /// The stop-snapshot a stopped checker handed back, for the partial
    /// cache (everything it settled; resumes the next run).
    snapshot: Option<brass_typeck::stream::StreamSnapshot>,
    /// A delta carried channel content since the last MIR (re)build. Bodies
    /// lowered before it may be missing entries the checker settled later
    /// (a cross-body pinning: an init's array literal fixed by a function's
    /// `push`), so the lowering is rebuilt before its output is trusted.
    dirty: bool,
}

#[cfg(jit_backend)]
impl LazyState {
    /// Release the checker's background queue (idempotent). Called when
    /// execution begins, and before any wait on the checker's own progress.
    fn resume_background(&self) {
        self.paused
            .store(false, std::sync::atomic::Ordering::Relaxed);
    }

    fn take(&mut self, event: brass_typeck::stream::CheckEvent) {
        use brass_typeck::stream::{BodyId, CheckEvent};
        match &event {
            CheckEvent::StaticChecked(errors) => self.held.extend(errors.iter().cloned()),
            CheckEvent::ContextReady(d) => self.absorb_delta(d),
            CheckEvent::BodyChecked(id, d) => {
                self.absorb_delta(d);
                match id {
                    BodyId::Init(_) => self.inits_checked += 1,
                    BodyId::Function(symbol) => {
                        self.checked_fns.insert(symbol.clone());
                    }
                }
            }
            CheckEvent::Finished(d, errors) => {
                self.absorb_delta(d);
                self.held.extend(errors.iter().cloned());
            }
            CheckEvent::Restarted => self.restarted = true,
            CheckEvent::Interrupted(snapshot) => self.snapshot = Some(snapshot.clone()),
        }
        self.merged.apply(event);
    }

    /// Track a delta: errors are held for span-attributed judgement, channel
    /// content marks the current lowering stale.
    fn absorb_delta(&mut self, d: &brass_typeck::stream::ChannelDelta) {
        self.held.extend(d.errors.iter().cloned());
        self.dirty |= !d.expr_types.is_empty()
            || !d.expr_types_removed.is_empty()
            || !d.view_args.is_empty()
            || !d.lift_errs.is_empty()
            || !d.null_props.is_empty()
            || !d.fields_loops.is_empty()
            || !d.sum_views.is_empty()
            || !d.type_names.is_empty()
            || !d.typeof_types.is_empty()
            || !d.typeof_types_removed.is_empty();
    }

    fn pump_blocking(&mut self) {
        match self.events.blocking_recv() {
            Some(event) => self.take(event),
            None => self.closed = true,
        }
    }

    /// Absorb everything already queued without blocking.
    fn pump_pending(&mut self) {
        while let Ok(event) = self.events.try_recv() {
            self.take(event);
        }
    }

    /// The held diagnostics execution cannot ignore: those inside a NEEDED
    /// body and those inside no known body at all (top-level statements,
    /// declarations, spanless internal reports). Sorted and deduplicated
    /// like the eager report.
    fn fatal(&self, bodies: &BodySpans) -> Vec<(String, Span)> {
        let mut out: Vec<(String, Span)> = self
            .held
            .iter()
            .filter(|e| match bodies.owner(e.span) {
                Some(owner) => self.needed.contains(owner),
                None => true,
            })
            .map(|e| (e.message.clone(), e.span))
            .collect();
        out.sort_by(|a, b| (a.1.lo, &a.0).cmp(&(b.1.lo, &b.0)));
        out.dedup();
        out
    }

    /// Every held diagnostic, needed or not: the report for a failure the
    /// span attribution cannot explain (a mono rejection against the
    /// checker's final state).
    fn held_all(&self) -> Vec<(String, Span)> {
        let mut out: Vec<(String, Span)> = self
            .held
            .iter()
            .map(|e| (e.message.clone(), e.span))
            .collect();
        out.sort_by(|a, b| (a.1.lo, &a.0).cmp(&(b.1.lo, &b.0)));
        out.dedup();
        out
    }

    /// Block until the entry is settled: every module initializer and (when
    /// the program has one) `main`. False means the checker hung up (or
    /// restarted) before settling them; held diagnostics are the caller's
    /// judgement to make.
    fn wait_gate(&mut self, inits: usize, has_main: bool) -> bool {
        let settled =
            |s: &Self| s.inits_checked >= inits && (!has_main || s.checked_fns.contains("main"));
        while !self.restarted && !self.closed && !settled(self) {
            self.pump_blocking();
        }
        !self.restarted && settled(self)
    }

    /// Ask the checker to settle `symbol` next -- the demanded function's
    /// path and the concrete argument types of the call that needs it --
    /// and block until it is. The body joins the NEEDED set: its held
    /// diagnostics become fatal, so callers judge [`LazyState::fatal`]
    /// after every demand. False means the checker hung up or restarted.
    fn demand(&mut self, symbol: &str, type_args: Vec<brass_hir::Type>) -> bool {
        self.needed.insert(symbol.to_string());
        if !self.checked_fns.contains(symbol) {
            let _ = self.requests.send(brass_typeck::stream::BodyRequest {
                symbol: symbol.to_string(),
                type_args,
            });
            while !self.restarted && !self.closed && !self.checked_fns.contains(symbol) {
                self.pump_blocking();
            }
        }
        !self.restarted && self.checked_fns.contains(symbol)
    }

    /// The merged channel state as the lowering bundle. Call locations are
    /// computed by the executor from its own module ASTs, not streamed.
    fn channels<'a>(
        &'a self,
        call_locations: &'a HashMap<Span, (String, u32, u32)>,
    ) -> brass_mir::CheckerChannels<'a> {
        brass_mir::CheckerChannels {
            expr_types: &self.merged.expr_types,
            view_args: &self.merged.view_args,
            sum_views: &self.merged.sum_views,
            call_locations,
            lift_errs: &self.merged.lift_errs,
            fields_loops: &self.merged.fields_loops,
            type_names: &self.merged.type_names,
            typeof_types: &self.merged.typeof_types,
            null_props: &self.merged.null_props,
        }
    }
}

/// Fall back to the whole-analysis verdict: reclaim the checker thread and
/// re-run the pipeline EAGERLY, in process. The streaming analysis's payload
/// is never executed or reported from -- its lazy profile types some calls
/// from signatures without recording their instances' channel entries or
/// per-instance diagnostics, so only a genuinely eager analysis is a whole
/// verdict. The re-run is cache-assisted: a keyed re-pass that completed
/// eagerly on the checker thread has already persisted the full analysis,
/// which this load then hits.
#[cfg(jit_backend)]
#[allow(clippy::too_many_arguments)]
fn finish_eagerly(
    rt: &tokio::runtime::Runtime,
    checker: tokio::task::JoinHandle<Result<AnalyzedProgram, Vec<String>>>,
    stop: &std::sync::Arc<std::sync::atomic::AtomicBool>,
    paused: &std::sync::Arc<std::sync::atomic::AtomicBool>,
    mut events: tokio::sync::mpsc::UnboundedReceiver<brass_typeck::stream::CheckEvent>,
    label: &str,
    src: &str,
    root: &Path,
) -> Result<(), u8> {
    // Reclaim the thread: stop it at the next boundary (releasing the held
    // background queue so it can reach one), drain its events, and join.
    stop.store(true, std::sync::atomic::Ordering::Relaxed);
    paused.store(false, std::sync::atomic::Ordering::Relaxed);
    while events.blocking_recv().is_some() {}
    let _ = rt
        .block_on(checker)
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic.into_panic()));
    run_fresh_eager(label, src, root)
}

/// Compile and prime EVERY recorded deferred target, to a fixpoint: called
/// when a batch containing `spawn` was compiled, before its code runs.
/// Spawned code executes on worker threads, which answer deferred calls only
/// from the cross-thread resolved cache; after this drain, every site any
/// worker could reach is in it. False aborts the run (a target's check or
/// compilation failed -- `resolve_deferred` reported it).
#[cfg(jit_backend)]
#[allow(clippy::too_many_arguments)] // the execution-side state is one bundle
fn drain_targets_for_spawn(
    backend: &mut brass_jit_llvm::LlvmCodegen,
    program: &Program,
    tables: &brass_mir::LowerTables,
    call_locations: &HashMap<Span, (String, u32, u32)>,
    sources: &brass_resolve::SourceMap,
    bodies: &BodySpans,
    globals: &[(String, brass_hir::Type)],
    resume: Option<&Path>,
    lowering: &mut brass_mir::SubsetLowering,
    lazy: &mut LazyState,
    targets: &mut HashMap<String, brass_engine::DeferredSig>,
) -> bool {
    loop {
        let pending: Vec<String> = targets
            .keys()
            .filter(|symbol| backend.address_of(symbol).is_none())
            .cloned()
            .collect();
        if pending.is_empty() {
            return true;
        }
        for symbol in pending {
            let addr = resolve_deferred(
                backend,
                &symbol,
                program,
                tables,
                call_locations,
                sources,
                bodies,
                globals,
                resume,
                lowering,
                lazy,
                targets,
            );
            if addr == 0 {
                return false;
            }
            brass_jit_llvm::prime_resolved(&symbol, addr);
        }
    }
}

/// The runtime half of deferral: called (through `pp_resolve`) the first
/// time execution reaches a deferred call site. Ensures the target's body is
/// checked -- sending the function's path and the site's concrete argument
/// types to the checker and waiting, when it is not -- lowers it, then
/// monomorphizes and compiles the instance (and everything it newly needs;
/// its own calls may defer further) into the LIVE engine. Returns the
/// callable address, or 0 after reporting -- the site then traps, keeping a
/// resolver failure defined.
///
/// Exit the process if the needed path holds a CONFIRMED fatal diagnostic
/// (see [`judge_fatal`]; reached from JIT code, which cannot unwind, hence
/// `exit`). A keyed-specialization restart discovered mid-run cannot fall
/// back -- the program is already executing on the first pass's spans -- so
/// it exits with a pointer to the eager path instead.
#[cfg(jit_backend)]
fn exit_if_fatal(lazy: &mut LazyState, bodies: &BodySpans, sources: &brass_resolve::SourceMap) {
    if lazy.fatal(bodies).is_empty() {
        return;
    }
    // Wait for the checker's hang-up (or a restart), NOT its terminal
    // event: a keyed program's first pass emits `Finished` before the
    // specialization re-pass announces itself with `Restarted`. The wait is
    // on the checker's own progress, so its queue must be running.
    lazy.resume_background();
    while !lazy.closed && !lazy.restarted {
        lazy.pump_blocking();
    }
    use std::io::Write;
    if lazy.restarted {
        let _ = io::stdout().flush();
        eprintln!(
            "error: reflective specialization restarted the analysis mid-run; rerun with --eager"
        );
        std::process::exit(1);
    }
    let fatal = lazy.fatal(bodies);
    if fatal.is_empty() {
        return;
    }
    let _ = io::stdout().flush();
    for line in render_errors(&fatal, sources) {
        eprintln!("{line}");
    }
    std::process::exit(1);
}

/// A fatal diagnostic discovered here means the program needed ill-typed
/// code: the needed-path report is printed and the process exits 1, exactly
/// as if the error had been found before execution -- output the program
/// already produced stands, as documented for lazy checking. Held
/// diagnostics elsewhere stay ignored.
#[cfg(jit_backend)]
#[allow(clippy::too_many_arguments)] // the execution-side state is one bundle
fn resolve_deferred(
    backend: &mut brass_jit_llvm::LlvmCodegen,
    symbol: &str,
    program: &Program,
    tables: &brass_mir::LowerTables,
    call_locations: &HashMap<Span, (String, u32, u32)>,
    sources: &brass_resolve::SourceMap,
    bodies: &BodySpans,
    globals: &[(String, brass_hir::Type)],
    resume: Option<&Path>,
    lowering: &mut brass_mir::SubsetLowering,
    lazy: &mut LazyState,
    targets: &mut HashMap<String, brass_engine::DeferredSig>,
) -> usize {
    tracing::debug!(target: "brass::perf", %symbol, "lazy: runtime resolve");
    // Already compiled -- by the startup set, or by an earlier resolution.
    if let Some(addr) = backend.address_of(symbol) {
        return addr;
    }
    let Some(sig) = targets.get(symbol).cloned() else {
        eprintln!("error: deferred call to unrecorded instance `{symbol}`");
        return 0;
    };
    // A diagnostic on the (just grown) needed path stops the run here,
    // before the ill-typed code could execute.
    let fatal_exit = |lazy: &mut LazyState, fallback: &str| -> usize {
        exit_if_fatal(lazy, bodies, sources);
        // A RESUMED run's failure here may only mean the prior run's
        // snapshot withheld an entry this body needs. Rerunning mid-run
        // would replay side effects, so: drop the stale partial cache
        // (the next run starts clean) and fail with the pointer.
        if let Some(entry) = resume {
            let _ = std::fs::remove_file(brass_cache::cache_path(entry));
            eprintln!(
                "error: the partial analysis cache was insufficient at run time; \
                 it was discarded -- rerun the program"
            );
            std::process::exit(1);
        }
        eprintln!("{fallback}");
        0
    };
    if !lowering.is_lowered(&sig.base) {
        tracing::debug!(target: "brass::perf", base = %sig.base, "lazy: runtime lower");
        if !lazy.demand(&sig.base, sig.type_args.clone()) {
            return fatal_exit(
                lazy,
                &format!("error: the check of `{}` did not complete", sig.base),
            );
        }
        // The demanded body joined the needed set: a held diagnostic in it
        // is now fatal, before its code could ever run.
        exit_if_fatal(lazy, bodies, sources);
        let channels = lazy.channels(call_locations);
        lowering.add_function(program, tables, &sig.base, &channels);
    }
    loop {
        match brass_engine::monomorphize_instance_deferred(
            &lowering.mir,
            program,
            &sig.base,
            sig.type_args.clone(),
            globals,
        ) {
            Ok(mono) => {
                targets.extend(mono.deferred.clone());
                let batch_spawns = brass_engine::batch_spawns(&mono);
                // Emit every new instance's module BEFORE resolving the one
                // address: the batch may be mutually recursive, and an
                // address lookup finalizes all added modules -- each
                // definition must be in place by then.
                for f in &mono.functions {
                    if backend.address_of(&f.symbol).is_some() {
                        continue;
                    }
                    tracing::debug!(target: "brass::perf", symbol = %f.symbol, "lazy: runtime compile");
                    if let Err(e) = backend.emit_instance_module(&mono, f) {
                        eprintln!("error: runtime compilation of `{}` failed: {e}", f.symbol);
                        return 0;
                    }
                }
                drop(mono);
                let addr = backend.address_of(symbol).unwrap_or(0);
                if addr != 0 {
                    brass_jit_llvm::prime_resolved(symbol, addr);
                }
                // The batch spawns: everything a worker thread could reach
                // must be compiled and primed before this call returns (the
                // spawn runs after it) -- workers cannot compile.
                if addr != 0
                    && batch_spawns
                    && !drain_targets_for_spawn(
                        backend,
                        program,
                        tables,
                        call_locations,
                        sources,
                        bodies,
                        globals,
                        resume,
                        lowering,
                        lazy,
                        targets,
                    )
                {
                    return 0;
                }
                return addr;
            }
            Err(brass_engine::MonoStop::MissingBodies(demands)) => {
                let mut progressed = false;
                for (miss, type_args) in demands {
                    if lowering.is_lowered(&miss) || !program.functions.contains_key(&miss) {
                        continue;
                    }
                    if !lazy.demand(&miss, type_args) {
                        return fatal_exit(
                            lazy,
                            &format!("error: the check of `{miss}` did not complete"),
                        );
                    }
                    exit_if_fatal(lazy, bodies, sources);
                    let channels = lazy.channels(call_locations);
                    lowering.add_function(program, tables, &miss, &channels);
                    progressed = true;
                }
                // A batch that supplied nothing new would come straight
                // back: a pipeline bug, not a user error -- fail readably.
                if !progressed {
                    eprintln!("error: lazy compilation cannot supply the demanded bodies");
                    return 0;
                }
            }
            Err(brass_engine::MonoStop::Fail(e)) => {
                // The same transient-vs-final rule as start-up: retry once
                // more of the check has landed; a failure against the final
                // state is real.
                if !lazy.closed {
                    lazy.pump_blocking();
                    lazy.pump_pending();
                    if !lazy.restarted {
                        continue;
                    }
                }
                return fatal_exit(
                    lazy,
                    &format!("error: runtime compilation of `{}` failed: {e}", sig.base),
                );
            }
        }
    }
}

/// The lazy-check run: type inference happens on the checker thread while
/// this thread prepares and executes the program, gating only on the bodies
/// execution actually needs.
///
/// 1. The checker thread runs the full streaming analysis; this thread
///    assembles its own identical module graph (lowering is deterministic,
///    so spans and type ids agree with the streamed channels).
/// 2. Once every module initializer and `main` are settled, entry-rooted
///    monomorphization starts. A reachable function whose body is not
///    settled yet stops it; the demand -- the function's path and the
///    concrete argument types of the call -- goes to the checker thread,
///    which checks that body next; its channel delta lands here, the body
///    is lowered, and monomorphization retries. Unreachable code never
///    gates execution.
/// 3. Any diagnostic that arrives before the program starts aborts the run
///    with the checker's full, eager-identical report. Once the program
///    ran, the still-running checker (working through what execution never
///    needed) is drained at exit, and anything it found is reported with a
///    non-zero exit: lazy checking defers WHEN errors surface, never
///    WHETHER.
/// 4. A keyed-specialization restart or an executor-side assembly failure
///    falls back to [`finish_eagerly`] -- behaviorally the eager pipeline.
///
/// The one diagnostic class that can land after its code ran is a
/// whole-program-terminal one (match exhaustiveness): a non-exhaustive match
/// reached before its diagnostic is still DEFINED behavior -- the lowered
/// match chain ends in an explicit no-arm panic, never LLVM `unreachable` --
/// so the program aborts cleanly and the exit is non-zero either way.
#[cfg(jit_backend)]
fn run_lazy(label: String, src: String, root: PathBuf) -> Result<(), u8> {
    // The checker recurses per call-site re-elaboration much like the
    // interpreter recurses per Brass call, so its thread gets the same
    // generous stack as the driver thread (virtual memory; pages commit only
    // as the stack grows).
    let rt = tokio::runtime::Builder::new_current_thread()
        .thread_name("brass-checker")
        .thread_stack_size(MAIN_STACK_BYTES)
        .build()
        .map_err(|e| {
            eprintln!("error: cannot start the checker runtime: {e}");
            1u8
        })?;
    // One front end for both sides: the checker thread gets a clone of the
    // assembled module graph, this thread keeps the original to execute --
    // lowering is deterministic, so spans and type ids agree with the
    // streamed channels. Syntax and module-graph problems abort here, before
    // any thread starts, exactly as eagerly.
    let search = brass_resolve::SearchPaths::from_env();
    let front = match front_load(&label, &src, &root, &search) {
        Ok(front) => front,
        Err(diags) => return Err(print_diags(diags)),
    };
    // Lower on this side first: the module graph decides the route. A keyed
    // (`-> infer!`) call anywhere in it restarts the analysis over a
    // specialization-rewritten program, which a lazy run only ever survives
    // by falling back to the eager verdict -- after paying for its own gate
    // first. Route such a program to the eager pipeline before any thread
    // starts (which also persists the full cache, so its repeat runs hit
    // the fastest path). Lowering errors report through the same eager path.
    let (program, lower_errors) = lower(&front.modules);
    if lower_errors.is_empty() && brass_typeck::has_keyed_calls(&program) {
        return run_fresh_eager(&label, &src, &root);
    }
    let (events_tx, events_rx) = tokio::sync::mpsc::unbounded_channel();
    let (requests_tx, requests_rx) = tokio::sync::mpsc::unbounded_channel();
    // A prior stopped run's PARTIAL cache: the checker resumes from it
    // (settled bodies skip their pass) and this side primes its merged
    // channel state from the same snapshot. Stamp-validated like the full
    // cache, so a changed source discards it wholesale.
    let entry_path = PathBuf::from(&label);
    let resume = if brass_cache::enabled() {
        brass_cache::load_partial(&entry_path, PARTIAL_CACHE_FLAVOR, &search)
    } else {
        None
    };
    let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    // The checker starts PAUSED: until execution begins, it serves only the
    // driver's demands, so no demand ever waits behind a definitional pass
    // the background queue happened to start first (an unannotated body's
    // open-frame pass can be arbitrarily slow; see `Scheduler::paused`).
    let paused = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(true));
    let checker = rt.spawn_blocking({
        let (label, front) = (label.clone(), front.clone());
        let stop = stop.clone();
        let paused = paused.clone();
        let resume = resume.clone();
        move || {
            let search = brass_resolve::SearchPaths::from_env();
            let mut sched = ThreadScheduler {
                events: events_tx,
                requests: requests_rx,
                stop,
                interrupted: std::cell::Cell::new(false),
                paused,
            };
            check_front(&label, front, &search, Some(&mut sched), resume)
        }
    });

    // Front-pass diagnostics (qualified uses, spawn ownership) are not
    // rendered here: the checker reports them with the rest, eager-identical.
    if !front.errors.is_empty() {
        return finish_eagerly(&rt, checker, &stop, &paused, events_rx, &label, &src, &root);
    }
    if !lower_errors.is_empty() {
        return finish_eagerly(&rt, checker, &stop, &paused, events_rx, &label, &src, &root);
    }
    let call_locations = call_site_locations(&front.modules, &front.sources);
    let bodies = BodySpans::new(&program);

    let mut lazy = LazyState {
        events: events_rx,
        requests: requests_tx,
        merged: MergedChannels::default(),
        checked_fns: HashSet::new(),
        inits_checked: 0,
        held: Vec::new(),
        needed: HashSet::from(["main".to_string()]),
        stop,
        paused,
        restarted: false,
        closed: false,
        snapshot: None,
        dirty: false,
    };
    if let Some(snap) = &resume {
        // The snapshot's channel state stands in for the deltas the prior
        // run received; the checker's resumed flushes emit only what is new.
        // Settled-body COUNTERS are not primed: the checker announces every
        // skipped body immediately, and counting those events keeps one
        // bookkeeping path.
        lazy.merged = MergedChannels::from_snapshot(snap);
    }
    let resumed = resume.is_some();
    let resume_entry: Option<&Path> = resumed.then_some(entry_path.as_path());
    let settled = lazy.wait_gate(program.inits.len(), program.functions.contains_key("main"));
    if lazy.restarted {
        return finish_eagerly(
            &rt,
            checker,
            &lazy.stop,
            &lazy.paused,
            lazy.events,
            &label,
            &src,
            &root,
        );
    }
    match judge_fatal(&mut lazy, &bodies, &front.sources) {
        FatalVerdict::Clean => {}
        FatalVerdict::Fatal(code) => return Err(code),
        FatalVerdict::Restarted => {
            return finish_eagerly(
                &rt,
                checker,
                &lazy.stop,
                &lazy.paused,
                lazy.events,
                &label,
                &src,
                &root,
            );
        }
    }
    if !settled {
        // The checker hung up cleanly without settling the entry: nothing
        // fatal was held, so fall back to the whole-analysis verdict. A
        // RESUMED checker skipped bodies, so its payload is incomplete --
        // rerun eagerly instead.
        if resumed {
            // Reclaimability: the paused checker thread must exit before `rt`
            // drops (it joins blocking tasks), and this path abandons it.
            lazy.stop.store(true, std::sync::atomic::Ordering::Relaxed);
            return run_fresh_eager(&label, &src, &root);
        }
        return finish_eagerly(
            &rt,
            checker,
            &lazy.stop,
            &lazy.paused,
            lazy.events,
            &label,
            &src,
            &root,
        );
    }

    // Demand-driven compilation: methods and inits lower up front, function
    // bodies as monomorphization discovers it needs them. A delta arriving
    // after a body was lowered can carry entries for that body's spans (a
    // cross-body pinning settles an earlier body's literal), so the whole
    // lowering is rebuilt whenever the channel state moved -- per-body
    // lowering is cheap next to checking and codegen.
    let mut demanded: Vec<String> = Vec::new();
    // The HIR-derived lowering tables are channel-independent: computed once,
    // shared across every rebuild.
    let tables = brass_mir::LowerTables::new(&program);
    let mut lowering = 'rebuild: loop {
        lazy.dirty = false;
        tracing::debug!(
            target: "brass::perf",
            demanded = demanded.len(),
            closed = lazy.closed,
            "lazy: lowering rebuild"
        );
        let mut built = {
            let channels = lazy.channels(&call_locations);
            let mut built = brass_mir::SubsetLowering::new(&program, &tables, &channels);
            for symbol in &demanded {
                built.add_function(&program, &tables, symbol, &channels);
            }
            built
        };
        // The demand loop: monomorphize, and supply each missing body as it
        // is reported, INCREMENTALLY -- new bodies are appended against the
        // channel state of their arrival, and only a mono pass over a fully
        // rebuilt (all-deltas-folded) lowering with no pending revisions is
        // trusted. Rebuilding once per missing body would re-lower every
        // method for each round.
        loop {
            match brass_engine::monomorphize_entry(&built.mir, &program, true) {
                Ok(mono) => {
                    // A `main` that fell outside the typed subset can be
                    // TRANSIENT under lazy checking -- most prominently a
                    // keyed (`-> infer!`) call whose specialization re-pass
                    // is about to restart the whole analysis. Only a skip
                    // against the checker's final state is the real
                    // rejection (which the re-run below then reports,
                    // exactly like the eager JIT).
                    let main_skipped =
                        program.functions.contains_key("main") && mono.lookup("main").is_none();
                    drop(mono);
                    if main_skipped {
                        if !lazy.closed {
                            // Waiting on the checker's own progress: run its
                            // queue, or no event would ever come.
                            lazy.resume_background();
                            lazy.pump_blocking();
                            lazy.pump_pending();
                            if lazy.restarted {
                                return finish_eagerly(
                                    &rt,
                                    checker,
                                    &lazy.stop,
                                    &lazy.paused,
                                    lazy.events,
                                    &label,
                                    &src,
                                    &root,
                                );
                            }
                            match judge_fatal(&mut lazy, &bodies, &front.sources) {
                                FatalVerdict::Clean => {}
                                FatalVerdict::Fatal(code) => return Err(code),
                                FatalVerdict::Restarted => {
                                    return finish_eagerly(
                                        &rt,
                                        checker,
                                        &lazy.stop,
                                        &lazy.paused,
                                        lazy.events,
                                        &label,
                                        &src,
                                        &root,
                                    );
                                }
                            }
                            continue 'rebuild;
                        }
                        if lazy.dirty {
                            continue 'rebuild;
                        }
                        match judge_fatal(&mut lazy, &bodies, &front.sources) {
                            FatalVerdict::Clean => {}
                            FatalVerdict::Fatal(code) => return Err(code),
                            FatalVerdict::Restarted => {
                                return finish_eagerly(
                                    &rt,
                                    checker,
                                    &lazy.stop,
                                    &lazy.paused,
                                    lazy.events,
                                    &label,
                                    &src,
                                    &root,
                                );
                            }
                        }
                        // A resumed snapshot may under-describe `main`
                        // itself (its pass was skipped): rerun eagerly
                        // rather than reject a fine program.
                        if resumed {
                            // Reclaimability: the paused checker thread must exit before `rt`
                            // drops (it joins blocking tasks), and this path abandons it.
                            lazy.stop.store(true, std::sync::atomic::Ordering::Relaxed);
                            return run_fresh_eager(&label, &src, &root);
                        }
                    } else if lazy.dirty {
                        // Success over a stale (incrementally extended)
                        // lowering: fold every delta in and prove it again.
                        continue 'rebuild;
                    }
                    break 'rebuild built;
                }
                Err(brass_engine::MonoStop::MissingBodies(demands)) => {
                    tracing::debug!(target: "brass::perf", count = demands.len(), "lazy: missing bodies");
                    let mut progressed = false;
                    for (symbol, type_args) in demands {
                        if demanded.contains(&symbol) || !program.functions.contains_key(&symbol) {
                            continue;
                        }
                        if !lazy.demand(&symbol, type_args) {
                            if lazy.restarted {
                                return finish_eagerly(
                                    &rt,
                                    checker,
                                    &lazy.stop,
                                    &lazy.paused,
                                    lazy.events,
                                    &label,
                                    &src,
                                    &root,
                                );
                            }
                            match judge_fatal(&mut lazy, &bodies, &front.sources) {
                                FatalVerdict::Clean => {}
                                FatalVerdict::Fatal(code) => return Err(code),
                                FatalVerdict::Restarted => {
                                    return finish_eagerly(
                                        &rt,
                                        checker,
                                        &lazy.stop,
                                        &lazy.paused,
                                        lazy.events,
                                        &label,
                                        &src,
                                        &root,
                                    );
                                }
                            }
                            eprintln!("error: lazy compilation cannot supply `{symbol}`");
                            return Err(1);
                        }
                        // The demanded body joined the needed set: its held
                        // diagnostics, if any, are now fatal -- before its
                        // code could ever run.
                        match judge_fatal(&mut lazy, &bodies, &front.sources) {
                            FatalVerdict::Clean => {}
                            FatalVerdict::Fatal(code) => return Err(code),
                            FatalVerdict::Restarted => {
                                return finish_eagerly(
                                    &rt,
                                    checker,
                                    &lazy.stop,
                                    &lazy.paused,
                                    lazy.events,
                                    &label,
                                    &src,
                                    &root,
                                );
                            }
                        }
                        let channels = lazy.channels(&call_locations);
                        built.add_function(&program, &tables, &symbol, &channels);
                        demanded.push(symbol);
                        progressed = true;
                    }
                    if !progressed {
                        // No demand in the batch could be satisfied: not
                        // functions of the program, or supplied already yet
                        // reported missing again. A pipeline bug, not a user
                        // error -- fail readably.
                        if resumed {
                            // Reclaimability: the paused checker thread must exit before `rt`
                            // drops (it joins blocking tasks), and this path abandons it.
                            lazy.stop.store(true, std::sync::atomic::Ordering::Relaxed);
                            return run_fresh_eager(&label, &src, &root);
                        }
                        eprintln!("error: lazy compilation cannot supply the demanded bodies");
                        return Err(1);
                    }
                }
                Err(brass_engine::MonoStop::Fail(e)) => {
                    // Monomorphization can fail TRANSIENTLY under lazy
                    // checking: an entry a later body pins (or a whole delta
                    // still in flight) may be exactly what the failed
                    // inference needed. Wait for more of the check and
                    // retry; only a failure against the checker's FINAL
                    // state -- where eager would have failed identically --
                    // is real. Diagnostics, when the checker found any,
                    // explain the program better than the mono error does;
                    // prefer them.
                    if !lazy.closed {
                        // Waiting on the checker's own progress: run its
                        // queue, or no event would ever come.
                        lazy.resume_background();
                        lazy.pump_blocking();
                        lazy.pump_pending();
                        if lazy.restarted {
                            return finish_eagerly(
                                &rt,
                                checker,
                                &lazy.stop,
                                &lazy.paused,
                                lazy.events,
                                &label,
                                &src,
                                &root,
                            );
                        }
                        match judge_fatal(&mut lazy, &bodies, &front.sources) {
                            FatalVerdict::Clean => {}
                            FatalVerdict::Fatal(code) => return Err(code),
                            FatalVerdict::Restarted => {
                                return finish_eagerly(
                                    &rt,
                                    checker,
                                    &lazy.stop,
                                    &lazy.paused,
                                    lazy.events,
                                    &label,
                                    &src,
                                    &root,
                                );
                            }
                        }
                        continue 'rebuild;
                    }
                    if lazy.dirty {
                        continue 'rebuild;
                    }
                    match judge_fatal(&mut lazy, &bodies, &front.sources) {
                        FatalVerdict::Clean => {}
                        FatalVerdict::Fatal(code) => return Err(code),
                        FatalVerdict::Restarted => {
                            return finish_eagerly(
                                &rt,
                                checker,
                                &lazy.stop,
                                &lazy.paused,
                                lazy.events,
                                &label,
                                &src,
                                &root,
                            );
                        }
                    }
                    // A resumed snapshot may simply lack an entry the prior
                    // run withheld: rerun eagerly rather than misreport.
                    if resumed {
                        // Reclaimability: the paused checker thread must exit before `rt`
                        // drops (it joins blocking tasks), and this path abandons it.
                        lazy.stop.store(true, std::sync::atomic::Ordering::Relaxed);
                        return run_fresh_eager(&label, &src, &root);
                    }
                    // A rejection against the checker's final state: held
                    // diagnostics elsewhere (a broken method the entry
                    // needs) usually explain it better than the mono error.
                    let held = lazy.held_all();
                    if !held.is_empty() {
                        for line in render_errors(&held, &front.sources) {
                            eprintln!("{line}");
                        }
                        return Err(1);
                    }
                    report_runtime_error(&format!("typed lowering failed: {e}"));
                    return Err(1);
                }
            }
        }
    };
    // Deterministic inputs: the re-run reproduces the loop's successful pass.
    let Ok(mono) = brass_engine::monomorphize_entry(&lowering.mir, &program, true) else {
        eprintln!("error: lazy compilation diverged between passes");
        return Err(1);
    };

    // Everything execution can reach is settled. A diagnostic on the needed
    // path that arrived meanwhile aborts before the program runs; held
    // diagnostics elsewhere stay held -- lazy checking ignores code the run
    // never executes.
    lazy.pump_pending();
    if lazy.restarted {
        drop(mono);
        return finish_eagerly(
            &rt,
            checker,
            &lazy.stop,
            &lazy.paused,
            lazy.events,
            &label,
            &src,
            &root,
        );
    }
    match judge_fatal(&mut lazy, &bodies, &front.sources) {
        FatalVerdict::Clean => {}
        FatalVerdict::Fatal(code) => return Err(code),
        FatalVerdict::Restarted => {
            return finish_eagerly(
                &rt,
                checker,
                &lazy.stop,
                &lazy.paused,
                lazy.events,
                &label,
                &src,
                &root,
            );
        }
    }
    install_jit_panic_guard();
    // The deferred runtime: reject an untypeable `main` exactly as `run_mono`
    // would, compile the startup set, then run with the resolver installed --
    // a deferred site's first call lands there.
    if program.functions.contains_key("main") && mono.lookup("main").is_none() {
        let reason = match &mono.main_skip {
            Some(reason) => {
                format!("program uses constructs outside the typed (Value-free) subset: {reason}")
            }
            None => "program uses constructs outside the typed (Value-free) subset".to_string(),
        };
        report_runtime_error(&reason);
        return Err(1);
    }
    use brass_engine::Codegen as _;
    let context = inkwell::context::Context::create();
    let mut backend = brass_jit_llvm::LlvmCodegen::new_backend(&context, &program);
    backend.begin_program(&mono);
    backend.codegen_program(&mono);
    let mut targets: HashMap<String, brass_engine::DeferredSig> = mono.deferred.clone();
    // The startup run typed every init, so its global table is complete;
    // runtime single-instance monos read module globals through it.
    let globals: Vec<(String, brass_hir::Type)> = mono.globals.clone();
    let startup_spawns = brass_engine::batch_spawns(&mono);
    // Free the lowering for the resolver's on-demand additions.
    drop(mono);
    let result = match backend.finalize() {
        Ok(()) => {
            // The startup set spawns: compile and prime every recorded
            // target BEFORE anything runs, so worker threads -- which can
            // only read the resolved-address cache -- never reach an
            // unresolved site.
            let drained = !startup_spawns
                || drain_targets_for_spawn(
                    &mut backend,
                    &program,
                    &tables,
                    &call_locations,
                    &front.sources,
                    &bodies,
                    &globals,
                    resume_entry,
                    &mut lowering,
                    &mut lazy,
                    &mut targets,
                );
            if drained {
                // Execution begins: from here the background queue fills the
                // wait on the running program (and grows the partial cache).
                lazy.resume_background();
                let mut resolve = |backend: &mut brass_jit_llvm::LlvmCodegen, symbol: &str| {
                    resolve_deferred(
                        backend,
                        symbol,
                        &program,
                        &tables,
                        &call_locations,
                        &front.sources,
                        &bodies,
                        &globals,
                        resume_entry,
                        &mut lowering,
                        &mut lazy,
                        &mut targets,
                    )
                };
                backend.execute_deferred(&mut resolve)
            } else {
                Err("lazy compilation could not pre-compile the spawned code".to_string())
            }
        }
        Err(e) => Err(e),
    };
    // The program finished (or failed at runtime); the checker may still be
    // working through code this run never executed, and lazy checking
    // ignores whatever it would find there -- the complete verdict is
    // `brass check`'s job. Stop it at the next body boundary, persist what
    // it settled as the partial cache (the next run resumes from it), and
    // reclaim the thread; held diagnostics are discarded by policy.
    stop_checker(&rt, checker, &mut lazy);
    save_partial_cache(&entry_path, &front.sources, &search, &bodies, &mut lazy);
    match result {
        Ok(()) => Ok(()),
        Err(e) => {
            report_runtime_error(&e);
            Err(1)
        }
    }
}

/// The last-resort fallback for a RESUMED run whose snapshot proves
/// insufficient (an entry the prior run withheld as still-open never made
/// it into the cache, and the skipped body will not re-emit it): rerun the
/// whole pipeline eagerly, in process. `finish_eagerly` cannot serve here --
/// a resumed checker skipped bodies, so its final payload is incomplete.
/// The eager rerun also REPLACES the failing partial cache with a full one,
/// self-healing the next run.
#[cfg(jit_backend)]
fn run_fresh_eager(label: &str, src: &str, root: &Path) -> Result<(), u8> {
    tracing::debug!(target: "brass::perf", "lazy: resume fell short, rerunning eagerly");
    let checked = match analyze(label, src, root) {
        Ok(c) => c,
        Err(diags) => return Err(print_diags(diags)),
    };
    execute(
        &checked.program,
        &checked.expr_types,
        &checked.view_args,
        &checked.sum_views,
        &checked.call_locations,
        &checked.lift_errs,
        &checked.fields_loops,
        &checked.type_names,
        &checked.typeof_types,
        &checked.null_props,
        false,
    )
    .map_err(|e| {
        report_runtime_error(&e);
        1
    })
}

/// Stamp every loaded source for a cache payload's validity guard, exactly
/// as the full-cache save does: `.cz` sources from the parsed text (a
/// re-read would race an editor), native plugin libraries from the file.
/// `None` when anything cannot be stamped -- the build is then uncacheable.
#[cfg(jit_backend)]
fn stamp_sources(
    entry: &Path,
    sources: &brass_resolve::SourceMap,
    search: &brass_resolve::SearchPaths,
) -> Option<Vec<brass_cache::FileStamp>> {
    let roots = brass_cache::StampRoots::new(entry, search);
    let mut deps = Vec::new();
    for (path, text) in sources.sourced() {
        let native = matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("so" | "dylib" | "dll")
        );
        let stamp = if native {
            brass_cache::FileStamp::of(path, &roots)
        } else {
            Some(brass_cache::FileStamp::of_text(path, text, &roots))
        };
        deps.push(stamp?);
    }
    Some(deps)
}

/// Persist a stopped run's settled state as the PARTIAL cache, so the next
/// lazy run resumes checking where this one left off. Bodies owning a held
/// diagnostic are dropped from the settled set (per body, the cache implies
/// clean); a keyed restart leaves nothing coherent to save.
#[cfg(jit_backend)]
fn save_partial_cache(
    entry: &Path,
    sources: &brass_resolve::SourceMap,
    search: &brass_resolve::SearchPaths,
    bodies: &BodySpans,
    lazy: &mut LazyState,
) {
    if !brass_cache::enabled() || lazy.restarted {
        return;
    }
    let Some(mut snapshot) = lazy.snapshot.take() else {
        return;
    };
    let errored: HashSet<&str> = lazy
        .held
        .iter()
        .filter_map(|e| bodies.owner(e.span))
        .collect();
    snapshot
        .checked
        .retain(|symbol| !errored.contains(symbol.as_str()));
    let Some(deps) = stamp_sources(entry, sources, search) else {
        return;
    };
    brass_cache::save_partial(
        entry,
        PARTIAL_CACHE_FLAVOR,
        &brass_cache::PartialPayload {
            deps,
            packages: brass_cache::package_names(search),
            snapshot,
        },
    );
}

/// Stop the checker and reclaim its thread. The stop flag is polled at body
/// boundaries, so the join is bounded by the body in flight; the drain runs
/// the event channel to close so the join never waits on a full buffer.
#[cfg(jit_backend)]
fn stop_checker(
    rt: &tokio::runtime::Runtime,
    checker: tokio::task::JoinHandle<Result<AnalyzedProgram, Vec<String>>>,
    lazy: &mut LazyState,
) {
    lazy.stop.store(true, std::sync::atomic::Ordering::Relaxed);
    while !lazy.closed {
        lazy.pump_blocking();
    }
    let _ = rt
        .block_on(checker)
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic.into_panic()));
}

/// Interpreter-only builds never take the lazy path (`drive` gates it on
/// `jit_backend`); this stand-in keeps them compiling and, if ever reached,
/// behaves exactly like an eager run.
#[cfg(not(jit_backend))]
fn run_lazy(label: String, src: String, root: PathBuf) -> Result<(), u8> {
    let checked = match analyze(&label, &src, &root) {
        Ok(c) => c,
        Err(diags) => return Err(print_diags(diags)),
    };
    execute(
        &checked.program,
        &checked.expr_types,
        &checked.view_args,
        &checked.sum_views,
        &checked.call_locations,
        &checked.lift_errs,
        &checked.fields_loops,
        &checked.type_names,
        &checked.typeof_types,
        &checked.null_props,
        false,
    )
    .map_err(|e| {
        report_runtime_error(&e);
        1
    })
}

/// The full front-end pipeline on the calling thread: parse, resolve, lower,
/// and statically check, with no cache probe. Returns the analysis in
/// thread-transportable form ([`AnalyzedProgram`]); the executable program is
/// rebuilt from it with [`assemble_checked`]. Persists the analysis to the
/// cache when possible.
///
/// With a scheduler, the type check streams its progress through it (see
/// `brass_typeck::stream`); a keyed-specialization re-pass emits `Restarted`
/// first, because the rewritten program's spans invalidate everything
/// streamed by the first pass.
fn analyze_fresh(
    main_label: &str,
    main_src: &str,
    root: &Path,
    sched: Option<&mut dyn brass_typeck::stream::Scheduler>,
) -> Result<AnalyzedProgram, Vec<String>> {
    let search = brass_resolve::SearchPaths::from_env();
    let front = front_load(main_label, main_src, root, &search)?;
    check_front(main_label, front, &search, sched, None)
}

/// The assembled front end, ready to check: the final module graph
/// (post-resolution, post-rewrite), its sources, and what the front passes
/// reported. Everything here is thread-transportable and clonable, so the
/// lazy runner can keep one copy to execute and hand an identical one to the
/// checker thread -- assembling once instead of parsing the program twice.
#[derive(Clone)]
struct FrontEnd {
    modules: Vec<LoadedModule>,
    sources: brass_resolve::SourceMap,
    /// Byte-offset base the entry source was parsed at (identifies the entry
    /// in `sources` when hashing the context).
    entry_base: usize,
    /// Clean-program warnings (spawn auto-acquire notes), already printed;
    /// carried for the cache payload so warm runs replay them.
    warnings: Vec<String>,
    /// Qualified-use and spawn-ownership diagnostics: not fatal on their own
    /// here -- they abort the analysis together with lowering and type
    /// errors, keeping the eager report order.
    errors: Vec<(String, Span)>,
}

/// Parse, resolve the module graph, and run the AST rewrites (qualified-use
/// promotion, spawn auto-acquire): the deterministic front half of
/// [`analyze_fresh`]. Aborts (rendered) on syntax errors and a broken module
/// graph -- the driver's error policy is per problem class, and checking a
/// recovered AST would bury the real problem under cascading name/type
/// errors. Also prints the spawn warnings, once.
fn front_load(
    main_label: &str,
    main_src: &str,
    root: &Path,
    search: &brass_resolve::SearchPaths,
) -> Result<FrontEnd, Vec<String>> {
    let t = std::time::Instant::now();
    let entry_path = PathBuf::from(main_label);
    let front = brass_resolve::frontend::assemble(&entry_path, main_src, root, search);
    // A prelude parse failure is a build bug; nothing else can be trusted.
    if let Some(message) = front.stdlib_error {
        return Err(vec![message]);
    }
    let sources = front.sources;
    if !front.parse_errors.is_empty() {
        return Err(render_errors(&front.parse_errors, &sources));
    }
    if !front.load_errors.is_empty() {
        return Err(render_errors(&front.load_errors, &sources));
    }
    let mut modules = front.modules;
    brass_utils::perf_phase("front/load-modules", t.elapsed());

    // Resolve qualified uses of module imports (`import a.b` + `b.name`),
    // promoting the used names onto the imports so everything downstream sees
    // name-based imports. Problems join the analysis diagnostics.
    let mut errors: Vec<(String, Span)> = Vec::new();
    for e in brass_resolve::resolve_qualified_uses(&mut modules) {
        errors.push((e.message, e.span));
    }

    // The spawn-ownership pass only matters for the JIT runtime (the REPL does not
    // execute concurrency); it lives in the LLVM crate, so it is feature-gated.
    // The pass may reject a `spawn` it cannot analyze; those diagnostics join the
    // analysis errors.
    #[cfg(jit_backend)]
    let warnings: Vec<String> = {
        let warnings = report_spawn_ownership(&modules);
        for w in &warnings {
            eprintln!("{w}");
        }
        errors.extend(auto_acquire_modules(&mut modules));
        warnings
    };
    #[cfg(not(jit_backend))]
    let warnings: Vec<String> = Vec::new();

    Ok(FrontEnd {
        modules,
        sources,
        entry_base: front.entry_base,
        warnings,
        errors,
    })
}

/// Statically check an assembled front end and package the result: the check
/// half of [`analyze_fresh`], and what the lazy runner's checker thread
/// executes over its copy of the modules. Persists the analysis to the cache
/// when possible.
fn check_front(
    main_label: &str,
    front: FrontEnd,
    search: &brass_resolve::SearchPaths,
    mut sched: Option<&mut dyn brass_typeck::stream::Scheduler>,
    resume: Option<brass_typeck::stream::StreamSnapshot>,
) -> Result<AnalyzedProgram, Vec<String>> {
    let phase = |name: &'static str, at: std::time::Instant| {
        brass_utils::perf_phase(name, at.elapsed());
    };
    let entry_path = PathBuf::from(main_label);
    let FrontEnd {
        mut modules,
        sources,
        entry_base: base,
        warnings,
        errors: front_errors,
    } = front;

    // The context key: module names plus the hash of every source that is not
    // the entry's. Contents, not ASTs, because the entry's length shifts every
    // later module's spans -- an AST key would treat each entry edit as a new
    // context. The front rewrites are deterministic functions of these
    // sources, so pre-rewrite content identifies the post-rewrite context.
    let ctx_end = modules.len() - 1;
    let ctx_key = brass_cache::context_key(
        CACHE_FLAVOR,
        modules[..ctx_end].iter().map(|m| m.path.join(".")),
        sources
            .entries()
            .filter(|(b, _)| *b != base)
            .map(|(_, src)| brass_cache::content_hash(src.as_bytes())),
    );

    // Per-module (dotted path, source hash) pairs for the incremental context
    // rebuild. Each module is matched to its source through the injected span
    // base; dependency traversal gives modules and sources different orders.
    let ctx_module_hashes = context_module_hashes(&modules[..ctx_end], &sources);
    // The context seed: the analysis tables of every module EXCEPT the entry,
    // reused so the full check below re-infers only the entry. Looked up in the
    // shared on-disk store when caching is enabled; rebuilt (and stored) from a
    // context-only run otherwise -- incrementally when the previous build of
    // this same context is on disk. A context with diagnostics yields no seed
    // and the full run reports everything as before.
    let ctx_seed = cached_context_seed(
        &ctx_key,
        &modules[..ctx_end],
        ctx_module_hashes.as_deref(),
        "front/context-check",
    );

    tracing::debug!(modules = modules.len(), "lowering module graph to HIR");
    let t = std::time::Instant::now();
    let (program, lower_errors) = lower(&modules);
    phase("front/lower-hir", t);
    let mut errors: Vec<(String, Span)> = front_errors;
    for e in lower_errors {
        errors.push((e.message, e.span));
    }
    for e in brass_resolve::check_imports(&modules) {
        errors.push((e.message, e.span));
    }
    tracing::debug!(
        functions = program.functions.len(),
        types = program.types.len(),
        "running type analysis"
    );
    // A lazy consumer must learn the module-level verdicts (lowering,
    // qualified uses, import checks) as events too: their spans lie outside
    // every body, which the lazy gate treats as always fatal -- an import
    // collision stops the run before anything executes, deterministically.
    if let Some(s) = sched.as_deref_mut()
        && !errors.is_empty()
    {
        s.emit(brass_typeck::stream::CheckEvent::StaticChecked(
            errors
                .iter()
                .map(|(message, span)| brass_typeck::TypeError {
                    message: message.clone(),
                    span: *span,
                })
                .collect(),
        ));
    }
    let t = std::time::Instant::now();
    let mut analysis = match sched.as_deref_mut() {
        Some(s) => brass_typeck::analyze_streaming(&program, ctx_seed.as_ref(), s, resume.as_ref()),
        None => brass_typeck::analyze_with(&program, ctx_seed.as_ref()),
    };
    phase("front/typecheck", t);
    // Reflective decoders: a `-> infer!` method call is keyed by the caller's
    // expectation. Generate a concrete method per requested key, inject them,
    // rewrite the calls to their specializations, and re-run the pipeline over
    // the now fully-concrete program. Errors from the first pass are held until
    // after specialization (a keyed call would otherwise report as an
    // undeclared method); a genuine error re-surfaces in the second pass.
    let mut program = program;
    // No re-pass once the consumer stopped the session (its program already
    // ran to completion): the specialization verdict would serve nobody --
    // the driver never executes from this payload, the full-cache save is
    // suppressed for a stopped run anyway, and the driver's exit would
    // otherwise block on a whole eager re-analysis. The lazy run that DOES
    // need the specializations sees `Restarted` before execution and falls
    // back to the eager pipeline.
    let repass_wanted = !sched.as_deref().is_some_and(|s| s.stopped());
    if !analysis.keyed_calls.is_empty() && repass_wanted {
        // The re-pass context is the pre-pass context PLUS the injected
        // specializations -- a deterministic function of the context sources
        // and the requested (receiver, method, key) set. Extending the context
        // key with that set lets the re-pass reuse a seed exactly when the
        // same decoders are requested again, which is every entry edit that
        // does not change what gets decoded.
        let mut spec_symbols: Vec<String> = analysis
            .keyed_calls
            .values()
            .map(|(recv, method, key)| format!("{recv}.{method}:{}", brass_hir::type_key(key)))
            .collect();
        spec_symbols.sort();
        spec_symbols.dedup();
        let repass_key = ctx_key.map(|key| {
            let mut keyed = key.to_vec();
            for sym in &spec_symbols {
                keyed.push(0);
                keyed.extend_from_slice(sym.as_bytes());
            }
            brass_cache::content_hash(&keyed)
        });
        match specialize_keyed(&mut modules, &program, &analysis) {
            Ok(injected) => {
                // The specialization rewrote some modules in place, so their
                // loaded sources no longer describe their ASTs. For the
                // incremental sidecar, fold the specialization identity into
                // the TOUCHED modules' hashes (injection targets plus every
                // module containing a rewritten call site -- a keyed call's
                // span lies in its module's source segment, and sources and
                // modules are pushed in the same load order) and add a
                // synthetic path entry, so the keyed context's sidecar is
                // distinct from the plain one yet diffs the same way.
                let mut touched = injected;
                let attributable = modules
                    .iter()
                    .all(|module| module_source_base(module).is_some());
                if attributable {
                    for span in analysis.keyed_calls.keys() {
                        if let Some(path) = module_path_at(&modules, &sources, span.lo) {
                            touched.insert(path);
                        }
                    }
                }
                let repass_hashes: Option<Vec<(String, [u8; 20])>> = ctx_module_hashes
                    .as_ref()
                    .filter(|_| attributable)
                    .map(|hashes| {
                        let mut spec_buf = Vec::new();
                        for s in &spec_symbols {
                            spec_buf.extend_from_slice(s.as_bytes());
                            spec_buf.push(0);
                        }
                        let spec_hash = brass_cache::content_hash(&spec_buf);
                        let touched_paths: HashSet<String> =
                            touched.iter().map(|t| t.join(".")).collect();
                        let mut v: Vec<(String, [u8; 20])> = hashes
                            .iter()
                            .map(|(p, h)| {
                                if touched_paths.contains(p) {
                                    let mut buf = h.to_vec();
                                    buf.extend_from_slice(&spec_hash);
                                    (p.clone(), brass_cache::content_hash(&buf))
                                } else {
                                    (p.clone(), *h)
                                }
                            })
                            .collect();
                        v.push(("(keyed-specializations)".to_string(), spec_hash));
                        v
                    });
                let repass_seed = cached_context_seed(
                    &repass_key,
                    &modules[..modules.len() - 1],
                    repass_hashes.as_deref(),
                    "front/keyed-context-check",
                );
                let t = std::time::Instant::now();
                let (program2, lower_errors2) = lower(&modules);
                for e in lower_errors2 {
                    errors.push((e.message, e.span));
                }
                program = program2;
                // The injected specializations and rewritten call sites moved
                // spans: a streaming consumer starts over on the re-pass.
                // The re-pass itself is EAGER even under a streaming session
                // -- the driver always falls back to the whole-analysis
                // verdict on `Restarted` (execution cannot survive the span
                // rewrite), so streaming it would serve nobody, and the
                // eager result is complete enough to persist as the full
                // cache the fallback then loads.
                if let Some(s) = sched.as_deref_mut() {
                    s.emit(brass_typeck::stream::CheckEvent::Restarted);
                }
                analysis = brass_typeck::analyze_with(&program, repass_seed.as_ref());
                phase("front/keyed-repass", t);
            }
            Err(e) => errors.push(e),
        }
    }
    for e in &analysis.errors {
        errors.push((e.message.clone(), e.span));
    }
    tracing::debug!(errors = errors.len(), "front-end analysis complete");
    if !errors.is_empty() {
        errors.sort_by_key(|(_, s)| s.lo);
        return Err(render_errors(&errors, &sources));
    }

    let expr_types = brass_typeck::stream::aggregate_result_types(&analysis.typed, &program);
    let call_locations = call_site_locations(&modules, &sources);
    let channels = brass_cache::Channels {
        expr_types: expr_types.into_iter().collect(),
        view_args: analysis.view_args.into_iter().collect(),
        sum_views: analysis.sum_views.into_iter().collect(),
        call_locations: call_locations.into_iter().collect(),
        lift_errs: analysis.lift_errs.into_iter().collect(),
        fields_loops: analysis.fields_loops.into_iter().collect(),
        type_names: analysis.type_names.into_iter().collect(),
        typeof_types: analysis.typeof_types.into_iter().collect(),
        null_props: analysis.null_props.into_iter().collect(),
    };
    // A stopped (lazy-exit) analysis is INCOMPLETE: bodies past the stop
    // point were never checked, so caching it as a full verdict would replay
    // missing channels into future runs. Only a run the checker finished may
    // persist.
    let stopped = sched.as_deref().is_some_and(|s| s.interrupted());
    // Persist the clean analysis for the next run. Every on-disk source in
    // the map is stamped (the embedded stdlib has no path and is covered by
    // the compiler tag in the header): `.cz` sources from the very text that
    // was parsed -- a re-read would race an editor saving during the analysis
    // -- and native plugin libraries from the file itself (their entry's text
    // is the synthesized wrapper, not the library). The entry file is the
    // first path-bearing source (the stdlib precedes it pathless), which is
    // the load-time entry-identity contract. A file that cannot be stamped
    // anymore makes the build uncacheable rather than wrongly cacheable.
    if brass_cache::enabled() && !stopped {
        let t = std::time::Instant::now();
        let roots = brass_cache::StampRoots::new(&entry_path, search);
        let mut deps = Vec::new();
        let mut stampable = true;
        for (path, text) in sources.sourced() {
            let native = matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("so" | "dylib" | "dll")
            );
            let stamp = if native {
                brass_cache::FileStamp::of(path, &roots)
            } else {
                Some(brass_cache::FileStamp::of_text(path, text, &roots))
            };
            match stamp {
                Some(stamp) => deps.push(stamp),
                None => stampable = false,
            }
        }
        if stampable {
            let payload = brass_cache::Payload {
                deps,
                packages: brass_cache::package_names(search),
                modules,
                warnings,
                channels,
            };
            brass_cache::save(&entry_path, CACHE_FLAVOR, &payload);
            phase("front/cache-save", t);
            return Ok(AnalyzedProgram {
                modules: payload.modules,
                channels: payload.channels,
            });
        }
    }
    Ok(AnalyzedProgram { modules, channels })
}

/// Generate concrete specializations of the reflective (`-> infer!`) methods
/// the checker keyed, inject them into their defining modules' ASTs, and
/// rewrite each keyed call site to its specialization. After this the program
/// is fully concrete: the second checking/lowering pass sees ordinary methods.
/// Returns the module paths the injection touched (generated methods and
/// synthetic imports); call-site rewrites are the caller's to attribute (it
/// owns the span-to-module mapping).
fn specialize_keyed(
    modules: &mut [LoadedModule],
    program: &Program,
    analysis: &brass_typeck::Analysis,
) -> Result<HashSet<Vec<String>>, (String, Span)> {
    // Deduplicate the requested (receiver, method, key) roots.
    let mut roots: Vec<brass_typesys::KeyedNeed> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for (recv, method, key) in analysis.keyed_calls.values() {
        let sym = format!("{recv}.{method}:{}", brass_hir::type_key(key));
        if seen.insert(sym) {
            roots.push(brass_typesys::KeyedNeed {
                recv: recv.clone(),
                method: method.clone(),
                key: key.clone(),
            });
        }
    }
    // Deterministic order so the specializations (and the shared-solver
    // re-elaboration that checks them) do not vary run to run.
    roots.sort_by(|a, b| {
        (&a.recv, &a.method, brass_hir::type_key(&a.key)).cmp(&(
            &b.recv,
            &b.method,
            brass_hir::type_key(&b.key),
        ))
    });
    let generated = brass_typesys::specialize_all(program, &roots).map_err(|e| {
        (
            format!("reflective specialization failed: {e}"),
            Span::new(0, 0),
        )
    })?;
    // Inject each generated method into the module that defines its receiver.
    // A record key defined in another module (`User` in the caller, decoder in
    // the json library) is not visible there, so also inject a synthetic import
    // of the key type into the receiver's module. Collected per module first so
    // one import covers every specialization that needs it.
    use brass_hir::Type;
    let mut synthetic_imports: HashMap<Vec<String>, Vec<(Vec<String>, String)>> = HashMap::new();
    for g in &generated {
        if let Type::Record(n) | Type::Sum(n) = &g.key
            && let Some(info) = program.type_by_id(n.id)
            && info.module != g.module
        {
            let entry = synthetic_imports.entry(g.module.clone()).or_default();
            let import = (info.module.clone(), n.name.clone());
            if !entry.contains(&import) {
                entry.push(import);
            }
        }
    }
    let mut touched: HashSet<Vec<String>> = HashSet::new();
    for g in generated {
        if let Some(m) = modules.iter_mut().find(|m| m.path == g.module) {
            m.ast.items.push(TopLevel::Fun(g.decl));
            touched.insert(g.module);
        }
    }
    for (module_path, imports) in synthetic_imports {
        touched.insert(module_path.clone());
        if let Some(m) = modules.iter_mut().find(|m| m.path == module_path) {
            for (from_module, name) in imports {
                m.ast.imports.push(brass_parser::ast::ImportDecl {
                    path: from_module,
                    names: vec![brass_parser::ast::ImportedName::plain(
                        name,
                        Span::new(0, 0),
                    )],
                    bare: false,
                    alias: None,
                    explicit_alias: false,
                    span: Span::new(0, 0),
                });
            }
        }
    }
    // Rewrite the keyed call sites to their specializations.
    let renames: std::collections::HashMap<Span, String> = analysis
        .keyed_calls
        .iter()
        .map(|(span, (_, method, key))| (*span, brass_typesys::mangled_name(method, key)))
        .collect();
    for m in modules.iter_mut() {
        for item in &mut m.ast.items {
            if let TopLevel::Fun(f) = item {
                rewrite_calls_block(&mut f.body, &renames);
            } else if let TopLevel::Stmt(s) = item {
                rewrite_calls_stmt(s, &renames);
            }
        }
    }
    Ok(touched)
}

/// Rewrite `recv.m(..)` calls whose span is in `renames` to `recv.<new>(..)`.
fn rewrite_calls_block(
    b: &mut brass_parser::ast::Block,
    renames: &std::collections::HashMap<Span, String>,
) {
    for s in &mut b.stmts {
        rewrite_calls_stmt(s, renames);
    }
}

fn rewrite_calls_stmt(s: &mut Stmt, renames: &std::collections::HashMap<Span, String>) {
    match s {
        Stmt::Let { value: Some(v), .. } => rewrite_calls_expr(v, renames),
        Stmt::Assign { target, value, .. } => {
            rewrite_calls_expr(target, renames);
            rewrite_calls_expr(value, renames);
        }
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => rewrite_calls_expr(e, renames),
        Stmt::While { cond, body, .. } => {
            rewrite_calls_expr(cond, renames);
            rewrite_calls_block(body, renames);
        }
        Stmt::For { iter, body, .. } => {
            rewrite_calls_expr(iter, renames);
            rewrite_calls_block(body, renames);
        }
        _ => {}
    }
}

fn rewrite_calls_expr(
    e: &mut brass_parser::ast::Expr,
    renames: &std::collections::HashMap<Span, String>,
) {
    use brass_parser::ast::{Expr, StrSeg};
    match e {
        Expr::Call(callee, args, span) => {
            if let Some(new_name) = renames.get(span)
                && let Expr::Field(_, m, _) = &mut **callee
            {
                *m = new_name.clone();
            }
            rewrite_calls_expr(callee, renames);
            for a in args.iter_mut() {
                rewrite_calls_expr(&mut a.expr, renames);
            }
        }
        Expr::Field(b, _, _) | Expr::Unary(_, b, _) | Expr::ErrorProp(b, _) => {
            rewrite_calls_expr(b, renames)
        }
        Expr::Binary(_, l, r, _) | Expr::Index(l, r, _) | Expr::Range(l, r, _) => {
            rewrite_calls_expr(l, renames);
            rewrite_calls_expr(r, renames);
        }
        Expr::Array(es, _) => es.iter_mut().for_each(|e| rewrite_calls_expr(e, renames)),
        Expr::TypeLit(_, fs, _) | Expr::VariantLit(_, _, fs, _) => fs
            .iter_mut()
            .for_each(|(_, e)| rewrite_calls_expr(e, renames)),
        Expr::Str(segs, _) => segs.iter_mut().for_each(|seg| {
            if let StrSeg::Expr(e) = seg {
                rewrite_calls_expr(e, renames);
            }
        }),
        Expr::If(c, t, els, _) => {
            rewrite_calls_expr(c, renames);
            rewrite_calls_block(t, renames);
            if let Some(e) = els {
                rewrite_calls_expr(e, renames);
            }
        }
        Expr::IfLet(_, scrut, t, els, _) => {
            rewrite_calls_expr(scrut, renames);
            rewrite_calls_block(t, renames);
            if let Some(e) = els {
                rewrite_calls_expr(e, renames);
            }
        }
        Expr::Match(scrut, arms, _) => {
            rewrite_calls_expr(scrut, renames);
            for arm in arms.iter_mut() {
                rewrite_calls_expr(&mut arm.body, renames);
            }
        }
        Expr::Block(b, _) => rewrite_calls_block(b, renames),
        Expr::Closure(_, b, _) => rewrite_calls_expr(b, renames),
        _ => {}
    }
}

/// Every call expression's span mapped to its source position (diagnostic
/// label, 1-based line and column). MIR lowering reads this to fill a
/// callee's implicit trailing `Location` parameter with the call site;
/// computing it here keeps source access out of the type-free lowering, and
/// the map reproduces from the cache (whose ASTs carry the same spans).
fn call_site_locations(
    modules: &[LoadedModule],
    sources: &brass_resolve::SourceMap,
) -> HashMap<Span, (String, u32, u32)> {
    let mut spans: Vec<Span> = Vec::new();
    for m in modules {
        for item in &m.ast.items {
            match item {
                brass_parser::ast::TopLevel::Fun(f) => {
                    collect_call_spans_block(&f.body, &mut spans)
                }
                brass_parser::ast::TopLevel::Stmt(st) => collect_call_spans_stmt(st, &mut spans),
                brass_parser::ast::TopLevel::Type(_) => {}
            }
        }
    }
    // Labels are relativized against the working directory and the include
    // roots' parents, so a baked expectation (an e2e `.out`) does not embed a
    // machine-specific absolute path.
    let mut prefixes: Vec<String> = Vec::new();
    if let Ok(cwd) = std::env::current_dir()
        && let Ok(c) = cwd.canonicalize()
    {
        prefixes.push(format!("{}/", c.display()));
    }
    if let Ok(inc) = std::env::var("BRASS_INCLUDE") {
        for root in inc.split(':').filter(|r| !r.is_empty()) {
            if let Ok(c) = Path::new(root).canonicalize()
                && let Some(parent) = c.parent()
            {
                prefixes.push(format!("{}/", parent.display()));
            }
        }
    }
    // A package root serves modules under `<root>/<name>/...`, so the root
    // itself is the prefix to strip (`std=/toolchain` renders the standard
    // library as `std/fs.cz`).
    if let Ok(pkgs) = std::env::var("BRASS_PACKAGES") {
        for entry in pkgs.split(':').filter(|e| !e.is_empty()) {
            if let Some((_, path)) = entry.split_once('=')
                && let Ok(c) = Path::new(path).canonicalize()
            {
                prefixes.push(format!("{}/", c.display()));
            }
        }
    }
    let relativize = |label: &str| -> String {
        // Canonicalize the label's path first (a plugin label wraps one), so
        // the caller's spelling (`../../x.cz`) does not leak into the
        // recorded position.
        let mut label = if let Some(inner) = label
            .strip_prefix("<plugin:")
            .and_then(|r| r.strip_suffix('>'))
        {
            match std::fs::canonicalize(inner) {
                Ok(c) => format!("<plugin:{}>", c.display()),
                Err(_) => label.to_string(),
            }
        } else {
            match std::fs::canonicalize(label) {
                Ok(c) => c.display().to_string(),
                Err(_) => label.to_string(),
            }
        };
        for p in &prefixes {
            label = label.replace(p.as_str(), "");
        }
        label
    };
    let mut out = HashMap::new();
    for span in spans {
        if let Some(loc) = sources.locate(span.lo) {
            let (line, col) = brass_parser::line_col(loc.src, loc.local);
            out.insert(span, (relativize(loc.label), line as u32, col as u32));
        }
    }
    out
}

fn collect_call_spans_block(b: &brass_parser::ast::Block, out: &mut Vec<Span>) {
    for s in &b.stmts {
        collect_call_spans_stmt(s, out);
    }
}

fn collect_call_spans_stmt(s: &Stmt, out: &mut Vec<Span>) {
    match s {
        Stmt::Let { value: Some(v), .. } => collect_call_spans_expr(v, out),
        Stmt::Assign { target, value, .. } => {
            collect_call_spans_expr(target, out);
            collect_call_spans_expr(value, out);
        }
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => collect_call_spans_expr(e, out),
        Stmt::While { cond, body, .. } => {
            collect_call_spans_expr(cond, out);
            collect_call_spans_block(body, out);
        }
        Stmt::For { iter, body, .. } => {
            collect_call_spans_expr(iter, out);
            collect_call_spans_block(body, out);
        }
        _ => {}
    }
}

fn collect_call_spans_expr(e: &brass_parser::ast::Expr, out: &mut Vec<Span>) {
    use brass_parser::ast::{Expr, StrSeg};
    match e {
        Expr::Call(callee, args, span) => {
            out.push(*span);
            collect_call_spans_expr(callee, out);
            for a in args {
                collect_call_spans_expr(&a.expr, out);
            }
        }
        Expr::Field(b, _, _) | Expr::Unary(_, b, _) => collect_call_spans_expr(b, out),
        // `!` sites need positions too: a lifted propagation stamps its own.
        Expr::ErrorProp(b, span) => {
            out.push(*span);
            collect_call_spans_expr(b, out);
        }
        Expr::Binary(_, l, r, _) | Expr::Index(l, r, _) | Expr::Range(l, r, _) => {
            collect_call_spans_expr(l, out);
            collect_call_spans_expr(r, out);
        }
        Expr::Array(es, _) => es.iter().for_each(|e| collect_call_spans_expr(e, out)),
        // Construction spans are collected too: a lifted forwarded return
        // stamps the construction's own position into the wrapped Error.
        Expr::TypeLit(_, fs, span) | Expr::VariantLit(_, _, fs, span) => {
            out.push(*span);
            fs.iter().for_each(|(_, e)| collect_call_spans_expr(e, out))
        }
        Expr::Str(segs, _) => segs.iter().for_each(|seg| {
            if let StrSeg::Expr(e) = seg {
                collect_call_spans_expr(e, out);
            }
        }),
        Expr::If(c, t, els, _) => {
            collect_call_spans_expr(c, out);
            collect_call_spans_block(t, out);
            if let Some(e) = els {
                collect_call_spans_expr(e, out);
            }
        }
        Expr::IfLet(_, scrut, t, els, _) => {
            collect_call_spans_expr(scrut, out);
            collect_call_spans_block(t, out);
            if let Some(e) = els {
                collect_call_spans_expr(e, out);
            }
        }
        Expr::Match(scrut, arms, _) => {
            collect_call_spans_expr(scrut, out);
            for arm in arms {
                collect_call_spans_expr(&arm.body, out);
            }
        }
        Expr::Block(b, _) => collect_call_spans_block(b, out),
        Expr::Closure(_, b, _) => collect_call_spans_expr(b, out),
        _ => {}
    }
}

/// Print a runtime failure. A message that is already a rendered error trace
/// (the prelude's unhandled-`!` rendering, whose lines carry their own
/// `[file:line:col] unhandled error:` framing) prints verbatim; every other
/// failure uses the same `runtime error:` prefix as the native runtime.
fn report_runtime_error(e: &str) {
    if e.starts_with('[') && e.contains("unhandled error:") {
        eprintln!("{e}");
    } else {
        eprintln!("runtime error: {e}");
    }
}

/// Render each `(message, span)` diagnostic as `path:line:col: error: message`,
/// locating the span's file by its globally-unique offset (or a bare `error:`
/// line when no source contains it).
fn render_errors(errors: &[(String, Span)], sources: &brass_resolve::SourceMap) -> Vec<String> {
    render_diagnostics(errors, sources, "error")
}

fn render_diagnostics(
    items: &[(String, Span)],
    sources: &brass_resolve::SourceMap,
    level: &str,
) -> Vec<String> {
    let mut out = Vec::with_capacity(items.len());
    for (msg, span) in items {
        match sources.locate(span.lo) {
            Some(loc) => {
                let (line, col) = line_col(loc.src, loc.local);
                out.push(format!("{}:{line}:{col}: {level}: {msg}", loc.label));
            }
            None => out.push(format!("{level}: {msg}")),
        }
    }
    out
}

// ===== interactive REPL =====

/// Run an interactive REPL session. Top-level definitions (functions, types,
/// imports) accumulate; statements and expressions execute in an implicit `main`
/// whose history re-runs each turn so earlier bindings stay visible. Because the
/// program is deterministic and history-prefixed, only the new output suffix is
/// shown. A bare expression is echoed by wrapping it in `println`.
fn repl_interactive() -> ExitCode {
    let root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let stdin = io::stdin();
    eprintln!("brass REPL -- enter definitions or statements; Ctrl-D to exit.");

    let mut defs: Vec<String> = Vec::new();
    let mut body: Vec<String> = Vec::new();
    let mut last_output = String::new();

    loop {
        eprint!("> ");
        let _ = io::stderr().flush();
        let Some(item) = read_item(&stdin) else {
            eprintln!();
            break;
        };
        let item = item.trim().to_string();
        if item.is_empty() {
            continue;
        }

        if is_definition(&item) {
            defs.push(item);
            match run_capture(&defs, &body, &root) {
                Ok(_) => {}
                Err(e) => {
                    defs.pop();
                    eprintln!("{e}");
                }
            }
            continue;
        }

        // A bare expression is echoed: try `println(expr)`, then fall back to the
        // raw statement (e.g. a void-valued call that cannot be wrapped).
        let candidates: Vec<String> = if is_bare_expr(&item) {
            vec![format!("println({item})"), item.clone()]
        } else {
            vec![item.clone()]
        };
        let mut committed = false;
        let mut last_err = String::new();
        for cand in candidates {
            body.push(cand);
            match run_capture(&defs, &body, &root) {
                Ok(out) => {
                    print_new_output(&out, &last_output);
                    last_output = out;
                    committed = true;
                    break;
                }
                Err(e) => {
                    body.pop();
                    last_err = e;
                }
            }
        }
        if !committed {
            eprintln!("{last_err}");
        }
    }
    ExitCode::SUCCESS
}

/// Print the portion of `out` past the already-shown `prev` prefix (history
/// re-runs, so `out` extends `prev`); fall back to the whole output if the prefix
/// no longer matches.
fn print_new_output(out: &str, prev: &str) {
    let suffix = out.strip_prefix(prev).unwrap_or(out);
    print!("{suffix}");
    let _ = io::stdout().flush();
}

/// Assemble the accumulated definitions and `main` body, check, and interpret it,
/// capturing `print`/`println` output. Returns the captured output or the error.
fn run_capture(defs: &[String], body: &[String], root: &Path) -> Result<String, String> {
    let src = assemble(defs, body);
    let checked = analyze("<repl>", &src, root).map_err(|d| d.join("\n"))?;
    let mut buf: Vec<u8> = Vec::new();
    brass_repl::run(
        &checked.program,
        &checked.expr_types,
        &checked.view_args,
        &checked.sum_views,
        &checked.call_locations,
        &checked.lift_errs,
        &checked.fields_loops,
        &checked.type_names,
        &checked.typeof_types,
        &checked.null_props,
        &mut buf,
    )?;
    Ok(String::from_utf8_lossy(&buf).into_owned())
}

/// Build a single source unit from accumulated top-level definitions and an
/// implicit `main` holding the entered statements.
fn assemble(defs: &[String], body: &[String]) -> String {
    let mut s = String::new();
    for d in defs {
        s.push_str(d);
        s.push('\n');
    }
    s.push_str("fun main() {\n");
    for b in body {
        s.push_str(b);
        s.push('\n');
    }
    s.push_str("}\n");
    s
}

/// Whether an entered item is a top-level definition (a function/type definition
/// or an import) rather than a statement to execute in `main`.
fn is_definition(item: &str) -> bool {
    match parse(item) {
        Ok(m) => {
            !m.imports.is_empty()
                || m.items
                    .iter()
                    .any(|i| matches!(i, TopLevel::Fun(_) | TopLevel::Type(_)))
        }
        Err(_) => false,
    }
}

/// Whether an entered item is a single bare expression (eligible for value echo).
fn is_bare_expr(item: &str) -> bool {
    match parse(item) {
        Ok(m) => {
            m.imports.is_empty()
                && m.items.len() == 1
                && matches!(m.items.first(), Some(TopLevel::Stmt(Stmt::Expr(_))))
        }
        Err(_) => false,
    }
}

/// Read one REPL item: keep reading lines until the braces balance (so a
/// multi-line definition can be entered) or EOF. Returns `None` at end of input
/// with nothing pending.
fn read_item(stdin: &io::Stdin) -> Option<String> {
    let mut buf = String::new();
    loop {
        let mut line = String::new();
        let n = stdin.read_line(&mut line).ok()?;
        if n == 0 {
            return if buf.trim().is_empty() {
                None
            } else {
                Some(buf)
            };
        }
        buf.push_str(&line);
        if brace_balanced(&buf) {
            return Some(buf);
        }
        // Continuation prompt for an unfinished multi-line item.
        eprint!(". ");
        let _ = io::stderr().flush();
    }
}

/// Whether every `{` in `s` has a matching `}` (a coarse multi-line continuation
/// check; string/comment contents are not excluded, which is acceptable for an
/// interactive prompt).
fn brace_balanced(s: &str) -> bool {
    let mut depth: i32 = 0;
    for c in s.chars() {
        match c {
            '{' => depth += 1,
            '}' => depth -= 1,
            _ => {}
        }
    }
    depth <= 0
}

#[cfg(test)]
mod tests {
    use super::{context_identity, context_module_hashes, module_path_at, program_file_index};
    use brass_hir::LoadedModule;
    use brass_parser::Span;
    use brass_parser::ast::Module;
    use std::ffi::OsString;

    fn argv(args: &[&str]) -> Vec<OsString> {
        std::iter::once("brass")
            .chain(args.iter().copied())
            .map(OsString::from)
            .collect()
    }

    #[test]
    fn root_flags_may_precede_repl_and_check() {
        // Root flags are parsed by clap, but they must not hide the subcommand
        // that decides whether a following positional value is a program file.
        assert_eq!(
            program_file_index(&argv(&["--eager", "repl", "main.cz", "--program-flag"])),
            Some(3)
        );
        assert_eq!(
            program_file_index(&argv(&["--eager", "check", "main.cz"])),
            None
        );
    }

    #[test]
    fn option_terminator_makes_subcommand_words_file_names() {
        // After `--`, clap treats every token positionally. The manual split
        // must make the same choice or a file literally named `repl` is lost.
        assert_eq!(program_file_index(&argv(&["--", "repl", "arg"])), Some(2));
    }

    fn loaded(path: &str, base: usize) -> LoadedModule {
        let mut ast = Module {
            imports: Vec::new(),
            items: Vec::new(),
        };
        brass_resolve::inject_module_path(&mut ast, path, Span::new(base, base));
        LoadedModule {
            is_prelude: false,
            path: vec![path.to_string()],
            ast,
        }
    }

    #[test]
    fn context_hashes_follow_source_bases_not_module_order() {
        // Recursive loading records a parent source before its dependency but
        // appends the dependency module first. Hash ownership follows spans.
        let mut sources = brass_resolve::SourceMap::default();
        let a = sources.add(None, "a".to_string(), "source a".to_string());
        let b = sources.add(None, "b".to_string(), "source b".to_string());
        let modules = vec![loaded("b", b), loaded("a", a)];

        let hashes = context_module_hashes(&modules, &sources).expect("attributable modules");
        assert_eq!(hashes[0].0, "b");
        assert_eq!(hashes[0].1, brass_cache::content_hash(b"source b"));
        assert_eq!(hashes[1].0, "a");
        assert_eq!(hashes[1].1, brass_cache::content_hash(b"source a"));
        assert_eq!(
            module_path_at(&modules, &sources, a + 1),
            Some(vec!["a".into()])
        );
    }

    #[test]
    fn context_bundle_identity_separates_frontend_flavors() {
        let modules = vec![("core.io".to_string(), [7; 20])];
        assert_ne!(
            context_identity("jit", &modules),
            context_identity("repl", &modules)
        );
    }
}
