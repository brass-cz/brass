//! Brass command-line driver.
//!
//! Pipeline: resolve the module graph, parse, lower to HIR, check
//! (resolve + typeck), then run the checked program. The `core` library is
//! embedded and implicitly imported; the standard library is the `std` package,
//! found through the package search paths (`brass_resolve::SearchPaths`).
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

mod item_preparation;
mod item_shadow;
#[cfg(jit_backend)]
mod lazy;
#[cfg(jit_backend)]
use lazy::run_lazy;

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};

use brass_hir::{LoadedModule, Program, lower};
use brass_parser::Span;
use brass_parser::ast::{Stmt, TopLevel};
use brass_parser::parse;

mod cache;
mod repl_replay;
mod source_locations;

use source_locations::{LocationTables, call_site_locations, collect_call_spans_stmt};

/// The Brass toolchain driver.
///
/// The program file is a bare positional argument (`brass file.cz`) rather than
/// a `run` subcommand. A leading `check`/`repl`/`cache` parses as the subcommand; any
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
    /// Disable JIT object cache reads and writes for this process, equivalent to
    /// BRASS_JIT_CACHE=off. Must precede the program file.
    #[arg(long)]
    no_jit_cache: bool,
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand)]
enum Command {
    /// Inspect or clean the shared JIT object cache.
    Cache {
        #[command(subcommand)]
        action: cache::CacheAction,
    },
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
/// surfacing the guard's clean error. The reservation is virtual memory -- pages
/// are committed only as the stack actually grows.
#[cfg(not(target_family = "wasm"))]
pub(crate) const MAIN_STACK_BYTES: usize = 256 * 1024 * 1024;

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
    #[cfg(jit_backend)]
    if cli.no_jit_cache {
        brass_jit_llvm::disable_jit_cache();
    }
    match cli.command {
        Some(Command::Cache { action }) => cache::run(action, cli.no_jit_cache),
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
/// the bare-file form, after `repl` for the interpreter form. `check`, `cache`, and
/// `help` take no program arguments, so their lines stay fully clap's.
fn parse_cli() -> Cli {
    let argv: Vec<std::ffi::OsString> = std::env::args_os().collect();
    let file_at = program_file_index(&argv);
    let split = file_at.map_or(argv.len(), |i| i + 1);
    let mut cli = Cli::try_parse_from(argv[..split].iter().cloned())
        .unwrap_or_else(|error| item_shadow::parse_project_cli(&argv[..split], error));
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
/// subcommand recognition, so a following `check`, `cache`, or `repl` is a file name.
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
            index += if token == "--project-root" { 2 } else { 1 };
            continue;
        }
        if !positional_only && matches!(token.as_ref(), "check" | "help" | "cache") {
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
                index += if token == "--project-root" { 2 } else { 1 };
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
/// a helper that spawns is promoted and guarded too. Returns rejected spawn
/// arguments and warnings describing inserted access guards.
#[cfg(jit_backend)]
fn auto_acquire_modules<const SELECTED: bool>(
    modules: &mut [LoadedModule],
    view: Option<&brass_typeck::reachability::AnalysisView>,
) -> (Vec<(String, Span)>, Vec<String>, bool) {
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
                Pattern::Binding(name, _, _) => {
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

        let mut globals: HashSet<String> = HashSet::default();
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
        let mut mutated: HashSet<String> = HashSet::default();
        for g in &globals {
            if bodies.iter().any(|b| mutates(b, g)) {
                mutated.insert(g.clone());
            }
        }
        mutated
    };

    let mut may_rewrite = false;
    let mut warnings = Vec::new();
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
                    if SELECTED && view.is_some_and(|view| !view.selects_body(f.span)) {
                        continue;
                    }
                    let params = names(&f.params);
                    push_errors(brass_jit_llvm::ownership::pre_spawn_errors(
                        &f.body.stmts,
                        &params,
                        &mutated_globals,
                    ));
                    let report = auto_acquire(&mut f.body.stmts, &params, &summaries);
                    if SELECTED {
                        may_rewrite |= report.may_rewrite;
                    }
                    let context = match &f.recv {
                        Some(brass_parser::ast::TypeExpr::Named(name, _)) => {
                            format!("{name}.{}", f.name)
                        }
                        Some(brass_parser::ast::TypeExpr::Array(inner, _, _)) => {
                            if let brass_parser::ast::TypeExpr::Named(name, _) = inner.as_ref() {
                                format!("{name}[].{}", f.name)
                            } else {
                                f.name.clone()
                            }
                        }
                        _ => f.name.clone(),
                    };
                    warnings.extend(report_spawn_ownership(&report, &context));
                    push_errors(report.errors);
                }
                TopLevel::Type(t) => {
                    let members = match &mut t.body {
                        TypeBody::Record(members) => members,
                        TypeBody::Sum(_) | TypeBody::Alias(_) => continue,
                    };
                    for member in members {
                        if let Member::Method(method) = member
                            && (!SELECTED || view.is_none_or(|view| view.selects_body(method.span)))
                            && let Some(body) = &mut method.body
                        {
                            let params = names(&method.params);
                            push_errors(brass_jit_llvm::ownership::pre_spawn_errors(
                                &body.stmts,
                                &params,
                                &mutated_globals,
                            ));
                            let report = auto_acquire(&mut body.stmts, &params, &summaries);
                            if SELECTED {
                                may_rewrite |= report.may_rewrite;
                            }
                            warnings.extend(report_spawn_ownership(
                                &report,
                                &format!("{}.{}", t.name, method.name),
                            ));
                            push_errors(report.errors);
                        }
                    }
                }
                TopLevel::Stmt(_) => {}
            }
        }
    }
    (errors, warnings, may_rewrite)
}

/// Format one warning per execution scope and lock root with an inserted access
/// guard. Captures alone and explicit acquisitions do not produce warnings.
#[cfg(jit_backend)]
fn report_spawn_ownership(
    report: &brass_jit_llvm::ownership::AutoAcquireReport,
    context: &str,
) -> Vec<String> {
    let mut seen = HashSet::default();
    report
        .guarded_accesses
        .iter()
        .filter_map(|access| {
            if !seen.insert((access.scope, &access.root_binding)) {
                return None;
            }
            let scope = if access.scope.is_some() {
                format!("in a spawned task within `{context}`")
            } else {
                format!("in `{context}`")
            };
            Some(format!(
                "warning: variable '{}' is shared with a spawned task; accesses outside \
             `with` are auto-guarded by its cown lock {scope}\n  = note: for \
             finer-grained concurrency, acquire it explicitly with 'with(cown, \
             (c) -> {{ ... }})'",
                access.root_binding,
            ))
        })
        .collect()
}

/// Make any Rust panic abort the process instead of unwinding. JIT-compiled
/// frames carry no unwind tables, so a panic in a runtime function called from
/// JIT code that unwinds into them is undefined behavior. Aborting in the panic
/// hook -- before unwinding begins -- keeps such a failure well-defined (a clean
/// abort with the panic message). Installed once, only on the JIT execution path;
/// the interpreter is pure Rust and unwinds normally, and the in-process JIT
/// tests drive the back end directly without going through here.
#[cfg(jit_backend)]
pub(crate) fn install_jit_panic_guard() {
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
pub(crate) fn execute(
    program: &Program,
    channels: &brass_mir::CheckerChannels<'_>,
) -> Result<(), String> {
    install_jit_panic_guard();
    brass_jit_llvm::run(program, channels)
}

/// Run a checked program through the default runtime: the REPL interpreter, used
/// when the JIT back end is unavailable (no `jit` feature, or a wasm target).
#[cfg(not(jit_backend))]
pub(crate) fn execute(
    program: &Program,
    channels: &brass_mir::CheckerChannels<'_>,
) -> Result<(), String> {
    brass_repl::run(program, channels, &mut io::stdout())
}

/// Run a checked program through the REPL interpreter (the `repl` subcommand),
/// regardless of the `jit` feature.
fn execute_repl(
    program: &Program,
    channels: &brass_mir::CheckerChannels<'_>,
) -> Result<(), String> {
    brass_repl::run(program, channels, &mut io::stdout())
}

/// A program that passed every front-end check, ready to run.
struct Checked {
    program: Program,
    channels: OwnedChannels,
}

impl Checked {
    /// Borrow the checker's complete MIR-lowering sidecar.
    fn channels(&self) -> brass_mir::CheckerChannels<'_> {
        self.channels.borrow()
    }
}

/// The checker outputs MIR lowering consumes, owned: the counterpart of
/// [`brass_mir::CheckerChannels`]. The channels are keyed by source span (the
/// per-instance ones by span, then instance), except `instance_returns`,
/// keyed by function symbol and argument types; lowering is deterministic, so
/// the spans match the HIR rebuilt from the same module graph on another
/// thread.
#[derive(Default)]
struct OwnedChannels {
    /// Eligibility from the same analysis that supplied these channels.
    selected_bodies: Option<std::sync::Arc<HashSet<Span>>>,
    /// Checker-resolved aggregate result types that seed MIR locals, keyed by
    /// span (see `brass_typeck::stream::aggregate_result_types`).
    expr_types: HashMap<Span, brass_hir::Type>,
    /// Method receiver types are isolated from aggregate result seeds so their
    /// source observations can only affect signature selection.
    receiver_types: HashMap<Span, brass_hir::Type>,
    /// Method calls whose instances resolve different owners, with every
    /// owner (see `brass_typeck::stream::method_receiver_owners`).
    receiver_owners: HashMap<Span, Vec<brass_hir::Type>>,
    /// Spans of anonymous structural arguments the checker approved for view
    /// conversion; MIR lowering wraps exactly these in `Rvalue::RecordView`.
    view_args: HashSet<Span>,
    numeric_calls: brass_hir::NumericCalls,
    /// `recv.name(..)` calls of a function-valued field (all instantiations,
    /// or the receivers' patterns that do); MIR lowering emits a field call
    /// for these.
    field_calls: HashMap<Span, Option<Vec<brass_hir::Type>>>,
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
    /// Field lists selected by callable instance.
    instance_fields: brass_hir::InstanceChannel<Vec<String>>,
    /// Resolved `typeof(x)` strings, keyed by call span.
    type_names: HashMap<Span, String>,
    /// Resolved binding types of `typeof`-bearing local annotations.
    typeof_types: HashMap<Span, brass_hir::Type>,
    /// Spans of `expr!` operators with a nullable operand (null propagates as
    /// `Result.Null`); MIR lowering emits the presence-test shape for these.
    null_props: HashSet<Span>,
    /// Resolved type-test patterns (`if v: T`), keyed by the test's span; MIR
    /// lowering embeds each into the test's rvalue.
    type_tests: HashMap<Span, brass_hir::Type>,
    /// Reflective call sites routed to append-only generated methods.
    keyed_dispatch: HashMap<Span, String>,
    /// Exact-instance aggregate seeds, authoritative over `expr_types`
    /// (see `brass_typeck::stream::aggregate_instance_seeds`).
    instance_seeds: brass_hir::InstanceChannel<brass_hir::Type>,
    /// Reflective call sites whose instances dispatch to different
    /// specializations (span -> instance -> generated method).
    instance_dispatch: brass_hir::InstanceChannel<String>,
    /// The checker's settled returns of unannotated function instances.
    instance_returns: HashMap<(String, Vec<brass_hir::Type>), brass_hir::Type>,
}

impl OwnedChannels {
    fn borrow(&self) -> brass_mir::CheckerChannels<'_> {
        brass_mir::CheckerChannels {
            selected_bodies: self.selected_bodies.as_deref(),
            expr_types: &self.expr_types,
            receiver_types: &self.receiver_types,
            receiver_owners: &self.receiver_owners,
            view_args: &self.view_args,
            numeric_calls: &self.numeric_calls,
            field_calls: &self.field_calls,
            sum_views: &self.sum_views,
            call_locations: &self.call_locations,
            lift_errs: &self.lift_errs,
            fields_loops: &self.fields_loops,
            instance_fields: &self.instance_fields,
            type_names: &self.type_names,
            typeof_types: &self.typeof_types,
            null_props: &self.null_props,
            type_tests: &self.type_tests,
            keyed_dispatch: &self.keyed_dispatch,
            instance_seeds: &self.instance_seeds,
            instance_dispatch: &self.instance_dispatch,
            instance_returns: &self.instance_returns,
        }
    }
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
    // check eagerly on this thread.
    if cfg!(jit_backend) && matches!(mode, Mode::Run { eager: false }) {
        return run_lazy(file.to_string(), main_src, root);
    }
    let locations = match mode {
        Mode::Check => LocationTables::Omit,
        Mode::Run { .. } | Mode::Repl => LocationTables::Execution,
    };
    let checked = match analyze(file, &main_src, &root, locations) {
        Ok(c) => c,
        Err(diagnostics) => return Err(print_diags(diagnostics)),
    };

    match mode {
        // Silence on success, as a checker in a pipeline should be: the exit code
        // carries the answer, and anything on stdout is noise an editor or a script
        // has to filter out.
        Mode::Check => Ok(()),
        Mode::Run { .. } => execute(&checked.program, &checked.channels()).map_err(|e| {
            report_runtime_error(&e);
            1
        }),
        Mode::Repl => execute_repl(&checked.program, &checked.channels()).map_err(|e| {
            report_runtime_error(&e);
            1
        }),
    }
}

/// The context seed for `ctx` (every module except the entry): the tables of
/// a context-only analysis, which the full check then reuses so only the entry
/// is re-inferred. A context with diagnostics retains only modules outside the
/// diagnostic modules' importer closure.
fn context_seed(
    ctx: &[LoadedModule],
    sources: &brass_resolve::SourceMap,
    phase_name: &'static str,
) -> Option<brass_typeck::ContextTables> {
    let t = std::time::Instant::now();
    let (ctx_program, ctx_errors) = brass_hir::lower_context(ctx);
    let analysis = brass_typeck::analyze_with(&ctx_program, None);
    for error in analysis.errors.iter().take(5) {
        tracing::debug!(
            target: "brass::perf",
            "context diagnostic: {} @ {:?}",
            error.message,
            error.span
        );
    }
    let diagnostic_spans = ctx_errors
        .iter()
        .map(|error| error.span)
        .chain(analysis.errors.iter().map(|error| error.span));
    let seed = retain_diagnostic_free_context(
        ctx,
        sources,
        &ctx_program,
        analysis.context_tables,
        diagnostic_spans,
    );
    brass_utils::perf_phase(phase_name, t.elapsed());
    seed
}

/// The source-map base encoded by the `_PATH` declaration injected at the
/// start of every loaded module.
fn module_source_base(module: &LoadedModule) -> Option<usize> {
    match module.ast.items.first()? {
        TopLevel::Stmt(Stmt::Let {
            pat: brass_parser::ast::Pattern::Binding(name, _, span),
            is_const: true,
            ..
        }) if name == brass_resolve::MODULE_PATH_CONST => Some(span.lo),
        _ => None,
    }
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

/// Modules outside `dirty` and every transitive importer of a dirty module.
/// A dirty implicit-prelude module affects every module without an explicit
/// import edge, so none can be retained in that case.
fn context_modules_outside_dirty_closure(
    ctx: &[LoadedModule],
    mut dirty: HashSet<String>,
) -> HashSet<Vec<String>> {
    if dirty.is_empty() {
        return ctx.iter().map(|m| m.path.clone()).collect();
    }
    if ctx
        .iter()
        .any(|m| m.is_prelude && dirty.contains(&m.path.join(".")))
    {
        return HashSet::default();
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

/// Keep tables only for modules with no attributed diagnostic and no import
/// path to one. If any diagnostic cannot be attributed to a source module, no
/// partial seed is safe to advertise.
fn retain_diagnostic_free_context(
    ctx: &[LoadedModule],
    sources: &brass_resolve::SourceMap,
    program: &brass_hir::Program,
    mut tables: brass_typeck::ContextTables,
    diagnostics: impl IntoIterator<Item = Span>,
) -> Option<brass_typeck::ContextTables> {
    let mut dirty = HashSet::default();
    for span in diagnostics {
        dirty.insert(module_path_at(ctx, sources, span.lo)?.join("."));
    }
    if dirty.is_empty() {
        return Some(tables);
    }
    let keep = context_modules_outside_dirty_closure(ctx, dirty);
    if keep.is_empty() || !tables.retain_modules(program, &keep) {
        return None;
    }
    tracing::debug!(
        target: "brass::perf",
        kept = keep.len(),
        total = ctx.len(),
        "retaining diagnostic-free context modules"
    );
    Some(tables)
}

/// A finished front-end analysis in thread-transportable form: the unchanged
/// module graph, append-only generated declarations, and checker channels.
/// HIR holds `Rc`, so a checked `Program` cannot cross the checker-thread
/// boundary; the receiver rebuilds it from the modules with
/// [`assemble_checked`].
pub(crate) struct AnalyzedProgram {
    modules: Vec<LoadedModule>,
    generated: Vec<brass_hir::GeneratedDecl>,
    channels: OwnedChannels,
}

/// Re-lower an analysis result into an executable [`Checked`] program.
/// Lowering is deterministic, so the rebuilt HIR carries the same spans and
/// type ids the channels are keyed by. A clean analysis re-lowers cleanly; an
/// error here means a driver bug.
fn assemble_checked(analyzed: AnalyzedProgram) -> Result<Checked, Vec<String>> {
    let (mut program, lower_errors) = lower(&analyzed.modules);
    if !lower_errors.is_empty() {
        return Err(lower_errors
            .into_iter()
            .map(|e| format!("error: {}", e.message))
            .collect());
    }
    if let Err(lower_errors) = brass_hir::lower_generated_into(&mut program, &analyzed.generated) {
        return Err(lower_errors
            .into_iter()
            .map(|e| format!("error: {}", e.message))
            .collect());
    }
    Ok(Checked {
        program,
        channels: analyzed.channels,
    })
}

/// Parse, resolve the module graph, lower, and statically check `main_src` (a
/// program whose label is `main_label`, imports resolved relative to `root`)
/// on the calling thread. Returns the checked program or the rendered
/// diagnostics. Shared by eager file execution and the interactive REPL, so
/// both report identical errors.
pub(crate) fn analyze(
    main_label: &str,
    main_src: &str,
    root: &Path,
    locations: LocationTables,
) -> Result<Checked, Vec<String>> {
    assemble_checked(analyze_fresh(main_label, main_src, root, locations, None)?)
}

/// Render diagnostics to stderr and yield the front end's failure exit code.
pub(crate) fn print_diags(diags: Vec<String>) -> u8 {
    for d in diags {
        eprintln!("{d}");
    }
    1
}

/// Interpreter-only builds never take the lazy path (`drive` gates it on
/// `jit_backend`); this stand-in keeps them compiling and, if ever reached,
/// behaves exactly like an eager run.
#[cfg(not(jit_backend))]
fn run_lazy(label: String, src: String, root: PathBuf) -> Result<(), u8> {
    let checked = match analyze(&label, &src, &root, LocationTables::Execution) {
        Ok(c) => c,
        Err(diags) => return Err(print_diags(diags)),
    };
    execute(&checked.program, &checked.channels()).map_err(|e| {
        report_runtime_error(&e);
        1
    })
}

/// The full front-end pipeline on the calling thread: parse, resolve, lower,
/// and statically check. Returns the analysis in thread-transportable form
/// ([`AnalyzedProgram`]); the executable program is rebuilt from it with
/// [`assemble_checked`].
///
/// With a scheduler, the type check streams its progress through it (see
/// `brass_typeck::stream`). Keyed continuations append generated declarations
/// and publish their dispatch/channel delta without invalidating prior events.
fn analyze_fresh(
    main_label: &str,
    main_src: &str,
    root: &Path,
    locations: LocationTables,
    sched: Option<&mut dyn brass_typeck::stream::Scheduler>,
) -> Result<AnalyzedProgram, Vec<String>> {
    let search = brass_resolve::SearchPaths::from_env();
    let (front, prepared) = front_load(main_label, main_src, root, &search)?;
    check_front(front, prepared, &search, locations, sched)
}

/// The assembled front end, ready to check: the final module graph
/// (post-resolution, post-rewrite), its sources, and what the front passes
/// reported. Everything here is thread-transportable and clonable, so the
/// lazy runner can keep one copy to execute and hand an identical one to the
/// checker thread -- assembling once instead of parsing the program twice.
#[derive(Clone)]
pub(crate) struct FrontEnd {
    /// Stable selected request carried across the checker thread boundary.
    selection: Option<std::sync::Arc<brass_typeck::reachability::CheckSelection>>,
    modules: Vec<LoadedModule>,
    sources: brass_resolve::SourceMap,
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
/// errors. Also prints the spawn warnings, once, unless a spawn was rejected.
pub(crate) fn front_load(
    main_label: &str,
    main_src: &str,
    root: &Path,
    search: &brass_resolve::SearchPaths,
) -> Result<(FrontEnd, Option<Box<item_preparation::Prepared>>), Vec<String>> {
    let t = std::time::Instant::now();
    let entry_path = PathBuf::from(main_label);
    let front = brass_resolve::frontend::assemble_recovered(&entry_path, main_src, root, search);
    // A prelude parse failure is a build bug; nothing else can be trusted.
    if let Some(message) = front.stdlib_error {
        return Err(vec![message]);
    }
    let item_check = item_preparation::has_dependencies(&front.modules);
    let sources = front.sources;
    if tracing::enabled!(target: "brass::item_selection", tracing::Level::TRACE)
        && !front.parse_errors.is_empty()
    {
        item_shadow::syntax(&front.modules, &sources, &front.parse_errors);
    }
    if !front.parse_errors.is_empty() {
        return Err(render_errors(&front.parse_errors, &sources));
    }
    if !front.load_errors.is_empty() && !item_check {
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
    // The pass may reject a `spawn` it cannot analyze (or a task that reassigns
    // a capture); those diagnostics join the analysis errors, and the ownership
    // warnings -- which describe how an accepted spawn is compiled -- are then
    // withheld.
    let prepared = if item_check {
        Some(item_preparation::front(
            &mut modules,
            &sources,
            &mut errors,
            front.load_errors,
        )?)
    } else {
        #[cfg(jit_backend)]
        {
            let (spawn_errors, warnings, _) = auto_acquire_modules::<false>(&mut modules, None);
            if spawn_errors.is_empty() {
                for warning in warnings {
                    eprintln!("{warning}");
                }
            }
            errors.extend(spawn_errors);
        }
        None
    };

    if tracing::enabled!(target: "brass::item_selection", tracing::Level::TRACE) {
        item_shadow::observe(&modules, &entry_path);
    }

    let selection = prepared.as_ref().map(|p| p.view.selection().clone());
    Ok((
        FrontEnd {
            selection,
            modules,
            sources,
            errors,
        },
        prepared,
    ))
}

/// Statically check an assembled front end and package the result: the check
/// half of [`analyze_fresh`], and what the lazy runner's checker thread
/// executes over its copy of the modules.
pub(crate) fn check_front(
    front: FrontEnd,
    prepared: Option<Box<item_preparation::Prepared>>,
    search: &brass_resolve::SearchPaths,
    locations: LocationTables,
    mut sched: Option<&mut dyn brass_typeck::stream::Scheduler>,
) -> Result<AnalyzedProgram, Vec<String>> {
    let phase = |name: &'static str, at: std::time::Instant| {
        brass_utils::perf_phase(name, at.elapsed());
    };
    let streaming = sched.is_some();
    let FrontEnd {
        selection,
        modules,
        sources,
        errors: front_errors,
    } = front;

    // The context seed: the analysis tables of every module EXCEPT the entry
    // (the last one loaded), reused so the full check below re-infers only the
    // entry. A context with diagnostics yields no seed (or a partial one), and
    // the full run reports every diagnostic itself.
    let ctx_end = modules.len() - 1;
    // Dependency selection needs the combined catalog before context preparation.
    let selected = prepared.or_else(|| {
        selection.map(|selection| {
            let started = std::time::Instant::now();
            let lowered = lower(&modules);
            brass_utils::perf_phase("item/checker-hir", started.elapsed());
            let view = brass_typeck::reachability::AnalysisView::with_selection(
                &lowered.0,
                selection,
                Default::default(),
                Default::default(),
            );
            Box::new(item_preparation::Prepared { lowered, view })
        })
    });
    let ctx_seed = match &selected {
        Some(prepared) => {
            item_preparation::context_seed(&modules[..ctx_end], &sources, prepared.view.selection())
        }
        None => context_seed(&modules[..ctx_end], &sources, "front/context-check"),
    };

    tracing::debug!(modules = modules.len(), "lowering module graph to HIR");
    let t = std::time::Instant::now();
    let (lowered, view) = selected.map_or_else(
        || (lower(&modules), None),
        |prepared| (prepared.lowered, Some(prepared.view)),
    );
    let (program, lower_errors) = lowered;
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
        Some(s) => match &view {
            Some(view) => {
                brass_typeck::analyze_streaming_selected(&program, ctx_seed.as_ref(), s, view)
            }
            None => brass_typeck::analyze_streaming(&program, ctx_seed.as_ref(), s),
        },
        None => match &view {
            Some(view) => brass_typeck::analyze_selected(&program, ctx_seed.as_ref(), view),
            None => brass_typeck::analyze_with(&program, ctx_seed.as_ref()),
        },
    };
    phase("front/typecheck", t);
    if tracing::enabled!(target: "brass::item_selection", tracing::Level::TRACE) {
        item_shadow::diagnostics(&program, &analysis.errors, &analysis.warnings);
    }
    // Reflective decoders are appended directly to this HIR. The continuation
    // checker reuses the completed first pass's tables and visits only the new
    // method bodies; source ASTs and existing HIR items remain untouched.
    let mut program = program;
    let (generated, keyed_dispatch, instance_dispatch) = if analysis.keyed_calls.is_empty()
        || sched.as_deref().is_some_and(|s| s.stopped())
    {
        (Vec::new(), HashMap::default(), HashMap::default())
    } else {
        let t = std::time::Instant::now();
        match specialize_keyed(&mut program, &mut analysis) {
            Ok((generated, keyed_dispatch, instance_dispatch)) => {
                phase("front/keyed-continuation", t);
                if let Some(s) = sched {
                    if let Some(view) = &analysis.context_tables.items {
                        s.emit(brass_typeck::stream::CheckEvent::SelectedBodies(
                            view.body_spans().clone(),
                        ));
                    }
                    let mut delta = analysis_channel_delta(&analysis, &program);
                    delta.instance_dispatch = instance_dispatch
                        .iter()
                        .map(|(span, targets)| {
                            (
                                *span,
                                targets
                                    .iter()
                                    .map(|(instance, target)| (instance.clone(), target.clone()))
                                    .collect(),
                            )
                        })
                        .collect();
                    delta.errors.extend(errors.iter().map(|(message, span)| {
                        brass_typeck::TypeError {
                            message: message.clone(),
                            span: *span,
                        }
                    }));
                    s.emit(brass_typeck::stream::CheckEvent::KeyedReady(
                        generated.clone(),
                        keyed_dispatch
                            .iter()
                            .map(|(span, symbol)| (*span, symbol.clone()))
                            .collect(),
                        delta,
                    ));
                }
                (generated, keyed_dispatch, instance_dispatch)
            }
            Err(error) => {
                // A streaming consumer cannot observe this function's
                // returned Result while executing a runtime demand. Send
                // the final snapshot so provisional errors removed by
                // specialization cannot survive in the consumer either.
                if let Some(s) = sched {
                    if let Some(view) = &analysis.context_tables.items {
                        s.emit(brass_typeck::stream::CheckEvent::SelectedBodies(
                            view.body_spans().clone(),
                        ));
                    }
                    let mut delta = analysis_channel_delta(&analysis, &program);
                    delta
                        .errors
                        .extend(errors.iter().chain(std::iter::once(&error)).map(
                            |(message, span)| brass_typeck::TypeError {
                                message: message.clone(),
                                span: *span,
                            },
                        ));
                    s.emit(brass_typeck::stream::CheckEvent::KeyedReady(
                        Vec::new(),
                        Vec::new(),
                        delta,
                    ));
                }
                errors.push(error);
                (Vec::new(), HashMap::default(), HashMap::default())
            }
        }
    };
    for e in &analysis.errors {
        errors.push((e.message.clone(), e.span));
    }
    let mut checker_warnings: Vec<(String, Span)> = analysis
        .warnings
        .iter()
        .map(|warning| (warning.message.clone(), warning.span))
        .collect();
    checker_warnings.sort_by(|a, b| (a.1.lo, &a.0).cmp(&(b.1.lo, &b.0)));
    checker_warnings.dedup();
    // A streaming consumer prints warnings as their body deltas arrive.
    if !streaming {
        for warning in render_warnings(&checker_warnings, &sources) {
            eprintln!("{warning}");
        }
    }
    tracing::debug!(errors = errors.len(), "front-end analysis complete");
    if !errors.is_empty() {
        errors.sort_by(|a, b| (a.1.lo, &a.0).cmp(&(b.1.lo, &b.0)));
        errors.dedup();
        return Err(render_errors(&errors, &sources));
    }

    let expr_types = brass_typeck::stream::aggregate_result_types(&analysis.typed, &program);
    let instance_seeds = brass_typeck::stream::aggregate_instance_seeds(
        &analysis.instance_typed,
        &analysis.typed,
        &program,
    );
    let receiver_types = brass_typeck::stream::method_receiver_types(&analysis.typed, &program);
    let receiver_owners = brass_typeck::stream::method_receiver_owners(&analysis.typed, &program);
    let call_locations = match locations {
        LocationTables::Execution => call_site_locations(&modules, &sources, search),
        LocationTables::Omit => HashMap::default(),
    };
    let channels = OwnedChannels {
        selected_bodies: analysis
            .context_tables
            .items
            .as_ref()
            .map(|v| v.body_spans().clone()),
        expr_types,
        instance_seeds,
        receiver_types,
        receiver_owners,
        view_args: analysis.view_args,
        numeric_calls: analysis.numeric_calls,
        field_calls: analysis.field_calls,
        sum_views: analysis.sum_views,
        call_locations,
        lift_errs: analysis.lift_errs,
        fields_loops: analysis.fields_loops,
        instance_fields: analysis.instance_fields,
        type_names: analysis.type_names,
        typeof_types: analysis.typeof_types,
        null_props: analysis.null_props,
        type_tests: analysis.type_tests,
        keyed_dispatch,
        instance_dispatch,
        instance_returns: analysis.instance_returns,
    };
    Ok(AnalyzedProgram {
        modules,
        generated,
        channels,
    })
}

/// Snapshot the completed analysis as one overwrite-safe streaming delta.
/// Used only for the generated-body continuation, after the first pass has
/// already flushed its own incremental windows.
fn analysis_channel_delta(
    analysis: &brass_typeck::Analysis,
    program: &Program,
) -> brass_typeck::stream::ChannelDelta {
    let expr_types = brass_typeck::stream::aggregate_result_types(&analysis.typed, program);
    let instance_seeds = brass_typeck::stream::aggregate_instance_seeds(
        &analysis.instance_typed,
        &analysis.typed,
        program,
    )
    .into_iter()
    .map(|(span, seeds)| (span, seeds.into_iter().collect()))
    .collect();
    brass_typeck::stream::ChannelDelta {
        expr_types: expr_types.into_iter().collect(),
        instance_seeds,
        receiver_types: brass_typeck::stream::method_receiver_types(&analysis.typed, program)
            .into_iter()
            .collect(),
        receiver_owners: brass_typeck::stream::method_receiver_owners(&analysis.typed, program)
            .into_iter()
            .collect(),
        view_args: analysis.view_args.iter().copied().collect(),
        numeric_calls: analysis
            .numeric_calls
            .iter()
            .map(|(key, ty)| (key.clone(), ty.clone()))
            .collect(),
        field_calls: analysis
            .field_calls
            .iter()
            .map(|(span, receivers)| (*span, receivers.clone()))
            .collect(),
        lift_errs: analysis.lift_errs.iter().copied().collect(),
        null_props: analysis.null_props.iter().copied().collect(),
        instance_fields: analysis
            .instance_fields
            .iter()
            .map(|(s, es)| (*s, es.iter().map(|(k, v)| (k.clone(), v.clone())).collect()))
            .collect(),
        fields_loops: analysis
            .fields_loops
            .iter()
            .map(|(span, fields)| (*span, fields.clone()))
            .collect(),
        sum_views: analysis
            .sum_views
            .iter()
            .map(|(span, ty)| (*span, ty.clone()))
            .collect(),
        type_names: analysis
            .type_names
            .iter()
            .map(|(span, name)| (*span, name.clone()))
            .collect(),
        typeof_types: analysis
            .typeof_types
            .iter()
            .map(|(span, ty)| (*span, ty.clone()))
            .collect(),
        type_tests: analysis
            .type_tests
            .iter()
            .map(|(span, ty)| (*span, ty.clone()))
            .collect(),
        errors: analysis.errors.clone(),
        warnings: analysis.warnings.clone(),
        ..Default::default()
    }
}

/// What [`specialize_keyed`] produces: the generated declarations, the keyed
/// call sites every instance routes to one specialization (span -> generated
/// method), and those whose instances route to different ones (span ->
/// instance -> generated method).
type KeyedSpecializationResult = (
    Vec<brass_hir::GeneratedDecl>,
    HashMap<Span, String>,
    brass_hir::InstanceChannel<String>,
);

/// Append and check every keyed specialization requested by `analysis`.
/// Nested requests discovered while checking generated bodies repeat the same
/// append-only step; already generated `(receiver, method, key)` triples make
/// the loop finite for recursive type graphs.
fn specialize_keyed(
    program: &mut Program,
    analysis: &mut brass_typeck::Analysis,
) -> Result<KeyedSpecializationResult, (String, Span)> {
    let mut seed = analysis.context_tables.clone();
    let mut pending = analysis.keyed_calls.clone();
    let mut pending_instances = analysis.instance_keyed_calls.clone();
    let keyed_spans: HashSet<Span> = pending.keys().copied().collect();
    let provisional_spans = keyed_provisional_spans(program, &keyed_spans);
    // A keyed call is initially elaborated against the generic template, so
    // constraints from a second key can leave a provisional error at that
    // call span. The generated-body continuation is the verdict for those
    // sites; discovery errors that prevented recording a key are unaffected.
    remove_provisional_keyed_diagnostics(&mut analysis.errors, &provisional_spans);
    let mut generated_all = Vec::new();
    let mut generated_symbols = fxhash::FxHashSet::default();
    let mut keyed_dispatch = HashMap::default();
    let mut instance_dispatch: brass_hir::InstanceChannel<String> = HashMap::default();

    for _ in 0..64 {
        if pending.is_empty() && pending_instances.is_empty() {
            return Ok((generated_all, keyed_dispatch, instance_dispatch));
        }
        // A call whose instances key it differently dispatches per instance;
        // its span-level entry only marks it reflective.
        for (span, per_instance) in &pending_instances {
            keyed_dispatch.remove(span);
            let targets = instance_dispatch.entry(*span).or_default();
            for (instance, (_, method, key)) in per_instance {
                targets.insert(instance.clone(), brass_typesys::mangled_name(method, key));
            }
        }
        for (span, (_, method, key)) in &pending {
            if !instance_dispatch.contains_key(span) {
                keyed_dispatch.insert(*span, brass_typesys::mangled_name(method, key));
            }
        }
        let mut roots: Vec<brass_typesys::KeyedNeed> = pending
            .values()
            .chain(
                pending_instances
                    .values()
                    .flat_map(|targets| targets.values()),
            )
            .map(|(recv, method, key)| brass_typesys::KeyedNeed {
                recv: recv.clone(),
                method: method.clone(),
                key: key.clone(),
            })
            .collect();
        roots.sort_by(|a, b| {
            (&a.recv, &a.method, brass_hir::type_key(&a.key)).cmp(&(
                &b.recv,
                &b.method,
                brass_hir::type_key(&b.key),
            ))
        });
        roots.dedup_by(|a, b| {
            a.recv == b.recv
                && a.method == b.method
                && brass_hir::type_key(&a.key) == brass_hir::type_key(&b.key)
        });
        let generated = brass_typesys::specialize_all(program, &roots).map_err(|error| {
            (
                format!("reflective specialization failed: {error}"),
                Span::new(0, 0),
            )
        })?;
        let fresh: Vec<_> = generated
            .into_iter()
            .filter(|generated| {
                generated_symbols.insert(format!(
                    "{}.{}.{}:{}",
                    generated.module.join("."),
                    generated.receiver,
                    generated.template,
                    brass_hir::type_key(&generated.key)
                ))
            })
            .collect();
        if fresh.is_empty() {
            return Err((
                "reflective specialization failed: recursive specialization made no progress"
                    .to_string(),
                Span::new(0, 0),
            ));
        }
        brass_hir::lower_generated_into(program, &fresh).map_err(|errors| {
            let error = &errors[0];
            (error.message.clone(), brass_hir::unshift_span(error.span))
        })?;
        if let Some(view) = &seed.items {
            seed.items = Some(view.with_generated(program, &fresh));
            analysis.context_tables.items = seed.items.clone();
        }
        let mut next_pending = HashMap::default();
        let mut next_pending_instances: brass_hir::InstanceChannel<_> = HashMap::default();
        for generated in &fresh {
            let continuation =
                brass_typeck::analyze_generated(program, &seed, std::slice::from_ref(generated));
            next_pending.extend(continuation.keyed_calls.clone());
            next_pending_instances.extend(continuation.instance_keyed_calls.clone());
            analysis.keyed_calls.extend(continuation.keyed_calls);
            analysis
                .instance_keyed_calls
                .extend(continuation.instance_keyed_calls);
            let typed_offset = analysis.typed.expressions.len();
            analysis
                .typed
                .expressions
                .extend(continuation.typed.expressions);
            analysis
                .instance_typed
                .append(continuation.instance_typed, typed_offset);
            analysis.view_args.extend(continuation.view_args);
            analysis.numeric_calls.extend(continuation.numeric_calls);
            analysis.field_calls.extend(continuation.field_calls);
            analysis.sum_views.extend(continuation.sum_views);
            analysis.lift_errs.extend(continuation.lift_errs);
            analysis.fields_loops.extend(continuation.fields_loops);
            analysis
                .instance_fields
                .extend(continuation.instance_fields);
            analysis.type_names.extend(continuation.type_names);
            analysis.typeof_types.extend(continuation.typeof_types);
            analysis.type_tests.extend(continuation.type_tests);
            analysis.null_props.extend(continuation.null_props);
            analysis
                .errors
                .extend(continuation.errors.into_iter().map(|mut error| {
                    error.span = brass_hir::unshift_span(error.span);
                    error
                }));
            analysis
                .warnings
                .extend(continuation.warnings.into_iter().map(|mut warning| {
                    warning.span = brass_hir::unshift_span(warning.span);
                    warning.message =
                        brass_typeck::remap_diagnostic_source_offsets(&warning.message, |offset| {
                            brass_hir::unshift_span(Span::new(offset, offset)).lo
                        });
                    warning
                }));
        }
        pending = next_pending;
        pending_instances = next_pending_instances;
        generated_all.extend(fresh);
    }
    Err((
        "reflective specialization failed: specialization depth exceeded".to_string(),
        Span::new(0, 0),
    ))
}

/// Source spans at which first-pass keyed result-flow diagnostics can land: the
/// call itself or its owning statement's required-type check.
fn keyed_provisional_spans(program: &Program, keyed: &HashSet<Span>) -> HashSet<Span> {
    let mut spans = keyed.clone();
    let mut inspect = |stmt: &Stmt| {
        let mut calls = Vec::new();
        collect_call_spans_stmt(stmt, &mut calls);
        if calls.iter().any(|span| keyed.contains(span)) {
            spans.insert(stmt.span());
        }
    };
    for function in program.functions.values() {
        function.decl.body.stmts.iter().for_each(&mut inspect);
    }
    for init in &program.inits {
        init.stmts.iter().for_each(&mut inspect);
    }
    for info in program.types.values() {
        match &info.kind {
            brass_hir::TypeKind::Record { methods, .. } => methods
                .values()
                .filter_map(|method| method.decl.body.as_ref())
                .flat_map(|body| &body.stmts)
                .for_each(&mut inspect),
            brass_hir::TypeKind::Sum { variants } => variants
                .iter()
                .flat_map(|variant| variant.methods.values())
                .filter_map(|method| method.decl.body.as_ref())
                .flat_map(|body| &body.stmts)
                .for_each(&mut inspect),
        }
    }
    spans
}

/// Remove only required-type mismatches emitted by the keyed call's provisional
/// first-pass result. Other diagnostics at the same span remain actionable.
fn remove_provisional_keyed_diagnostics(
    errors: &mut Vec<brass_typeck::TypeError>,
    provisional_spans: &HashSet<Span>,
) {
    errors.retain(|error| {
        let provisional_flow = (error.message.starts_with("cannot use `")
            && error.message.contains("` where `")
            && error.message.ends_with("` is required"))
            || error.message.starts_with("cannot implicitly convert `");
        !provisional_flow || !provisional_spans.contains(&error.span)
    });
}

/// Print a runtime failure. A message that is already a rendered error trace
/// (the prelude's unhandled-`!` rendering, whose lines carry their own
/// `[file:line:col] unhandled error:` framing) prints verbatim; every other
/// failure uses the same `runtime error:` prefix as the native runtime.
pub(crate) fn report_runtime_error(e: &str) {
    if e.starts_with('[') && e.contains("unhandled error:") {
        eprintln!("{e}");
    } else {
        eprintln!("runtime error: {e}");
    }
}

/// Render each `(message, span)` diagnostic as `path:line:col: error: message`,
/// locating the span's file by its globally-unique offset (or a bare `error:`
/// line when no source contains it).
/// Render source-attributed errors in their supplied order.
pub(crate) fn render_errors(
    errors: &[(String, Span)],
    sources: &brass_resolve::SourceMap,
) -> Vec<String> {
    render_diagnostics(errors, sources, "error")
}

/// Render source-attributed warnings in their supplied order.
pub(crate) fn render_warnings(
    warnings: &[(String, Span)],
    sources: &brass_resolve::SourceMap,
) -> Vec<String> {
    render_diagnostics(warnings, sources, "warning")
}

fn render_diagnostics(
    items: &[(String, Span)],
    sources: &brass_resolve::SourceMap,
    level: &str,
) -> Vec<String> {
    let mut out = Vec::with_capacity(items.len());
    for (msg, span) in items {
        let msg = brass_typeck::render_diagnostic_message(msg, |offset| {
            let loc = sources.locate(offset)?;
            let (line, col) = loc.line_col();
            Some(format!("{}:{line}:{col}", loc.label))
        });
        match sources.locate(span.lo) {
            Some(loc) => {
                let (line, col) = loc.line_col();
                out.push(format!("{}:{line}:{col}: {level}: {msg}", loc.label));
            }
            None => out.push(format!("{level}: {msg}")),
        }
    }
    out
}

// ===== interactive REPL =====

/// Run an interactive REPL session. Top-level definitions (functions, types,
/// imports) and statements accumulate for static checking. Each accepted input
/// executes once; the earlier statements that only rebuild values -- bindings
/// and updates free of side effects -- run again ahead of it to provide the
/// values it reads (see [`repl_replay::plan`]). A bare expression is echoed by
/// wrapping it in `println`.
fn repl_interactive() -> ExitCode {
    let root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let stdin = io::stdin();
    eprintln!("brass REPL -- enter definitions or statements; Ctrl-D to exit.");

    let mut defs: Vec<String> = Vec::new();
    let mut body: Vec<String> = Vec::new();

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
            match check_capture(&defs, &body, &root) {
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
            body.push(cand.clone());
            let session = match check_capture(&defs, &body, &root) {
                Ok(checked) => checked,
                Err(e) => {
                    body.pop();
                    last_err = e;
                    continue;
                }
            };

            let replay = repl_replay::plan(&body[..body.len() - 1], &session.program);
            let mut execution = replay.statements.clone();
            execution.push(cand);
            let execution = match check_capture(&defs, &execution, &root) {
                Ok(checked) => checked,
                Err(e) => {
                    body.pop();
                    last_err = replay.explain(&e).unwrap_or(e);
                    continue;
                }
            };
            if let Err(e) = brass_repl::validate(&execution.program, &execution.channels()) {
                body.pop();
                last_err = e;
                continue;
            }
            match run_checked_capture(&execution) {
                Ok(out) => {
                    print!("{out}");
                    let _ = io::stdout().flush();
                    committed = true;
                }
                Err(e) => {
                    body.pop();
                    last_err = e;
                }
            }
            // Once a statically valid candidate has run, trying another form
            // could execute the entered expression a second time.
            break;
        }
        if !committed {
            eprintln!("{last_err}");
        }
    }
    ExitCode::SUCCESS
}

/// Interpret one already checked and runtime-supported candidate, capturing
/// `print`/`println` output.
fn run_checked_capture(checked: &Checked) -> Result<String, String> {
    let mut buf: Vec<u8> = Vec::new();
    brass_repl::run(&checked.program, &checked.channels(), &mut buf)?;
    Ok(String::from_utf8_lossy(&buf).into_owned())
}

/// Check an accumulated REPL program without evaluating it.
fn check_capture(defs: &[String], body: &[String], root: &Path) -> Result<Checked, String> {
    let src = assemble(defs, body);
    analyze("<repl>", &src, root, LocationTables::Execution).map_err(|d| d.join("\n"))
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
            let has_definition = !m.imports.is_empty()
                || m.items
                    .iter()
                    .any(|i| matches!(i, TopLevel::Fun(_) | TopLevel::Type(_)));
            has_definition
                && m.items
                    .iter()
                    .all(|i| matches!(i, TopLevel::Fun(_) | TopLevel::Type(_)))
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
    use super::{
        Cli, Command, item_shadow, module_path_at, program_file_index,
        remove_provisional_keyed_diagnostics, retain_diagnostic_free_context,
    };
    use brass_hir::LoadedModule;
    use brass_parser::Span;
    use brass_parser::ast::Module;
    use clap::Parser;
    use std::ffi::OsString;
    use std::path::PathBuf;

    fn argv(args: &[&str]) -> Vec<OsString> {
        std::iter::once("brass")
            .chain(args.iter().copied())
            .map(OsString::from)
            .collect()
    }

    #[test]
    fn explicit_project_root_uses_only_the_cold_cli_extension() {
        for args in [
            argv(&["--project-root", "/package", "check", "main.cz"]),
            argv(&["check", "main.cz", "--project-root=/package"]),
        ] {
            let error = match Cli::try_parse_from(&args) {
                Ok(_) => panic!("ordinary parser unexpectedly contains project metadata"),
                Err(error) => error,
            };
            let cli = item_shadow::parse_project_cli(&args, error);
            assert!(matches!(cli.command, Some(Command::Check { file }) if file == "main.cz"));
            assert_eq!(
                item_shadow::PROJECT_ROOT.get(),
                Some(&PathBuf::from("/package"))
            );
        }
    }

    #[test]
    fn project_root_is_driver_input_only_before_the_program_file() {
        for (args, expected) in [
            (
                vec![
                    "--project-root",
                    "/package",
                    "main.cz",
                    "--project-root",
                    "arg",
                ],
                Some(3),
            ),
            (vec!["--project-root=/package", "main.cz"], Some(2)),
            (
                vec!["repl", "--project-root", "/package", "main.cz"],
                Some(4),
            ),
            (vec!["--project-root", "/package", "check", "main.cz"], None),
        ] {
            assert_eq!(program_file_index(&argv(&args)), expected);
        }
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
    fn keyed_cleanup_preserves_nearby_diagnostics() {
        // Only the diagnostic emitted at the provisional call span is removed.
        let keyed = Span::new(10, 15);
        let nearby = Span::new(17, 22);
        let mut errors = vec![
            brass_typeck::TypeError {
                message: "cannot use `int64` where `string` is required".into(),
                span: keyed,
            },
            brass_typeck::TypeError {
                message: "independent error".into(),
                span: keyed,
            },
            brass_typeck::TypeError {
                message: "independent".into(),
                span: nearby,
            },
        ];
        remove_provisional_keyed_diagnostics(&mut errors, &fxhash::FxHashSet::from_iter([keyed]));

        assert_eq!(errors.len(), 2);
        assert!(errors.iter().any(|error| error.span == keyed));
        assert!(errors.iter().any(|error| error.span == nearby));
    }

    #[test]
    fn option_terminator_makes_subcommand_words_file_names() {
        // After `--`, clap treats every token positionally. The manual split
        // must make the same choice or a file literally named `repl` is lost.
        for word in ["repl", "check", "cache", "help"] {
            assert_eq!(program_file_index(&argv(&["--", word, "arg"])), Some(2));
        }
        assert_eq!(program_file_index(&argv(&["cache", "info"])), None);
        assert_eq!(
            program_file_index(&argv(&["--no-jit-cache", "cache", "info"])),
            None
        );
    }

    fn loaded(path: &str, base: usize) -> LoadedModule {
        let mut ast = Module {
            imports: Vec::new(),
            items: Vec::new(),
        };
        brass_resolve::inject_module_path(&mut ast, path, Span::new(base, base));
        LoadedModule {
            source: None,
            is_prelude: false,
            path: vec![path.to_string()],
            ast,
        }
    }

    #[test]
    fn module_ownership_follows_source_bases_not_module_order() {
        // Recursive loading records a parent source before its dependency but
        // appends the dependency module first. Ownership follows spans.
        let mut sources = brass_resolve::SourceMap::default();
        let a = sources.add(None, "a".to_string(), "source a".to_string());
        let b = sources.add(None, "b".to_string(), "source b".to_string());
        let modules = vec![loaded("b", b), loaded("a", a)];

        assert_eq!(
            module_path_at(&modules, &sources, a + 1),
            Some(vec!["a".into()])
        );
        assert_eq!(
            module_path_at(&modules, &sources, b + 1),
            Some(vec!["b".into()])
        );
    }

    #[test]
    fn context_diagnostic_retains_other_modules() {
        // A diagnostic attributed to one source drops that module while keeping
        // an independent module's tables available as a partial seed.
        let mut sources = brass_resolve::SourceMap::default();
        let a = sources.add(None, "a".to_string(), "source a".to_string());
        let b = sources.add(None, "b".to_string(), "source b".to_string());
        let modules = vec![loaded("a", a), loaded("b", b)];
        let (program, errors) = brass_hir::lower(&modules);
        assert!(errors.is_empty());
        let tables = brass_typeck::context_seed(&program).expect("clean context");

        let seed = retain_diagnostic_free_context(
            &modules,
            &sources,
            &program,
            tables,
            [Span::new(b + 1, b + 1)],
        )
        .expect("one clean module remains");

        assert_eq!(
            seed.covered,
            Some(fxhash::FxHashSet::from_iter([vec!["a".to_string()]]))
        );
    }
}
