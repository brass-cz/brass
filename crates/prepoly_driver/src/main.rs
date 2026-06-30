//! Prepoly command-line driver.
//!
//! Pipeline: resolve the module graph, parse, lower to HIR, check
//! (resolve + typeck), then run the checked program. The standard library is an
//! embedded prelude.
//!
//! Two execution back ends share the same front end. When the JIT back end is
//! available, `prepoly <file>` compiles and runs through the LLVM JIT
//! (`prepoly_jit_llvm`); otherwise the default runtime is the REPL interpreter
//! (`prepoly_repl`). The JIT is available when the default `jit` feature is on AND
//! the target is not wasm (LLVM cannot link for wasm), so a wasm build
//! automatically disables it and falls back to the interpreter -- this is the
//! `jit_backend` cfg from `build.rs`. `prepoly repl [file]` always uses the
//! interpreter: with a file it runs the file, with none it starts an interactive
//! session. Argument parsing is `clap`'s derive interface.

use std::collections::{HashMap, HashSet};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};

use prepoly_hir::{LoadedModule, Program, lower};
use prepoly_lexer::{Span, line_col};
use prepoly_parser::ast::{ImportDecl, Module, Stmt, TopLevel};
use prepoly_parser::{ParseError, parse, parse_with_base};

/// Embedded standard-library modules (implicit prelude).
const STDLIB: &[(&str, &str)] = &[
    ("io", include_str!("../../../std/io.pp")),
    ("array", include_str!("../../../std/array.pp")),
    ("string", include_str!("../../../std/string.pp")),
    ("math", include_str!("../../../std/math.pp")),
    ("conv", include_str!("../../../std/conv.pp")),
    ("assert", include_str!("../../../std/assert.pp")),
];

/// The Prepoly toolchain driver.
///
/// The program file is a bare positional argument (`prepoly file.pp`) rather than
/// a `run` subcommand. A leading `check`/`repl` parses as the subcommand; any
/// other first argument is taken as the file.
#[derive(Parser)]
#[command(name = "prepoly", version, about = "The Prepoly compiler and REPL")]
struct Cli {
    /// A program file to type-check and run with the default runtime (the LLVM JIT
    /// when it is available -- the `jit` feature on a non-wasm target -- otherwise
    /// the REPL interpreter). With neither a file nor a subcommand, the
    /// interactive REPL starts instead.
    file: Option<String>,
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand)]
enum Command {
    /// Type-check a program without running it.
    Check { file: String },
    /// Start the interactive REPL, or run a file through the REPL interpreter.
    Repl { file: Option<String> },
}

/// Which back end / phase `drive` runs after the front end produces a checked
/// program.
enum Mode {
    Run,
    Check,
    Repl,
}

/// Initialize the tracing subscriber from the `PREPOLY_LOG` environment variable.
/// `PREPOLY_LOG` uses `tracing_subscriber`'s `EnvFilter` syntax, so a level
/// (`PREPOLY_LOG=debug`) or per-target directives
/// (`PREPOLY_LOG=prepoly_typeck=debug,prepoly_solver=trace`) both work. Unset or
/// empty, the filter defaults to `warn`, so an ordinary run only surfaces
/// warnings and errors and the compiler's `debug!` traces stay silent. Logs are
/// written to stderr (program output owns stdout) without timestamps, which keeps
/// them readable as a compile trace and avoids a clock call on the wasm build.
/// `try_init` so a second call (e.g. from a test harness) is a no-op rather than a
/// panic.
fn init_tracing() {
    use tracing_subscriber::filter::LevelFilter;
    let filter = tracing_subscriber::EnvFilter::builder()
        .with_default_directive(LevelFilter::WARN.into())
        .with_env_var("PREPOLY_LOG")
        .from_env_lossy();
    let _ = tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_writer(io::stderr)
        .without_time()
        .try_init();
}

fn main() -> ExitCode {
    init_tracing();
    let cli = Cli::parse();
    match cli.command {
        // A bare file argument is type-checked and run; with neither a file nor a
        // subcommand, start an interactive REPL session.
        None => match cli.file {
            Some(file) => exit_code(drive(Mode::Run, &file)),
            None => repl_interactive(),
        },
        Some(Command::Check { file }) => exit_code(drive(Mode::Check, &file)),
        Some(Command::Repl { file: None }) => repl_interactive(),
        Some(Command::Repl { file: Some(file) }) => exit_code(drive(Mode::Repl, &file)),
    }
}

fn exit_code(r: Result<(), u8>) -> ExitCode {
    match r {
        Ok(()) => ExitCode::SUCCESS,
        Err(code) => ExitCode::from(code),
    }
}

/// Apply the spawn auto-acquire transform to every function and
/// method body in each module, before lowering. This rewrites a `spawn` closure
/// that mutates a captured cown to acquire it with `with`, so the source needs no
/// ownership annotations yet concurrent mutation is serialized by the cown lock.
#[cfg(jit_backend)]
fn auto_acquire_modules(modules: &mut [LoadedModule]) {
    use prepoly_jit_llvm::ownership::auto_acquire;
    use prepoly_parser::ast::{Member, TypeBody};

    let names = |params: &[prepoly_parser::ast::Param]| -> HashSet<String> {
        params.iter().map(|p| p.name.clone()).collect()
    };
    for m in modules {
        for item in &mut m.ast.items {
            match item {
                TopLevel::Fun(f) => {
                    let params = names(&f.params);
                    auto_acquire(&mut f.body.stmts, &params);
                }
                TopLevel::Type(t) => {
                    let members = match &mut t.body {
                        TypeBody::Record(members) => members,
                        TypeBody::Sum(_) => continue,
                    };
                    for member in members {
                        if let Member::Method(method) = member
                            && let Some(body) = &mut method.body
                        {
                            let params = names(&method.params);
                            auto_acquire(&mut body.stmts, &params);
                        }
                    }
                }
                TopLevel::Stmt(_) => {}
            }
        }
    }
}

/// Emit a warning for every `spawn` capture the compiler auto-cowns. The shared ownership analysis (`prepoly_jit_llvm::ownership`) decides
/// move/freeze/cown from liveness and mutation; a `Cown` decision means the capture
/// is mutated and still live, so the compiler wraps it for safe concurrent access.
///
/// Runs on the original module ASTs *before* `auto_acquire_modules` rewrites the
/// mutated captures into explicit `with` scopes: the warning must reflect what
/// auto-acquire is about to do, so it has to see the pre-transform source.
#[cfg(jit_backend)]
fn report_spawn_ownership(modules: &[LoadedModule]) {
    use prepoly_jit_llvm::ownership::{CaptureDecision, Ownership, analyze_spawns_stmts};
    use prepoly_parser::ast::{Member, TypeBody};

    fn warn(decisions: Vec<CaptureDecision>, ctx: &str) {
        for d in decisions {
            if d.ownership == Ownership::Cown {
                eprintln!(
                    "warning: variable '{}' is auto-wrapped in cown with \
                     function-level acquire{ctx}",
                    d.var
                );
                eprintln!(
                    "  = note: for finer-grained concurrency, use explicit \
                     'with(cown, (c) -> {{ ... }})'"
                );
            }
        }
    }

    fn param_names(params: &[prepoly_parser::ast::Param]) -> HashSet<String> {
        params.iter().map(|p| p.name.clone()).collect()
    }

    for m in modules {
        let mut init_stmts: Vec<Stmt> = Vec::new();
        for item in &m.ast.items {
            match item {
                TopLevel::Fun(f) => warn(
                    analyze_spawns_stmts(&f.body.stmts, &param_names(&f.params)),
                    &format!(" in `{}`", f.name),
                ),
                TopLevel::Type(t) => {
                    let members = match &t.body {
                        TypeBody::Record(members) => members,
                        TypeBody::Sum(_) => continue,
                    };
                    for member in members {
                        if let Member::Method(method) = member
                            && let Some(body) = &method.body
                        {
                            warn(
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
                analyze_spawns_stmts(&init_stmts, &HashSet::new()),
                &format!(" in module `{}`", m.path.join(".")),
            );
        }
    }
}

/// Make any Rust panic abort the process instead of unwinding. JIT-compiled
/// frames carry no unwind tables, so a panic in a runtime function called from
/// JIT code that unwinds into them is undefined behavior. Aborting in the panic
/// hook -- before unwinding begins -- keeps such a failure well-defined (a clean
/// abort with the panic message). Installed once, only on the JIT execution path;
/// the interpreter is pure Rust and unwinds normally, and the in-process JIT
/// tests call `prepoly_jit_llvm::run` directly without going through here.
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
fn execute(
    program: &Program,
    int_lit_types: &HashMap<Span, prepoly_hir::IntKind>,
) -> Result<(), String> {
    install_jit_panic_guard();
    prepoly_jit_llvm::run(program, int_lit_types)
}

/// Run a checked program through the default runtime: the REPL interpreter, used
/// when the JIT back end is unavailable (no `jit` feature, or a wasm target).
#[cfg(not(jit_backend))]
fn execute(
    program: &Program,
    _int_lit_types: &HashMap<Span, prepoly_hir::IntKind>,
) -> Result<(), String> {
    prepoly_repl::run(program, &mut io::stdout())
}

/// Run a checked program through the REPL interpreter (the `repl` subcommand),
/// regardless of the `jit` feature.
fn execute_repl(program: &Program) -> Result<(), String> {
    prepoly_repl::run(program, &mut io::stdout())
}

/// Resolve each integer literal's source span to its inferred integer kind when
/// that kind is unambiguous across all (re-)inferences, for typed-literal codegen. A span recorded with more than one integer kind (a literal in a
/// polymorphic context) is left out, so codegen defaults it.
fn int_literal_types(typed: &prepoly_hir::TypedProgram) -> HashMap<Span, prepoly_hir::IntKind> {
    use prepoly_hir::{Type, TypedExprKind};
    let mut per_span: HashMap<Span, Option<prepoly_hir::IntKind>> = HashMap::new();
    for e in &typed.expressions {
        if e.kind != TypedExprKind::Int {
            continue;
        }
        let kind = match &e.ty {
            Type::Int(k) => Some(*k),
            Type::ConstOf(inner) | Type::Mut(inner) | Type::Ref(inner) => match inner.as_ref() {
                Type::Int(k) => Some(*k),
                _ => None,
            },
            _ => None,
        };
        match (per_span.get(&e.span), kind) {
            (None, k) => {
                per_span.insert(e.span, k);
            }
            (Some(prev), k) if *prev != k => {
                per_span.insert(e.span, None);
            }
            _ => {}
        }
    }
    per_span
        .into_iter()
        .filter_map(|(span, k)| k.map(|k| (span, k)))
        .collect()
}

/// A program that passed every front-end check, ready to run.
struct Checked {
    program: Program,
    int_lit_types: HashMap<Span, prepoly_hir::IntKind>,
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

    let checked = match analyze(file, &main_src, &root) {
        Ok(c) => c,
        Err(diagnostics) => {
            for d in diagnostics {
                eprintln!("{d}");
            }
            return Err(1);
        }
    };

    match mode {
        Mode::Check => {
            println!("ok");
            Ok(())
        }
        Mode::Run => execute(&checked.program, &checked.int_lit_types).map_err(|e| {
            eprintln!("error: {e}");
            1
        }),
        Mode::Repl => execute_repl(&checked.program).map_err(|e| {
            eprintln!("error: {e}");
            1
        }),
    }
}

/// Parse, resolve the module graph, lower, and statically check `main_src` (a
/// program whose label is `main_label`, imports resolved relative to `root`).
/// Returns the checked program or the rendered diagnostics. Shared by file
/// execution and the interactive REPL, so both report identical errors.
fn analyze(main_label: &str, main_src: &str, root: &Path) -> Result<Checked, Vec<String>> {
    let mut sources = SourceMap::default();
    #[allow(unused_mut)]
    let mut modules: Vec<LoadedModule> = Vec::new();

    for (name, src) in STDLIB {
        let label = format!("<std/{name}>");
        let base = sources.add(PathBuf::from(&label), (*src).to_string());
        let ast = parse_module(src, &label, base).map_err(|m| vec![m])?;
        modules.push(LoadedModule {
            path: vec!["std".into(), (*name).into()],
            ast,
        });
    }

    let base = sources.add(PathBuf::from(main_label), main_src.to_string());
    let mut main_ast = parse_module(main_src, main_label, base).map_err(|m| vec![m])?;

    let mut visited = HashSet::new();
    let mut stack = HashSet::new();
    let mut deps = Vec::new();
    // The main file's imports resolve relative to its own directory (`root`), so
    // its canonical base is empty.
    for target in canonicalize_imports(&[], &mut main_ast.imports) {
        load_module(
            &target,
            root,
            &mut sources,
            &mut visited,
            &mut stack,
            &mut deps,
        )
        .map_err(|m| vec![m])?;
    }
    modules.extend(deps);
    modules.push(LoadedModule {
        path: vec!["main".into()],
        ast: main_ast,
    });

    // The spawn-ownership pass only matters for the JIT runtime (the REPL does not
    // execute concurrency); it lives in the LLVM crate, so it is feature-gated.
    #[cfg(jit_backend)]
    {
        report_spawn_ownership(&modules);
        auto_acquire_modules(&mut modules);
    }

    tracing::debug!(modules = modules.len(), "lowering module graph to HIR");
    let (program, lower_errors) = lower(&modules);
    let mut errors: Vec<(String, Span)> = Vec::new();
    for e in lower_errors {
        errors.push((e.message, e.span));
    }
    for e in prepoly_resolve::check_imports(&program, &modules) {
        errors.push((e.message, e.span));
    }
    tracing::debug!(
        functions = program.functions.len(),
        types = program.types.len(),
        "running type analysis"
    );
    let analysis = prepoly_typeck::analyze(&program);
    for e in &analysis.errors {
        errors.push((e.message.clone(), e.span));
    }
    tracing::debug!(errors = errors.len(), "front-end analysis complete");
    if !errors.is_empty() {
        errors.sort_by_key(|(_, s)| s.lo);
        return Err(render_errors(&errors, &sources));
    }

    let int_lit_types = int_literal_types(&analysis.typed);
    Ok(Checked {
        program,
        int_lit_types,
    })
}

/// Resolve an import path, written relative to the importing file, to the
/// imported module's canonical (root-relative) path. Imports are relative to the
/// importing file's own directory `base` (a root-relative path), so `import b`
/// from `modules/a.pp` refers to `modules/b.pp`. A `std.*` path or a bare prelude
/// module (`io`, `array`, ...) is global rather than file-relative and returns
/// `None`, so the caller leaves it untouched and does not load it from disk.
fn relativize(base: &[String], imp_path: &[String]) -> Option<Vec<String>> {
    if imp_path.first().map(|s| s == "std").unwrap_or(false) || is_prelude_path(imp_path) {
        return None;
    }
    let mut canonical = base.to_vec();
    canonical.extend_from_slice(imp_path);
    Some(canonical)
}

/// Rewrite each import's path from importer-relative to canonical (root-relative)
/// form in place -- so the loaded modules and downstream name resolution share one
/// path per file -- and return the canonical paths of the file modules to load.
/// `base` is the importing file's canonical directory.
fn canonicalize_imports(base: &[String], imports: &mut [ImportDecl]) -> Vec<Vec<String>> {
    let mut targets = Vec::new();
    for imp in imports.iter_mut() {
        if let Some(canonical) = relativize(base, &imp.path) {
            imp.path = canonical.clone();
            targets.push(canonical);
        }
    }
    targets
}

/// Load the module at canonical (root-relative) `path` and, transitively, every
/// module it imports. Each module's own imports are resolved relative to its
/// directory (`path` without its last segment); `canonicalize_imports` rewrites
/// them to canonical form before they are loaded, so a file has one identity no
/// matter how it is reached. `std`/prelude paths never arrive here (they are
/// filtered out as non-file modules during canonicalization).
fn load_module(
    path: &[String],
    root: &Path,
    sources: &mut SourceMap,
    visited: &mut HashSet<String>,
    stack: &mut HashSet<String>,
    out: &mut Vec<LoadedModule>,
) -> Result<(), String> {
    let key = path.join(".");
    // A module file whose name begins with `_` is private and cannot be imported
    // from another module.
    if prepoly_resolve::is_private_module(path) {
        return Err(format!("error: cannot import private module `{key}`"));
    }
    if visited.contains(&key) {
        return Ok(());
    }
    if !stack.insert(key.clone()) {
        return Err(format!("error: circular import involving `{key}`"));
    }
    let mut file = root.to_path_buf();
    for seg in path {
        file.push(seg);
    }
    file.set_extension("pp");
    let src = match std::fs::read_to_string(&file) {
        Ok(s) => s,
        Err(_) => {
            stack.remove(&key);
            visited.insert(key.clone());
            return Err(format!(
                "error: cannot find module `{key}` (expected `{}`)",
                file.display()
            ));
        }
    };
    let label = file.display().to_string();
    let base = sources.add(file, src.clone());
    let mut ast = parse_module(&src, &label, base)?;
    // This module's imports resolve relative to its own directory.
    let dir = &path[..path.len() - 1];
    for target in canonicalize_imports(dir, &mut ast.imports) {
        load_module(&target, root, sources, visited, stack, out)?;
    }
    stack.remove(&key);
    visited.insert(key.clone());
    out.push(LoadedModule {
        path: path.to_vec(),
        ast,
    });
    Ok(())
}

/// Whether an import path refers to a prelude module supplied as STDLIB rather
/// than a file on disk.
fn is_prelude_path(path: &[String]) -> bool {
    matches!(path, [single] if STDLIB.iter().any(|(name, _)| name == single))
}

/// Each loaded source file with the disjoint byte-offset base its spans were
/// parsed at, so a span's offset locates its file. Every file is lexed from
/// offset zero, but `parse_with_base` shifts each file's spans by its base, so a
/// span is globally unique and a diagnostic lands in the right file and line --
/// where the previous `span.hi <= src.len()` guess could pick the wrong file
/// non-deterministically, and never located standard-library spans at all.
#[derive(Default)]
struct SourceMap {
    next_base: usize,
    entries: Vec<SourceEntry>,
}

struct SourceEntry {
    base: usize,
    path: PathBuf,
    src: String,
}

impl SourceMap {
    /// Reserve a disjoint base for `src`, record it, and return the base to parse
    /// at. The one-byte gap keeps an end-of-file span from colliding with the
    /// next file's first byte.
    fn add(&mut self, path: PathBuf, src: String) -> usize {
        let base = self.next_base;
        self.next_base = base + src.len() + 1;
        self.entries.push(SourceEntry { base, path, src });
        base
    }

    /// Locate the file containing global byte offset `off`: its path, source, and
    /// the file-local offset.
    fn locate(&self, off: usize) -> Option<(&PathBuf, &str, usize)> {
        self.entries.iter().find_map(|e| {
            (off >= e.base && off <= e.base + e.src.len()).then_some((
                &e.path,
                e.src.as_str(),
                off - e.base,
            ))
        })
    }
}

/// Parse `src` (labelled `name`) at byte-offset `base`, rendering a parse error
/// with the file-local line/column.
fn parse_module(src: &str, name: &str, base: usize) -> Result<Module, String> {
    parse_with_base(src, base).map_err(|e: ParseError| {
        let (line, col) = line_col(src, e.span.lo - base);
        format!("{name}:{line}:{col}: parse error: {}", e.message)
    })
}

/// Render each `(message, span)` diagnostic as `path:line:col: error: message`,
/// locating the span's file by its globally-unique offset (or a bare `error:`
/// line when no source contains it).
fn render_errors(errors: &[(String, Span)], sources: &SourceMap) -> Vec<String> {
    let mut out = Vec::with_capacity(errors.len());
    for (msg, span) in errors {
        match sources.locate(span.lo) {
            Some((path, src, off)) => {
                let (line, col) = line_col(src, off);
                out.push(format!("{}:{line}:{col}: error: {msg}", path.display()));
            }
            None => out.push(format!("error: {msg}")),
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
    eprintln!("prepoly REPL -- enter definitions or statements; Ctrl-D to exit.");

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
    prepoly_repl::run(&checked.program, &mut buf)?;
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
