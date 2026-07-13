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
use prepoly_parser::ast::{Stmt, TopLevel};
use prepoly_parser::parse;
use prepoly_parser::{Span, line_col};

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
    /// Everything after the program file, passed through to the program
    /// verbatim (flags included): the env library's `args()` returns the
    /// program file followed by these.
    #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
    args: Vec<String>,
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
        /// verbatim (see the env library's `args()`).
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
}

/// Which back end / phase `drive` runs after the front end produces a checked
/// program.
enum Mode {
    Run,
    Check,
    Repl,
}

/// Host stack for the worker thread `main` delegates to. The REPL interpreter
/// recurses natively once per Prepoly call (plus expression nesting inside each
/// body), so its call-depth guard (`prepoly_repl`'s 8000-call limit) is only
/// reachable when the stack holds that many interpreter activation records; the
/// default 8 MiB main stack overflows first and aborts the process instead of
/// surfacing the guard's clean error. The reservation is virtual memory — pages
/// are committed only as the stack actually grows.
#[cfg(not(target_family = "wasm"))]
const MAIN_STACK_BYTES: usize = 256 * 1024 * 1024;

fn main() -> ExitCode {
    // Shared across the prepoly binaries: PREPOLY_LOG (EnvFilter syntax) and
    // PREPOLY_LOG_TYPE (comma-separated named log types) select the output.
    prepoly_utils::init_tracing();
    #[cfg(not(target_family = "wasm"))]
    {
        std::thread::Builder::new()
            .name("prepoly-main".into())
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
    let cli = Cli::parse();
    match cli.command {
        // A bare file argument is type-checked and run; with neither a file nor a
        // subcommand, start an interactive REPL session.
        None => match cli.file {
            Some(file) => {
                set_program_args(Some(&file), &cli.args);
                exit_code(drive(Mode::Run, &file))
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
    prepoly_utils::set_program_argv(argv);
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
    use prepoly_jit_llvm::ownership::{auto_acquire, spawn_capture_summaries};
    use prepoly_parser::ast::{Block, Member, TypeBody};

    let names = |params: &[prepoly_parser::ast::Param]| -> HashSet<String> {
        params.iter().map(|p| p.name.clone()).collect()
    };
    let name_list = |params: &[prepoly_parser::ast::Param]| -> Vec<String> {
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
        use prepoly_jit_llvm::ownership::mutates;
        use prepoly_parser::ast::{Pattern, Stmt};

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
                span: prepoly_parser::Span::new(0, 0),
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
    let mut push_errors = |errs: Vec<prepoly_jit_llvm::ownership::SpawnError>| {
        errors.extend(errs.into_iter().map(|e| (e.message, e.span)));
    };
    for m in modules {
        // Init code never runs through the ownership pass, so a module-top-level
        // spawn would get no promotion or guarding at all: reject it.
        let top_stmts: Vec<prepoly_parser::ast::Stmt> = m
            .ast
            .items
            .iter()
            .filter_map(|item| match item {
                TopLevel::Stmt(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        push_errors(
            prepoly_jit_llvm::ownership::all_spawn_spans(&top_stmts)
                .into_iter()
                .map(|span| prepoly_jit_llvm::ownership::SpawnError {
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
                    push_errors(prepoly_jit_llvm::ownership::pre_spawn_errors(
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
                            push_errors(prepoly_jit_llvm::ownership::pre_spawn_errors(
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
                    "warning: variable '{}' is shared with a spawned task; every \
                     access to it is auto-guarded by its cown lock{ctx}",
                    d.var
                );
                eprintln!(
                    "  = note: for finer-grained concurrency, acquire it explicitly \
                     with 'with(cown, (c) -> {{ ... }})'"
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
                        TypeBody::Sum(_) | TypeBody::Alias(_) => continue,
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
#[allow(clippy::too_many_arguments)] // mirrors the checker's channel outputs
fn execute(
    program: &Program,
    expr_types: &HashMap<Span, prepoly_hir::Type>,
    view_args: &HashSet<Span>,
    fields_loops: &HashMap<Span, Vec<String>>,
    type_names: &HashMap<Span, String>,
    typeof_types: &HashMap<Span, prepoly_hir::Type>,
    null_props: &HashSet<Span>,
) -> Result<(), String> {
    install_jit_panic_guard();
    prepoly_jit_llvm::run(
        program,
        expr_types,
        view_args,
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
    expr_types: &HashMap<Span, prepoly_hir::Type>,
    view_args: &HashSet<Span>,
    fields_loops: &HashMap<Span, Vec<String>>,
    type_names: &HashMap<Span, String>,
    typeof_types: &HashMap<Span, prepoly_hir::Type>,
    null_props: &HashSet<Span>,
) -> Result<(), String> {
    prepoly_repl::run(
        program,
        expr_types,
        view_args,
        fields_loops,
        type_names,
        typeof_types,
        null_props,
        &mut io::stdout(),
    )
}

/// Run a checked program through the REPL interpreter (the `repl` subcommand),
/// regardless of the `jit` feature.
fn execute_repl(
    program: &Program,
    expr_types: &HashMap<Span, prepoly_hir::Type>,
    view_args: &HashSet<Span>,
    fields_loops: &HashMap<Span, Vec<String>>,
    type_names: &HashMap<Span, String>,
    typeof_types: &HashMap<Span, prepoly_hir::Type>,
    null_props: &HashSet<Span>,
) -> Result<(), String> {
    prepoly_repl::run(
        program,
        expr_types,
        view_args,
        fields_loops,
        type_names,
        typeof_types,
        null_props,
        &mut io::stdout(),
    )
}

/// Resolve each aggregate-producing expression's source span to its
/// checker-resolved instance type, for the back end to follow. This carries the
/// element/field types the checker inferred from use into MIR lowering, so a
/// witness-free constructor (`HashMap.new()`) whose result type the back end
/// could not infer on its own is seeded from the caller's resolved type. Only
/// fully-known aggregates (record/sum/array, no remaining inference variable) are
/// kept; a span recorded with conflicting types (a polymorphic position) is
/// dropped so a wrong type is never seeded.
fn aggregate_result_types(
    typed: &prepoly_hir::TypedProgram,
    program: &Program,
) -> HashMap<Span, prepoly_hir::Type> {
    use prepoly_hir::TypedExprKind;
    // Per span: the one type every instantiation of the enclosing body agreed on
    // and whether it may be seeded, or `None` once two instantiations disagreed.
    //
    // Seedability is judged AFTER agreement, never before. A generic body checked
    // once per instantiation reaches the same span at different types -- a call
    // that yields a `Path` for one receiver and a `string` for another -- and
    // seeding either onto the shared MIR local would reinterpret the other. Only
    // FULLY KNOWN types count as observations: a partially inferred sighting of
    // the same span (an empty `[]` before its element type is fixed) is less
    // information about the same instantiation, not a disagreement.
    let mut per_span: HashMap<Span, Option<(prepoly_hir::Type, bool)>> = HashMap::new();
    for e in &typed.expressions {
        // A `ref`/`mut`/`const` view of a value is the same value: the same span
        // seen once as `int32[]` and once as `const int32[]` agrees with itself.
        let ty = prepoly_hir::peel_modes(&e.ty);
        let seedable = match e.kind {
            TypedExprKind::Call
            | TypedExprKind::TypeLiteral(_)
            | TypedExprKind::VariantLiteral { .. } => is_seedable_instance(ty),
            // An array literal is seeded only when its element representation
            // (a nullable cell, a non-default numeric width) cannot be
            // re-derived from the bare element values, so the checked type must
            // flow into lowering. Other literals stay inferred. An EMPTY
            // literal has no element values at all, so any fully-known checked
            // type (an annotation, or inference from a later use) is seeded.
            TypedExprKind::Array { empty } => {
                is_seedable_array(ty) || (empty && is_seedable_empty_array(ty))
            }
            _ => continue,
        };
        if !is_fully_known(ty) {
            continue;
        }
        // The checker records only the inferred (unannotated) fields in a record's
        // substitution; the back end's constructor builds the full one. Complete
        // it so the seeded type is the same nominal the back end constructs --
        // otherwise the binding's type and its methods key off a sparser type and
        // misresolve the annotated fields.
        let ty = complete_aggregate(ty, program);
        match per_span.get(&e.span) {
            None => {
                per_span.insert(e.span, Some((ty, seedable)));
            }
            Some(Some((prev, _))) if *prev != ty => {
                per_span.insert(e.span, None);
            }
            _ => {}
        }
    }
    per_span
        .into_iter()
        .filter_map(|(span, t)| match t {
            Some((ty, true)) => Some((span, ty)),
            _ => None,
        })
        .collect()
}

/// Complete a record's field substitution with its declared fields, recursing
/// through array elements and nested records. The checker records only the
/// inferred fields; the back end lays a constructed record out from every
/// declared field, so the seeded type must carry them all to be the same nominal.
fn complete_aggregate(ty: &prepoly_hir::Type, program: &Program) -> prepoly_hir::Type {
    complete_aggregate_rec(ty, program, &mut Vec::new())
}

/// The recursion of [`complete_aggregate`]. `in_progress` holds the nominal ids
/// currently being completed on this descent: a self-referential type (e.g.
/// `type Node = { next: Node? }`) mentions itself in its own declared field
/// types, so descending into that occurrence would rebuild the same fields
/// forever. The inner occurrence is left as written -- the nominal id is what the
/// back end keys on, and its own construction sites are seeded separately.
fn complete_aggregate_rec(
    ty: &prepoly_hir::Type,
    program: &Program,
    in_progress: &mut Vec<i32>,
) -> prepoly_hir::Type {
    use prepoly_hir::{NominalType, Type, TypeKind};
    match ty {
        Type::Slice(e) => Type::Slice(Box::new(complete_aggregate_rec(e, program, in_progress))),
        Type::Array(e, n) => Type::Array(
            Box::new(complete_aggregate_rec(e, program, in_progress)),
            *n,
        ),
        Type::Nullable(e) => {
            Type::Nullable(Box::new(complete_aggregate_rec(e, program, in_progress)))
        }
        Type::Record(n) => {
            if in_progress.contains(&n.id) {
                return ty.clone();
            }
            in_progress.push(n.id);
            let mut subst = prepoly_hir::Substitution::empty();
            if let Some(TypeKind::Record { fields, .. }) = program.type_by_id(n.id).map(|i| &i.kind)
            {
                for f in fields {
                    let seeded = n.substitution.get(&f.name).cloned();
                    // A declared-nullable field keeps its declared type whatever
                    // the constructor stored (the rule mono's `record_type` also
                    // applies): a `null` seeds `never?` and a non-null value
                    // seeds its raw type, but the slot is laid out -- and read
                    // back -- as the declared nullable cell, so a seeded raw
                    // type would make the destructor/readers reinterpret the
                    // cell. A seeded proper nullable (a refined `infer?` slot)
                    // stays.
                    let value = match (&f.resolved_ty, seeded) {
                        (Some(decl @ prepoly_hir::Type::Nullable(_)), seeded)
                            if is_fully_known(decl)
                                && !matches!(
                                    &seeded,
                                    Some(prepoly_hir::Type::Nullable(i))
                                        if !matches!(**i, prepoly_hir::Type::Never)
                                ) =>
                        {
                            Some(decl.clone())
                        }
                        (_, Some(s)) => Some(s),
                        (decl, None) => decl.clone(),
                    };
                    if let Some(v) = value {
                        subst.insert(
                            f.name.clone(),
                            complete_aggregate_rec(&v, program, in_progress),
                        );
                    }
                }
            } else {
                // A structural record (no declaration): keep its own fields.
                for (k, v) in n.substitution.iter() {
                    subst.insert(k, complete_aggregate_rec(v, program, in_progress));
                }
            }
            in_progress.pop();
            Type::Record(NominalType::with_substitution(
                n.id,
                n.name().to_string(),
                subst,
            ))
        }
        // Sums carry per-variant fields; the constructor records the active
        // variant's fields. Recurse into the existing substitution values without
        // adding declared fields (which are variant-keyed), enough for the payloads.
        Type::Sum(n) => {
            if in_progress.contains(&n.id) {
                return ty.clone();
            }
            in_progress.push(n.id);
            let mut subst = prepoly_hir::Substitution::empty();
            for (k, v) in n.substitution.iter() {
                subst.insert(k, complete_aggregate_rec(v, program, in_progress));
            }
            in_progress.pop();
            Type::Sum(NominalType::with_substitution(
                n.id,
                n.name().to_string(),
                subst,
            ))
        }
        other => other.clone(),
    }
}

/// Whether a resolved type is a fully-known record/sum worth seeding onto a call
/// result: no remaining inference variable anywhere in it. Matches the back end's
/// [`prepoly_mir`] seeding filter (records/sums only -- a constructor's result,
/// whose array fields the back end cannot otherwise type).
fn is_seedable_instance(ty: &prepoly_hir::Type) -> bool {
    use prepoly_hir::Type;
    matches!(ty, Type::Record(_) | Type::Sum(_)) && is_fully_known(ty)
}

/// Whether an array literal's checked type is worth seeding onto its result
/// local: a fully-known slice/array whose *element representation* the back end
/// would re-derive differently from the element values -- a nullable element (a
/// heap cell) or a non-default numeric element (`int64[]`, `uint8[]`,
/// `float32[]`, a different width than the literal defaults). Matches the
/// [`prepoly_mir`] filter for array literals.
fn is_seedable_array(ty: &prepoly_hir::Type) -> bool {
    use prepoly_hir::{FloatKind, IntKind, Type};
    let elem = match ty {
        Type::Slice(e) | Type::Array(e, _) => e,
        _ => return false,
    };
    let needs_pin = match elem.as_ref() {
        Type::Nullable(_) => true,
        Type::Int(k) => *k != IntKind::I32,
        Type::Float(f) => *f != FloatKind::F64,
        _ => false,
    };
    needs_pin && is_fully_known(ty)
}

/// Whether an *empty* array literal's checked type is worth seeding: any
/// fully-known slice/array. With no element values to derive from, the checked
/// type is the back end's only possible source for the element representation
/// (`let xs: int32[] = []` read before any push would otherwise be refused).
fn is_seedable_empty_array(ty: &prepoly_hir::Type) -> bool {
    matches!(
        ty,
        prepoly_hir::Type::Slice(_) | prepoly_hir::Type::Array(..)
    ) && is_fully_known(ty)
}

use prepoly_hir::is_fully_known;

/// A program that passed every front-end check, ready to run.
struct Checked {
    program: Program,
    /// Checker-resolved instance types of aggregate-producing expressions, keyed
    /// by span; the back-end seeding channel (see [`aggregate_result_types`]).
    expr_types: HashMap<Span, prepoly_hir::Type>,
    /// Spans of anonymous structural arguments the checker approved for view
    /// conversion; MIR lowering wraps exactly these in `Rvalue::RecordView`.
    view_args: HashSet<Span>,
    /// Field lists of checker-approved fields-loops, keyed by loop-statement
    /// span; MIR lowering unrolls them (see `prepoly_hir::expand`).
    fields_loops: HashMap<Span, Vec<String>>,
    /// Resolved `typeof(x)` strings, keyed by call span.
    type_names: HashMap<Span, String>,
    /// Resolved binding types of `typeof`-bearing local annotations.
    typeof_types: HashMap<Span, prepoly_hir::Type>,
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
        // Silence on success, as a checker in a pipeline should be: the exit code
        // carries the answer, and anything on stdout is noise an editor or a script
        // has to filter out.
        Mode::Check => Ok(()),
        Mode::Run => execute(
            &checked.program,
            &checked.expr_types,
            &checked.view_args,
            &checked.fields_loops,
            &checked.type_names,
            &checked.typeof_types,
            &checked.null_props,
        )
        .map_err(|e| {
            eprintln!("error: {e}");
            1
        }),
        Mode::Repl => execute_repl(
            &checked.program,
            &checked.expr_types,
            &checked.view_args,
            &checked.fields_loops,
            &checked.type_names,
            &checked.typeof_types,
            &checked.null_props,
        )
        .map_err(|e| {
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
    let search = prepoly_resolve::SearchPaths::from_env();
    let mut sources = prepoly_resolve::SourceMap::default();
    #[allow(unused_mut)]
    let mut modules: Vec<LoadedModule> =
        prepoly_resolve::parse_stdlib(&mut sources).map_err(|m| vec![m])?;

    let base = sources.add(
        Some(PathBuf::from(main_label)),
        main_label.to_string(),
        main_src.to_string(),
    );
    let (mut main_ast, parse_errors) = prepoly_parser::parse_recovering(main_src, base);
    prepoly_resolve::inject_module_path(
        &mut main_ast,
        &std::fs::canonicalize(main_label)
            .unwrap_or_else(|_| PathBuf::from(main_label))
            .display()
            .to_string(),
        Span::new(base, base),
    );
    if !parse_errors.is_empty() {
        let rendered: Vec<(String, Span)> = parse_errors
            .into_iter()
            .map(|e| (format!("syntax error: {}", e.message), e.span))
            .collect();
        return Err(render_errors(&rendered, &sources));
    }

    let mut visited = HashSet::new();
    let mut stack = HashSet::new();
    let mut deps = Vec::new();
    let mut load_errors = Vec::new();
    for (target, span) in
        prepoly_resolve::canonicalize_imports(&[], root, &mut main_ast.imports, &search)
    {
        prepoly_resolve::load_module(
            &target,
            root,
            &mut sources,
            &mut visited,
            &mut stack,
            &mut deps,
            span,
            &mut load_errors,
            &search,
        );
    }
    // A broken module graph aborts before lowering: analyzing a partial graph
    // would drown the real problem in cascading unknown-name errors. Unlike the
    // old first-error abort, every load problem is reported, with its location.
    if !load_errors.is_empty() {
        let rendered: Vec<(String, Span)> = load_errors
            .into_iter()
            .map(|e| (e.message, e.span))
            .collect();
        return Err(render_errors(&rendered, &sources));
    }
    modules.extend(deps);
    modules.push(LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast: main_ast,
    });

    // Nested std modules (`std.collections`, ...) are not in
    // the implicit prelude; load only the ones actually imported, transitively.
    let nested = prepoly_resolve::load_std_nested(&modules, &[], &mut sources);
    modules.extend(nested);

    // Resolve qualified uses of module imports (`import a.b` + `b.name`),
    // promoting the used names onto the imports so everything downstream sees
    // name-based imports. Problems join the front-end diagnostics below.
    let qualified_errors = prepoly_resolve::resolve_qualified_uses(&mut modules);

    // The spawn-ownership pass only matters for the JIT runtime (the REPL does not
    // execute concurrency); it lives in the LLVM crate, so it is feature-gated.
    // The pass may reject a `spawn` it cannot analyze; those diagnostics join the
    // front-end errors below.
    #[cfg(jit_backend)]
    let spawn_errors: Vec<(String, Span)> = {
        report_spawn_ownership(&modules);
        auto_acquire_modules(&mut modules)
    };
    #[cfg(not(jit_backend))]
    let spawn_errors: Vec<(String, Span)> = Vec::new();

    tracing::debug!(modules = modules.len(), "lowering module graph to HIR");
    let (program, lower_errors) = lower(&modules);
    let mut errors: Vec<(String, Span)> = spawn_errors;
    for e in qualified_errors {
        errors.push((e.message, e.span));
    }
    for e in lower_errors {
        errors.push((e.message, e.span));
    }
    for e in prepoly_resolve::check_imports(&modules) {
        errors.push((e.message, e.span));
    }
    tracing::debug!(
        functions = program.functions.len(),
        types = program.types.len(),
        "running type analysis"
    );
    let mut analysis = prepoly_typeck::analyze(&program);
    // Reflective decoders: a `-> infer!` method call is keyed by the caller's
    // expectation. Generate a concrete method per requested key, inject them,
    // rewrite the calls to their specializations, and re-run the pipeline over
    // the now fully-concrete program. Errors from the first pass are held until
    // after specialization (a keyed call would otherwise report as an
    // undeclared method); a genuine error re-surfaces in the second pass.
    let mut program = program;
    if !analysis.keyed_calls.is_empty() {
        match specialize_keyed(&mut modules, &program, &analysis) {
            Ok(()) => {
                let (program2, lower_errors2) = lower(&modules);
                for e in lower_errors2 {
                    errors.push((e.message, e.span));
                }
                program = program2;
                analysis = prepoly_typeck::analyze(&program);
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

    let expr_types = aggregate_result_types(&analysis.typed, &program);
    Ok(Checked {
        program,
        expr_types,
        view_args: analysis.view_args,
        fields_loops: analysis.fields_loops,
        type_names: analysis.type_names,
        typeof_types: analysis.typeof_types,
        null_props: analysis.null_props,
    })
}

/// Generate concrete specializations of the reflective (`-> infer!`) methods
/// the checker keyed, inject them into their defining modules' ASTs, and
/// rewrite each keyed call site to its specialization. After this the program
/// is fully concrete: the second checking/lowering pass sees ordinary methods.
fn specialize_keyed(
    modules: &mut [LoadedModule],
    program: &Program,
    analysis: &prepoly_typeck::Analysis,
) -> Result<(), (String, Span)> {
    // Deduplicate the requested (receiver, method, key) roots.
    let mut roots: Vec<prepoly_typesys::KeyedNeed> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for (recv, method, key) in analysis.keyed_calls.values() {
        let sym = format!("{recv}.{method}:{}", prepoly_hir::type_key(key));
        if seen.insert(sym) {
            roots.push(prepoly_typesys::KeyedNeed {
                recv: recv.clone(),
                method: method.clone(),
                key: key.clone(),
            });
        }
    }
    // Deterministic order so the specializations (and the shared-solver
    // re-elaboration that checks them) do not vary run to run.
    roots.sort_by(|a, b| {
        (&a.recv, &a.method, prepoly_hir::type_key(&a.key)).cmp(&(
            &b.recv,
            &b.method,
            prepoly_hir::type_key(&b.key),
        ))
    });
    let generated = prepoly_typesys::specialize_all(program, &roots).map_err(|e| {
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
    use prepoly_hir::Type;
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
    for g in generated {
        if let Some(m) = modules.iter_mut().find(|m| m.path == g.module) {
            m.ast.items.push(TopLevel::Fun(g.decl));
        }
    }
    for (module_path, imports) in synthetic_imports {
        if let Some(m) = modules.iter_mut().find(|m| m.path == module_path) {
            for (from_module, name) in imports {
                m.ast.imports.push(prepoly_parser::ast::ImportDecl {
                    path: from_module,
                    names: vec![prepoly_parser::ast::ImportedName::plain(
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
        .map(|(span, (_, method, key))| (*span, prepoly_typesys::mangled_name(method, key)))
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
    Ok(())
}

/// Rewrite `recv.m(..)` calls whose span is in `renames` to `recv.<new>(..)`.
fn rewrite_calls_block(
    b: &mut prepoly_parser::ast::Block,
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
    e: &mut prepoly_parser::ast::Expr,
    renames: &std::collections::HashMap<Span, String>,
) {
    use prepoly_parser::ast::{Expr, StrSeg};
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

/// Render each `(message, span)` diagnostic as `path:line:col: error: message`,
/// locating the span's file by its globally-unique offset (or a bare `error:`
/// line when no source contains it).
fn render_errors(errors: &[(String, Span)], sources: &prepoly_resolve::SourceMap) -> Vec<String> {
    let mut out = Vec::with_capacity(errors.len());
    for (msg, span) in errors {
        match sources.locate(span.lo) {
            Some(loc) => {
                let (line, col) = line_col(loc.src, loc.local);
                out.push(format!("{}:{line}:{col}: error: {msg}", loc.label));
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
    prepoly_repl::run(
        &checked.program,
        &checked.expr_types,
        &checked.view_args,
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
