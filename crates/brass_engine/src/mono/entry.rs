//! The monomorphizer's entry points: which roots a run types, and how a
//! root that cannot be typed is reported. The eager pipeline
//! ([`monomorphize`]) roots every module initializer and zero-parameter
//! function; the lazy pipeline roots the initializers and `main`
//! ([`monomorphize_entry`]) or one runtime-resolved instance
//! ([`monomorphize_instance_deferred`]), and stops with
//! [`MonoStop::MissingBodies`] when reachable code needs a function body
//! that is not lowered yet.

use super::*;

/// Monomorphize a MIR program against its HIR program. Returns one concrete
/// instance per reachable (callable, type-tuple), or an error describing the
/// first construct outside the typed subset.
pub fn monomorphize<'m>(
    mir: &'m MirProgram,
    program: &'m Program,
) -> Result<MonoProgram<'m>, String> {
    let mut mono = Monomorphizer::new(mir, program);

    // Monomorphization is best-effort across roots: a root outside the typed
    // subset (e.g. a stdlib I/O function, or a `main` that does I/O) is skipped
    // rather than failing the whole program, so the typed path can still compile
    // everything reachable that *is* typeable. The driver decides per program
    // whether to run the typed path (when `main` typed) or fall back. `in_progress`
    // is cleared after each root so a skipped root leaves no stale recursion mark.
    //
    // Module inits are the exception: every init runs before `main`, and a
    // skipped one leaves its module's globals unset for every later read (and
    // the main module's top-level statements are the program's entry point,
    // the same role as `main`), so an init outside the typed subset fails the
    // program instead of being dropped.
    let mut init_symbols = Vec::with_capacity(mir.inits.len());
    for (i, init) in mir.inits.iter().enumerate() {
        let sym = format!("{SYNTH_SIGIL}init{i}");
        let res = mono.type_root(|mono| {
            mono.type_and_store(
                sym.clone(),
                &init.body,
                &init.module,
                Vec::new(),
                Some(Type::Void),
                None,
                None,
                &[],
                Vec::new(),
                false,
                false,
                None,
            )
        });
        mono.clear_frame_state();
        match res {
            Ok(_) => init_symbols.push(sym),
            Err(e) => return Err(init_failure(&init.module, &e)),
        }
    }

    // Roots: every zero-parameter function. Their bodies pull in the rest.
    let mut main_skip = None;
    for f in &mir.functions {
        if f.body.params.is_empty() {
            if let Err(e) = mono.type_root(|mono| mono.instantiate_fn(&f.symbol, Vec::new())) {
                // Best-effort (see above), but the reason a root was skipped is
                // the first thing needed when a checked program is rejected as
                // "outside the typed subset" -- surface it in the debug trace,
                // and keep `main`'s reason for the driver's error message.
                tracing::debug!(root = %f.symbol, error = %e, "skipping untypeable root");
                if f.symbol == "main" {
                    main_skip = Some(e);
                }
            }
            mono.clear_frame_state();
        }
    }

    let mut mono_program = mono.into_program(init_symbols, program);
    mono_program.main_skip = main_skip;
    Ok(mono_program)
}

/// The error for a module init outside the typed subset: the main module's
/// is its top-level code; another module's names that module.
fn init_failure(module: &[String], error: &str) -> String {
    match module {
        [m] if m == "main" => refusal("top-level code is outside the typed subset", error),
        _ => refusal(
            &format!(
                "top-level code of module `{}` is outside the typed subset",
                module.join(".")
            ),
            error,
        ),
    }
}

/// The report for a body monomorphization refused, framed by `context`
/// ("... is outside the typed subset"). A refusal no checked program can
/// reach -- a compiler defect, whose message starts with `internal error` --
/// is reported as itself, so it never reads as a language restriction.
pub fn refusal(context: &str, reason: &str) -> String {
    if reason.starts_with("internal error") {
        reason.to_string()
    } else {
        format!("{context}: {reason}")
    }
}

/// Why entry-rooted monomorphization ([`monomorphize_entry`]) stopped.
#[derive(Debug)]
pub enum MonoStop {
    /// Reachable calls needed function bodies that are not in the MIR
    /// program (the lazy pipeline lowers function bodies on demand), each at
    /// the concrete argument types of the call that needed it. One pass
    /// collects EVERY missing body it can see -- a missing call's result is
    /// left unresolved and the walk continues -- so the caller lowers them
    /// all and retries: the retry count is the call graph's depth, not its
    /// node count. Never empty. The third element is whether the demand
    /// NEEDS the lowered body: `false` marks an unannotated
    /// deferral candidate, where the caller may instead answer with the
    /// checker's instance return (see `Monomorphizer::instance_returns`)
    /// and never lower the body at all.
    MissingBodies(Vec<(String, Vec<Type>, bool)>),
    /// Monomorphization genuinely failed (the same rejection
    /// [`monomorphize`] reports for the entry).
    Fail(String),
}

/// [`monomorphize`] with the LAZY pipeline's roots: the module initializers
/// and the entry `main` only, instead of every zero-parameter function. The
/// reachable graph is identical for code execution can reach -- execution
/// only enters through inits and `main` -- so unreachable functions are
/// never pulled in, which is the point: their bodies may not be checked or
/// lowered yet. A missing reachable body stops the run with
/// [`MonoStop::MissingBodies`] (even inside a best-effort init, which
/// [`monomorphize`] would silently skip) so the caller can supply the body
/// and retry rather than mis-classify it as untypeable.
pub fn monomorphize_entry<'m>(
    mir: &'m MirProgram,
    program: &'m Program,
    defer: bool,
) -> Result<MonoProgram<'m>, MonoStop> {
    monomorphize_entry_with_returns(mir, program, defer, HashMap::default())
}

/// [`monomorphize_entry`] with the checker's instance-return contracts for
/// UNANNOTATED functions (see `Monomorphizer::instance_returns`): a call
/// whose contract is present compiles as a runtime-deferred site instead of
/// demanding the body, so a statically live but never-executed call tree is
/// neither lowered nor handed to LLVM.
pub fn monomorphize_entry_with_returns<'m>(
    mir: &'m MirProgram,
    program: &'m Program,
    defer: bool,
    instance_returns: HashMap<(String, Vec<Type>), Type>,
) -> Result<MonoProgram<'m>, MonoStop> {
    let mut mono = Monomorphizer::new(mir, program);
    mono.instance_returns = instance_returns;
    if defer {
        mono.defer = Some(HashMap::default());
    }
    let (init_symbols, main_skip) = entry_roots(&mut mono, mir, program)?;
    let mut mono_program = mono.into_program(init_symbols, program);
    mono_program.main_skip = main_skip;
    Ok(mono_program)
}

/// Execute lazy roots in their original order, retaining demand watermarks.
pub(super) fn entry_roots<'m>(
    mono: &mut Monomorphizer<'m, '_>,
    mir: &'m MirProgram,
    program: &Program,
) -> Result<(Vec<String>, Option<String>), MonoStop> {
    let mut init_symbols = Vec::with_capacity(mir.inits.len());
    for (i, init) in mir.inits.iter().enumerate() {
        let sym = format!("{SYNTH_SIGIL}init{i}");
        // Demands recorded during a root that completes cleanly came from
        // dead branches or recovered speculative probes (a presence test):
        // roll them back to this watermark so dead code demands no body. A
        // failed root keeps its demands and the loop CONTINUES -- every
        // root's missing set is collected before the batch is returned.
        let watermark = mono.missing_demands.borrow().len();
        let res = mono.session_root(session::Root::Init(i), |mono| {
            mono.type_and_store(
                sym.clone(),
                &init.body,
                &init.module,
                Vec::new(),
                Some(Type::Void),
                None,
                None,
                &[],
                Vec::new(),
                false,
                false,
                None,
            )
        });
        mono.in_progress.clear();
        mono.assumed_rets.clear();
        mono.self_call_rets.clear();
        match res {
            Ok(_) => {
                mono.missing_demands.borrow_mut().truncate(watermark);
                init_symbols.push(sym);
            }
            Err(e) => {
                // A failure with missing bodies is retried once they land.
                if mono.missing_demands.borrow().len() == watermark {
                    return Err(MonoStop::Fail(init_failure(&init.module, &e)));
                }
            }
        }
    }
    let mut main_skip = None;
    if mir.functions.iter().any(|f| f.symbol == "main") || program.functions.contains_key("main") {
        let watermark = mono.missing_demands.borrow().len();
        match mono.function_root("main", Vec::new()) {
            Ok(_) => mono.missing_demands.borrow_mut().truncate(watermark),
            Err(e) => {
                // Only a miss-free failure is a genuine skip; a failure with
                // missing bodies is retried once they land.
                if mono.missing_demands.borrow().len() == watermark {
                    tracing::debug!(root = "main", error = %e, "skipping untypeable entry");
                    main_skip = Some(e);
                }
            }
        }
        mono.in_progress.clear();
        mono.assumed_rets.clear();
        mono.self_call_rets.clear();
    }
    let missing = std::mem::take(&mut *mono.missing_demands.borrow_mut());
    if !missing.is_empty() {
        return Err(MonoStop::MissingBodies(missing));
    }
    Ok((init_symbols, main_skip))
}

/// Monomorphize a single callable on demand for a concrete argument-type
/// tuple, with runtime deferral enabled (the lazy JIT's resolver): calls out
/// of the new instance may themselves compile to
/// runtime-resolved sites (collected in the result's `deferred`) instead of
/// pulling their bodies in, so one resolution compiles one call's worth of
/// code. A missing body that cannot defer surfaces as
/// [`MonoStop::MissingBodies`] for the resolver to supply and retry.
pub fn monomorphize_instance_deferred<'m>(
    mir: &'m MirProgram,
    program: &'m Program,
    base: &str,
    type_args: Vec<Type>,
    globals: &[(String, Type)],
) -> Result<MonoProgram<'m>, MonoStop> {
    monomorphize_instance_deferred_with_returns(
        mir,
        program,
        base,
        type_args,
        globals,
        HashMap::default(),
    )
}

/// [`monomorphize_instance_deferred`] with checker-reported return contracts
/// for unannotated callees. This keeps calls discovered while resolving one
/// deferred instance runtime-deferred themselves instead of pulling their
/// bodies into the current compilation batch.
pub fn monomorphize_instance_deferred_with_returns<'m>(
    mir: &'m MirProgram,
    program: &'m Program,
    base: &str,
    type_args: Vec<Type>,
    globals: &[(String, Type)],
    instance_returns: HashMap<(String, Vec<Type>), Type>,
) -> Result<MonoProgram<'m>, MonoStop> {
    let mut mono = Monomorphizer::new(mir, program);
    mono.defer = Some(HashMap::default());
    mono.instance_returns = instance_returns;
    // Global types are discovered by typing init bodies, which a
    // single-instance run never does: the caller passes the startup run's
    // complete table (every init typed before execution began), or a body
    // reading a module global could not be typed.
    mono.global_types = globals.iter().cloned().collect();
    instance_root(&mut mono, base, type_args)?;
    Ok(mono.into_program(Vec::new(), program))
}

/// Execute a runtime root, preserving the ordinary missing-demand decision.
pub(super) fn instance_root(
    mono: &mut Monomorphizer<'_, '_>,
    base: &str,
    type_args: Vec<Type>,
) -> Result<(), MonoStop> {
    let res = mono.function_root(base, type_args);
    mono.in_progress.clear();
    mono.assumed_rets.clear();
    mono.self_call_rets.clear();
    match res {
        // Demands a clean run recorded came from dead branches or recovered
        // probes; dead code needs no body.
        Ok(_) => Ok(()),
        Err(e) => {
            let missing = std::mem::take(&mut *mono.missing_demands.borrow_mut());
            if !missing.is_empty() {
                return Err(MonoStop::MissingBodies(missing));
            }
            Err(MonoStop::Fail(e))
        }
    }
}
