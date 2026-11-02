//! Static type checking for Brass. Code reaches MIR lowering and the back
//! ends only after this crate accepts it, and they build on the types
//! recorded here instead of checking types themselves.
//!
//! [`analyze`] runs, in order:
//!
//! - the declaration-level passes: annotation resolution, construction
//!   checks, protocol conformance ([`interface`]), return completeness
//!   ([`flow`]), definite assignment ([`definite`]), global initialization
//!   order ([`globals`]), reserved names, the shape of a shadowing `Result`,
//!   and const checking ([`constck`]);
//! - the authoritative checker, [`infer`]. A pre-pass (the light pass and
//!   `precompute`) discovers unannotated returns, record schemes and global
//!   bindings without reporting errors; then every body is checked, and a
//!   call re-elaborates the callee's body at the call's argument types. It
//!   produces the typed sidecar and the channels MIR lowering and
//!   monomorphization consume, keyed by span and, where the instances of a
//!   generic body need different answers, by instance (see [`Analysis`]);
//! - match exhaustiveness ([`exhaustive`]), which needs the inferred
//!   scrutinee types.
//!
//! [`analyze_streaming`] runs the same analysis for the lazy JIT: bodies are
//! checked in an execution-first order and each completion is reported with
//! its channel delta (see [`stream`]), so execution can start before every
//! body is checked. A diagnostic in a body execution needs still stops the
//! run before that body's code executes.

pub mod constck;
pub mod constraint;
pub mod definite;
pub mod exhaustive;
pub mod flow;
pub mod globals;
pub mod infer;
pub mod interface;
pub mod narrow;
pub mod reachability;
pub mod stream;
pub mod structural;
mod taint;
mod walk;

// The constraint solver lives in `brass_solver` (shared with the value-flow
// rules in `brass_typesys`); the checker's modules name it as `crate::solver`
// / `crate::unify`.
pub use brass_solver::{solver, unify};

use fxhash::FxHashSet as HashSet;

use brass_hir::{MethodInfo, NominalInfo, Program, TypeKind, TypedProgram};
use brass_parser::Span;
use brass_parser::ast::*;

/// A checker diagnostic (an error or a warning): its message and the span it
/// points at. A message that mentions a secondary location carries it as a
/// source-offset placeholder; render it with [`render_diagnostic_message`].
#[derive(Clone, Debug, PartialEq)]
pub struct TypeError {
    pub message: String,
    pub span: Span,
}

impl TypeError {
    /// Attribute a body-pass diagnostic through an explicitly constructed
    /// ownership index. Declaration-pass errors remain catalog diagnostics.
    pub fn body_owner(
        &self,
        owners: &brass_hir::diagnostics::DiagnosticOwners,
    ) -> brass_hir::diagnostics::DiagnosticOwner {
        owners.body_owner(self.span)
    }
}

/// Delimits a source-offset placeholder inside a diagnostic message.
const SOURCE_LOCATION_MARKER: char = '\u{1f}';

/// Render a diagnostic message: each source-offset placeholder (a secondary
/// location the message mentions) becomes `locate(offset)`, or `unknown
/// location` when that returns `None`. Carrying the offsets inside the
/// message keeps every diagnostic a plain message plus span, so every
/// consumer renders the same text.
pub fn render_diagnostic_message(
    message: &str,
    mut locate: impl FnMut(usize) -> Option<String>,
) -> String {
    let mut parts = message.split(SOURCE_LOCATION_MARKER);
    let Some(first) = parts.next() else {
        return message.to_string();
    };
    let mut rendered = first.to_string();
    let mut location = true;
    for part in parts {
        if location {
            let replacement = part
                .parse()
                .ok()
                .and_then(&mut locate)
                .unwrap_or_else(|| "unknown location".to_string());
            rendered.push_str(&replacement);
        } else {
            rendered.push_str(part);
        }
        location = !location;
    }
    rendered
}

/// Remap source-offset placeholders without rendering them. Incremental
/// consumers use this when an unchanged diagnostic moves with its containing
/// source item, preserving accurate secondary locations until final display.
pub fn remap_diagnostic_source_offsets(
    message: &str,
    mut remap: impl FnMut(usize) -> usize,
) -> String {
    render_diagnostic_message(message, |offset| Some(source_offset(remap(offset))))
}

fn source_offset(offset: usize) -> String {
    format!("{SOURCE_LOCATION_MARKER}{offset}{SOURCE_LOCATION_MARKER}")
}

fn source_location(span: Span) -> String {
    source_offset(span.lo)
}

/// The result of a static analysis: the diagnostics, the typed sidecar, and
/// the channels MIR lowering, monomorphization, the driver and the language
/// server read.
#[derive(Clone, Debug, PartialEq)]
pub struct Analysis {
    /// The errors, sorted by (offset, message) and deduplicated.
    pub errors: Vec<TypeError>,
    /// Non-fatal checker diagnostics. Warnings are sorted and deduplicated
    /// independently from errors so an identical message in both channels
    /// cannot suppress either diagnostic.
    pub warnings: Vec<TypeError>,
    /// Every distinct typed observation the checker made (expression,
    /// binding, receiver), resolved against the final substitution. A span of
    /// a generic body appears once per distinct type its checks gave it.
    pub typed: TypedProgram,
    /// The aggregate-seed observations of `typed` made while elaborating a
    /// callable instance, attributed to it: the source of the per-instance
    /// seeds ([`stream::aggregate_instance_seeds`]), including spans whose
    /// observed instances agree.
    pub instance_typed: stream::InstanceObservations,
    /// Per record-type generalized scheme (inferred type parameters and the
    /// field/method signatures over them), keyed by the type's storage symbol. The
    /// language server renders a method generically from this.
    pub schemes: fxhash::FxHashMap<String, brass_hir::TypeScheme>,
    /// The inferred return type of every free function, keyed by symbol. An
    /// unannotated return is absent from the signature table, so this is where
    /// the checker's answer lives.
    pub function_returns: fxhash::FxHashMap<String, brass_hir::Type>,
    /// The same for methods, keyed by (type or variant storage qualifier, method name).
    pub method_returns: fxhash::FxHashMap<(String, String), brass_hir::Type>,
    /// Unambiguous display-only closure-parameter instantiations, var id ->
    /// observed type. A closure application's unification is local to the
    /// call (committing it would defeat let-polymorphism), so the typed
    /// sidecar keeps the open variable; the language server substitutes these
    /// observations in before rendering. The compile pipeline ignores them.
    pub closure_bindings: fxhash::FxHashMap<u32, brass_hir::Type>,
    /// The fully-known return of each unannotated function instance the
    /// checker's call-site elaborations settled, keyed by (function symbol,
    /// argument types). MIR carries it to monomorphization, which types
    /// against it what an instance's body alone cannot give: a call into an
    /// instance it is still typing (an unannotated mutual recursion), a
    /// returned closure, and in the lazy JIT a call compiled as a
    /// runtime-deferred site without lowering the callee.
    pub instance_returns: fxhash::FxHashMap<(String, Vec<brass_hir::Type>), brass_hir::Type>,
    /// The run's cross-module tables (see [`infer::ContextTables`]): a context
    /// seed for later runs when this was a context-only run (restricted to
    /// its diagnostic-free modules when some have diagnostics), and what
    /// [`analyze_generated`] continues this run from.
    pub context_tables: infer::ContextTables,
    /// Spans of anonymous structural arguments that passed the callee's row
    /// check for a view-eligible parameter (`brass_typesys::rows`); MIR
    /// lowering converts exactly these arguments into the parameter's view.
    pub view_args: fxhash::FxHashSet<Span>,
    /// The `recv.name(..)` calls resolved to calling the function value a
    /// record field holds: `None` when every instantiation does, else the
    /// type-test patterns of the receivers that do (the others call a
    /// method). MIR lowering emits a field call for these.
    pub field_calls: fxhash::FxHashMap<Span, Option<Vec<brass_hir::Type>>>,
    /// Value expressions accepted as a declared sum subtype at a flow site
    /// (span -> the parent sum instance the site requires); MIR lowering
    /// rebuilds exactly these values as the parent.
    pub sum_views: fxhash::FxHashMap<Span, brass_hir::Type>,
    /// `expr!` sites whose propagated Err payload is re-raised wrapped into
    /// the prelude `Error`; MIR's propagation arm rebuilds the value.
    pub lift_errs: fxhash::FxHashSet<Span>,
    /// Field lists of checker-approved `for f in fields(x)` loops, keyed by the
    /// loop statement's span; MIR lowering unrolls the same expanded copies the
    /// checker typed (see `brass_hir::expand`).
    /// A divergent span retains a representative here; `instance_fields` owns its selections.
    pub fields_loops: fxhash::FxHashMap<Span, Vec<String>>,
    /// Checked field lists for loops that differ between callable instances.
    pub instance_fields: brass_hir::InstanceChannel<Vec<String>>,
    /// Type symbols resolved for expressions, keyed by span: the type a
    /// `typeof(v).method(..)` static call names (keyed by the inner
    /// `typeof(v)`), and the declared record an anonymous record literal or a
    /// literal written through a record alias is built as. MIR lowering routes
    /// the call and builds the literal by these.
    pub type_names: fxhash::FxHashMap<Span, String>,
    /// Reflective (`-> infer!`) method calls keyed by expectation: call span ->
    /// (canonical receiver type symbol, method, target key). The driver specializes each and
    /// rewrites the call to the concrete method.
    pub keyed_calls: fxhash::FxHashMap<Span, (String, String, brass_hir::Type)>,
    /// Concrete return-origin contracts, keyed by call and enclosing instance.
    pub numeric_calls: brass_hir::NumericCalls,
    /// For a reflective call whose instances key it differently (a generic
    /// body calling `j.into()` at a per-instance type), the target of each
    /// instance; its `keyed_calls` entry then only marks the span reflective,
    /// and the driver dispatches it per instance.
    pub instance_keyed_calls: brass_hir::InstanceChannel<(String, String, brass_hir::Type)>,
    /// Resolved binding types of `typeof`-bearing local annotations, keyed by
    /// the annotation span; MIR seeds the slot from this.
    pub typeof_types: fxhash::FxHashMap<Span, brass_hir::Type>,
    /// Resolved patterns of type tests (`if v: T`), keyed by the test's span;
    /// MIR lowering embeds each into the test's rvalue so monomorphization
    /// folds the branch per instance.
    pub type_tests: fxhash::FxHashMap<Span, brass_hir::Type>,
    /// Spans of `expr!` operators whose operand is a nullable rather than a
    /// `Result` (the null case propagates as `Result.Null`); MIR lowering
    /// emits the presence-test shape for exactly these spans.
    pub null_props: fxhash::FxHashSet<Span>,
}

/// Run all static checks. Returns the errors found (sorted by position).
pub fn check(program: &Program) -> Vec<TypeError> {
    analyze(program).errors
}

pub use infer::ContextTables;

/// The modules an analysis checks: every module, or -- under a context seed
/// -- those the seed does not cover (the seeding run checked the rest).
#[derive(Clone, Copy)]
pub(crate) struct AnalysisModules<'a> {
    seed: Option<&'a ContextTables>,
    view: Option<&'a reachability::AnalysisView>,
}

impl<'a> AnalysisModules<'a> {
    fn new(seed: Option<&'a ContextTables>) -> Self {
        Self { seed, view: None }
    }

    fn all() -> Self {
        Self {
            seed: None,
            view: None,
        }
    }

    /// Whether this source body is requested; declarations are never pruned.
    pub(crate) fn checks_body(self, span: Span) -> bool {
        self.view.is_none_or(|view| view.selects_body(span))
    }

    /// Whether the per-item passes check `module`.
    pub(crate) fn checks(self, module: &[String]) -> bool {
        !self.seed.is_some_and(|seed| seed.covers_module(module))
    }
}

/// Extract the reusable context seed of `program` -- which must be a
/// CONTEXT-ONLY program (every module except the entry). `None` when the
/// context has any diagnostic: only a clean context's tables may stand in for
/// re-checking it.
pub fn context_seed(program: &Program) -> Option<ContextTables> {
    let analysis = analyze_with(program, None);
    if !analysis.errors.is_empty() {
        for e in analysis.errors.iter().take(5) {
            tracing::debug!(
                target: "brass::perf",
                "context not seedable: {} @ {:?}",
                e.message,
                e.span
            );
        }
        return None;
    }
    Some(analysis.context_tables)
}

/// Run all static checks and collect the typed-expression sidecar.
pub fn analyze(program: &Program) -> Analysis {
    analyze_with(program, None)
}

/// [`analyze`], optionally reusing a context seed so only the entry module is
/// re-inferred (see [`infer::ContextTables`]). The seed is dropped -- silently,
/// falling back to the full run -- when the entry declares a top-level name the
/// context also defines: the collision qualifies the context's storage symbols
/// in the combined program, detaching every seeded table key.
pub fn analyze_with(program: &Program, seed: Option<&ContextTables>) -> Analysis {
    analyze_impl(program, seed, None, None)
}

/// Continue a completed analysis by checking only the methods the driver
/// generated from reflective (`-> infer!`) templates (`generated`, already
/// appended to `program`), against the first pass's tables (`seed`). Only
/// [`infer`] runs, not the declaration-level passes; the caller merges the
/// returned channels into the first pass's.
pub fn analyze_generated(
    program: &Program,
    seed: &ContextTables,
    generated: &[brass_hir::GeneratedDecl],
) -> Analysis {
    let infer = infer::analyze_generated(program, seed, generated);
    let mut errors = infer.errors;
    errors.sort_by(|a, b| (a.span.lo, &a.message).cmp(&(b.span.lo, &b.message)));
    errors.dedup();
    let mut warnings = infer.warnings;
    warnings.sort_by(|a, b| (a.span.lo, &a.message).cmp(&(b.span.lo, &b.message)));
    warnings.dedup();
    Analysis {
        errors,
        warnings,
        typed: infer.typed,
        instance_typed: infer.instance_typed,
        schemes: infer.schemes,
        view_args: infer.view_args,
        field_calls: infer.field_calls,
        sum_views: infer.sum_views,
        lift_errs: infer.lift_errs,
        fields_loops: infer.fields_loops,
        instance_fields: infer.instance_fields,
        type_names: infer.type_names,
        keyed_calls: infer.keyed_calls,
        numeric_calls: infer.numeric_calls,
        instance_keyed_calls: infer.instance_keyed_calls,
        typeof_types: infer.typeof_types,
        type_tests: infer.type_tests,
        null_props: infer.null_props,
        function_returns: infer.function_returns,
        method_returns: infer.method_returns,
        closure_bindings: infer.closure_bindings,
        instance_returns: infer.instance_returns,
        context_tables: infer.context_tables,
    }
}

/// [`analyze_with`], streaming progress to `sched` (the lazy-check
/// pipeline): bodies are checked in an execution-first order the scheduler
/// can reprioritize between bodies, and each body's completion delivers the
/// delta of checker channels recorded in its window (see [`stream`]). The
/// returned `Analysis` is equivalent to the eager one; the event stream is
/// an incremental view of it, ending with [`stream::CheckEvent::Finished`].
pub fn analyze_streaming(
    program: &Program,
    seed: Option<&ContextTables>,
    sched: &mut dyn stream::Scheduler,
) -> Analysis {
    analyze_impl(program, seed, Some(sched), None)
}

/// Stream selected body work while preserving the complete declaration catalog.
/// Selection growth is published independently of real body checks and batch seals.
pub fn analyze_streaming_selected(
    program: &Program,
    seed: Option<&ContextTables>,
    sched: &mut dyn stream::Scheduler,
    view: &reachability::AnalysisView,
) -> Analysis {
    analyze_impl(program, seed, Some(sched), Some(view))
}

/// Prepare a selected context without claiming ordinary dedicated-body coverage.
/// The caller projects selection from the combined catalog; entry analysis must
/// complete uncovered preparation before running its ordinary body schedule.
pub fn prepare_context(program: &Program, view: &reachability::AnalysisView) -> Analysis {
    let mut view = view.clone();
    view.preparation_only = true;
    analyze_impl(program, None, None, Some(&view))
}

/// Check selected bodies against the complete declaration catalog. Coverage in
/// the seed is reused per item; omitted dependencies never cover a whole module.
pub fn analyze_selected(
    program: &Program,
    seed: Option<&ContextTables>,
    view: &reachability::AnalysisView,
) -> Analysis {
    analyze_impl(program, seed, None, Some(view))
}

/// Run body-filtered declaration facts and the const-call sidecar together.
fn static_checks(
    program: &Program,
    modules: AnalysisModules<'_>,
) -> (Vec<TypeError>, constck::ConstCalls) {
    let mut errors = Vec::new();
    errors.extend(resolve_annotations(program, modules));
    errors.extend(check_constructions(program, modules));
    errors.extend(interface::check_in(program, modules));
    errors.extend(flow::check_in(program, modules));
    errors.extend(definite::check_in(program, modules));
    errors.extend(globals::check_in(program, modules));
    errors.extend(check_reserved_names(program, modules));
    errors.extend(check_result_shadows(program, modules));
    let (const_errors, const_calls) = constck::check_in(program, modules);
    errors.extend(const_errors);
    (errors, const_calls)
}

fn analyze_impl(
    program: &Program,
    seed: Option<&ContextTables>,
    sched: Option<&mut dyn stream::Scheduler>,
    view: Option<&reachability::AnalysisView>,
) -> Analysis {
    let entry_declares =
        |name: &str| {
            program.functions.values().any(|f| {
                matches!(f.module.as_slice(), [m] if m == "main") && f.signature.name == name
            }) || program
                .types
                .values()
                .any(|t| matches!(t.module.as_slice(), [m] if m == "main") && t.name == name)
        };
    let seed = seed.filter(|s| {
        s.item_identity_matches(program) && !s.bare_names.iter().any(|name| entry_declares(name))
    });
    let modules = AnalysisModules { seed, view };
    let (mut errors, const_calls) = static_checks(program, modules);
    tracing::debug!(
        errors = errors.len(),
        "errors after the declaration-level passes"
    );
    // A streaming consumer that intends to execute learns the static
    // verdict before any body event: an error here is fatal to execution.
    let mut ctl = sched.map(|sched| stream::StreamCtl {
        sched,
        state: stream::FlushState::default(),
    });
    if let Some(ctl) = &mut ctl {
        ctl.sched
            .emit(stream::CheckEvent::StaticChecked(errors.clone()));
    }
    let (infer, final_delta, cleanup) = infer::analyze_inner(
        program,
        seed,
        ctl.as_mut(),
        std::rc::Rc::new(const_calls),
        view,
    );
    // An observed return read can extend an intentionally conservative request.
    // Re-run static facts against that larger request before publishing a verdict;
    // const-call facts must be available during inference, not filtered afterward.
    if ctl.is_none()
        && let (Some(request), Some(completed)) = (view, infer.context_tables.items.as_ref())
        && completed
            .selection
            .body_roots
            .iter()
            .any(|id| !request.selection.body_roots.contains(id))
    {
        let mut expanded = request.clone();
        expanded.set_selection(completed.selection.clone());
        drop(cleanup);
        return analyze_impl(program, seed, None, Some(&expanded));
    }
    // Exhaustiveness depends on the scrutinee's inferred nominal id. Running it
    // after inference prevents a same-named variant in another sum from being
    // mistaken for the match's owner.
    let final_modules = AnalysisModules {
        seed,
        view: infer.context_tables.items.as_ref().or(view),
    };
    errors.extend(exhaustive::check_in(program, &infer.typed, final_modules));
    errors.extend(infer.errors);
    // Message is the secondary key so identical diagnostics from re-checked
    // bodies (per-instance re-elaboration, expanded fields-loop copies) land
    // adjacent and collapse in the dedup.
    errors.sort_by(|a, b| (a.span.lo, &a.message).cmp(&(b.span.lo, &b.message)));
    errors.dedup();
    let mut warnings = infer.warnings;
    warnings.sort_by(|a, b| (a.span.lo, &a.message).cmp(&(b.span.lo, &b.message)));
    warnings.dedup();
    tracing::debug!(total = errors.len(), "type analysis finished");
    if let Some(ctl) = ctl {
        ctl.sched.emit(stream::CheckEvent::Finished(
            final_delta.unwrap_or_default(),
            errors.clone(),
        ));
    }
    drop(cleanup);
    Analysis {
        errors,
        warnings,
        typed: infer.typed,
        instance_typed: infer.instance_typed,
        schemes: infer.schemes,
        view_args: infer.view_args,
        field_calls: infer.field_calls,
        sum_views: infer.sum_views,
        lift_errs: infer.lift_errs,
        fields_loops: infer.fields_loops,
        instance_fields: infer.instance_fields,
        type_names: infer.type_names,
        keyed_calls: infer.keyed_calls,
        numeric_calls: infer.numeric_calls,
        instance_keyed_calls: infer.instance_keyed_calls,
        typeof_types: infer.typeof_types,
        type_tests: infer.type_tests,
        null_props: infer.null_props,
        function_returns: infer.function_returns,
        method_returns: infer.method_returns,
        closure_bindings: infer.closure_bindings,
        instance_returns: infer.instance_returns,
        context_tables: infer.context_tables,
    }
}

/// The Err payload as `!`-propagation re-raises it: a RESOLVED payload that
/// is not already the prelude `Error` record is wrapped into one at the
/// propagation site (`Error { value: <payload>, .. }`), gaining the site's
/// location. An `Error` -- or a payload still open -- passes through.
/// Mirrored by MIR's propagation arm, which rebuilds the value.
///
/// The wrapped type is the canonical `Error` instance every error source
/// produces (`error(..)`, `context`, a keyed decode): only the `value` slot is
/// pinned, the declared `location` and `frames` fields keep their declared
/// types. One shape means one join and one rendering (`Error<value=T>`) in
/// every diagnostic.
pub(crate) fn lift_err_payload(program: &Program, resolved: brass_hir::Type) -> brass_hir::Type {
    use brass_hir::{NominalType, Type};
    let Some(info) = program.prelude_type("Error") else {
        return resolved;
    };
    if resolved.is_unknown() || matches!(&resolved, Type::Record(n) if n.id == info.id) {
        return resolved;
    }
    let mut n = NominalType::new(info.id, &info.name);
    n.substitution.insert("value", resolved);
    Type::Record(n)
}

/// A user `type Result` shadows the prelude's for the fallibility sugar, so
/// it must carry the sugar's shape; checked at the declaration (not at use)
/// so the mistake is reported once, where it was made. An ALIAS named
/// `Result` cannot carry the sugar's identity at all.
fn check_result_shadows(program: &Program, modules: AnalysisModules<'_>) -> Vec<TypeError> {
    let mut errors = Vec::new();
    for info in program.types.values() {
        if info.name != brass_hir::RESULT_TYPE_NAME
            || program.prelude_modules.contains(&info.module)
            || info.module.is_empty()
            || !modules.checks(&info.module)
        {
            continue;
        }
        if program
            .scoped_result_instance(&info.module, &brass_hir::Type::Void, &brass_hir::Type::Void)
            .is_err()
        {
            errors.push(TypeError {
                message: format!(
                    "`{}` shadows the prelude's `Result` but is not `| Ok {{ value }} | Err {{ \
                     error }}`, the shape the fallibility sugar (`T!`, `error(..)`, `!`) builds",
                    info.name
                ),
                span: info.span,
            });
        }
    }
    for alias in program.type_aliases.values() {
        if program.prelude_modules.contains(&alias.module) || !modules.checks(&alias.module) {
            continue;
        }
        // The alias table is keyed by (possibly qualified) symbol; detect a
        // shadow by what the module's bare `Result` resolves to.
        let key = brass_hir::resolve_qualified(
            &program.type_aliases,
            &program.import_origins,
            &program.import_renames,
            &alias.module,
            brass_hir::RESULT_TYPE_NAME,
            |candidate| {
                brass_hir::definition_is_visible(
                    &program.import_origins,
                    &program.prelude_modules,
                    &alias.module,
                    brass_hir::RESULT_TYPE_NAME,
                    &candidate.module,
                )
            },
        );
        if key.is_some_and(|a| a.span == alias.span) {
            errors.push(TypeError {
                message: "a `type Result = ..` alias cannot shadow the fallibility sugar's \
                          `Result`; declare a sum type named `Result` (or name the aliased type \
                          explicitly)"
                    .to_string(),
                span: alias.span,
            });
        }
    }
    errors
}

/// Reject user definitions of a reserved function name
/// (`brass_hir::RESERVED_FUNCTION_NAMES`): the builtins the back ends
/// implement (`len`, `spawn`, `with`, `sync`), the compile-time forms
/// (`fields`, `typeof`), and the prelude's `error`, which the checker types as
/// the fallibility sugar's Err constructor. A user definition would silently
/// capture the standard library's own calls (e.g. `len(s)`) or detach
/// `error(..)` from the sugar.
fn check_reserved_names(program: &Program, modules: AnalysisModules<'_>) -> Vec<TypeError> {
    let mut errors = Vec::new();
    for info in program.functions.values() {
        let name = info.signature.name.as_str();
        if !brass_hir::RESERVED_FUNCTION_NAMES.contains(&name) {
            continue;
        }
        // The prelude itself provides some of these (`error` is an ordinary
        // core/error.cz function); only a user redefinition is rejected.
        if program.prelude_modules.contains(&info.module) || !modules.checks(&info.module) {
            continue;
        }
        errors.push(TypeError {
            message: format!("`{name}` is a builtin and cannot be redefined"),
            span: info.signature.span,
        });
    }
    errors
}

/// Verify record/variant literals name a known type and variant. Inference
/// types a literal whose type it cannot resolve as an open value without a
/// diagnostic of its own, so an unknown name is reported here.
fn check_constructions(program: &Program, modules: AnalysisModules<'_>) -> Vec<TypeError> {
    struct V<'a> {
        program: &'a Program,
        /// Local names some module's import renames (`import m.{ X as Y }`
        /// registers `Y`). This pass has no module context, so any renamed
        /// local is deferred to module-aware inference, like a multi-module
        /// name.
        renamed: HashSet<&'a str>,
        errors: Vec<TypeError>,
    }
    impl walk::ExprVisitor for V<'_> {
        fn visit(&mut self, e: &Expr) {
            match e {
                // These validation passes have no module context. For a unique
                // type name (a direct table key) the precise checks run; a name
                // defined in several modules is only checked for existence here
                // and resolved precisely by module-aware inference.
                // An empty name is an anonymous structure literal `{ f: v }`
                // (a structural record), not a named-type construction.
                Expr::TypeLit(name, _, span) if name != "Self" && !name.is_empty() && !name.contains('.') => match self.program.types.get(name) {
                    Some(info) if info.is_sum() => self.errors.push(TypeError {
                        message: format!("`{name}` is a sum type; construct a variant with `{name}.Variant {{ ... }}`"),
                        span: *span,
                    }),
                    Some(_) => {}
                    None if self.program.has_type_named(name) => {}
                    // A record named through `type A = R { .. }`; module-aware
                    // inference resolves the alias.
                    None if self.program.has_type_alias_named(name) => {}
                    None if self.renamed.contains(name.as_str()) => {}
                    None => self.errors.push(TypeError {
                        message: format!("unknown type `{name}`"),
                        span: *span,
                    }),
                },
                Expr::VariantLit(t, v, _, span) if t != "Self" && !t.contains('.') => match self.program.types.get(t) {
                    Some(info) if info.variant(v).is_none() => self.errors.push(TypeError {
                        message: format!("`{t}` has no variant `{v}`"),
                        span: *span,
                    }),
                    Some(_) => {}
                    None if self.program.has_type_named(t) => {}
                    // A sum named through `type A = S`; module-aware inference
                    // resolves the alias and its variant.
                    None if self.program.has_type_alias_named(t) => {}
                    None if self.renamed.contains(t.as_str()) => {}
                    None => self.errors.push(TypeError {
                        message: format!("unknown type `{t}`"),
                        span: *span,
                    }),
                },
                _ => {}
            }
        }
    }
    let mut v = V {
        program,
        renamed: program
            .import_renames
            .values()
            .flat_map(|m| m.keys())
            .map(String::as_str)
            .collect(),
        errors: Vec::new(),
    };
    walk::walk_program_exprs_in(program, modules, &mut v);
    v.errors
}

/// Verify every syntactic type annotation names a type visible from the module
/// it appears in. Nominal names are keyed by the
/// type's unique symbol, and each annotation is resolved from its declaring
/// module (own/unique, this module's qualified definition, or an imported one).
fn resolve_annotations(program: &Program, modules: AnalysisModules<'_>) -> Vec<TypeError> {
    // A type annotation may only name a type visible from its module: this
    // module's own definition, a built-in, the standard-library prelude, or one
    // brought in by `import` (named, renamed, or qualified through a whole-module
    // import). The program's resolver applies that rule; a `type Alias = ..`
    // name stands for its target type, nominal or not.
    let resolve_nominal = |module: &[String], name: &str| -> Option<NominalInfo> {
        let info = program.resolve_type(module, name)?;
        Some(match &info.kind {
            TypeKind::Record { .. } => NominalInfo::record(info.id),
            TypeKind::Sum { .. } => NominalInfo::sum(info.id),
        })
    };
    let resolve_alias = |module: &[String], name: &str| {
        program
            .resolve_type_alias(module, name)
            .map(|alias| alias.ty.clone())
    };

    // Annotations tagged with the module they appear in, so a bare type name
    // resolves against that module's visible types.
    let mut tes: Vec<(Vec<String>, TypeExpr)> = Vec::new();
    let push_decl =
        |module: &[String], local: Vec<TypeExpr>, out: &mut Vec<(Vec<String>, TypeExpr)>| {
            out.extend(local.into_iter().map(|te| (module.to_vec(), te)));
        };
    for info in program.types.values() {
        if !modules.checks(&info.module) {
            continue;
        }
        let mut local = Vec::new();
        match &info.kind {
            TypeKind::Record { fields, methods } => {
                for f in fields {
                    if let Some(t) = &f.ty {
                        local.push(t.clone());
                    }
                }
                for m in methods.values() {
                    collect_method(m, modules.checks_body(m.decl.span), &mut local);
                }
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    for f in &v.fields {
                        if let Some(t) = &f.ty {
                            local.push(t.clone());
                        }
                    }
                    for m in v.methods.values() {
                        collect_method(m, modules.checks_body(m.decl.span), &mut local);
                    }
                }
            }
        }
        push_decl(&info.module, local, &mut tes);
    }
    for f in program.functions.values() {
        if !modules.checks(&f.module) {
            continue;
        }
        let mut local = Vec::new();
        for p in &f.signature.params {
            if let Some(t) = &p.ty {
                local.push(t.clone());
            }
        }
        if let Some(r) = &f.signature.ret {
            local.push(r.clone());
        }
        if modules.checks_body(f.decl.span) {
            collect_block(&f.decl.body, &mut local);
        }
        push_decl(&f.module, local, &mut tes);
    }
    for init in &program.inits {
        if !modules.checks(&init.path) {
            continue;
        }
        let mut local = Vec::new();
        for stmt in &init.stmts {
            collect_stmt(stmt, &mut local);
        }
        push_decl(&init.path, local, &mut tes);
    }
    let mut errors = Vec::new();
    for (module, te) in &tes {
        // `Base { .. }` refinements, `Self.field`, and `type` slots are resolved
        // (and their errors reported) by the lowering-time slot resolver and the
        // checker's own `resolve_type`; the pure resolver cannot resolve them, so
        // skip any annotation that uses them here to avoid a spurious error.
        if mentions_decl_only_syntax(te) {
            continue;
        }
        if let Err(msg) = brass_hir::resolve_with_aliases(
            te,
            |n| resolve_nominal(module, n),
            |n| resolve_alias(module, n),
        ) {
            errors.push(TypeError {
                message: msg,
                span: te.span(),
            });
        }
    }
    errors
}

/// Whether a type expression uses syntax the pure resolver cannot handle: a
/// `type` slot, a `Self.field` reference, or a `Base { .. }` refinement.
fn mentions_decl_only_syntax(te: &TypeExpr) -> bool {
    match te {
        TypeExpr::TypeSlot(_) | TypeExpr::SelfField(..) | TypeExpr::Refine(..) => true,
        TypeExpr::Array(i, _, _)
        | TypeExpr::Nullable(i, _)
        | TypeExpr::Fallible(i, _)
        | TypeExpr::Mut(i, _)
        | TypeExpr::Ref(i, _) => mentions_decl_only_syntax(i),
        TypeExpr::Tuple(es, _) => es.iter().any(mentions_decl_only_syntax),
        TypeExpr::Fun(ps, r, _) => {
            ps.iter().any(mentions_decl_only_syntax) || mentions_decl_only_syntax(r)
        }
        TypeExpr::Anonymous(fs, _) => fs.iter().any(|(_, t, _)| mentions_decl_only_syntax(t)),
        TypeExpr::Named(..) | TypeExpr::TypeOf(..) => false,
    }
}

fn collect_method(m: &MethodInfo, selected: bool, out: &mut Vec<TypeExpr>) {
    for p in &m.signature.params {
        if let Some(t) = &p.ty {
            out.push(t.clone());
        }
    }
    if let Some(r) = &m.signature.ret {
        out.push(r.clone());
    }
    if selected && let Some(b) = &m.decl.body {
        collect_block(b, out);
    }
}

fn collect_block(b: &Block, out: &mut Vec<TypeExpr>) {
    for s in &b.stmts {
        collect_stmt(s, out);
    }
}

fn collect_stmt(stmt: &Stmt, out: &mut Vec<TypeExpr>) {
    match stmt {
        Stmt::Let { ty, value, .. } => {
            if let Some(t) = ty {
                out.push(t.clone());
            }
            if let Some(value) = value {
                collect_expr(value, out);
            }
        }
        Stmt::Assign { target, value, .. } => {
            collect_expr(target, out);
            collect_expr(value, out);
        }
        Stmt::Expr(expr) => collect_expr(expr, out),
        Stmt::While { cond, body, .. } => {
            collect_expr(cond, out);
            collect_block(body, out);
        }
        Stmt::For { iter, body, .. } => {
            collect_expr(iter, out);
            collect_block(body, out);
        }
        Stmt::Return(Some(expr), _) => collect_expr(expr, out),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

fn collect_expr(expr: &Expr, out: &mut Vec<TypeExpr>) {
    match expr {
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(expr) = seg {
                    collect_expr(expr, out);
                }
            }
        }
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) => collect_expr(inner, out),
        Expr::TypeTest(subject, te, _, _) => {
            out.push(te.clone());
            collect_expr(subject, out);
        }
        Expr::Binary(_, left, right, _) | Expr::Range(left, right, _) => {
            collect_expr(left, out);
            collect_expr(right, out);
        }
        Expr::Call(callee, args, _) => {
            collect_expr(callee, out);
            for arg in args {
                collect_expr(&arg.expr, out);
            }
        }
        Expr::Field(base, _, _) => collect_expr(base, out),
        Expr::Index(base, index, _) => {
            collect_expr(base, out);
            collect_expr(index, out);
        }
        Expr::Closure(params, body, _) => {
            for param in params {
                if let Some(ty) = &param.ty {
                    out.push(ty.clone());
                }
            }
            collect_expr(body, out);
        }
        Expr::Array(items, _) => {
            for item in items {
                collect_expr(item, out);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, value) in fields {
                collect_expr(value, out);
            }
        }
        Expr::If(cond, then, els, _) => {
            collect_expr(cond, out);
            collect_block(then, out);
            if let Some(els) = els {
                collect_expr(els, out);
            }
        }
        Expr::IfLet(_, scrutinee, then, els, _) => {
            collect_expr(scrutinee, out);
            collect_block(then, out);
            if let Some(els) = els {
                collect_expr(els, out);
            }
        }
        Expr::Match(scrutinee, arms, _) => {
            collect_expr(scrutinee, out);
            for arm in arms {
                collect_expr(&arm.body, out);
            }
        }
        Expr::Block(block, _) => collect_block(block, out),
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => {}
    }
}

#[cfg(test)]
mod tests;
