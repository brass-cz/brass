//! Streaming type checking: the checker-side API of the lazy-check pipeline.
//!
//! [`crate::analyze_streaming`] runs the same analysis as
//! [`crate::analyze_with`], but checks bodies in an execution-first order --
//! module initializers, then `main`, then the remaining functions -- lets the
//! caller reprioritize that order between bodies, and emits a [`CheckEvent`]
//! after each body with the delta of checker channels recorded since the
//! previous event. The lazy driver runs the analysis on a checker thread:
//! execution can start once the entry bodies are ready, and reaching a
//! not-yet-checked function asks (via [`Scheduler::drain_requests`]) for that
//! body to be checked next.
//!
//! Two properties of the checker shape this protocol (see the channel notes
//! on each [`ChannelDelta`] field):
//!
//! - The solver substitution is global and persistent, so a type recorded
//!   while checking one body may still contain inference variables that a
//!   LATER body pins. A delta therefore only carries fully-known values;
//!   an entry that resolves later is re-emitted by a later delta.
//! - Re-elaboration (checking a callee body again at a call site's concrete
//!   types) can revise span-keyed entries recorded earlier: overwrite them
//!   (`sum_views`, `type_names`), or remove them (`typeof_types` poisoning,
//!   the seed-conflict rule of [`aggregate_result_types`]). Deltas carry
//!   those revisions and removals explicitly, and the terminal delta -- the
//!   one flushed after the finalize re-resolution -- settles every entry.

use fxhash::FxHashMap as HashMap;

use brass_hir::{Program, Type, TypedProgram};
use brass_parser::Span;

use crate::TypeError;

/// A checked body's identity in progress events: a module initializer (its
/// index in `Program::inits`, which is execution order) or a free function
/// (its HIR symbol -- the key of `Program::functions`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BodyId {
    Init(usize),
    Function(String),
}

/// The change to the checker's MIR-lowering channels since the previous
/// event, plus the errors reported in the same window. Additions and
/// value revisions share the entry vectors (the consumer overwrites by
/// span); removals are listed separately and must be applied first.
#[derive(Clone, Debug, Default)]
pub struct ChannelDelta {
    /// Checker-resolved aggregate result types to seed onto MIR locals (the
    /// [`aggregate_result_types`] channel). An entry is emitted only once its
    /// type is fully known and every instantiation seen so far agrees; a span
    /// listed in `expr_types_removed` was contradicted by a later
    /// instantiation and must no longer be seeded.
    pub expr_types: Vec<(Span, Type)>,
    pub expr_types_removed: Vec<Span>,
    /// Append-only span sets (never retracted by later work).
    pub view_args: Vec<Span>,
    pub lift_errs: Vec<Span>,
    pub null_props: Vec<Span>,
    /// Append-once per span (a conflicting later observation is an error,
    /// not a revision).
    pub fields_loops: Vec<(Span, Vec<String>)>,
    /// Last-write-wins maps: a re-emitted span carries a revised value.
    /// `sum_views` values are emitted resolved; in the terminal delta a
    /// still-open `Result` payload defaults to `void`, mirroring the channel
    /// copy the eager analysis hands to MIR.
    pub sum_views: Vec<(Span, Type)>,
    pub type_names: Vec<(Span, String)>,
    /// Last-write-wins, and removable: a span in `typeof_types_removed` was
    /// poisoned by disagreeing instantiations.
    pub typeof_types: Vec<(Span, Type)>,
    pub typeof_types_removed: Vec<Span>,
    /// Errors reported since the previous event, in report order (unsorted,
    /// possibly duplicated across re-checked bodies; the final `Analysis`
    /// carries the sorted, deduplicated set).
    pub errors: Vec<TypeError>,
    /// The resolved return type of an UNANNOTATED body elaborated at a concrete
    /// instance (`(symbol, type_args, return)`): the consumer's monomorphizer
    /// uses it to compile the call site as a runtime-deferred call without
    /// lowering the body. Emitted only for a clean elaboration whose return
    /// resolved fully known; an annotated body already has a contract.
    pub instance_returns: Vec<(String, Vec<Type>, Type)>,
}

impl ChannelDelta {
    /// Whether the delta carries no information at all.
    pub fn is_empty(&self) -> bool {
        self.expr_types.is_empty()
            && self.expr_types_removed.is_empty()
            && self.view_args.is_empty()
            && self.lift_errs.is_empty()
            && self.null_props.is_empty()
            && self.fields_loops.is_empty()
            && self.sum_views.is_empty()
            && self.type_names.is_empty()
            && self.typeof_types.is_empty()
            && self.typeof_types_removed.is_empty()
            && self.errors.is_empty()
    }
}

/// Progress of a streaming analysis, in emission order.
#[derive(Clone, Debug)]
pub enum CheckEvent {
    /// The pre-inference static passes (annotation resolution, flow,
    /// definite assignment, HM, ...) finished with these errors. Emitted
    /// once, before any body event; a consumer that plans to execute should
    /// treat any error here as fatal.
    StaticChecked(Vec<TypeError>),
    /// Precompute and the method-body/scheme phase finished: every method
    /// body is checked and body scheduling starts. The delta covers
    /// everything recorded so far (method bodies included).
    ContextReady(ChannelDelta),
    /// One body finished its dedicated pass. The delta may also carry
    /// entries belonging to OTHER bodies: checking a caller re-elaborates
    /// its callees, and their recordings land in whichever window is open.
    BodyChecked(BodyId, ChannelDelta),
    /// The analysis is complete: the terminal delta (recorded types
    /// re-resolved against the final substitution) and the full, sorted,
    /// deduplicated error set -- the same set `Analysis::errors` carries.
    Finished(ChannelDelta, Vec<TypeError>),
    /// The consumer's stop request was honored at a body boundary: the
    /// snapshot is everything this run settled, for the caller to persist
    /// as a partial cache and resume from next time. Emitted only on a
    /// stopped run, just before the stream closes.
    Interrupted(StreamSnapshot),
    /// The whole analysis is starting over on a rewritten program (the
    /// reflective `-> infer!` specialization re-pass injects methods and
    /// renames call sites, which moves spans). Emitted by the pipeline
    /// driver, not the checker; a consumer drops everything accumulated so
    /// far. A fresh event sequence follows.
    Restarted,
}

/// A priority request: check function `symbol` next. `type_args` are the
/// concrete argument types of the call that needs the body, when the
/// requester knows them (a demand always originates at a concrete call).
/// Scheduling keys on the symbol -- the caller's own check already
/// elaborated the callee at these types, so the body's dedicated pass is
/// what remains -- and the types travel with the request so a
/// per-instantiation elaboration can use them.
#[derive(Clone, Debug)]
pub struct BodyRequest {
    pub symbol: String,
    pub type_args: Vec<Type>,
}

/// The consumer half of a streaming analysis: receives progress events and
/// is polled for priority requests between bodies. The checker calls
/// `drain_requests` after finishing a body and checks the returned function
/// symbols next, in request order, ahead of its static order; unknown and
/// already-checked symbols are ignored.
pub trait Scheduler {
    fn drain_requests(&mut self) -> Vec<BodyRequest>;
    fn emit(&mut self, event: CheckEvent);
    /// Whether the consumer asked the analysis to stop (the lazy driver's
    /// exit). Polled at body boundaries: the streaming run breaks out of its
    /// queue and returns through the normal tail.
    fn stopped(&self) -> bool {
        false
    }
    /// Whether the analysis WAS actually interrupted (it saw the stop at a
    /// body boundary and emitted [`CheckEvent::Interrupted`]). Distinct from
    /// [`Scheduler::stopped`]: a stop requested after the queue completed
    /// interrupts nothing, and that run's analysis IS a full verdict -- only
    /// an interrupted one must not be cached as complete.
    fn interrupted(&self) -> bool {
        false
    }
    /// Whether the consumer is still settling its entry (the lazy driver's
    /// gate and start-up demands). While paused, the streaming run serves
    /// only priority-requested bodies and holds the rest of the queue: a
    /// long definitional pass started between two demands would make every
    /// later demand wait for it (requests are drained at body boundaries).
    /// The consumer clears this when execution begins -- from then on the
    /// background queue fills the wait on the running program.
    fn paused(&self) -> bool {
        false
    }
}

/// The streaming control handle threaded through the inference pipeline: the
/// consumer's scheduler plus the flush bookkeeping that turns cumulative
/// checker tables into per-event deltas.
pub(crate) struct StreamCtl<'s> {
    pub(crate) sched: &'s mut dyn Scheduler,
    pub(crate) state: FlushState,
    /// Bodies a RESUMED run may skip: a prior run's stop-snapshot settled
    /// them, and `state` was seeded with everything their passes delivered,
    /// so they are announced as immediately settled (like seeded bodies).
    /// A priority request naming one forces its real pass instead.
    pub(crate) skip_fns: fxhash::FxHashSet<String>,
    /// How many leading module initializers the snapshot settled.
    pub(crate) skip_inits: usize,
}

/// The channel state already delivered to the consumer, kept by the
/// streaming run to turn the checker's cumulative tables into per-event
/// deltas. `typed_seen`/`errors_seen` are prefix cursors into append-only
/// vectors; the map/set fields mirror what the consumer currently holds.
#[derive(Default)]
pub(crate) struct FlushState {
    pub(crate) typed_seen: usize,
    pub(crate) errors_seen: usize,
    pub(crate) agg: AggState,
    pub(crate) expr_flushed: HashMap<Span, Type>,
    pub(crate) view_args: fxhash::FxHashSet<Span>,
    pub(crate) lift_errs: fxhash::FxHashSet<Span>,
    pub(crate) null_props: fxhash::FxHashSet<Span>,
    pub(crate) fields_loops: fxhash::FxHashSet<Span>,
    pub(crate) sum_views: HashMap<Span, Type>,
    pub(crate) type_names: HashMap<Span, String>,
    pub(crate) typeof_types: HashMap<Span, Type>,
    pub(crate) instance_returns: HashMap<(String, Vec<Type>), Type>,
}

/// Everything a stopped streaming run had settled, in serializable form:
/// the flush bookkeeping (so a resumed run's deltas diff against what the
/// prior run already delivered, poison markers included) plus which bodies
/// completed. The lazy driver persists this as the PARTIAL analysis cache
/// and both seeds the next checker run with it ([`crate::analyze_streaming`]
/// `resume`) and primes its own merged channel state from it.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct StreamSnapshot {
    /// Function symbols whose dedicated pass completed (seeded and skipped
    /// bodies included -- "settled", not "worked on").
    pub checked: Vec<String>,
    /// Leading module initializers settled (all of them, once the entry
    /// gate has passed).
    pub inits_checked: usize,
    /// [`AggState::per_span`]: the expr-seed agreement history. `None`
    /// marks a poisoned span -- losing it would let a revived seed
    /// miscompile a second instantiation.
    pub agg: Vec<(Span, Option<(Type, bool)>)>,
    pub expr_flushed: Vec<(Span, Type)>,
    pub view_args: Vec<Span>,
    pub lift_errs: Vec<Span>,
    pub null_props: Vec<Span>,
    pub fields_loops: Vec<(Span, Vec<String>)>,
    pub sum_views: Vec<(Span, Type)>,
    pub type_names: Vec<(Span, String)>,
    pub typeof_types: Vec<(Span, Type)>,
}

impl FlushState {
    /// Capture the delivered-state bookkeeping for a stop-snapshot.
    /// `fields` is the checker's full fields-loop table: the flush state
    /// tracks only WHICH spans were delivered, but a resumed consumer needs
    /// the field lists themselves back.
    pub(crate) fn snapshot(
        &self,
        checked: Vec<String>,
        inits_checked: usize,
        fields: &HashMap<Span, Vec<String>>,
    ) -> StreamSnapshot {
        StreamSnapshot {
            checked,
            inits_checked,
            agg: self
                .agg
                .per_span
                .iter()
                .map(|(s, t)| (*s, t.clone()))
                .collect(),
            expr_flushed: self
                .expr_flushed
                .iter()
                .map(|(s, t)| (*s, t.clone()))
                .collect(),
            view_args: self.view_args.iter().copied().collect(),
            lift_errs: self.lift_errs.iter().copied().collect(),
            null_props: self.null_props.iter().copied().collect(),
            fields_loops: self
                .fields_loops
                .iter()
                .filter_map(|s| fields.get(s).map(|f| (*s, f.clone())))
                .collect(),
            sum_views: self
                .sum_views
                .iter()
                .map(|(s, t)| (*s, t.clone()))
                .collect(),
            type_names: self
                .type_names
                .iter()
                .map(|(s, t)| (*s, t.clone()))
                .collect(),
            typeof_types: self
                .typeof_types
                .iter()
                .map(|(s, t)| (*s, t.clone()))
                .collect(),
        }
    }

    /// Rebuild the delivered-state bookkeeping from a prior run's snapshot,
    /// so this run's flushes emit only what that run had NOT delivered. The
    /// typed/error cursors start at zero: this run's checker vectors are
    /// fresh.
    pub(crate) fn from_snapshot(snap: &StreamSnapshot) -> FlushState {
        FlushState {
            typed_seen: 0,
            errors_seen: 0,
            agg: AggState {
                per_span: snap.agg.iter().map(|(s, t)| (*s, t.clone())).collect(),
            },
            expr_flushed: snap
                .expr_flushed
                .iter()
                .map(|(s, t)| (*s, t.clone()))
                .collect(),
            view_args: snap.view_args.iter().copied().collect(),
            lift_errs: snap.lift_errs.iter().copied().collect(),
            null_props: snap.null_props.iter().copied().collect(),
            fields_loops: snap.fields_loops.iter().map(|(s, _)| *s).collect(),
            sum_views: snap
                .sum_views
                .iter()
                .map(|(s, t)| (*s, t.clone()))
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
            // Contracts are deliberately not snapshotted. A resumed run
            // re-elaborates a demanded instance before deferring it again.
            instance_returns: HashMap::default(),
        }
    }
}

/// Resolve each aggregate-producing expression's source span to its
/// checker-resolved instance type, for the back end to follow. This carries
/// the element/field types the checker inferred from use into MIR lowering,
/// so a witness-free constructor (`HashMap.new()`) whose result type the back
/// end could not infer on its own is seeded from the caller's resolved type.
/// Only fully-known aggregates (record/sum/array, no remaining inference
/// variable) are kept; a span recorded with conflicting types (a polymorphic
/// position) is dropped so a wrong type is never seeded.
pub fn aggregate_result_types(typed: &TypedProgram, program: &Program) -> HashMap<Span, Type> {
    let mut agg = AggState::default();
    for e in &typed.expressions {
        agg.observe(e, program);
    }
    agg.seedable_map()
}

/// The incremental core of [`aggregate_result_types`]: per span, the one type
/// every instantiation of the enclosing body agreed on and whether it may be
/// seeded, or `None` once two instantiations disagreed.
///
/// Seedability is judged AFTER agreement, never before. A generic body
/// checked once per instantiation reaches the same span at different types --
/// a call that yields a `Path` for one receiver and a `string` for another --
/// and seeding either onto the shared MIR local would reinterpret the other.
/// Only FULLY KNOWN types count as observations: a partially inferred
/// sighting of the same span (an empty `[]` before its element type is fixed)
/// is less information about the same instantiation, not a disagreement.
#[derive(Default)]
pub(crate) struct AggState {
    per_span: HashMap<Span, Option<(Type, bool)>>,
}

impl AggState {
    pub(crate) fn observe(&mut self, e: &brass_hir::TypedExpr, program: &Program) {
        use brass_hir::TypedExprKind;
        // A `ref`/`mut`/`const` view of a value is the same value: the same
        // span seen once as `int32[]` and once as `const int32[]` agrees with
        // itself.
        let ty = brass_hir::peel_modes(&e.ty);
        let seedable = match e.kind {
            TypedExprKind::Call
            | TypedExprKind::TypeLiteral(_)
            | TypedExprKind::VariantLiteral { .. } => is_seedable_instance(ty),
            // An array literal is seeded only when its element representation
            // (a nullable cell, a non-default numeric width) cannot be
            // re-derived from the bare element values, so the checked type
            // must flow into lowering. Other literals stay inferred. An EMPTY
            // literal has no element values at all, so any fully-known
            // checked type (an annotation, or inference from a later use) is
            // seeded.
            TypedExprKind::Array { empty } => {
                is_seedable_array(ty) || (empty && is_seedable_empty_array(ty))
            }
            _ => return,
        };
        if !brass_hir::is_fully_known(ty) {
            return;
        }
        // The checker records only the inferred (unannotated) fields in a
        // record's substitution; the back end's constructor builds the full
        // one. Complete it so the seeded type is the same nominal the back
        // end constructs -- otherwise the binding's type and its methods key
        // off a sparser type and misresolve the annotated fields.
        let ty = complete_aggregate(ty, program);
        match self.per_span.get(&e.span) {
            None => {
                self.per_span.insert(e.span, Some((ty, seedable)));
            }
            Some(Some((prev, _))) if *prev != ty => {
                self.per_span.insert(e.span, None);
            }
            _ => {}
        }
    }

    /// The spans currently safe to seed, with their agreed types.
    pub(crate) fn seedable_map(&self) -> HashMap<Span, Type> {
        self.per_span
            .iter()
            .filter_map(|(span, t)| match t {
                Some((ty, true)) => Some((*span, ty.clone())),
                _ => None,
            })
            .collect()
    }
}

/// Complete a record's field substitution with its declared fields, recursing
/// through array elements and nested records. The checker records only the
/// inferred fields; the back end lays a constructed record out from every
/// declared field, so the seeded type must carry them all to be the same
/// nominal.
fn complete_aggregate(ty: &Type, program: &Program) -> Type {
    complete_aggregate_rec(ty, program, &mut Vec::new())
}

/// The recursion of [`complete_aggregate`]. `in_progress` holds the nominal
/// ids currently being completed on this descent: a self-referential type
/// (e.g. `type Node = { next: Node? }`) mentions itself in its own declared
/// field types, so descending into that occurrence would rebuild the same
/// fields forever. The inner occurrence is left as written -- the nominal id
/// is what the back end keys on, and its own construction sites are seeded
/// separately.
fn complete_aggregate_rec(ty: &Type, program: &Program, in_progress: &mut Vec<i32>) -> Type {
    use brass_hir::{NominalType, TypeKind};
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
            let mut subst = brass_hir::Substitution::empty();
            if let Some(TypeKind::Record { fields, .. }) = program.type_by_id(n.id).map(|i| &i.kind)
            {
                for f in fields {
                    let seeded = n.substitution.get(&f.name).cloned();
                    // A declared-nullable field keeps its declared type
                    // whatever the constructor stored (the rule mono's
                    // `record_type` also applies): a `null` seeds `never?`
                    // and a non-null value seeds its raw type, but the slot
                    // is laid out -- and read back -- as the declared
                    // nullable cell, so a seeded raw type would make the
                    // destructor/readers reinterpret the cell. A seeded
                    // proper nullable (a refined `infer?` slot) stays.
                    let value = match (&f.resolved_ty, seeded) {
                        (Some(decl @ Type::Nullable(_)), seeded)
                            if brass_hir::is_fully_known(decl)
                                && !matches!(
                                    &seeded,
                                    Some(Type::Nullable(i))
                                        if !matches!(**i, Type::Never)
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
        // variant's fields. Recurse into the existing substitution values
        // without adding declared fields (which are variant-keyed), enough
        // for the payloads.
        Type::Sum(n) => {
            if in_progress.contains(&n.id) {
                return ty.clone();
            }
            in_progress.push(n.id);
            let mut subst = brass_hir::Substitution::empty();
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

/// Whether a resolved type is a fully-known record/sum worth seeding onto a
/// call result: no remaining inference variable anywhere in it. Matches the
/// back end's `brass_mir` seeding filter (records/sums only -- a
/// constructor's result, whose array fields the back end cannot otherwise
/// type).
fn is_seedable_instance(ty: &Type) -> bool {
    matches!(ty, Type::Record(_) | Type::Sum(_)) && brass_hir::is_fully_known(ty)
}

/// Whether an array literal's checked type is worth seeding onto its result
/// local: a fully-known slice/array whose *element representation* the back
/// end would re-derive differently from the element values -- a nullable
/// element (a heap cell) or a non-default numeric element (`int64[]`,
/// `uint8[]`, `float32[]`, a different width than the literal defaults).
/// Matches the `brass_mir` filter for array literals.
fn is_seedable_array(ty: &Type) -> bool {
    use brass_hir::{FloatKind, IntKind};
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
    needs_pin && brass_hir::is_fully_known(ty)
}

/// Whether an *empty* array literal's checked type is worth seeding: any
/// fully-known slice/array. With no element values to derive from, the
/// checked type is the back end's only possible source for the element
/// representation (`let xs: int32[] = []` read before any push would
/// otherwise be refused).
fn is_seedable_empty_array(ty: &Type) -> bool {
    matches!(ty, Type::Slice(_) | Type::Array(..)) && brass_hir::is_fully_known(ty)
}

#[cfg(test)]
mod tests {
    use fxhash::FxHashSet as HashSet;

    use super::*;
    use crate::{TypeError, analyze, analyze_streaming};

    /// A test scheduler: hands out its canned priority requests on the first
    /// drain and records every event.
    struct Recorder {
        requests: Vec<String>,
        events: Vec<CheckEvent>,
    }

    impl Scheduler for Recorder {
        fn drain_requests(&mut self) -> Vec<BodyRequest> {
            std::mem::take(&mut self.requests)
                .into_iter()
                .map(|symbol| BodyRequest {
                    symbol,
                    type_args: Vec::new(),
                })
                .collect()
        }
        fn emit(&mut self, event: CheckEvent) {
            self.events.push(event);
        }
    }

    fn lower(src: &str) -> Program {
        let ast = brass_parser::parse(src).expect("parse");
        let (program, lerr) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(lerr.is_empty(), "lower: {lerr:?}");
        program
    }

    /// The consumer-side channel state after replaying a delta stream: what
    /// the lazy driver would hold.
    #[derive(Default)]
    struct Merged {
        expr_types: HashMap<Span, Type>,
        view_args: HashSet<Span>,
        lift_errs: HashSet<Span>,
        null_props: HashSet<Span>,
        fields_loops: HashMap<Span, Vec<String>>,
        sum_views: HashMap<Span, Type>,
        type_names: HashMap<Span, String>,
        typeof_types: HashMap<Span, Type>,
        final_errors: Option<Vec<TypeError>>,
    }

    impl Merged {
        // Removals first: a delta never both removes and re-adds one span,
        // and the driver applies them in this order too.
        fn apply(&mut self, d: &ChannelDelta) {
            for s in &d.expr_types_removed {
                self.expr_types.remove(s);
            }
            for s in &d.typeof_types_removed {
                self.typeof_types.remove(s);
            }
            for (s, t) in &d.expr_types {
                self.expr_types.insert(*s, t.clone());
            }
            self.view_args.extend(d.view_args.iter().copied());
            self.lift_errs.extend(d.lift_errs.iter().copied());
            self.null_props.extend(d.null_props.iter().copied());
            for (s, f) in &d.fields_loops {
                self.fields_loops.insert(*s, f.clone());
            }
            for (s, t) in &d.sum_views {
                self.sum_views.insert(*s, t.clone());
            }
            for (s, n) in &d.type_names {
                self.type_names.insert(*s, n.clone());
            }
            for (s, t) in &d.typeof_types {
                self.typeof_types.insert(*s, t.clone());
            }
        }
    }

    fn merge(events: &[CheckEvent]) -> Merged {
        let mut m = Merged::default();
        for e in events {
            match e {
                CheckEvent::StaticChecked(_) => {}
                CheckEvent::ContextReady(d) | CheckEvent::BodyChecked(_, d) => m.apply(d),
                CheckEvent::Finished(d, errors) => {
                    m.apply(d);
                    m.final_errors = Some(errors.clone());
                }
                // Single-pass analyses (no keyed specialization) never restart,
                // and nothing stops the recorder's runs.
                CheckEvent::Restarted => unreachable!("restart in a single-pass analysis"),
                CheckEvent::Interrupted(_) => unreachable!("stop in an unstopped analysis"),
            }
        }
        m
    }

    /// The replayed stream must land the consumer on exactly the channels
    /// (and errors) the eager analysis reports, whatever the body order was.
    fn assert_stream_matches_eager(src: &str) {
        let program = lower(src);
        let eager = analyze(&program);
        let mut rec = Recorder {
            requests: Vec::new(),
            events: Vec::new(),
        };
        let streamed = analyze_streaming(&program, None, &mut rec, None);
        assert_eq!(streamed.errors, eager.errors, "errors diverge for {src}");
        let m = merge(&rec.events);
        assert_eq!(
            m.final_errors.as_ref(),
            Some(&streamed.errors),
            "Finished must carry the full error set"
        );
        assert_eq!(
            m.expr_types,
            aggregate_result_types(&streamed.typed, &program)
        );
        assert_eq!(m.expr_types, aggregate_result_types(&eager.typed, &program));
        assert_eq!(m.view_args, eager.view_args);
        assert_eq!(m.lift_errs, eager.lift_errs);
        assert_eq!(m.null_props, eager.null_props);
        assert_eq!(m.fields_loops, eager.fields_loops);
        assert_eq!(m.sum_views, eager.sum_views);
        assert_eq!(m.type_names, eager.type_names);
        assert_eq!(m.typeof_types, eager.typeof_types);
    }

    #[test]
    fn streaming_matches_eager_on_a_clean_program() {
        assert_stream_matches_eager(
            "type P = { x: int32 }\n\
             fun P.bump(self) -> int32 { return self.x + 1 }\n\
             fun make(v: int32) -> P { return P { x: v } }\n\
             fun twice(v: int32) -> int32 { return v * 2 }\n\
             fun main() {\n  let p = make(3)\n  let n = p.bump()\n  println(twice(n))\n}\n\
             let greeting = \"hi\"\n",
        );
    }

    #[test]
    fn streaming_matches_eager_on_generic_reuse() {
        // `id` is re-elaborated at two argument types; the per-span agreement
        // must drop nothing it would not drop eagerly.
        assert_stream_matches_eager(
            "fun id(x) { return x }\n\
             fun main() {\n  println(id(1))\n  println(id(\"s\"))\n}\n",
        );
    }

    #[test]
    fn streaming_matches_eager_on_an_erroneous_program() {
        assert_stream_matches_eager("fun main() {\n  let x: int32 = \"no\"\n}\n");
    }

    #[test]
    fn snapshot_roundtrips_the_flush_state() {
        // A resumed run must diff against EXACTLY what the stopped run had
        // delivered: the snapshot -> state -> snapshot cycle loses nothing
        // (cursors excepted -- the new run's vectors are fresh).
        let program = lower(
            "type P = { x: int32 }\n\
             fun make(v: int32) -> P { return P { x: v } }\n\
             fun main() { println(make(2).x) }\n",
        );
        let mut rec = Recorder {
            requests: Vec::new(),
            events: Vec::new(),
        };
        analyze_streaming(&program, None, &mut rec, None);
        let mut state = FlushState::default();
        // Rebuild a plausible delivered state from the recorded stream.
        let merged = merge(&rec.events);
        state.expr_flushed = merged.expr_types.clone();
        state.sum_views = merged.sum_views.clone();
        state.view_args = merged.view_args.clone();
        let fields: HashMap<Span, Vec<String>> = HashMap::default();
        let snap = state.snapshot(vec!["make".into(), "main".into()], 1, &fields);
        let back = FlushState::from_snapshot(&snap);
        assert_eq!(back.expr_flushed, state.expr_flushed);
        assert_eq!(back.sum_views, state.sum_views);
        assert_eq!(back.view_args, state.view_args);
        assert_eq!(snap.checked, vec!["make".to_string(), "main".to_string()]);
        assert_eq!(snap.inits_checked, 1);
    }

    #[test]
    fn inits_and_main_precede_functions_and_requests_jump_the_queue() {
        let program = lower(
            "fun a_one() -> int32 { return 1 }\n\
             fun z_two() -> int32 { return 2 }\n\
             fun main() { println(3) }\n\
             let top = 4\n",
        );
        let mut rec = Recorder {
            requests: vec!["z_two".to_string()],
            events: Vec::new(),
        };
        analyze_streaming(&program, None, &mut rec, None);
        let mut bodies = Vec::new();
        for e in &rec.events {
            if let CheckEvent::BodyChecked(id, _) = e {
                bodies.push(id.clone());
            }
        }
        // Every init precedes every function body; the requested function is
        // checked before the static order would reach it (after `main`,
        // which was already queued first when the request was drained... the
        // request lands at the very front, ahead of `main` too).
        assert_eq!(
            bodies,
            vec![
                BodyId::Init(0),
                BodyId::Function("z_two".into()),
                BodyId::Function("main".into()),
                BodyId::Function("a_one".into()),
            ]
        );
    }

    #[test]
    fn zero_argument_request_reports_an_instance_return() {
        let program = lower(
            "fun answer() { return 42 }\n\
             fun main() { println(0) }\n",
        );
        let mut rec = Recorder {
            requests: vec!["answer".to_string()],
            events: Vec::new(),
        };

        analyze_streaming(&program, None, &mut rec, None);

        // An empty argument list is a concrete zero-argument instance, not a
        // request for the open definitional pass. Its resolved return is the
        // contract the lazy monomorphizer needs to defer the body.
        let returns: Vec<_> = rec
            .events
            .iter()
            .filter_map(|event| match event {
                CheckEvent::BodyChecked(BodyId::Function(symbol), delta) if symbol == "answer" => {
                    Some(delta.instance_returns.as_slice())
                }
                _ => None,
            })
            .flatten()
            .collect();
        assert_eq!(returns.len(), 1);
        assert_eq!(
            returns[0],
            &(
                "answer".to_string(),
                Vec::new(),
                Type::Int(brass_hir::IntKind::I32),
            )
        );
    }
}
