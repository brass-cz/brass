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
//!   LATER body pins. A delta therefore only carries fully-known values; an
//!   entry still open when its body is flushed is held pending and emitted by
//!   the first later delta in which it has resolved.
//! - Re-elaboration (checking a callee body again at a call site's concrete
//!   types) can revise span-keyed entries recorded earlier: overwrite them
//!   (`sum_views`, `type_names`), or remove them (`typeof_types` poisoning,
//!   the seed-conflict rule of [`aggregate_result_types`]). Deltas carry
//!   those revisions and removals explicitly, and the terminal delta -- the
//!   one flushed after the finalize re-resolution -- settles every entry.
//!
//! Priority batches are served and sealed in send order. Every received batch
//! gets exactly one `settles_batch` delta, including requests already checked
//! in the background. Consumers apply that delta before settling the batch;
//! checked-symbol events and empty deltas alone are not completion barriers.
//! `Finished` follows the bodies and settles every outstanding batch.

use fxhash::FxHashMap as HashMap;

use brass_hir::{InstanceChannel, InstanceKey, Program, Type, TypedProgram};
use brass_parser::Span;

use crate::TypeError;

#[cfg(test)]
mod batches;

/// A checked body's identity in progress events: a module initializer (its
/// index in `Program::inits`, which is execution order) or a free function
/// (its HIR symbol -- the key of `Program::functions`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BodyId {
    Init(usize),
    Function(String),
}

/// A loop's replacement field lists, one ordered sequence per callable instance.
pub type InstanceFieldsEntries = Vec<(InstanceKey, Vec<String>)>;

/// The change to the checker's MIR-lowering channels since the previous
/// event, plus the errors reported in the same window. Additions and
/// value revisions share the entry vectors (the consumer overwrites by
/// span); removals are listed separately and must be applied first.
#[derive(Clone, Debug, Default)]
pub struct ChannelDelta {
    /// The priority batch completed by this delta. Every requested body's
    /// effects are in this or earlier deltas; seals follow request-set order.
    /// A seal can be the delta's only content when its requests were stale.
    pub settles_batch: Option<u64>,
    /// Checker-resolved aggregate seeds of MIR locals (see
    /// [`aggregate_result_types`]). An entry is emitted only once fully known
    /// and cross-instantiation-agreeing; a span listed in `expr_types_removed`
    /// was later contradicted and must be removed.
    pub expr_types: Vec<(Span, Type)>,
    pub expr_types_removed: Vec<Span>,
    /// Exact-instance aggregate seeds (see [`aggregate_instance_seeds`]),
    /// authoritative even when the observed instances agree on `expr_types`:
    /// each entry REPLACES the span's whole per-instance map, and an entry
    /// with no instances removes the span.
    pub instance_seeds: Vec<(Span, Vec<(InstanceKey, Type)>)>,
    /// Settled return-origin contracts, keyed by call and enclosing instance.
    pub numeric_calls: Vec<brass_hir::NumericCallEntry>,
    /// Contracts whose enclosing identity was superseded at final resolution.
    pub numeric_calls_removed: Vec<(Span, Option<InstanceKey>)>,
    /// Checker-resolved method receiver types, kept separate from aggregate
    /// seeds so observing an identifier never forces that type onto a result
    /// local at an unrelated use of the same source span.
    pub receiver_types: Vec<(Span, Type)>,
    pub receiver_types_removed: Vec<Span>,
    /// The method calls whose instances resolve the method on different
    /// owners (see [`method_receiver_owners`]); a re-emitted span carries
    /// its grown owner list. Such a span has no `receiver_types` entry.
    pub receiver_owners: Vec<(Span, Vec<Type>)>,
    /// Append-only span set (never retracted by later work), like
    /// `lift_errs` and `null_props`.
    pub view_args: Vec<Span>,
    /// `recv.name(..)` calls of a function-valued field (see
    /// [`crate::Analysis::field_calls`]); a re-emitted span carries a
    /// revised value.
    pub field_calls: Vec<(Span, Option<Vec<Type>>)>,
    /// Append-only span set.
    pub lift_errs: Vec<Span>,
    /// Append-only span set.
    pub null_props: Vec<Span>,
    /// Shared field lists; a re-emitted span replaces its representative when
    /// new instances disagree. `instance_fields` selects each differing list.
    pub fields_loops: Vec<(Span, Vec<String>)>,
    /// Replacement per-instance field lists; an empty entry removes the override.
    pub instance_fields: Vec<(Span, InstanceFieldsEntries)>,
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
    /// Resolved type-test patterns (same discipline as `typeof_types`; a
    /// wildcard hole in a pattern is a final value, not missing information).
    pub type_tests: Vec<(Span, Type)>,
    pub type_tests_removed: Vec<Span>,
    /// Errors reported since the previous event, in report order (unsorted,
    /// possibly duplicated across re-checked bodies; the final `Analysis`
    /// carries the sorted, deduplicated set).
    pub errors: Vec<TypeError>,
    /// Warnings first reported in this window. They are non-fatal and use a
    /// separate channel so error deduplication can never suppress them.
    pub warnings: Vec<TypeError>,
    /// The resolved return type of an UNANNOTATED body elaborated at a concrete
    /// instance (`(symbol, type_args, return)`): the consumer's monomorphizer
    /// uses it to compile the call site as a runtime-deferred call without
    /// lowering the body. Emitted only for a clean elaboration whose return
    /// resolved fully known; an annotated body already has a contract.
    pub instance_returns: Vec<(String, Vec<Type>, Type)>,
    /// Reflective calls first observed in this window: (call span, receiver
    /// type symbol, method, key type).
    pub keyed_calls: Vec<(Span, String, String, Type)>,
    /// The per-instance dispatch of reflective calls whose instances key
    /// them differently (span -> instance -> generated method), set only by
    /// the specialization snapshot that accompanies
    /// [`CheckEvent::KeyedReady`]; same replacement discipline as
    /// `instance_seeds`.
    pub instance_dispatch: Vec<(Span, Vec<(InstanceKey, String)>)>,
}

impl ChannelDelta {
    /// Whether the delta carries no information at all.
    pub fn is_empty(&self) -> bool {
        self.settles_batch.is_none()
            && self.expr_types.is_empty()
            && self.expr_types_removed.is_empty()
            && self.instance_seeds.is_empty()
            && self.numeric_calls.is_empty()
            && self.numeric_calls_removed.is_empty()
            && self.receiver_types.is_empty()
            && self.receiver_types_removed.is_empty()
            && self.receiver_owners.is_empty()
            && self.view_args.is_empty()
            && self.field_calls.is_empty()
            && self.lift_errs.is_empty()
            && self.null_props.is_empty()
            && self.fields_loops.is_empty()
            && self.instance_fields.is_empty()
            && self.sum_views.is_empty()
            && self.type_names.is_empty()
            && self.typeof_types.is_empty()
            && self.typeof_types_removed.is_empty()
            && self.type_tests.is_empty()
            && self.type_tests_removed.is_empty()
            && self.errors.is_empty()
            && self.warnings.is_empty()
            && self.instance_returns.is_empty()
            && self.keyed_calls.is_empty()
            && self.instance_dispatch.is_empty()
    }
}

/// Progress of a streaming analysis, in emission order.
#[derive(Clone, Debug)]
pub enum CheckEvent {
    /// Monotone body eligibility, emitted before affected body/channel events.
    /// Omitted declarations remain visible; this event claims no checked coverage
    /// and cannot settle a priority batch or replace a terminal event.
    SelectedBodies(std::sync::Arc<fxhash::FxHashSet<Span>>),
    /// The pre-inference static passes (annotation resolution, flow,
    /// definite assignment, ...) finished with these errors. Emitted
    /// before any body event. Consumers attribute diagnostics to
    /// declarations or bodies and gate execution of the affected code. (The
    /// lazy driver sends one of its own first when its lowering or import
    /// checks report diagnostics.)
    StaticChecked(Vec<TypeError>),
    /// Precompute and the method-body/scheme phase finished: every method
    /// body is checked and body scheduling starts. The delta covers
    /// everything recorded so far (method bodies included).
    ContextReady(ChannelDelta),
    /// One body finished its dedicated pass. The delta may also carry
    /// entries belonging to OTHER bodies: checking a caller re-elaborates
    /// its callees, and their recordings land in whichever window is open.
    /// Dependency completion passes emit ordinary body events inside the
    /// priority batch. Only the last requested member's event carries the
    /// batch's cumulative delta and seal; the others carry an empty one.
    /// A stale final member publishes that delta through `BatchSettled`.
    BodyChecked(BodyId, ChannelDelta),
    /// A priority batch with no remaining body pass completed. Carries its
    /// seal without claiming another dedicated pass for a stale or unknown
    /// symbol. All effects must be applied before treating the seal as settled.
    BatchSettled(ChannelDelta),
    /// The analysis is complete: the terminal delta (recorded types
    /// re-resolved against the final substitution) and the full, sorted,
    /// deduplicated error set -- the same set `Analysis::errors` carries.
    Finished(ChannelDelta, Vec<TypeError>),
    /// Sent by the lazy driver, not the checker, after `Finished`: the
    /// verdict of the keyed (`-> infer!`) specialization continuation, which
    /// appends the generated declarations to the analysis instead of
    /// restarting it. Carries the generated declarations, the keyed calls'
    /// dispatch (call span -> generated method symbol), and a snapshot delta
    /// of the whole continued analysis whose `errors` are the complete final
    /// verdict, replacing any provisional errors of the first pass. A failed
    /// continuation carries no declarations and no dispatch, and its errors
    /// include the failure.
    KeyedReady(
        Vec<brass_hir::GeneratedDecl>,
        Vec<(Span, String)>,
        ChannelDelta,
    ),
    /// Optional completion metadata emitted immediately before ContextReady.
    /// These symbols have a context-seeded definitional pass and their background
    /// entries skip checking. This neither seals a priority batch nor certifies
    /// later concrete instances. Ordinary consumers do not request this event.
    ContextChecked(Vec<String>),
}

/// A priority request: check function `symbol` next (see [`Scheduler`]).
/// Scheduling keys on the symbol: each function body gets one dedicated pass.
#[derive(Clone, Debug)]
pub struct BodyRequest {
    pub symbol: String,
    /// The concrete argument types of the call that needs the body (a demand
    /// always originates at a concrete call). When they are fully known, one
    /// per parameter, and contain no anonymous record, the body's pass runs
    /// at this instance -- reporting an unannotated body's resolved return in
    /// [`ChannelDelta::instance_returns`] -- and otherwise at the open
    /// signature.
    pub type_args: Vec<Type>,
    /// Driver-assigned demand set. The checker publishes one cumulative
    /// channel delta after the set's final body (see
    /// [`CheckEvent::BodyChecked`]) instead of rescanning its tables after
    /// every member.
    pub batch: u64,
}

/// The consumer half of a streaming analysis: receives progress events and
/// is polled for priority requests between bodies. The checker calls
/// `drain_requests` after finishing a body and checks the returned function
/// symbols next, in request order, ahead of its static order; unknown and
/// already-checked symbols need no dedicated pass but still receive a seal.
pub trait Scheduler {
    /// Request context-pass metadata for optional completion planning. Ordinary
    /// consumers leave this disabled and allocate no symbol snapshot.
    fn completion_observations(&self) -> bool {
        false
    }
    /// Every priority request that arrived since the last call, without
    /// blocking. Each batch is contiguous and complete in one returned vector;
    /// batch ids are unique within the stream and ordered by sending.
    fn drain_requests(&mut self) -> Vec<BodyRequest>;
    /// Park until at least one priority request arrives or the consumer wakes
    /// the background queue, then return every request currently available.
    /// Threaded schedulers override this with a blocking channel receive;
    /// in-process schedulers can keep the non-blocking default.
    fn wait_for_requests(&mut self) -> Vec<BodyRequest> {
        self.drain_requests()
    }
    /// Receive one progress event, in emission order.
    fn emit(&mut self, event: CheckEvent);
    /// Whether the consumer asked the analysis to stop (the lazy driver's
    /// exit). Polled at body boundaries: received batches finish and emit
    /// their seals before the run returns through the normal tail.
    fn stopped(&self) -> bool {
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
}

/// The channel state already delivered to the consumer, kept by the
/// streaming run to turn the checker's cumulative tables into per-event
/// deltas. `typed_seen`/`errors_seen` are prefix cursors into append-only
/// vectors; the map/set fields mirror what the consumer currently holds.
#[derive(Default)]
pub(crate) struct FlushState {
    /// Independent publication history for opt-in differential verification.
    pub(crate) reference: Option<Box<FlushState>>,
    /// Work performed by the most recent publication boundary.
    pub(crate) counters: ChannelCounters,
    /// Resolutions shared by observation folds and invalidated by solver changes.
    pub(crate) publication: crate::infer::publication::Publication,
    pub(crate) typed_seen: usize,
    /// Indices into the typed expressions whose type was still open when the
    /// prefix cursor passed them. Revisited when a dependency changes, so their
    /// seeds arrive at the first boundary after a later body closes them.
    pub(crate) typed_pending: std::collections::BTreeSet<usize>,
    pub(crate) errors_seen: usize,
    pub(crate) warnings_flushed: Vec<TypeError>,
    /// Prefix already reconciled with the published warning membership.
    pub(crate) warnings_seen: usize,
    /// Warning identity preserves report order while avoiding repeated scans.
    pub(crate) warning_members: fxhash::FxHashSet<(Span, String)>,
    pub(crate) agg: AggState,
    pub(crate) expr_flushed: HashMap<Span, Type>,
    /// Prefix cursor into the checker's instance observations, and the
    /// indices whose instance or type was still open when the cursor passed
    /// them (revisited when a dependency changes, like `typed_pending`).
    pub(crate) instance_seen: usize,
    pub(crate) instance_pending: std::collections::BTreeSet<usize>,
    pub(crate) instance_agg: InstanceAggState,
    pub(crate) instance_flushed: InstanceChannel<Type>,
    /// Prefix of numeric contracts already considered for publication.
    pub(crate) numeric_seen: usize,
    /// Contracts waiting on variables in their enclosing instance identity.
    pub(crate) numeric_pending: std::collections::BTreeSet<usize>,
    /// Current and delivered contracts; final resolution can replace a key.
    pub(crate) numeric_current: brass_hir::NumericCalls,
    pub(crate) numeric_flushed: brass_hir::NumericCalls,
    pub(crate) receivers: ReceiverState,
    pub(crate) receivers_flushed: HashMap<Span, Type>,
    pub(crate) receiver_owners_flushed: HashMap<Span, Vec<Type>>,
    pub(crate) view_args: fxhash::FxHashSet<Span>,
    pub(crate) field_calls: HashMap<Span, Option<Vec<Type>>>,
    pub(crate) lift_errs: fxhash::FxHashSet<Span>,
    pub(crate) null_props: fxhash::FxHashSet<Span>,
    pub(crate) fields_loops: HashMap<Span, Vec<String>>,
    /// Last published instance-qualified field lists.
    pub(crate) instance_fields: InstanceChannel<Vec<String>>,
    pub(crate) sum_views: HashMap<Span, Type>,
    pub(crate) type_names: HashMap<Span, String>,
    pub(crate) typeof_types: HashMap<Span, Type>,
    pub(crate) type_tests: HashMap<Span, Type>,
    pub(crate) instance_returns: HashMap<(String, Vec<Type>), Type>,
    pub(crate) keyed_calls: fxhash::FxHashSet<Span>,
}

/// Work performed while publishing one checker boundary.
#[derive(Default, Debug)]
pub(crate) struct ChannelCounters {
    /// Typed observations resolved at this boundary.
    pub(crate) typed_resolutions: usize,
    /// Instance observations resolved at this boundary.
    pub(crate) instance_resolutions: usize,
    /// Instance tags normalized at this boundary.
    pub(crate) tag_resolutions: usize,
    /// Typed readings reused without walking their type trees.
    pub(crate) typed_cache_hits: usize,
    /// Interned identities reused without normalizing their argument types.
    pub(crate) tag_cache_hits: usize,
    /// Cached reads invalidated by this boundary's coalesced solver changes.
    pub(crate) invalidated_readers: usize,
    /// Monotonic solver epoch at this publication boundary.
    pub(crate) solution_epoch: u64,
    /// Aggregate spans whose published views were reconsidered.
    pub(crate) dirty_seed_spans: usize,
    /// Nonempty instance replacement maps materialized at this boundary.
    pub(crate) instance_maps: usize,
}

/// Whether the streaming flush holds a typed expression of this kind pending
/// while its type is still open (`FlushState::typed_pending`), to feed it to
/// [`AggState`] or [`ReceiverState`] once a later body resolves it: calls,
/// record/variant/array literals, and method receivers.
pub(crate) fn seeds_from_kind(kind: &brass_hir::TypedExprKind) -> bool {
    use brass_hir::TypedExprKind;
    matches!(
        kind,
        TypedExprKind::Call
            | TypedExprKind::TypeOfAnnotation
            | TypedExprKind::NumericBinding
            | TypedExprKind::NumericArgument
            | TypedExprKind::InstanceNumericBinding
            | TypedExprKind::InstanceNumericArgument
            | TypedExprKind::TypeLiteral(_)
            | TypedExprKind::VariantLiteral { .. }
            | TypedExprKind::Array { .. }
            | TypedExprKind::MethodReceiver
    )
}

/// The span-keyed aggregate seeds: per expression span, the checker-resolved
/// type MIR lowering seeds that expression's local with, for the expressions
/// whose type the back end cannot re-derive from their operands (a
/// constructor's instance, an array literal's element representation, a
/// range's counter type, a closure's or function value's checked type, the
/// join of literal `if`/`match` branches adapted to a numeric slot). Only
/// fully-known types every observed instantiation agrees on are retained.
/// Callable locals use the exact-instance channel first, so an unseen instance
/// cannot inherit an observed instance's seed ([`aggregate_instance_seeds`]).
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

/// Whether the numeric storage contract requires an exact callable identity.
pub(crate) fn instance_numeric(kind: &brass_hir::TypedExprKind) -> bool {
    matches!(
        kind,
        brass_hir::TypedExprKind::InstanceNumericBinding
            | brass_hir::TypedExprKind::InstanceNumericArgument
    )
}

/// Whether a typed expression of this kind is an aggregate-seed observation
/// ([`AggState`]); only these are attributed to the instance they were made
/// in (see [`InstanceObservations`]).
pub(crate) fn aggregates_from_kind(kind: &brass_hir::TypedExprKind) -> bool {
    use brass_hir::TypedExprKind;
    matches!(
        kind,
        TypedExprKind::Call
            | TypedExprKind::TypeOfAnnotation
            | TypedExprKind::NumericBinding
            | TypedExprKind::NumericArgument
            | TypedExprKind::InstanceNumericBinding
            | TypedExprKind::InstanceNumericArgument
            | TypedExprKind::TypeLiteral(_)
            | TypedExprKind::VariantLiteral { .. }
            | TypedExprKind::Array { .. }
            | TypedExprKind::Range
            | TypedExprKind::Closure
            | TypedExprKind::Ident(_)
            | TypedExprKind::LiteralBranchJoin
    )
}

/// The aggregate-seed reading of one observation: the type the back end
/// would be seeded with (completed with the declaration's fields) and whether
/// this kind of expression may be seeded with it at all. `None` for an
/// observation that carries no seed information: another expression kind, or
/// a type that is not fully known yet.
pub(crate) fn aggregate_observation(
    kind: &brass_hir::TypedExprKind,
    ty: &Type,
    program: &Program,
) -> Option<(Type, bool)> {
    use brass_hir::TypedExprKind;
    // A `ref`/`mut`/`const` view of a value is the same value: the same
    // span seen once as `int32[]` and once as `const int32[]` agrees with
    // itself. A function value's type also carries the passing modes of
    // its parameters, which the back ends do not represent: erased at
    // every depth.
    let erased;
    let ty = match kind {
        TypedExprKind::Closure | TypedExprKind::Ident(_) => {
            erased = brass_hir::erase_modes(ty);
            &erased
        }
        _ => brass_hir::peel_modes(ty),
    };
    let seedable = match kind {
        TypedExprKind::TypeOfAnnotation => true,
        TypedExprKind::NumericBinding | TypedExprKind::NumericArgument => {
            matches!(ty, Type::Int(_) | Type::Float(_))
        }
        TypedExprKind::InstanceNumericBinding | TypedExprKind::InstanceNumericArgument => {
            if !matches!(ty, Type::Int(_) | Type::Float(_)) {
                return None;
            }
            true
        }
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
            is_seedable_array(ty) || (*empty && is_seedable_empty_array(ty))
        }
        // A range's element type depends on BOTH bounds (a narrow `lo`
        // with a wider `hi` counts at the wider type), which lowering
        // cannot see; its counter would otherwise take `lo`'s type and
        // wrap before reaching `hi`. Always carried.
        TypedExprKind::Range => {
            matches!(ty, Type::Slice(elem) if matches!(**elem, Type::Int(_)))
        }
        // A closure literal's checked function type: its parameter types
        // come from the expected type it was checked against or from its
        // applications, which the back end cannot re-derive from the
        // literal (an uncalled closure, a returned one, a `float32`
        // parameter fed an integer-typed operand).
        TypedExprKind::Closure => matches!(ty, Type::Fun(..)),
        // A name used as a function value: lowering builds the value as a
        // closure at the name's occurrence (a function's forwarding
        // closure), typed like a literal. Only function types are kept,
        // and only such an occurrence ever reads the entry.
        TypedExprKind::Ident(_) if matches!(ty, Type::Fun(..)) => true,
        // The join type of an `if`/`match` whose literal branches adapted to
        // a numeric requirement: lowering seeds the value's join local with
        // it (the literal values alone join at their default type).
        TypedExprKind::LiteralBranchJoin => match ty {
            Type::Nullable(inner) => matches!(**inner, Type::Int(_) | Type::Float(_)),
            other => matches!(other, Type::Int(_) | Type::Float(_)),
        },
        _ => return None,
    };
    if !brass_hir::is_fully_known(ty) {
        return None;
    }
    // The checker records only the inferred (unannotated) fields in a
    // record's substitution; the back end's constructor builds the full
    // one. Complete it so the seeded type is the same nominal the back
    // end constructs -- otherwise the binding's type and its methods key
    // off a sparser type and misresolve the annotated fields.
    Some((complete_aggregate(ty, program), seedable))
}

impl AggState {
    pub(crate) fn observe(&mut self, e: &brass_hir::TypedExpr, program: &Program) {
        if instance_numeric(&e.kind)
            && matches!(brass_hir::peel_modes(&e.ty), Type::Int(_) | Type::Float(_))
        {
            self.poison(e.span);
            return;
        }
        self.observe_prepared(
            e.span,
            aggregate_observation(&e.kind, &e.ty, program).as_ref(),
        );
    }

    /// A scalar contract belonging to an instance can never seed a shared body.
    pub(crate) fn poison(&mut self, span: Span) -> bool {
        if self.per_span.get(&span).is_some_and(Option::is_none) {
            return false;
        }
        self.per_span.insert(span, None);
        true
    }

    /// Fold an already resolved aggregate reading, reporting a state change.
    pub(crate) fn observe_prepared(&mut self, span: Span, reading: Option<&(Type, bool)>) -> bool {
        let Some((ty, seedable)) = reading else {
            return false;
        };
        match self.per_span.get(&span) {
            None => {
                self.per_span.insert(span, Some((ty.clone(), *seedable)));
                true
            }
            Some(Some((prev, _))) if prev != ty => {
                self.per_span.insert(span, None);
                true
            }
            _ => false,
        }
    }

    /// The agreed seed at one span; poisoned and unseedable spans are absent.
    pub(crate) fn seed_at(&self, span: &Span) -> Option<&Type> {
        match self.per_span.get(span) {
            Some(Some((ty, true))) => Some(ty),
            _ => None,
        }
    }

    /// The spans currently safe to seed, with their agreed types.
    pub(crate) fn seedable_map(&self) -> HashMap<Span, Type> {
        self.per_span
            .keys()
            .filter_map(|span| self.seed_at(span).map(|ty| (*span, ty.clone())))
            .collect()
    }
}

/// The aggregate-seed observations an analysis made while elaborating
/// callable instances, keeping only the instances whose argument types end
/// fully known. Each entry pairs an instance (an index into `keys`)
/// with the typed expression it observed (an index into the analysis's
/// `typed.expressions`), so no type is copied. Monomorphization seeds an
/// instance's local from these only for that exact instance, even if the
/// observed instances agree at the span (see [`aggregate_instance_seeds`]).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct InstanceObservations {
    pub keys: Vec<InstanceKey>,
    pub entries: Vec<(u32, u32)>,
}

impl InstanceObservations {
    /// Append `other`, whose typed-expression indices count from
    /// `typed_offset` in the sidecar the two analyses' typed expressions are
    /// merged into (a keyed continuation appended to its first pass).
    pub fn append(&mut self, other: InstanceObservations, typed_offset: usize) {
        let mut ids: HashMap<&InstanceKey, u32> = self
            .keys
            .iter()
            .enumerate()
            .map(|(id, key)| (key, id as u32))
            .collect();
        let mut remap = Vec::with_capacity(other.keys.len());
        let mut added = Vec::new();
        for key in &other.keys {
            let id = match ids.get(key) {
                Some(id) => *id,
                None => {
                    let id = (self.keys.len() + added.len()) as u32;
                    ids.insert(key, id);
                    added.push(key.clone());
                    id
                }
            };
            remap.push(id);
        }
        self.keys.extend(added);
        self.entries.extend(
            other
                .entries
                .into_iter()
                .map(|(key, index)| (remap[key as usize], index + typed_offset as u32)),
        );
    }
}

/// The per-instance counterpart of [`AggState`]: per span and instance (an
/// interned key id), the one type that instance's observations agree on
/// (with its seedability), or `None` once one instance's own observations
/// disagree.
#[derive(Default)]
pub(crate) struct InstanceAggState {
    keys: Vec<InstanceKey>,
    key_ids: HashMap<InstanceKey, u32>,
    per_span: HashMap<Span, HashMap<u32, Option<(Type, bool)>>>,
}

impl InstanceAggState {
    /// Recover the structural identity of an interned key.
    pub(crate) fn key(&self, id: u32) -> &InstanceKey {
        &self.keys[id as usize]
    }

    /// The id of instance `key` (interned).
    pub(crate) fn key_id(&mut self, key: &InstanceKey) -> u32 {
        if let Some(id) = self.key_ids.get(key) {
            return *id;
        }
        let id = self.keys.len() as u32;
        self.keys.push(key.clone());
        self.key_ids.insert(key.clone(), id);
        id
    }

    /// Fold one observation (an expression of `kind` at `span`, of type
    /// `ty`) made in the instance `key` (an id from [`Self::key_id`]).
    pub(crate) fn observe(
        &mut self,
        key: u32,
        kind: &brass_hir::TypedExprKind,
        span: Span,
        ty: &Type,
        program: &Program,
    ) {
        self.observe_prepared(key, span, aggregate_observation(kind, ty, program).as_ref());
    }

    /// Fold a shared reading into one instance, reporting a state change.
    pub(crate) fn observe_prepared(
        &mut self,
        key: u32,
        span: Span,
        reading: Option<&(Type, bool)>,
    ) -> bool {
        let Some((ty, seedable)) = reading else {
            return false;
        };
        let per_instance = self.per_span.entry(span).or_default();
        match per_instance.get(&key) {
            None => {
                per_instance.insert(key, Some((ty.clone(), *seedable)));
                true
            }
            Some(Some((prev, _))) if prev != ty => {
                per_instance.insert(key, None);
                true
            }
            _ => false,
        }
    }

    /// Materialize the seeds known for this span at their exact callable instances.
    /// Agreement among observed instances does not authorize an unseen instance.
    pub(crate) fn seeds_at(&self, span: &Span) -> Option<HashMap<InstanceKey, Type>> {
        let seeds: HashMap<_, _> = self
            .per_span
            .get(span)?
            .iter()
            .filter_map(|(key, reading)| match reading {
                Some((ty, true)) => Some((self.keys[*key as usize].clone(), ty.clone())),
                _ => None,
            })
            .collect();
        (!seeds.is_empty()).then_some(seeds)
    }

    /// The exact-instance seeds of every observed span, including spans whose
    /// observed instances agree on a shared seed.
    pub(crate) fn seed_map(&self) -> InstanceChannel<Type> {
        self.per_span
            .keys()
            .filter_map(|span| self.seeds_at(span).map(|seeds| (*span, seeds)))
            .collect()
    }
}

/// The per-instance aggregate seeds: per span, the type each exact instance's
/// observations agreed on. These remain authoritative even when all observed
/// instances agree: a later, unobserved instance must infer its own local rather
/// than inherit another instance's representation. `typed` is the analysis's
/// typed sidecar the observations index.
pub fn aggregate_instance_seeds(
    observations: &InstanceObservations,
    typed: &TypedProgram,
    program: &Program,
) -> InstanceChannel<Type> {
    let mut agg = InstanceAggState::default();
    let ids: Vec<u32> = observations
        .keys
        .iter()
        .map(|key| agg.key_id(key))
        .collect();
    for (key, index) in &observations.entries {
        let e = &typed.expressions[*index as usize];
        agg.observe(ids[*key as usize], &e.kind, e.span, &e.ty, program);
    }
    agg.seed_map()
}

/// Resolve every checker-recorded method receiver by its enclosing call span.
/// This channel is intentionally distinct from aggregate result seeds: receiver
/// evidence is used only to select the signature at that exact call site.
/// A call whose instances resolve the method on different owners is absent
/// here and listed by [`method_receiver_owners`] instead.
pub fn method_receiver_types(typed: &TypedProgram, program: &Program) -> HashMap<Span, Type> {
    receiver_state(typed, program).agreed_map()
}

/// The method calls of a generic body whose instances resolve the method on
/// different owners -- `x.describe()` reaching `Dog.describe` in one instance
/// and `Cat.describe` in another -- with every owner, most specific first
/// (see `ReceiverState::owner_map`). The owners' signatures may
/// complete omitted trailing arguments differently, so lowering branches on
/// the receiver's type per owner (each instance folds the test) instead of
/// completing them from one signature.
pub fn method_receiver_owners(typed: &TypedProgram, program: &Program) -> HashMap<Span, Vec<Type>> {
    receiver_state(typed, program).owner_map(program)
}

fn receiver_state(typed: &TypedProgram, program: &Program) -> ReceiverState {
    let mut receivers = ReceiverState::default();
    for expression in &typed.expressions {
        receivers.observe(expression, program);
    }
    receivers
}

/// Per-span owners of a method call. A generic body can be checked at
/// several concrete receiver instances, but the declared signature (and thus
/// its omitted-argument defaults) belongs to the nominal or primitive owner,
/// not to those instances' substitutions: the instances of one call agree
/// when they share the owner, and a call reaching several owners keeps all
/// of them so lowering never completes arguments from the wrong method.
#[derive(Default)]
pub(crate) struct ReceiverState {
    per_span: HashMap<Span, Vec<Type>>,
}

impl ReceiverState {
    pub(crate) fn observe(&mut self, expression: &brass_hir::TypedExpr, program: &Program) -> bool {
        if !matches!(expression.kind, brass_hir::TypedExprKind::MethodReceiver) {
            return false;
        }
        let ty = brass_hir::peel_modes(&expression.ty);
        // Preserve only the owner identity for nominals. An Err-only Result,
        // for example, legitimately leaves its Ok payload open at this point,
        // but the checker has still resolved `context` to the prelude Result's
        // declaration and MIR can safely read defaults from that declaration.
        let ty = match ty {
            // A direct nullable method receiver can only be the compiler-owned
            // `context` hook (all other nullable member calls are rejected).
            // Preserve one canonical marker across generic instantiations;
            // keeping the concrete inner type would poison the shared call span
            // when the same generic body is used at more than one T.
            Type::Nullable(_) => Some(Type::Nullable(Box::new(Type::Unknown(
                brass_hir::INFER_VAR,
            )))),
            Type::Record(n) | Type::Sum(n) => program.type_by_id(n.id).map(|info| info.type_ref()),
            other if other.primitive_class().is_some() && brass_hir::is_fully_known(other) => {
                Some(other.clone())
            }
            _ => None,
        };
        let Some(ty) = ty else { return false };
        let owners = self.per_span.entry(expression.span).or_default();
        if !owners.contains(&ty) {
            owners.push(ty);
            true
        } else {
            false
        }
    }

    /// The agreed receiver owner at one call span.
    pub(crate) fn agreed_at(&self, span: &Span) -> Option<&Type> {
        match self.per_span.get(span)?.as_slice() {
            [owner] => Some(owner),
            _ => None,
        }
    }

    /// The ordered dispatch owners at a call, absent for ambiguous owner tests.
    pub(crate) fn owners_at(&self, span: &Span, program: &Program) -> Option<Vec<Type>> {
        let owners = self.per_span.get(span)?;
        if owners.len() <= 1 {
            return None;
        }
        let accepted_by = |owner: &Type| {
            owners
                .iter()
                .filter(|other| {
                    *other != owner && brass_typesys::type_test_accepts(program, other, owner)
                })
                .count()
        };
        let ambiguous = owners.iter().enumerate().any(|(i, a)| {
            owners[i + 1..].iter().any(|b| {
                brass_typesys::type_test_accepts(program, a, b)
                    && brass_typesys::type_test_accepts(program, b, a)
            })
        });
        if ambiguous {
            return None;
        }
        let mut ordered = owners.clone();
        ordered
            .sort_by_cached_key(|owner| (std::cmp::Reverse(accepted_by(owner)), owner.display()));
        Some(ordered)
    }

    /// The calls whose instances all resolve one owner, with that owner.
    pub(crate) fn agreed_map(&self) -> HashMap<Span, Type> {
        self.per_span
            .iter()
            .filter_map(|(span, owners)| match owners.as_slice() {
                [owner] => Some((*span, owner.clone())),
                _ => None,
            })
            .collect()
    }

    /// The calls whose instances resolve several owners, with all of them,
    /// most specific first: when one owner's receivers also pass another
    /// owner's type test (a declared sum subtype and its parent, a record and
    /// one it structurally satisfies), the first comes before the second, so
    /// testing the owners in order selects each receiver's own owner. The
    /// test is [`brass_typesys::type_test_accepts`], which the per-owner
    /// lowering folds in each instance. A call whose owners pass each other's
    /// tests has no such order and is left out. The order does not depend on
    /// the order the instances were checked in.
    pub(crate) fn owner_map(&self, program: &Program) -> HashMap<Span, Vec<Type>> {
        self.per_span
            .keys()
            .filter_map(|span| self.owners_at(span, program).map(|owners| (*span, owners)))
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
        Type::Tuple(elems) => Type::Tuple(
            elems
                .iter()
                .map(|e| complete_aggregate_rec(e, program, in_progress))
                .collect(),
        ),
        // A function value's parameter and result records are the values the
        // closure body receives and builds: the same completed instances.
        Type::Fun(params, ret) => Type::Fun(
            params
                .iter()
                .map(|p| complete_aggregate_rec(p, program, in_progress))
                .collect(),
            Box::new(complete_aggregate_rec(ret, program, in_progress)),
        ),
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
/// call result: no remaining inference variable anywhere in it. Matches MIR
/// lowering's call-result seeding filter (`is_seedable_result`: records/sums
/// only -- a constructor's result, whose array fields the back end cannot
/// otherwise type).
fn is_seedable_instance(ty: &Type) -> bool {
    (matches!(ty, Type::Record(_) | Type::Sum(_))
        || matches!(ty, Type::Nullable(inner) if matches!(inner.as_ref(), Type::Record(_) | Type::Sum(_))))
        && brass_hir::is_fully_known(ty)
}

/// Whether an array literal's checked type is worth seeding onto its result
/// local: a fully-known type whose element representation the back end would
/// re-derive differently from the element values
/// ([`brass_hir::array_literal_needs_seed`], the rule MIR lowering applies).
fn is_seedable_array(ty: &Type) -> bool {
    brass_hir::array_literal_needs_seed(ty) && brass_hir::is_fully_known(ty)
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
                    batch: 0,
                })
                .collect()
        }
        fn emit(&mut self, event: CheckEvent) {
            self.events.push(event);
        }
    }

    /// Lower a fixture for stream and batch-barrier tests.
    pub(super) fn lower(src: &str) -> Program {
        let ast = brass_parser::parse(src).expect("parse");
        let (program, lerr) = brass_hir::lower(&[brass_hir::LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(lerr.is_empty(), "lower: {lerr:?}");
        program
    }

    #[test]
    fn instance_return_makes_a_delta_nonempty() {
        // Lazy consumers must receive a return-only delta instead of dropping
        // the concrete contract as empty bookkeeping.
        let delta = ChannelDelta {
            instance_returns: vec![(
                "answer".to_string(),
                Vec::new(),
                Type::Int(brass_hir::IntKind::I32),
            )],
            ..ChannelDelta::default()
        };
        assert!(!delta.is_empty());
    }

    #[test]
    fn warning_makes_a_delta_nonempty() {
        let delta = ChannelDelta {
            warnings: vec![TypeError {
                message: "warning".to_string(),
                span: Span::new(0, 1),
            }],
            ..ChannelDelta::default()
        };
        assert!(!delta.is_empty());
    }

    /// The consumer-side channel state after replaying a delta stream: what
    /// the lazy driver would hold.
    #[derive(Default)]
    struct Merged {
        expr_types: HashMap<Span, Type>,
        instance_seeds: InstanceChannel<Type>,
        field_calls: HashMap<Span, Option<Vec<Type>>>,
        receiver_types: HashMap<Span, Type>,
        receiver_owners: HashMap<Span, Vec<Type>>,
        view_args: HashSet<Span>,
        numeric_calls: brass_hir::NumericCalls,
        lift_errs: HashSet<Span>,
        null_props: HashSet<Span>,
        fields_loops: HashMap<Span, Vec<String>>,
        instance_fields: InstanceChannel<Vec<String>>,
        sum_views: HashMap<Span, Type>,
        type_names: HashMap<Span, String>,
        typeof_types: HashMap<Span, Type>,
        type_tests: HashMap<Span, Type>,
        warnings: Vec<TypeError>,
        final_errors: Option<Vec<TypeError>>,
    }

    impl Merged {
        // Removals first: a delta never both removes and re-adds one span,
        // and the driver applies them in this order too.
        fn apply(&mut self, d: &ChannelDelta) {
            for s in &d.expr_types_removed {
                self.expr_types.remove(s);
            }
            for s in &d.receiver_types_removed {
                self.receiver_types.remove(s);
            }
            for s in &d.typeof_types_removed {
                self.typeof_types.remove(s);
            }
            for (s, t) in &d.expr_types {
                self.expr_types.insert(*s, t.clone());
            }
            for (s, seeds) in &d.instance_seeds {
                if seeds.is_empty() {
                    self.instance_seeds.remove(s);
                } else {
                    self.instance_seeds
                        .insert(*s, seeds.iter().cloned().collect());
                }
            }
            for (s, receivers) in &d.field_calls {
                self.field_calls.insert(*s, receivers.clone());
            }
            for (s, t) in &d.receiver_types {
                self.receiver_types.insert(*s, t.clone());
            }
            for (s, owners) in &d.receiver_owners {
                self.receiver_owners.insert(*s, owners.clone());
            }
            self.view_args.extend(d.view_args.iter().copied());
            for key in &d.numeric_calls_removed {
                self.numeric_calls.remove(key);
            }
            self.numeric_calls.extend(d.numeric_calls.iter().cloned());
            self.lift_errs.extend(d.lift_errs.iter().copied());
            self.null_props.extend(d.null_props.iter().copied());
            for (s, f) in &d.fields_loops {
                self.fields_loops.insert(*s, f.clone());
            }
            for (s, entries) in &d.instance_fields {
                if entries.is_empty() {
                    self.instance_fields.remove(s);
                } else {
                    self.instance_fields
                        .insert(*s, entries.iter().cloned().collect());
                }
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
            for s in &d.type_tests_removed {
                self.type_tests.remove(s);
            }
            for (s, t) in &d.type_tests {
                self.type_tests.insert(*s, t.clone());
            }
            self.warnings.extend(d.warnings.iter().cloned());
        }
    }

    fn merge(events: &[CheckEvent]) -> Merged {
        let mut m = Merged::default();
        for e in events {
            match e {
                CheckEvent::SelectedBodies(_)
                | CheckEvent::StaticChecked(_)
                | CheckEvent::ContextChecked(_) => {}
                CheckEvent::ContextReady(d)
                | CheckEvent::BodyChecked(_, d)
                | CheckEvent::BatchSettled(d) => m.apply(d),
                CheckEvent::Finished(d, errors) => {
                    m.apply(d);
                    m.final_errors = Some(errors.clone());
                }
                CheckEvent::KeyedReady(_, _, d) => m.apply(d),
            }
        }
        m
    }

    /// The replayed stream must land the consumer on its analysis's channels
    /// and agree with eager analysis wherever both observed the same instance.
    fn assert_stream_matches_eager(src: &str) {
        let program = lower(src);
        let eager = analyze(&program);
        let mut rec = Recorder {
            requests: Vec::new(),
            events: Vec::new(),
        };
        let streamed = analyze_streaming(&program, None, &mut rec);
        assert_eq!(streamed.errors, eager.errors, "errors diverge for {src}");
        let m = merge(&rec.events);
        assert_eq!(
            m.final_errors.as_ref(),
            Some(&streamed.errors),
            "Finished must carry the full error set"
        );
        assert_eq!(m.warnings, eager.warnings, "warnings diverge for {src}");
        assert_eq!(
            m.expr_types,
            aggregate_result_types(&streamed.typed, &program)
        );
        assert_eq!(m.expr_types, aggregate_result_types(&eager.typed, &program));
        assert_eq!(
            m.instance_seeds,
            aggregate_instance_seeds(&streamed.instance_typed, &streamed.typed, &program)
        );
        // The lazy profile skips call-site walks for fully annotated bodies.
        // That absence must not grant another instance's seed to the caller.
        let eager_seeds = aggregate_instance_seeds(&eager.instance_typed, &eager.typed, &program);
        for (span, instances) in &m.instance_seeds {
            for (key, ty) in instances {
                if let Some(other) = eager_seeds.get(span).and_then(|seeds| seeds.get(key)) {
                    assert_eq!(ty, other);
                }
            }
        }
        assert_eq!(m.field_calls, eager.field_calls);
        assert_eq!(
            m.receiver_types,
            method_receiver_types(&streamed.typed, &program)
        );
        assert_eq!(
            m.receiver_types,
            method_receiver_types(&eager.typed, &program)
        );
        assert_eq!(
            m.receiver_owners,
            method_receiver_owners(&eager.typed, &program)
        );
        assert_eq!(m.view_args, eager.view_args);
        assert_eq!(m.numeric_calls, eager.numeric_calls);
        assert_eq!(m.lift_errs, eager.lift_errs);
        assert_eq!(m.null_props, eager.null_props);
        assert_eq!(m.fields_loops, eager.fields_loops);
        assert_eq!(m.instance_fields, eager.instance_fields);
        assert_eq!(m.sum_views, eager.sum_views);
        assert_eq!(m.type_names, eager.type_names);
        assert_eq!(m.typeof_types, eager.typeof_types);
        assert_eq!(m.type_tests, eager.type_tests);
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
    fn streaming_matches_eager_on_per_instance_seeds() {
        // `wrap`'s record literal is built at a different instance type in
        // each instantiation: the span is seeded per instance, identically in
        // the stream and eagerly.
        let src = "type Box = { item }\n\
                   fun wrap(x) {\n  let b = Box { item: x }\n  return b\n}\n\
                   fun main() {\n  println(wrap(1).item)\n  println(wrap(\"s\").item)\n}\n";
        assert_stream_matches_eager(src);
        let program = lower(src);
        let eager = analyze(&program);
        let seeds = aggregate_instance_seeds(&eager.instance_typed, &eager.typed, &program);
        assert!(
            seeds.values().any(|per_instance| per_instance.len() == 2),
            "the literal's span carries one seed per instance: {seeds:?}"
        );
    }

    #[test]
    fn streaming_matches_eager_on_recursive_field_lists() {
        let src = "type Inner = { name: string }\ntype Outer = { child: Inner, age: int32 }\n\
            fun walk(v) {\n if v: anonymous {} {\n for f in fields(v) {\n println(f)\n walk(v[f])\n }\n }\n }\n\
            fun main() {\n walk(Outer { child: Inner { name: \"Aki\" }, age: 30 })\n walk(Inner { name: \"Bo\" })\n }\n";
        assert_stream_matches_eager(src);
        let result = analyze(&lower(src));
        assert!(result.errors.is_empty(), "{:?}", result.errors);
        assert!(
            result
                .instance_fields
                .values()
                .any(|entries| entries.len() == 2)
        );
    }

    #[test]
    fn streaming_matches_eager_on_an_erroneous_program() {
        assert_stream_matches_eager("fun main() {\n  let x: int32 = \"no\"\n}\n");
    }

    #[test]
    fn streaming_matches_eager_on_a_warning() {
        assert_stream_matches_eager(
            "fun mixed(c: int32) {\n\
                 if c == 1 { error(\"a\")! } else if c == 2 { null! }\n\
                 return 1\n\
             }\n",
        );
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
        analyze_streaming(&program, None, &mut rec);
        let mut bodies = Vec::new();
        for e in &rec.events {
            if let CheckEvent::BodyChecked(id, _) = e {
                bodies.push(id.clone());
            }
        }
        // Every init precedes every function body, and the requested function
        // lands at the very front of the queue, ahead of `main` too.
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

        analyze_streaming(&program, None, &mut rec);

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

    #[test]
    fn unresolved_error_contract_precedes_function_ready() {
        // A lazy consumer can stop reading after this event; Finished is too late.
        let program = lower("fun f(c: bool) -> int32! { if c { return f(c)! }\n return 1 }\n");
        let mut rec = Recorder {
            requests: vec!["f".to_string()],
            events: Vec::new(),
        };
        analyze_streaming(&program, None, &mut rec);
        assert!(rec.events.iter().any(|event| matches!(
            event,
            CheckEvent::BodyChecked(BodyId::Function(name), delta)
                if name == "f" && delta.errors.iter().any(|error|
                    error.message.starts_with("cannot infer the error type of `!`"))
        )));
    }

    #[test]
    fn unresolved_error_contract_precedes_method_context_ready() {
        // Methods have no individual BodyChecked event; their context must carry the verdict.
        let program = lower(
            "type T = {}\n\
             fun T.f(self, c: bool) -> int32! { if c { return self.f(c)! }\n return 1 }\n",
        );
        let mut rec = Recorder {
            requests: Vec::new(),
            events: Vec::new(),
        };
        analyze_streaming(&program, None, &mut rec);
        assert!(rec.events.iter().any(|event| matches!(
            event,
            CheckEvent::ContextReady(delta) if delta.errors.iter().any(|error|
                error.message.starts_with("cannot infer the error type of `!`"))
        )));
    }
}
