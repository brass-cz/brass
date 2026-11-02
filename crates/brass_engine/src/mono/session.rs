//! Owned mono results across refreshes of one lazy compilation's inputs.
//!
//! Roots are atomic retention units. Their complete reachable graph and effects
//! are replayed together; partial descendants of a failed root never escape its
//! ordinary rollback. Prefix identities keep roots dependent on all earlier
//! roots, including globals, speculative demands and deferred targets.

use super::*;
use dependencies::Read;
use std::cell::RefCell;
use std::rc::Rc;

/// Persistent monomorphization state for one lazy compilation and checker stream.
///
/// Pass every refresh window, even at an unchanged epoch. Recreate the session
/// when replacing the HIR program or checker stream. Body changes, missed epochs
/// and untracked channels discard all retained state. Results own their types;
/// each call borrows bodies afresh from the supplied MIR.
#[derive(Default)]
pub struct MonoSession {
    cache: Cache,
    epoch: Option<u64>,
    context: Option<Context>,
}

#[derive(Clone, PartialEq, Eq)]
enum Context {
    Entry(bool),
    Instance(DeferredSig, Vec<(String, Type)>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// A root request, including the complete checker instance identity.
pub(super) enum Root {
    Init(usize),
    Function {
        base: String,
        args: Vec<Type>,
        instance: Option<brass_hir::InstanceKey>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Key {
    root: Root,
    prefix: Vec<u64>,
}

/// Position in a MIR snapshot. Every body mutation resets its generation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct BodyHandle {
    generation: u64,
    index: usize,
}

// Concrete storage is owned in local_types and the effective symbols in symbol,
// keyed and closure_targets. No borrowed negotiation state survives a refresh.
struct MonoFacts {
    body: BodyHandle,
    symbol: String,
    type_args: Vec<Type>,
    ret: Type,
    local_types: Vec<Type>,
    captures: Vec<LocalId>,
    is_closure: bool,
    fallible: bool,
    keyed: HashMap<brass_parser::Span, String>,
    fields: HashMap<brass_parser::Span, Vec<String>>,
    closure_targets: HashMap<ClosureId, String>,
}

impl MonoFacts {
    fn rehydrate<'m>(&self, bodies: &[&'m MirBody], generation: u64) -> MonoFunction<'m> {
        assert_eq!(self.body.generation, generation);
        MonoFunction {
            body: bodies[self.body.index],
            symbol: self.symbol.clone(),
            type_args: self.type_args.clone(),
            ret: self.ret.clone(),
            local_types: self.local_types.clone(),
            captures: self.captures.clone(),
            is_closure: self.is_closure,
            fallible: self.fallible,
            keyed: self.keyed.clone(),
            fields: self.fields.clone(),
            closure_targets: self.closure_targets.clone(),
        }
    }
}

struct Outcome {
    id: u64,
    result: Result<String, String>,
    facts: Vec<MonoFacts>,
    globals: HashMap<String, Type>,
    deferred: Option<HashMap<String, DeferredSig>>,
    demands: Vec<(String, Vec<Type>, bool)>,
    observations: u64,
    failures: HashMap<String, MissingFailure>,
    overflow: Option<String>,
    reads: HashSet<Read>,
}

#[derive(Default)]
struct Cache {
    entries: HashMap<Key, Rc<Outcome>>,
    scans: HashMap<BodyHandle, Rc<BodyScans>>,
    generation: u64,
    next_id: u64,
}

/// Pass-local borrowed body index and read tracking; only `cache` survives.
#[derive(Default)]
pub(super) struct Run<'m> {
    cache: Cache,
    enabled: bool,
    bodies: Vec<&'m MirBody>,
    handles: HashMap<usize, BodyHandle>,
    prefix: Vec<u64>,
    reads: RefCell<HashSet<Read>>,
    hits: usize,
    misses: usize,
}

impl MonoSession {
    fn start<'m>(
        &mut self,
        mir: &'m MirProgram,
        changes: &brass_mir::ChangedInputs,
        context: Context,
    ) -> Run<'m> {
        let reset = changes.full_reset
            || self.epoch != Some(changes.base_epoch)
            || self.context.as_ref() != Some(&context);
        if reset {
            self.cache.entries.clear();
            self.cache.scans.clear();
            self.cache.generation = self
                .cache
                .generation
                .checked_add(1)
                .expect("MIR generation exhausted");
        } else {
            self.cache
                .entries
                .retain(|_, outcome| !outcome.reads.iter().any(|read| read.changed(changes)));
        }
        self.epoch = Some(changes.epoch);
        self.context = Some(context);
        let bodies: Vec<_> = mir
            .functions
            .iter()
            .map(|f| &f.body)
            .chain(mir.methods.iter().map(|m| &m.body))
            .chain(mir.closures.iter().map(|c| &c.body))
            .chain(mir.inits.iter().map(|i| &i.body))
            .collect();
        let handles = bodies
            .iter()
            .enumerate()
            .map(|(index, body)| {
                (
                    *body as *const MirBody as usize,
                    BodyHandle {
                        generation: self.cache.generation,
                        index,
                    },
                )
            })
            .collect();
        Run {
            cache: std::mem::take(&mut self.cache),
            enabled: true,
            bodies,
            handles,
            ..Run::default()
        }
    }

    fn finish(&mut self, mono: &mut Monomorphizer<'_, '_>) {
        let run = std::mem::take(&mut mono.session);
        tracing::debug!(target: "brass::perf", hits = run.hits, misses = run.misses, retained = run.cache.entries.len(), "mono session roots");
        self.cache = run.cache;
    }

    /// Type initializers and main, reusing roots unaffected by this refresh.
    /// Without runtime deferral, use the ordinary uncached traversal.
    pub fn entry<'m>(
        &mut self,
        mir: &'m MirProgram,
        program: &'m Program,
        defer: bool,
        returns: HashMap<(String, Vec<Type>), Type>,
        changes: &brass_mir::ChangedInputs,
    ) -> Result<MonoProgram<'m>, MonoStop> {
        if !defer {
            // The eager postponement queue belongs to a whole traversal.
            // It is not part of a lazy root's replayable effects.
            *self = Self::default();
            return monomorphize_entry_with_returns(mir, program, false, returns);
        }
        let mut mono = Monomorphizer::new(mir, program);
        mono.session = self.start(mir, changes, Context::Entry(defer));
        mono.instance_returns = returns;
        if defer {
            mono.defer = Some(HashMap::default());
        }
        let result = entry::entry_roots(&mut mono, mir, program);
        self.finish(&mut mono);
        result.map(|(inits, skip)| {
            let mut program = mono.into_program(inits, program);
            program.main_skip = skip;
            program
        })
    }

    /// Type one runtime target across its retries, in a separate compilation epoch.
    pub fn instance<'m>(
        &mut self,
        mir: &'m MirProgram,
        program: &'m Program,
        target: &DeferredSig,
        globals: &[(String, Type)],
        returns: HashMap<(String, Vec<Type>), Type>,
        changes: &brass_mir::ChangedInputs,
    ) -> Result<MonoProgram<'m>, MonoStop> {
        let mut mono = Monomorphizer::new(mir, program);
        mono.session = self.start(
            mir,
            changes,
            Context::Instance(target.clone(), globals.to_vec()),
        );
        mono.defer = Some(HashMap::default());
        mono.instance_returns = returns;
        mono.global_types = globals.iter().cloned().collect();
        let result = entry::instance_root(&mut mono, &target.base, target.type_args.clone());
        self.finish(&mut mono);
        result.map(|()| mono.into_program(Vec::new(), program))
    }
}

impl<'m> Monomorphizer<'m, '_> {
    /// Observe presence or absence while a retained root is being typed.
    pub(super) fn read_input(&self, read: Read) {
        if self.session.enabled {
            self.session.reads.borrow_mut().insert(read);
        }
    }

    /// Read a return contract and track its exact channel key.
    pub(super) fn instance_return(&self, base: &str, args: &[Type]) -> Option<&Type> {
        let key = (base.to_string(), args.to_vec());
        if self.session.enabled {
            self.read_input(Read::Return(key.0.clone(), key.1.clone()));
        }
        self.instance_returns.get(&key)
    }

    /// Reuse structural scans only within an unchanged MIR generation.
    pub(super) fn body_scans(&mut self, body: &MirBody) -> Rc<BodyScans> {
        if !self.session.enabled {
            return Rc::new(BodyScans::of(body));
        }
        let handle = self.session.handles[&(body as *const MirBody as usize)];
        Rc::clone(
            self.session
                .cache
                .scans
                .entry(handle)
                .or_insert_with(|| Rc::new(BodyScans::of(body))),
        )
    }

    /// Type a function root under its complete instance identity.
    pub(super) fn function_root(&mut self, base: &str, args: Vec<Type>) -> Result<String, String> {
        let root = Root::Function {
            base: base.to_string(),
            instance: self.function_instance(base, &args),
            args: args.clone(),
        };
        self.session_root(root, |mono| mono.instantiate_fn(base, args))
    }

    /// Replay or evaluate one root together with its ordinary pass effects.
    pub(super) fn session_root(
        &mut self,
        root: Root,
        run: impl FnOnce(&mut Self) -> Result<String, String>,
    ) -> Result<String, String> {
        if !self.session.enabled {
            return run(self);
        }
        let key = Key {
            root,
            prefix: self.session.prefix.clone(),
        };
        if let Some(outcome) = self.session.cache.entries.get(&key).cloned() {
            self.session.hits += 1;
            self.session.prefix.push(outcome.id);
            self.session
                .reads
                .borrow_mut()
                .extend(outcome.reads.iter().cloned());
            for facts in &outcome.facts {
                let instance = facts.rehydrate(&self.session.bodies, self.session.cache.generation);
                self.instance_log.push(instance.symbol.clone());
                self.instances.insert(instance.symbol.clone(), instance);
            }
            self.global_types.clone_from(&outcome.globals);
            self.defer.clone_from(&outcome.deferred);
            self.missing_demands.replace(outcome.demands.clone());
            self.missing_observations
                .set(self.missing_observations.get() + outcome.observations);
            self.missing_failures.clone_from(&outcome.failures);
            self.nesting_overflow.clone_from(&outcome.overflow);
            return outcome.result.clone();
        }
        self.session.misses += 1;
        // Numeric channel presence selects the ordinary fast path, including
        // closure identity. An absent table is a dependency too.
        self.read_input(Read::NumericCalls);
        let watermark = self.instance_log.len();
        let observations = self.missing_observations.get();
        let result = run(self);
        let facts = self.instance_log[watermark..]
            .iter()
            .map(|symbol| {
                let instance = &self.instances[symbol];
                MonoFacts {
                    body: self.session.handles[&(instance.body as *const MirBody as usize)],
                    symbol: instance.symbol.clone(),
                    type_args: instance.type_args.clone(),
                    ret: instance.ret.clone(),
                    local_types: instance.local_types.clone(),
                    captures: instance.captures.clone(),
                    is_closure: instance.is_closure,
                    fallible: instance.fallible,
                    keyed: instance.keyed.clone(),
                    fields: instance.fields.clone(),
                    closure_targets: instance.closure_targets.clone(),
                }
            })
            .collect();
        self.session.cache.next_id = self
            .session
            .cache
            .next_id
            .checked_add(1)
            .expect("mono root identity exhausted");
        let id = self.session.cache.next_id;
        let outcome = Outcome {
            id,
            result: result.clone(),
            facts,
            globals: self.global_types.clone(),
            deferred: self.defer.clone(),
            demands: self.missing_demands.borrow().clone(),
            observations: self.missing_observations.get() - observations,
            failures: self.missing_failures.clone(),
            overflow: self.nesting_overflow.clone(),
            reads: self.session.reads.borrow().clone(),
        };
        self.session.cache.entries.insert(key, Rc::new(outcome));
        self.session.prefix.push(id);
        result
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod numeric_tests;
