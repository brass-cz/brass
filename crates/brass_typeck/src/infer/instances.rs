//! The callable instance each channel observation belongs to.
//!
//! A generic body is elaborated once per call-site instantiation, but MIR
//! lowers it once: a fact that differs between instantiations (the type a
//! witness-free constructor builds) has no single span-keyed value. The
//! checker therefore remembers which instance it is elaborating and tags the
//! observations that feed such channels with it; publishing turns the tag into
//! a [`brass_hir::InstanceKey`] once the substitution has pinned its argument
//! types, and monomorphization reads the value back for the instance it types
//! (see [`brass_hir::InstanceChannel`]).

use super::*;
use brass_hir::{InstanceCallable, InstanceKey, TypedExprKind};

/// The callable instance an elaboration checks, spelled as the checker sees
/// it while elaborating: the argument types may still hold inference
/// variables that later statements or bodies pin, so the published key is
/// derived from the tag only when its observations are flushed.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct InstanceTag {
    pub(super) callable: InstanceCallable,
    pub(super) args: Vec<Type>,
    /// Concrete return-origin storage negotiated by the enclosing solution.
    pub(super) numeric_layout: Option<brass_hir::NumericLayout>,
}

/// A shared [`InstanceTag`]. The checker interns every tag it records
/// observations under (`Checker::intern_tag`), so equal tags are one
/// allocation and a tag compares and hashes by address: tagging an
/// observation or a journal entry costs no type traversal. (A memo entry's
/// skeleton tags are templates, never recorded under; they are interned
/// when a replay instantiates them.)
#[derive(Clone, Debug)]
pub(super) struct TagRef(Rc<InstanceTag>);

impl PartialEq for TagRef {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for TagRef {}

impl std::hash::Hash for TagRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state);
    }
}

impl std::ops::Deref for TagRef {
    type Target = InstanceTag;

    fn deref(&self) -> &InstanceTag {
        &self.0
    }
}

impl TagRef {
    /// A tag that is not interned: a memo skeleton's template.
    pub(super) fn template(tag: InstanceTag) -> Self {
        TagRef(Rc::new(tag))
    }
}

/// One aggregate-seed observation (the expression kinds
/// [`stream::aggregates_from_kind`] accepts) made while elaborating an
/// instance: the typed expression `index` of `Checker::typed` (kept in step
/// when the typed entries are reordered, see `Checker::defer_typed_entries`).
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstanceTyped {
    pub(super) tag: TagRef,
    pub(super) index: u32,
}

impl Checker<'_> {
    /// The instance the innermost active elaboration checks, if any: `None`
    /// in module initializers and shared preparation. Dedicated function passes
    /// carry their declaration frame; call-site elaborations carry their inputs.
    pub(super) fn current_instance(&self) -> Option<TagRef> {
        self.instance_stack.last().cloned()
    }

    /// The interned tag of `callable` at `args`, allocated only the first
    /// time that instance is seen.
    pub(super) fn intern_tag(&mut self, callable: InstanceCallable, args: &[Type]) -> TagRef {
        self.intern_numeric_tag(callable, args, None)
    }

    /// Intern a tag including its concrete returned-origin storage contract.
    fn intern_numeric_tag(
        &mut self,
        callable: InstanceCallable,
        args: &[Type],
        numeric_layout: Option<brass_hir::NumericLayout>,
    ) -> TagRef {
        let hash = {
            use std::hash::{Hash, Hasher};
            let mut hasher = fxhash::FxHasher::default();
            callable.hash(&mut hasher);
            args.hash(&mut hasher);
            if let Some(layout) = &numeric_layout {
                layout.hash(&mut hasher);
            }
            hasher.finish()
        };
        let bucket = self.instance_tags.entry(hash).or_default();
        if let Some(interned) = bucket.iter().find(|tag| {
            tag.callable == callable && tag.args == args && tag.numeric_layout == numeric_layout
        }) {
            return TagRef(Rc::clone(interned));
        }
        let interned = Rc::new(InstanceTag {
            callable,
            args: args.to_vec(),
            numeric_layout,
        });
        bucket.push(Rc::clone(&interned));
        TagRef(interned)
    }

    /// Enter the elaboration of `callable` at `args`; observations recorded
    /// until the matching [`Checker::leave_instance`] belong to it (or to an
    /// instance nested inside it).
    pub(super) fn enter_instance(&mut self, callable: InstanceCallable, args: &[Type]) {
        let tag = self.intern_tag(callable, args);
        self.instance_stack.push(tag);
    }

    /// Retag a dedicated body after its own numeric settlement.
    pub(super) fn settle_numeric_instance(&mut self, layout: Option<brass_hir::NumericLayout>) {
        if !self.numeric_enabled {
            return;
        }
        if let Some(tag) = self.current_instance() {
            let next = self.intern_numeric_tag(tag.callable.clone(), &tag.args, layout);
            *self.instance_stack.last_mut().unwrap() = next;
        }
    }

    /// Close the innermost elaboration [`Checker::enter_instance`] opened.
    pub(super) fn leave_instance(&mut self) {
        self.instance_stack.pop();
    }

    /// The interned instantiation of the memo template `tag` under
    /// `substitution` (a replay), cached per template within one replay.
    pub(super) fn replay_tag(
        &mut self,
        tag: &TagRef,
        substitution: &std::collections::BTreeMap<u32, Type>,
        cache: &mut HashMap<TagRef, TagRef>,
    ) -> TagRef {
        if let Some(done) = cache.get(tag) {
            return done.clone();
        }
        let args: Vec<Type> = tag
            .args
            .iter()
            .map(|arg| brass_hir::substitute_vars(arg, substitution))
            .collect();
        let instantiated =
            self.intern_numeric_tag(tag.callable.clone(), &args, tag.numeric_layout.clone());
        cache.insert(tag.clone(), instantiated.clone());
        instantiated
    }

    /// Whether an observation of this kind and type can carry an aggregate
    /// seed, so it is worth attributing to its instance. Only the expression
    /// kinds [`stream::aggregates_from_kind`] accepts can; of the
    /// identifiers only a function value, and never a scalar value --
    /// keeping those would only grow the table. A type whose constructor is
    /// still open may become anything (a replay substitutes it), so it is
    /// kept.
    pub(super) fn seeds_per_instance(&self, kind: &TypedExprKind, ty: &Type) -> bool {
        if !stream::aggregates_from_kind(kind) {
            return false;
        }
        if matches!(
            kind,
            TypedExprKind::TypeOfAnnotation
                | TypedExprKind::NumericBinding
                | TypedExprKind::NumericArgument
                | TypedExprKind::InstanceNumericBinding
                | TypedExprKind::InstanceNumericArgument
        ) {
            return true;
        }
        match self.head_constructor(ty) {
            Type::Unknown(_) => true,
            Type::Fun(..) => true,
            Type::Bool | Type::Int(_) | Type::Float(_) | Type::Str | Type::Void | Type::Never => {
                false
            }
            _ => !matches!(kind, TypedExprKind::Ident(_)),
        }
    }

    /// Attribute the typed expression `index` to `tag` (deduplicated:
    /// replays and re-elaborations of one instance repeat identical
    /// observations).
    pub(super) fn record_instance_typed(&mut self, tag: TagRef, index: usize) {
        let entry = InstanceTyped {
            tag,
            index: index as u32,
        };
        if self.instance_typed_seen.insert(entry.clone()) {
            self.instance_typed.push(entry);
        }
    }

    /// The constructor of `ty` under the current substitution, seen through
    /// passing modes, without copying it.
    fn head_constructor<'t>(&'t self, ty: &'t Type) -> &'t Type {
        let mut head = self.solver.resolve_head_ref(ty);
        while let Type::Ref(inner) | Type::Mut(inner) | Type::ConstOf(inner) = head {
            head = self.solver.resolve_head_ref(inner);
        }
        head
    }

    /// The published key of `tag` under the current substitution, or `None`
    /// while an argument type is still open.
    pub(crate) fn instance_key_of(&self, tag: &InstanceTag) -> Option<InstanceKey> {
        let args: Vec<Type> = tag.args.iter().map(|arg| self.resolve(arg)).collect();
        let mut key = InstanceKey::new(self.program, tag.callable.clone(), &args)?;
        key.numeric_layout = tag.numeric_layout.clone();
        Some(key)
    }

    /// The instance observations, their instances resolved against the
    /// final substitution, dropping those whose instance never became fully
    /// known (an elaboration nested in a generic declaration's own pass).
    /// The typed expressions they index are already resolved (see
    /// `Checker::finalize_typed`).
    pub(super) fn finalized_instance_typed(&self) -> stream::InstanceObservations {
        let mut ids: HashMap<TagRef, Option<u32>> = HashMap::default();
        let mut observations = stream::InstanceObservations::default();
        for entry in &self.instance_typed {
            let id = *ids.entry(entry.tag.clone()).or_insert_with(|| {
                let key = self.instance_key_of(&entry.tag)?;
                observations.keys.push(key);
                Some(observations.keys.len() as u32 - 1)
            });
            if let Some(id) = id {
                observations.entries.push((id, entry.index));
            }
        }
        observations
    }
}

/// One reflective (`-> infer!`) call observation: the call at `span` keyed
/// as (receiver symbol, method, key) by the elaboration of `instance` (or by
/// a pass outside any instance).
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct KeyedObservation {
    pub(super) instance: Option<TagRef>,
    pub(super) span: Span,
    pub(super) receiver: String,
    pub(super) method: String,
    pub(super) key: Type,
}

/// A reflective call's target: (receiver type symbol, method, key).
pub(crate) type KeyedTarget = (String, String, Type);

impl Checker<'_> {
    /// Remember a reflective call observation (deduplicated).
    pub(super) fn record_keyed_observation(&mut self, observation: KeyedObservation) {
        if !self.keyed_observations.contains(&observation) {
            self.keyed_observations.push(observation);
        }
    }

    /// The reflective calls of the analysis, settled against the final
    /// substitution: per span, the target every instance agrees on, plus --
    /// for a span whose instances key it differently (a generic body calling
    /// `j.into()` at `typeof(sample)`) -- the target of each instance.
    ///
    /// Only fully known keys count as observations; a span observed with
    /// open keys alone (a generic body no instance elaborated) keeps its last
    /// observation. A divergent span still has a span-level entry
    /// (one of its targets, chosen deterministically) so it is known to be
    /// reflective; its dispatch comes from the per-instance targets. An
    /// instance that keyed one span two different ways has no target there.
    pub(super) fn settled_keyed_calls(
        &self,
    ) -> (
        HashMap<Span, KeyedTarget>,
        brass_hir::InstanceChannel<KeyedTarget>,
    ) {
        let mut order: Vec<Span> = Vec::new();
        let mut by_span: HashMap<Span, Vec<&KeyedObservation>> = HashMap::default();
        for observation in &self.keyed_observations {
            let entry = by_span.entry(observation.span).or_default();
            if entry.is_empty() {
                order.push(observation.span);
            }
            entry.push(observation);
        }
        let mut span_level: HashMap<Span, KeyedTarget> = HashMap::default();
        let mut per_instance: brass_hir::InstanceChannel<KeyedTarget> = HashMap::default();
        for span in order {
            let observations = &by_span[&span];
            let resolved: Vec<(Option<&TagRef>, KeyedTarget)> = observations
                .iter()
                .map(|o| {
                    let key = peel_modes(&self.resolve(&o.key)).clone();
                    (
                        o.instance.as_ref(),
                        (o.receiver.clone(), o.method.clone(), key),
                    )
                })
                .collect();
            let mut known: Vec<&KeyedTarget> = resolved
                .iter()
                .map(|(_, target)| target)
                .filter(|(_, _, key)| brass_hir::is_fully_known(key))
                .collect();
            known.sort_by(|a, b| {
                (&a.0, &a.1, brass_hir::type_key(&a.2)).cmp(&(
                    &b.0,
                    &b.1,
                    brass_hir::type_key(&b.2),
                ))
            });
            known.dedup();
            match known.as_slice() {
                [] => {
                    let (_, last) = resolved.last().expect("a span has an observation");
                    span_level.insert(span, last.clone());
                }
                [only] => {
                    span_level.insert(span, (*only).clone());
                }
                [first, ..] => {
                    span_level.insert(span, (*first).clone());
                    let mut targets: HashMap<brass_hir::InstanceKey, Option<KeyedTarget>> =
                        HashMap::default();
                    for (tag, target) in &resolved {
                        let Some(tag) = tag else { continue };
                        if !brass_hir::is_fully_known(&target.2) {
                            continue;
                        }
                        let Some(instance) = self.instance_key_of(tag) else {
                            continue;
                        };
                        match targets.get(&instance) {
                            None => {
                                targets.insert(instance, Some(target.clone()));
                            }
                            Some(Some(prev)) if prev != target => {
                                targets.insert(instance, None);
                            }
                            _ => {}
                        }
                    }
                    let targets: HashMap<_, _> = targets
                        .into_iter()
                        .filter_map(|(instance, target)| Some((instance, target?)))
                        .collect();
                    per_instance.insert(span, targets);
                }
            }
        }
        (span_level, per_instance)
    }
}

impl Checker<'_> {
    /// Reject a recursive call that would instantiate its callable at types
    /// growing without bound (polymorphic recursion: `f(x)` calling
    /// `f([x])`): monomorphization would need a new instance for every
    /// level. `callable` is being re-entered at `args`; `params` are its
    /// parameter names (the receiver first for a method), for the message.
    ///
    /// The call is rejected when an argument type properly contains the
    /// type the innermost active instance of the callable was entered at, in
    /// the same position, and that containment is evidence of growth: the
    /// outer type is still generic (the body passes its own parameter back
    /// wrapped -- the declaration's own pass shows this), or the outer
    /// instance was itself entered that way from the instance below it. A
    /// one-off change of concrete types (`f(5)` calling `f([1, 2])` once,
    /// which then recurses at that type) is ordinary recursion.
    pub(super) fn check_polymorphic_recursion(
        &mut self,
        callable: &InstanceCallable,
        name: &str,
        params: &[&str],
        args: &[Type],
        span: Span,
    ) {
        let resolve_all = |this: &Self, args: &[Type]| -> Vec<Type> {
            args.iter()
                .map(|arg| peel_modes(&this.resolve(arg)).clone())
                .collect()
        };
        let mut frames = self
            .instance_stack
            .iter()
            .rev()
            .filter(|tag| tag.callable == *callable);
        let Some(outer) = frames.next() else {
            return;
        };
        let inner = resolve_all(self, args);
        let outer = resolve_all(self, &outer.args);
        let Some(position) = growth_position(&outer, &inner) else {
            return;
        };
        let generic = !brass_hir::is_fully_known(&outer[position]);
        let repeated = frames.next().is_some_and(|below| {
            growth_position(&resolve_all(self, &below.args), &outer) == Some(position)
        });
        if !(generic || repeated) || !self.polymorphic_recursion_reported.insert(span) {
            return;
        }
        let param = params.get(position).copied().unwrap_or("_");
        self.errors.push(TypeError {
            message: format!(
                "polymorphic recursion is not supported: `{name}` calls itself with `{param}` \
                 at `{}`, which contains the type `{}` it is instantiated at, so every call \
                 would need a new instance at a larger type; call it at the same type",
                inner[position].display(),
                outer[position].display()
            ),
            span,
        });
    }
}

/// The first argument position at which `inner` properly contains `outer`
/// (the same position's type as a strict part of it).
fn growth_position(outer: &[Type], inner: &[Type]) -> Option<usize> {
    outer
        .iter()
        .zip(inner)
        .position(|(outer, inner)| properly_contains(inner, outer))
}

/// Whether `part` occurs strictly inside `ty`.
fn properly_contains(ty: &Type, part: &Type) -> bool {
    let inside = |t: &Type| t == part || properly_contains(t, part);
    match ty {
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Nullable(inner)
        | Type::ConstOf(inner)
        | Type::Mut(inner)
        | Type::Ref(inner) => inside(inner),
        Type::Tuple(elems) => elems.iter().any(inside),
        Type::Fun(params, ret) => params.iter().any(inside) || inside(ret),
        Type::Record(n) | Type::Sum(n) => n.substitution.iter().any(|(_, t)| inside(t)),
        _ => false,
    }
}

/// How the elaborations of one `recv.name(..)` call resolved it.
#[derive(Clone, Default)]
pub(super) struct CallSite {
    /// Type-test patterns of the receivers whose function-valued field it
    /// called.
    pub(super) field_receivers: Vec<Type>,
    /// Whether some elaboration resolved it to a method instead.
    pub(super) method: bool,
}

impl Checker<'_> {
    /// The field calls of the analysis (see [`Inference::field_calls`]).
    pub(super) fn field_call_map(&self) -> HashMap<Span, Option<Vec<Type>>> {
        self.call_sites
            .iter()
            .filter(|(_, site)| !site.field_receivers.is_empty())
            .map(|(span, site)| {
                let receivers = site.method.then(|| site.field_receivers.clone());
                (*span, receivers)
            })
            .collect()
    }
}
