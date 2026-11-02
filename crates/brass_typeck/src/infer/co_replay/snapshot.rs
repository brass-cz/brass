//! Test-only semantic snapshots of equivalent checker forks.
//!
//! Pre-existing variables retain their fork identity. Fresh identities are
//! renamed consistently from inputs, results and other retained effects. Solver resolutions preserve
//! aliases and kinds. Operational caches, budgets and memo contents are excluded.
//! Channel maps are unordered; observations, diagnostics, links and boundaries
//! retain their order. A caller retains every boundary in `EffectHistory` so a
//! transient removal cannot disappear behind an equal final channel table.

use super::super::{Checker, channel_changes::ChannelChanges, delta};
use crate::constraint::ShapeConstraint;
use crate::stream::{ChannelDelta, FlushState};
use brass_hir::{InstanceKey, Type};
use std::collections::BTreeMap;
use std::fmt::Debug;

/// One test consumer's complete publication history, including empty boundaries.
#[derive(Default)]
pub(super) struct EffectHistory {
    /// Variables already owned before the compared operation.
    baseline_vars: u32,
    /// Incremental publication cursors owned by this test consumer.
    state: FlushState,
    /// Deltas in emission order, never merged across boundaries.
    deltas: Vec<ChannelDelta>,
}

impl EffectHistory {
    /// Preserve every pre-existing solver variable, even if the operation does
    /// not mention it. Unreachable fresh scratch variables are not effects.
    pub(super) fn new(checker: &Checker<'_>) -> Self {
        Self {
            baseline_vars: checker.next_unknown,
            ..Self::default()
        }
    }

    /// Publish at the same body boundary on each equivalent test fork.
    pub(super) fn boundary(&mut self, checker: &Checker<'_>) {
        self.deltas
            .push(delta::flush_delta(checker, &mut self.state, false));
    }
}

/// An ordered inventory whose comparison names the first differing effect.
#[derive(Debug, PartialEq, Eq)]
pub(in crate::infer) struct EffectSnapshot(Vec<(String, String)>);

/// Consistent variable renaming shared by every field in one snapshot.
#[derive(Default)]
struct Canonical {
    /// Original variable to its canonical slot, including solved variables.
    vars: BTreeMap<u32, Type>,
}

impl Canonical {
    /// Retain complete type structure and nominal identity while renaming ids.
    fn ty(&mut self, ty: &Type) -> Type {
        self.register(ty);
        brass_hir::substitute_vars(ty, &self.vars)
    }

    /// Assign slots by structural first occurrence, retaining repeated aliases.
    fn register(&mut self, ty: &Type) {
        match ty {
            Type::Unknown(id) if *id == brass_hir::INFER_VAR => {}
            Type::Unknown(id) => {
                let next = self.vars.len() as u32;
                self.vars.entry(*id).or_insert(Type::Unknown(next));
            }
            Type::Array(inner, _)
            | Type::Slice(inner)
            | Type::Nullable(inner)
            | Type::ConstOf(inner)
            | Type::Mut(inner)
            | Type::Ref(inner) => self.register(inner),
            Type::Tuple(items) => items.iter().for_each(|ty| self.register(ty)),
            Type::Fun(args, ret) => {
                args.iter().for_each(|ty| self.register(ty));
                self.register(ret);
            }
            Type::Record(nominal) | Type::Sum(nominal) => {
                nominal
                    .substitution
                    .iter()
                    .for_each(|(_, ty)| self.register(ty));
            }
            _ => {}
        }
    }

    /// Register every variable mentioned only by a deferred shape as well.
    fn shape(&mut self, shape: &ShapeConstraint) -> ShapeConstraint {
        match shape {
            ShapeConstraint::Equals(ty) => self.register(ty),
            ShapeConstraint::Operand { other, result, .. } => {
                self.register(other);
                if let Some(ty) = result {
                    self.register(ty);
                }
            }
            ShapeConstraint::HasMethod(_)
            | ShapeConstraint::HasField(_)
            | ShapeConstraint::Indexable => {}
        }
        shape.substitute(&self.vars)
    }

    /// Rename only argument variables; callable and numeric layout stay exact.
    fn instance(&mut self, key: &mut InstanceKey) {
        key.args = key.args.iter().map(|ty| self.ty(ty)).collect();
    }
}

/// Sort a semantic map or set, without sorting any nested ordered sequence.
fn unordered<T: Debug>(values: impl IntoIterator<Item = T>) -> Vec<String> {
    let mut values: Vec<_> = values
        .into_iter()
        .map(|value| format!("{value:?}"))
        .collect();
    values.sort();
    values
}

/// Interned tags can have different allocation addresses on replay. Compare
/// their full semantic identities, coalescing only exact idempotent repeats
/// while retaining first-observation order. Co-return links never use this.
fn unique_observations<T: Debug>(values: impl IntoIterator<Item = T>) -> Vec<String> {
    let mut seen = std::collections::BTreeSet::new();
    values
        .into_iter()
        .map(|value| format!("{value:?}"))
        .filter(|value| seen.insert(value.clone()))
        .collect()
}

impl EffectSnapshot {
    /// Make an independent test checker authoritative for a fresh consumer.
    /// Production probe clones intentionally cannot publish; this explicit test
    /// fork starts a new publication history rather than inheriting cursors.
    pub(in crate::infer) fn fork<'a>(checker: &Checker<'a>) -> Checker<'a> {
        let mut fork = checker.clone();
        *fork.channel_changes.get_mut() = ChannelChanges::default();
        fork
    }

    /// Project declaration-owned fields, schemes, qualified globals and their
    /// aliases after independent shared preparation. Body-local diagnostics,
    /// publications and unused sum method returns are deliberately excluded.
    pub(in crate::infer) fn capture_shared(checker: &Checker<'_>) -> Self {
        let mut snapshot = Self(Vec::new());
        let mut canon = Canonical::default();
        for id in 0..checker.program.next_infer_var {
            canon.ty(&Type::Unknown(id));
        }
        let mut cells = BTreeMap::new();
        for info in checker.program.types.values() {
            let groups = match &info.kind {
                brass_hir::TypeKind::Record { fields, .. } => vec![(String::new(), fields)],
                brass_hir::TypeKind::Sum { variants } => variants
                    .iter()
                    .map(|v| (v.name.clone(), &v.fields))
                    .collect(),
            };
            for (variant, fields) in groups {
                for field in fields {
                    if let Some(ty) = &field.resolved_ty {
                        cells.insert(
                            format!("{}.{}:{}", info.symbol, variant, field.name),
                            ty.clone(),
                        );
                    }
                }
            }
        }
        for (module, globals) in &checker.global_defs {
            for (name, ty) in globals {
                cells.insert(format!("global:{}/{}", module.join("/"), name), ty.clone());
            }
        }
        let shapes = cells
            .values()
            .flat_map(brass_hir::type_vars)
            .collect::<std::collections::BTreeSet<_>>();
        snapshot.put(
            "shared cells",
            cells
                .into_iter()
                .map(|(name, ty)| {
                    (
                        name,
                        canon.ty(&ty),
                        canon.ty(&checker.solver.resolve_reference(&ty)),
                    )
                })
                .collect::<Vec<_>>(),
        );
        snapshot.put(
            "shared shapes",
            shapes
                .into_iter()
                .map(|id| {
                    (
                        canon.ty(&Type::Unknown(id)),
                        checker.shape_constraints.get(&id).map(|shapes| {
                            shapes
                                .iter()
                                .map(|shape| canon.shape(shape))
                                .collect::<Vec<_>>()
                        }),
                    )
                })
                .collect::<Vec<_>>(),
        );
        snapshot.put(
            "schemes",
            unordered(
                checker
                    .build_schemes()
                    .into_iter()
                    .collect::<BTreeMap<_, _>>(),
            ),
        );
        snapshot.put(
            "record co return links",
            checker
                .co_return_links
                .iter()
                .collect::<BTreeMap<_, _>>()
                .into_iter()
                .map(|(owner, links)| {
                    (
                        owner,
                        links
                            .iter()
                            .map(|(a, b)| {
                                (canon.ty(&checker.resolve(a)), canon.ty(&checker.resolve(b)))
                            })
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
        );
        snapshot.put("co global reads", unordered(&checker.co_global_reads));
        snapshot
    }

    /// Capture input/result identities, the solver, co effects and every channel.
    /// Finalization occurs on a private test fork and cannot mutate the subject.
    pub(super) fn capture(
        checker: &Checker<'_>,
        inputs: &[Type],
        result: &Type,
        history: &EffectHistory,
    ) -> Self {
        let mut snapshot = Self(Vec::new());
        let mut canon = Canonical::default();
        for id in 0..history.baseline_vars {
            canon.ty(&Type::Unknown(id));
        }
        snapshot.put(
            "inputs",
            inputs.iter().map(|ty| canon.ty(ty)).collect::<Vec<_>>(),
        );
        snapshot.put("result", canon.ty(result));
        snapshot.put(
            "resolved inputs",
            inputs
                .iter()
                .map(|ty| canon.ty(&checker.solver.resolve_reference(ty)))
                .collect::<Vec<_>>(),
        );
        snapshot.put(
            "resolved result",
            canon.ty(&checker.solver.resolve_reference(result)),
        );
        snapshot.put(
            "deferred shapes",
            unordered(
                checker
                    .shape_constraints
                    .iter()
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .map(|(id, shapes)| {
                        (
                            canon.ty(&Type::Unknown(*id)),
                            shapes
                                .iter()
                                .map(|shape| canon.shape(shape))
                                .collect::<Vec<_>>(),
                        )
                    }),
            ),
        );
        snapshot.put(
            "co return links",
            unordered(
                checker
                    .co_return_links
                    .iter()
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .map(|(root, links)| {
                        (
                            root,
                            links
                                .iter()
                                .map(|(left, right)| (canon.ty(left), canon.ty(right)))
                                .collect::<Vec<_>>(),
                        )
                    }),
            ),
        );
        snapshot.put("co global reads", unordered(&checker.co_global_reads));
        snapshot.put(
            "co method returns",
            unordered(
                checker
                    .co_method_returns
                    .iter()
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .map(|(key, ty)| (key, canon.ty(ty))),
            ),
        );
        snapshot.put(
            "schemes",
            unordered(
                checker
                    .schemes
                    .iter()
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .map(|(name, scheme)| {
                        let mut scheme = scheme.clone();
                        scheme.params = scheme
                            .params
                            .iter()
                            .map(|id| match canon.ty(&Type::Unknown(*id)) {
                                Type::Unknown(id) => id,
                                _ => unreachable!(),
                            })
                            .collect();
                        for (_, ty) in &mut scheme.fields {
                            *ty = canon.ty(ty);
                        }
                        for method in scheme.methods.values_mut() {
                            for (_, ty) in &mut method.params {
                                *ty = canon.ty(ty);
                            }
                            method.ret = canon.ty(&method.ret);
                        }
                        (name, scheme)
                    }),
            ),
        );
        snapshot.put("errors", &checker.errors);
        snapshot.put("warnings", &checker.warnings);
        snapshot.put(
            "typed observations",
            checker
                .typed
                .expressions
                .iter()
                .map(|entry| {
                    (
                        &entry.kind,
                        entry.span,
                        canon.ty(&entry.ty),
                        entry.constness,
                    )
                })
                .collect::<Vec<_>>(),
        );
        snapshot.put(
            "instance observations",
            unique_observations(checker.instance_typed.iter().map(|entry| {
                let typed = &checker.typed.expressions[entry.index as usize];
                (
                    &entry.tag.callable,
                    entry
                        .tag
                        .args
                        .iter()
                        .map(|ty| canon.ty(ty))
                        .collect::<Vec<_>>(),
                    &entry.tag.numeric_layout,
                    &typed.kind,
                    typed.span,
                    canon.ty(&typed.ty),
                )
            })),
        );
        snapshot.put(
            "keyed observations",
            unique_observations(checker.keyed_observations.iter().map(|entry| {
                (
                    entry.span,
                    &entry.receiver,
                    &entry.method,
                    canon.ty(&entry.key),
                    entry.instance.as_ref().map(|tag| {
                        (
                            &tag.callable,
                            tag.args.iter().map(|ty| canon.ty(ty)).collect::<Vec<_>>(),
                            &tag.numeric_layout,
                        )
                    }),
                )
            })),
        );
        snapshot.put("typeof poison", unordered(&checker.typeof_poisoned));
        snapshot.put("type test poison", unordered(&checker.type_test_poisoned));
        snapshot.put("sum view poison", unordered(&checker.sum_view_poisoned));
        snapshot.put("lift poison", unordered(&checker.lift_poisoned));
        snapshot.put(
            "propagation kinds",
            unordered(checker.prop_kinds.iter().map(|(span, kind)| {
                (
                    span,
                    kind.map(|kind| match kind {
                        super::super::PropKind::Null => "null",
                        super::super::PropKind::Err => "error",
                    }),
                )
            })),
        );
        snapshot.put("lift kinds", unordered(&checker.lift_kinds));
        snapshot.put(
            "closure bindings",
            unordered(
                checker
                    .closure_bindings
                    .iter()
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .map(|(id, ty)| {
                        (
                            canon.ty(&Type::Unknown(*id)),
                            ty.as_ref().map(|ty| canon.ty(ty)),
                        )
                    }),
            ),
        );
        snapshot.put(
            "function returns",
            unordered(
                checker
                    .function_returns
                    .iter()
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .map(|(key, ty)| (key, canon.ty(ty))),
            ),
        );
        snapshot.put(
            "method returns",
            unordered(
                checker
                    .method_returns
                    .iter()
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .map(|(key, ty)| (key, canon.ty(ty))),
            ),
        );
        snapshot.put(
            "global definitions",
            unordered(
                checker
                    .global_defs
                    .iter()
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .map(|(module, globals)| {
                        (
                            module,
                            unordered(
                                globals
                                    .iter()
                                    .collect::<BTreeMap<_, _>>()
                                    .into_iter()
                                    .map(|(name, ty)| (name, canon.ty(ty))),
                            ),
                        )
                    }),
            ),
        );
        for (index, delta) in history.deltas.iter().enumerate() {
            snapshot.channels(
                &format!("stream boundary {index}"),
                delta.clone(),
                &mut canon,
            );
        }
        let mut final_checker = Self::fork(checker);
        final_checker.finalize_typed();
        let final_delta = delta::flush_delta(&final_checker, &mut FlushState::default(), true);
        snapshot.channels("final channels", final_delta, &mut canon);
        // Follow bindings to a fixpoint so fresh aliases reachable through a
        // retained effect keep their kinds even when absent from the result.
        let mut bindings = BTreeMap::new();
        loop {
            let pending: Vec<_> = canon
                .vars
                .keys()
                .copied()
                .filter(|id| !bindings.contains_key(id))
                .collect();
            if pending.is_empty() {
                break;
            }
            for id in pending {
                bindings.insert(
                    id,
                    (
                        canon.ty(&Type::Unknown(id)),
                        checker.solver.kind_of(id),
                        canon.ty(&checker.solver.resolve_reference(&Type::Unknown(id))),
                    ),
                );
            }
        }
        let solver = (
            "solver bindings, kinds and aliases".into(),
            format!("{:?}", unordered(bindings.into_values())),
        );
        snapshot.0.insert(4, solver);
        snapshot
    }

    /// Return the first semantic difference, including both values for diagnosis.
    pub(in crate::infer) fn compare(&self, other: &Self) -> Result<(), String> {
        for (left, right) in self.0.iter().zip(&other.0) {
            if left != right {
                return Err(format!("{}: walk={:?}, replay={:?}", left.0, left.1, right));
            }
        }
        if self.0.len() != other.0.len() {
            return Err(format!(
                "effect inventory length: {} != {}",
                self.0.len(),
                other.0.len()
            ));
        }
        Ok(())
    }

    /// Retain ordered diagnostic text; unordered callers normalize before entry.
    fn put(&mut self, name: impl Into<String>, value: impl Debug) {
        self.0.push((name.into(), format!("{value:?}")));
    }

    /// Capture every delta field, retaining map replacement and removal meaning.
    /// Exhaustive destructuring makes a new channel require an explicit choice.
    fn channels(&mut self, label: &str, delta: ChannelDelta, canon: &mut Canonical) {
        let ChannelDelta {
            settles_batch,
            expr_types,
            expr_types_removed,
            instance_seeds,
            numeric_calls,
            numeric_calls_removed,
            receiver_types,
            receiver_types_removed,
            receiver_owners,
            view_args,
            field_calls,
            lift_errs,
            null_props,
            fields_loops,
            instance_fields,
            sum_views,
            type_names,
            typeof_types,
            typeof_types_removed,
            type_tests,
            type_tests_removed,
            errors,
            warnings,
            instance_returns,
            keyed_calls,
            instance_dispatch,
        } = delta;
        self.put(format!("{label}/seal"), settles_batch);
        for (name, entries) in [
            ("expr types", expr_types),
            ("receiver types", receiver_types),
            ("sum views", sum_views),
            ("typeof types", typeof_types),
            ("type tests", type_tests),
        ] {
            self.put(
                format!("{label}/{name}"),
                unordered(entries.into_iter().map(|(span, ty)| (span, canon.ty(&ty)))),
            );
        }
        for (name, entries) in [
            ("expr removals", expr_types_removed),
            ("receiver removals", receiver_types_removed),
            ("view args", view_args),
            ("lift errors", lift_errs),
            ("null props", null_props),
            ("typeof removals", typeof_types_removed),
            ("type test removals", type_tests_removed),
        ] {
            self.put(format!("{label}/{name}"), unordered(entries));
        }
        self.put(
            format!("{label}/instance seeds"),
            unordered(instance_seeds.into_iter().map(|(span, entries)| {
                (
                    span,
                    unordered(entries.into_iter().map(|(mut key, ty)| {
                        canon.instance(&mut key);
                        (key, canon.ty(&ty))
                    })),
                )
            })),
        );
        self.put(
            format!("{label}/instance dispatch"),
            unordered(instance_dispatch.into_iter().map(|(span, entries)| {
                (
                    span,
                    unordered(entries.into_iter().map(|(mut key, target)| {
                        canon.instance(&mut key);
                        (key, target)
                    })),
                )
            })),
        );
        self.put(
            format!("{label}/numeric calls"),
            unordered(numeric_calls.into_iter().map(|((span, mut key), value)| {
                if let Some(key) = &mut key {
                    canon.instance(key);
                }
                ((span, key), value)
            })),
        );
        self.put(
            format!("{label}/numeric removals"),
            unordered(numeric_calls_removed.into_iter().map(|(span, mut key)| {
                if let Some(key) = &mut key {
                    canon.instance(key);
                }
                (span, key)
            })),
        );
        self.put(
            format!("{label}/receiver owners"),
            unordered(receiver_owners.into_iter().map(|(span, owners)| {
                (
                    span,
                    owners.iter().map(|ty| canon.ty(ty)).collect::<Vec<_>>(),
                )
            })),
        );
        self.put(
            format!("{label}/field calls"),
            unordered(field_calls.into_iter().map(|(span, types)| {
                (
                    span,
                    types.map(|types| types.iter().map(|ty| canon.ty(ty)).collect::<Vec<_>>()),
                )
            })),
        );
        self.put(format!("{label}/fields loops"), unordered(fields_loops));
        self.put(
            format!("{label}/instance fields"),
            unordered(instance_fields.into_iter().map(|(span, entries)| {
                (
                    span,
                    unordered(entries.into_iter().map(|(mut key, fields)| {
                        canon.instance(&mut key);
                        (key, fields)
                    })),
                )
            })),
        );
        self.put(format!("{label}/type names"), unordered(type_names));
        self.put(format!("{label}/errors"), errors);
        self.put(format!("{label}/warnings"), warnings);
        self.put(
            format!("{label}/instance returns"),
            unordered(instance_returns.into_iter().map(|(symbol, args, ret)| {
                (
                    symbol,
                    args.iter().map(|ty| canon.ty(ty)).collect::<Vec<_>>(),
                    canon.ty(&ret),
                )
            })),
        );
        self.put(
            format!("{label}/keyed calls"),
            unordered(
                keyed_calls
                    .into_iter()
                    .map(|(span, owner, method, key)| (span, owner, method, canon.ty(&key))),
            ),
        );
    }
}
