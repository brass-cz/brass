//! Read-only dependency inventory for method co-check body walks.
//!
//! Enable `brass::method_inventory=trace` to observe candidates. The inventory
//! never admits or stores a method memo entry. Nested memo replays contribute
//! their qualified read provenance. Untracked shared dependencies prevent a
//! certificate even when the unqualified reporting read set is empty.

use super::GlobalReadProvenance;
use crate::constraint::ShapeConstraint;
use crate::infer::journal::{
    ElaborationJournalEntry, ElaborationJournalFrame, ElaborationMemoContext,
};
use crate::infer::{Checker, MethodCall};
use brass_hir::{Type, TypeInfo};

/// A global's defining identity, independent of import aliases and short names.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::infer) struct QualifiedGlobal {
    /// Module that owns the global definition.
    pub module: Vec<String>,
    /// Name in that module, before any import rename.
    pub name: String,
}

/// Shared state a method replay would have to validate in its owning checker.
/// Types are resolved at the read, not after the body can bind their variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::infer) struct MethodMemoDependencies {
    /// Monotonic version of installed scheme tables within this checker.
    pub scheme_revision: u64,
    /// Qualified reads in encounter order, including conflicting repeated reads.
    pub globals: Vec<(QualifiedGlobal, Type)>,
    /// The shared fallback consulted by an unannotated return walk.
    pub return_dependency: Option<Type>,
    /// Nested replays or unresolved identities prevent a complete certificate.
    pub untracked: bool,
}

/// An observation window mirrors ordinary storage guards without storing an entry.
#[derive(Clone)]
struct MethodWindow {
    /// Identity and canonical inputs used by the ordinary memo key builder.
    context: Option<ElaborationMemoContext>,
    /// Separate journal: observation never changes the production journal stack.
    frame: ElaborationJournalFrame,
    /// Trace identity, including the variant or receiver function symbol.
    callable: String,
    /// Shared dependencies as seen at this walk's reads.
    dependencies: MethodMemoDependencies,
    /// Whether receiver, arguments and effective scheme inputs were all closed.
    closed: bool,
    /// Independent reasons that prevent reuse; none changes the current walk.
    reasons: Vec<&'static str>,
    /// Diagnostic and transitive cap boundaries for the whole nested walk.
    before: (usize, usize, u64),
    /// Nested hits require exact provenance even if their read set is empty.
    nested_replay: bool,
}

/// Optional checker-local observation state; absent in ordinary execution.
#[derive(Clone, Default)]
pub(in crate::infer) struct MethodInventory {
    /// Nested body windows receive the dependencies of their children.
    windows: Vec<MethodWindow>,
    /// Test evidence is not retained in production runs.
    #[cfg(test)]
    pub completed: Vec<(String, MethodMemoDependencies, Vec<&'static str>)>,
}

impl Checker<'_> {
    /// Copy committed journal writes into each active method observation window.
    /// Nested walks are already included; production frame merging is not observed.
    #[cold]
    #[inline(never)]
    pub(in crate::infer) fn observe_method_entry(&mut self, entry: &ElaborationJournalEntry) {
        if let Some(inventory) = &mut self.method_inventory {
            for window in &mut inventory.windows {
                window.frame.observe_entry(entry.clone());
            }
        }
    }

    /// Observe shape dependencies using the same skeleton eligibility rules.
    #[cold]
    #[inline(never)]
    pub(in crate::infer) fn observe_method_shape(&mut self, ty: &Type, shape: &ShapeConstraint) {
        if let Some(inventory) = &mut self.method_inventory {
            for window in &mut inventory.windows {
                window.frame.observe_shape(ty.clone(), shape.clone());
            }
        }
    }

    /// A closure body needs lexical state that a method memo cannot replay.
    pub(in crate::infer) fn observe_method_closure(&mut self) {
        if let Some(inventory) = &mut self.method_inventory {
            for window in &mut inventory.windows {
                window.frame.has_closure_bodies = true;
            }
        }
    }

    /// Mark replacement of the scheme table without touching analysis state.
    pub(in crate::infer) fn observe_scheme_install(&mut self) {
        self.method_scheme_revision += 1;
    }

    /// Observe receiver declarations routed through function elaboration.
    pub(in crate::infer) fn begin_receiver_inventory(
        &mut self,
        symbol: &str,
        args: &[Type],
        declared: Option<&Type>,
        fallback: &Type,
    ) -> bool {
        if self.method_inventory.is_none() || !self.co_checking || self.co_free_function(symbol) {
            return false;
        }
        let context = self.elaboration_memo_key("fn", symbol, None, args, &[]);
        self.open_method_inventory(format!("fn:{symbol}"), context, declared, fallback);
        true
    }

    /// Observe actual method walks with the same receiver and variant identity as
    /// ordinary memoization. Static methods use their declaring nominal as receiver.
    pub(in crate::infer) fn begin_method_inventory(&mut self, call: &MethodCall<'_>) -> bool {
        if self.method_inventory.is_none() || !self.co_checking {
            return false;
        }
        let receiver = call.receiver_ty.clone().or_else(|| {
            self.program
                .types
                .get(call.self_type)
                .map(TypeInfo::type_ref)
        });
        let variant = call
            .owner
            .split_once('.')
            .map_or("", |(_, variant)| variant);
        let callable = format!("{}:{variant}:{}", call.self_type, call.name);
        let context = receiver.as_ref().and_then(|receiver| {
            self.elaboration_memo_key(
                "m",
                &callable,
                Some(receiver),
                call.arg_types,
                call.scheme_params,
            )
        });
        self.open_method_inventory(
            format!("m:{callable}"),
            context,
            call.declared_ret.as_ref(),
            &call.fallback_ret,
        );
        true
    }

    /// Open a separate observation journal to test existing outer-variable and
    /// closure exclusions without changing the production journal stack.
    fn open_method_inventory(
        &mut self,
        callable: String,
        context: Option<ElaborationMemoContext>,
        declared: Option<&Type>,
        fallback: &Type,
    ) {
        let closed = context
            .as_ref()
            .is_some_and(|context| context.inputs.is_empty());
        let mut reasons = Vec::new();
        if !closed {
            reasons.push("open_frame");
        }
        if self.numeric.probing || self.co_memo_suspended {
            reasons.push("numeric_probe");
        }
        if !self.type_test_holes.is_empty() {
            reasons.push("type_test_probe");
        }
        if self.speculation_depth != 0 {
            reasons.push("speculative");
        }
        let return_dependency = declared.is_none().then(|| self.resolve(fallback));
        let inventory = self
            .method_inventory
            .as_mut()
            .expect("enabled method inventory");
        inventory.windows.push(MethodWindow {
            callable,
            context,
            frame: ElaborationJournalFrame::observation(self.next_unknown),
            closed,
            reasons,
            before: (self.errors.len(), self.warnings.len(), self.depth_capped),
            nested_replay: false,
            dependencies: MethodMemoDependencies {
                scheme_revision: self.method_scheme_revision,
                globals: Vec::new(),
                return_dependency,
                untracked: false,
            },
        });
    }

    /// Complete the observation at the body boundary. No candidate is installed;
    /// closed/admissible counts describe only the observed walk and its guards.
    pub(in crate::infer) fn finish_method_inventory(&mut self, active: bool, ret: &Type) {
        if !active {
            return;
        }
        let mut window = self
            .method_inventory
            .as_mut()
            .unwrap()
            .windows
            .pop()
            .expect("balanced method inventory");
        let frame = window.frame;
        let reasons = &mut window.reasons;
        if self.errors.len() != window.before.0 {
            reasons.push("error_walk");
        }
        if self.warnings.len() != window.before.1 {
            reasons.push("warning_walk");
        }
        if self.depth_capped != window.before.2 {
            reasons.push("depth_cap");
        }
        if frame.has_closure_bodies {
            reasons.push("closure_body");
        }
        if window.dependencies.untracked {
            reasons.push("untracked_dependency");
        }
        if window
            .dependencies
            .globals
            .iter()
            .any(|(_, ty)| !brass_hir::is_fully_known(ty))
        {
            reasons.push("open_global");
        }
        if window
            .dependencies
            .return_dependency
            .as_ref()
            .is_some_and(|ty| !brass_hir::is_fully_known(ty))
        {
            reasons.push("open_return");
        }
        if self.method_scheme_revision != window.dependencies.scheme_revision {
            reasons.push("changed_scheme");
        }
        if let Some(context) = &window.context
            && self
                .build_elaboration_memo_entry(&self.resolve(ret), frame, context)
                .is_none()
        {
            reasons.push("outer_variable");
        }
        tracing::trace!(target: "brass::method_inventory",
            callable = window.callable, closed = window.closed, admissible = reasons.is_empty(),
            without_provenance = reasons.is_empty() && !window.nested_replay,
            nested_replay = window.nested_replay, reasons = ?reasons, scheme_revision = window.dependencies.scheme_revision,
            globals = ?window.dependencies.globals, return_dependency = ?window.dependencies.return_dependency,
            has_root = self.current_co_method.is_some(), "check: method dependencies");
        #[cfg(test)]
        self.method_inventory.as_mut().unwrap().completed.push((
            window.callable,
            window.dependencies,
            window.reasons,
        ));
    }

    /// A child hit supplies its exact qualified reads to every active method.
    /// Empty provenance certifies no reads; unavailable identities still reject.
    pub(in crate::infer) fn observe_method_replay(&mut self, reads: Option<&GlobalReadProvenance>) {
        if let Some(inventory) = &mut self.method_inventory {
            for window in &mut inventory.windows {
                window.nested_replay = true;
                if let Some(reads) = reads {
                    window.dependencies.untracked |= reads.untracked;
                    for read in &reads.reads {
                        if !window.dependencies.globals.contains(read) {
                            window.dependencies.globals.push(read.clone());
                        }
                    }
                }
            }
        }
    }

    /// Observe an actual global value read separately from the reporting set.
    /// A nested call's read belongs to every active method dependency window.
    pub(in crate::infer) fn observe_method_global(
        &mut self,
        name: &str,
        ty: &Type,
        qualified: bool,
    ) {
        if !self
            .method_inventory
            .as_ref()
            .is_some_and(|i| !i.windows.is_empty())
        {
            return;
        }
        let identity = self.method_global_identity(name, qualified);
        let resolved = self.resolve(ty);
        for window in &mut self.method_inventory.as_mut().unwrap().windows {
            if let Some(identity) = &identity {
                let read = (identity.clone(), resolved.clone());
                if !window.dependencies.globals.contains(&read) {
                    window.dependencies.globals.push(read);
                }
            } else {
                window.dependencies.untracked = true;
            }
        }
    }

    /// Resolve the same precedence as globals_visible_from: own definitions,
    /// renamed imports, then the first sorted core module. Module qualifiers
    /// instead select their defining module directly, as lookup_aliased_global does.
    pub(super) fn method_global_identity(
        &self,
        name: &str,
        qualified: bool,
    ) -> Option<QualifiedGlobal> {
        if qualified {
            let (alias, name) = name.split_once('.')?;
            let module = self
                .program
                .module_aliases
                .get(&self.current_module)?
                .get(alias)?;
            return Some(QualifiedGlobal {
                module: module.clone(),
                name: name.into(),
            });
        }
        if self
            .global_defs
            .get(&self.current_module)
            .is_some_and(|defs| defs.contains_key(name))
        {
            return Some(QualifiedGlobal {
                module: self.current_module.clone(),
                name: name.into(),
            });
        }
        if let Some(origin) = self
            .program
            .import_origins
            .get(&self.current_module)
            .and_then(|origins| origins.get(name))
        {
            let remote = self
                .program
                .import_renames
                .get(&self.current_module)
                .and_then(|renames| renames.get(name))
                .map_or(name, String::as_str);
            if self
                .global_defs
                .get(origin)
                .is_some_and(|defs| defs.contains_key(remote))
            {
                return Some(QualifiedGlobal {
                    module: origin.clone(),
                    name: remote.into(),
                });
            }
        }
        let module = self
            .global_defs
            .iter()
            .filter(|(path, defs)| {
                path.first().is_some_and(|s| s == "core") && defs.contains_key(name)
            })
            .map(|(path, _)| path)
            .min()?;
        Some(QualifiedGlobal {
            module: module.clone(),
            name: name.into(),
        })
    }
}
