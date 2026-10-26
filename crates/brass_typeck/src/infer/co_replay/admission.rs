//! Closed method admission and validation of checker-local shared dependencies.

use super::methods::MethodMemoDependencies;
use crate::infer::Checker;
use crate::infer::journal::{
    ElaborationJournalFrame, ElaborationMemoContext, ElaborationMemoEntry, ElaborationMemoKey,
};
use brass_hir::Type;
use std::rc::Rc;

impl Checker<'_> {
    /// Require a second miss before paying for a method co journal and entry.
    /// Single-use keys otherwise retain effects that no later call repays. The
    /// first miss retains only its canonical key and walks normally, feeding any
    /// enclosing journal. This checker-local storage policy has no timing input;
    /// it neither changes hit validation nor admits an otherwise ineligible walk.
    pub(in crate::infer) fn method_co_storage_ready(&mut self, key: &ElaborationMemoKey) -> bool {
        if self.method_co_seen.contains(key) {
            return true;
        }
        self.method_co_seen.insert(key.clone());
        false
    }

    /// Reject probes and open inputs before allocating or canonicalizing a key.
    /// The fallback is shared state even when a full body later supersedes it.
    pub(in crate::infer) fn method_co_precheck(
        &self,
        receiver: Option<&Type>,
        args: &[Type],
        schemes: &[Option<Type>],
        declared: Option<&Type>,
        fallback: &Type,
    ) -> Option<&'static str> {
        if self.numeric.probing || self.co_memo_suspended {
            return Some("numeric_probe");
        }
        if !self.type_test_holes.is_empty() {
            return Some("type_test_probe");
        }
        if self.speculation_depth != 0 {
            return Some("speculative");
        }
        let closed = |ty: &Type| {
            brass_hir::is_fully_known(ty) || brass_hir::is_fully_known(&self.resolve(ty))
        };
        if !receiver
            .into_iter()
            .chain(args)
            .chain(schemes.iter().flatten())
            .all(closed)
        {
            return Some("open_frame");
        }
        if declared.is_none() && !closed(fallback) {
            return Some("open_return");
        }
        None
    }

    /// Capture the environment consulted before a closed method body starts.
    pub(in crate::infer) fn method_memo_dependencies(
        &self,
        declared: Option<&Type>,
        fallback: &Type,
    ) -> MethodMemoDependencies {
        MethodMemoDependencies {
            scheme_revision: self.method_scheme_revision,
            globals: Vec::new(),
            return_dependency: declared.is_none().then(|| self.resolve(fallback)),
            untracked: false,
        }
    }

    /// A method hit is valid only while its scheme, fallback and all qualified
    /// global reads are closed and unchanged. Ordinary lookup semantics stay local.
    pub(in crate::infer) fn lookup_elaboration_entry(
        &self,
        context: &ElaborationMemoContext,
        dependencies: Option<&MethodMemoDependencies>,
    ) -> Option<Rc<ElaborationMemoEntry>> {
        let entry = self.elaboration_memo.get(&context.key)?;
        if let Some(expected) = dependencies {
            let stored = entry.method_dependencies.as_deref()?;
            if stored.scheme_revision != expected.scheme_revision
                || stored.return_dependency != expected.return_dependency
                || !self.method_dependencies_valid(stored)
            {
                tracing::trace!(target: "brass::perf", callable = context.key.callable,
                    reason = "changed_dependency", "check: method memo bypass");
                return None;
            }
        }
        Some(Rc::clone(entry))
    }

    /// Validate retained read types without resolving the stored evidence again.
    fn method_dependencies_valid(&self, dependencies: &MethodMemoDependencies) -> bool {
        !dependencies.untracked
            && dependencies.scheme_revision == self.method_scheme_revision
            && dependencies
                .return_dependency
                .as_ref()
                .is_none_or(brass_hir::is_fully_known)
            && dependencies.globals.iter().all(|(identity, read)| {
                brass_hir::is_fully_known(read)
                    && self
                        .global_defs
                        .get(&identity.module)
                        .and_then(|globals| globals.get(&identity.name))
                        .is_some_and(|current| self.resolve(current) == *read)
            })
    }

    /// Reject an already-untracked method window before canonicalizing its
    /// observations. The complete certificate remains the storage authority;
    /// ordinary entries do not depend on this method-only certificate.
    pub(in crate::infer) fn method_storage_precheck(
        &self,
        callable: &str,
        method: bool,
        frame: &ElaborationJournalFrame,
    ) -> bool {
        if method && frame.global_reads.untracked {
            tracing::trace!(target: "brass::perf", callable,
                reason = "untracked_dependency", nested_replay = frame.memo_replayed,
                without_provenance = false, globals = frame.global_reads.reads.len(),
                "check: method memo storage");
            return false;
        }
        true
    }

    /// Attach a method certificate only when every recorded dependency remains
    /// valid at the end of the walk. Other entry guards are checked by the caller.
    pub(in crate::infer) fn certify_method_entry(
        &self,
        callable: &str,
        nested_replay: bool,
        entry: &mut ElaborationMemoEntry,
        dependencies: Option<MethodMemoDependencies>,
    ) -> bool {
        let Some(mut dependencies) = dependencies else {
            return true;
        };
        if let Some(reads) = &entry.global_reads {
            dependencies.globals.clone_from(&reads.reads);
            dependencies.untracked = reads.untracked;
        }
        let reason = if dependencies.untracked {
            "untracked_dependency"
        } else if dependencies
            .globals
            .iter()
            .any(|(_, ty)| !brass_hir::is_fully_known(ty))
        {
            "open_global"
        } else if !self.method_dependencies_valid(&dependencies) {
            "changed_dependency"
        } else {
            "stored"
        };
        tracing::trace!(target: "brass::perf", callable, reason, nested_replay,
            without_provenance = !nested_replay && reason == "stored",
            globals = dependencies.globals.len(), "check: method memo storage");
        if reason != "stored" {
            return false;
        }
        entry.method_dependencies = Some(Box::new(dependencies));
        true
    }
    /// Compare the certificate of a dry method hit with its actual body walk.
    /// Stored evidence is never late-resolved, including provisional global reads.
    pub(in crate::infer) fn assert_method_dependencies(
        &self,
        callable: &str,
        stored: &MethodMemoDependencies,
        initial: &MethodMemoDependencies,
    ) {
        let mut walked = initial.clone();
        walked.scheme_revision = self.method_scheme_revision;
        let reads = &self
            .elaboration_journals
            .last()
            .expect("method validation journal")
            .global_reads;
        walked.globals.clone_from(&reads.reads);
        walked.untracked = reads.untracked;
        debug_assert_eq!(*stored, walked, "method dependencies differ for {callable}");
    }
}
