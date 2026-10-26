//! Typing a deep chain of calls without one nested frame per call.
//!
//! Monomorphization types an instance when its first caller needs the
//! instance's return type, nested inside the caller's frame, so a chain of
//! distinct callables nests as deep as the program's static call chain. Past
//! [`POSTPONE_DEPTH`] nested instances, a call whose callee's return is
//! already settled -- by a fully known declared return, or by the checker's
//! return for that very instance (see [`Monomorphizer::call_contract`]) --
//! types against that return and queues the callee instead. The queue is
//! drained after the root that filled it, each queued instance starting a
//! fresh nesting of its own, so the traversal is iterative in the call
//! depth. It keeps counting the instances of each callable its callers were
//! nested in, so a callable reaching itself at ever-larger types still meets
//! the bound on its own nesting. A drained instance must return exactly what
//! its callers were typed against.

use super::*;

/// How many instance bodies are typed nested inside one another before a
/// call with a settled return is postponed (see the module documentation).
/// Shallow programs never reach it, so their typing order is unchanged.
pub(super) const POSTPONE_DEPTH: usize = 128;

/// A callee instance whose typing was postponed.
struct PostponedCall {
    base: String,
    arg_types: Vec<Type>,
    /// The return its callers were typed against.
    assumed: Type,
    /// The per-callable nesting of the frames that postponed it.
    nesting: HashMap<String, usize>,
}

/// The postponed calls of the root being typed.
#[derive(Default)]
pub(super) struct Postponed {
    /// Callee instances still to type.
    queue: Vec<PostponedCall>,
    /// The instance symbols ever queued for the current root.
    queued: HashSet<String>,
    /// Off while a root is typed again fully nested (see
    /// [`Monomorphizer::type_root`]).
    disabled: bool,
}

impl Monomorphizer<'_, '_> {
    /// The return type a call of free function `base` at `arg_types` is
    /// typed against without typing the callee's body, when it is settled:
    /// a fully known declared return of a body that raises no error, or the
    /// checker's return for this instance of an unannotated body that
    /// cannot fail (`!` and `error(..)` reshape the return into a `Result`
    /// or a nullable). `None` when only typing the body can tell.
    pub(super) fn call_contract(&self, base: &str, arg_types: &[Type]) -> Option<Type> {
        let info = self.program.functions.get(base)?;
        let ret = match info.signature.ret_ty.clone() {
            Some(ret) => {
                if brass_mir::constructs_error_block(&info.decl.body) {
                    return None;
                }
                ret
            }
            None => {
                if brass_mir::fallible_block(&info.decl.body) {
                    return None;
                }
                self.instance_return(base, arg_types)?.clone()
            }
        };
        // Checker contracts and MIR inference may spell the same concrete
        // declared record differently: the former can be a bare nominal while
        // the latter carries every declared field in its substitution. The
        // contract is resolved so both sides of a comparison spell it alike.
        let ret = resolve_nominal(self.program, &ret);
        let settled = brass_hir::is_fully_known(&ret)
            && is_supported(&ret)
            && self.self_describing(&ret)
            && arg_types.iter().all(brass_hir::is_fully_known)
            && info.decl.params.len() == arg_types.len();
        settled.then_some(ret)
    }

    /// Postpone the call of `base` at `arg_types` when the nesting is deep
    /// and its return is settled: queue the callee and return the type the
    /// call is typed against. `None` types the callee now, nested.
    pub(super) fn postpone_call(&mut self, base: &str, arg_types: &[Type]) -> Option<Type> {
        if self.postponed.disabled
            || self.defer.is_some()
            || self.instance_stack.len() < POSTPONE_DEPTH
        {
            return None;
        }
        let symbol = instance_symbol(base, arg_types);
        if self.instances.contains_key(&symbol) {
            return None;
        }
        let ret = self.call_contract(base, arg_types)?;
        if self.postponed.queued.insert(symbol) {
            self.postponed.queue.push(PostponedCall {
                base: base.to_string(),
                arg_types: arg_types.to_vec(),
                assumed: ret.clone(),
                nesting: self.callable_nesting.clone(),
            });
        }
        Some(ret)
    }

    /// Type one root (`root` types it) and then every callee its typing
    /// postponed. Should the root or a postponed callee fail after a call
    /// was postponed, everything stored for the root is discarded and the
    /// root is typed again with every callee nested in its caller's frame,
    /// which decides exactly as typing without postponement does (a callee
    /// that fails only in code its caller never runs does not fail the
    /// caller there).
    pub(super) fn type_root<T>(
        &mut self,
        mut root: impl FnMut(&mut Self) -> Result<T, String>,
    ) -> Result<T, String> {
        let watermark = self.instance_log.len();
        let result = root(self).and_then(|out| self.drain_postponed().map(|()| out));
        let postponed_any = !self.postponed.queued.is_empty();
        self.postponed.queue.clear();
        self.postponed.queued.clear();
        if result.is_ok() || !postponed_any {
            return result;
        }
        for stored in self.instance_log.drain(watermark..) {
            self.instances.remove(&stored);
        }
        self.clear_frame_state();
        self.postponed.disabled = true;
        let retried = root(self);
        self.postponed.disabled = false;
        retried
    }

    /// Type the postponed callees until none is left (typing one may
    /// postpone more), checking each returns what its callers assumed.
    fn drain_postponed(&mut self) -> Result<(), String> {
        while let Some(call) = self.postponed.queue.pop() {
            let PostponedCall {
                base,
                arg_types,
                assumed,
                nesting,
            } = call;
            let outer = std::mem::replace(&mut self.callable_nesting, nesting);
            let typed = self.instantiate_fn(&base, arg_types);
            self.callable_nesting = outer;
            let symbol = typed?;
            self.clear_frame_state();
            let ret = self
                .instances
                .get(&symbol)
                .map(|instance| resolve_nominal(self.program, &instance.ret));
            if ret.as_ref() != Some(&assumed) {
                return Err(format!(
                    "internal error: `{base}` returns `{}` but its callers were typed against \
                     `{}`",
                    ret.map_or_else(|| "nothing".to_string(), |ret| ret.display()),
                    assumed.display()
                ));
            }
        }
        Ok(())
    }

    /// Forget the per-frame recursion state a finished root leaves behind.
    pub(super) fn clear_frame_state(&mut self) {
        self.in_progress.clear();
        self.assumed_rets.clear();
        self.self_call_rets.clear();
    }
}
