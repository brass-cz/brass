//! The lazy pipeline's answers to a call whose MIR body is absent: compile
//! it as a runtime-resolved site when its whole ABI is known without the
//! body (a [`DeferredSig`] contract), or record the body as a demand the
//! caller lowers before it retries the pass (see
//! [`MonoStop::MissingBodies`]).

use super::*;

impl Monomorphizer<'_, '_> {
    /// Whether `ty` fully describes a value's layout on its own: no type
    /// slots, every declared member resolved and fully known. A bare
    /// `-> Box` annotation on a type with an open member (an unannotated
    /// field, a slot) is REFINED by each body's instance -- the annotation
    /// under-describes the return, so a call on it cannot defer; the body
    /// must be instantiated for its precise result.
    pub(super) fn self_describing(&self, ty: &Type) -> bool {
        match ty {
            Type::Record(n) | Type::Sum(n) => {
                let Some(info) = self.program.type_by_id(n.id) else {
                    return false;
                };
                if !info.slots.is_empty() {
                    return false;
                }
                let fields_ok = |fields: &[brass_hir::FieldInfo]| {
                    fields.iter().all(|f| {
                        f.resolved_ty
                            .as_ref()
                            .is_some_and(brass_hir::is_fully_known)
                    })
                };
                match &info.kind {
                    TypeKind::Record { fields, .. } => fields_ok(fields),
                    TypeKind::Sum { variants } => variants.iter().all(|v| fields_ok(&v.fields)),
                }
            }
            Type::Slice(e) | Type::Array(e, _) | Type::Nullable(e) => self.self_describing(e),
            Type::Tuple(ts) => ts.iter().all(|t| self.self_describing(t)),
            // A function-typed return carries a call contract the annotation
            // syntax cannot fully pin; stay on the instantiating path.
            Type::Fun(..) => false,
            _ => true,
        }
    }

    /// Record a demand for `base` at `arg_types` (deduplicated): one of the
    /// missing bodies this pass collects (see `missing_demands`).
    /// `needs_body` demands merge with OR: one site that must have the
    /// lowered body (a closure site, a non-deferrable shape) outweighs any
    /// number of deferral-candidate sites for the same instance.
    pub(super) fn note_missing(&self, base: &str, arg_types: &[Type], needs_body: bool) {
        self.missing_observations
            .set(self.missing_observations.get() + 1);
        let mut demands = self.missing_demands.borrow_mut();
        if let Some(d) = demands
            .iter_mut()
            .find(|(b, a, _)| b == base && a == arg_types)
        {
            d.2 |= needs_body;
            return;
        }
        demands.push((base.to_string(), arg_types.to_vec(), needs_body));
    }

    /// The deferral contract (the lazy JIT): a call to `base`, whose MIR body
    /// is not in the program, compiles to a runtime-resolved call when its
    /// whole ABI is annotation-determined -- a fully concrete DECLARED return
    /// (an inferred or fallible return needs the body; a body that raises
    /// errors changes the ABI to a `Result`), and fully known argument types
    /// (instances are keyed by them). Never inside a closure body: closure
    /// code can cross to worker threads, which cannot compile.
    pub(super) fn deferrable(&self, base: &str, arg_types: &[Type]) -> Option<DeferredSig> {
        self.defer.as_ref()?;
        if self.closure_depth > 0 || self.by_fn.contains_key(base) {
            return None;
        }
        let info = self.program.functions.get(base)?;
        let ret = self.call_contract(base, arg_types)?;
        // The site's ABI mirrors the instance's parameter typing exactly:
        // lowering seeds a parameter local's type only from a SIMPLE
        // annotation (`resolve_simple_type` -- scalars, strings, arrays and
        // nullables of them), and monomorphization's declared-type override
        // reads that local. So a simple annotation wins here (an `int64`
        // parameter widens an `int32` argument at the site), while a nominal
        // annotation leaves the CALLER's argument type in charge -- the
        // instance is specialized per caller type -- under the
        // declared-nullable rule (`Node?` takes a non-null `Node` argument as
        // `Node?`; see `instance_param_types`).
        let promoted = self.instance_param_types(&info.signature.params, arg_types);
        let mut params = Vec::with_capacity(arg_types.len());
        for (promoted, p) in promoted.into_iter().zip(&info.decl.params) {
            match p.ty.as_ref().and_then(brass_mir::resolve_simple_type) {
                Some(decl) => params.push(decl),
                None => params.push(promoted),
            }
        }
        Some(DeferredSig {
            base: base.to_string(),
            type_args: arg_types.to_vec(),
            params,
            ret,
        })
    }

    /// Whether a missing `base` at `arg_types` could compile as a
    /// runtime-deferred call once the checker reports the instance's return
    /// type: the shape half of the unannotated arm of `deferrable`, checked
    /// before any contract exists so the demand can be flagged as
    /// not-needing-the-body. Mirrors `deferrable`'s guards minus the return
    /// checks (those run when the contract arrives).
    pub(super) fn unannotated_deferral_candidate(&self, base: &str, arg_types: &[Type]) -> bool {
        if self.defer.is_none() || self.closure_depth > 0 || self.by_fn.contains_key(base) {
            return false;
        }
        let Some(info) = self.program.functions.get(base) else {
            return false;
        };
        info.signature.ret_ty.is_none()
            && !brass_mir::fallible_block(&info.decl.body)
            && arg_types.iter().all(brass_hir::is_fully_known)
            && info.decl.params.len() == arg_types.len()
    }
}
