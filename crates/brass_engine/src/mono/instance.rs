//! The checker instance a body is typed for, and the per-instance checker
//! channels read under it.
//!
//! The checker elaborates a generic body once per call-site instantiation and
//! records the facts that differ between instantiations under the instance
//! they belong to ([`brass_hir::InstanceKey`]). Monomorphization types the
//! same body once per instance, so it reads those facts back for the instance
//! it is typing instead of re-deriving them: the key is computed from the
//! callable and its argument types exactly as the checker computed it, and a
//! closure body belongs to the instance whose body creates it (the checker
//! checks a closure body as part of the enclosing elaboration).

use super::*;
use brass_hir::InstanceKey;
use brass_mir::LocalDecl;
use brass_parser::Span;

/// How many instances of one callable may be typed nested inside one
/// another (see `Monomorphizer::type_and_store`). Only a callable reaching
/// itself at new types piles its instances up; ordinary recursion reuses the
/// instance being typed, and a chain of distinct callables counts one each.
pub(super) const MAX_INSTANCE_NESTING: usize = 512;

/// A numeric storage discriminator is concrete and independent of literal spelling.
pub(super) fn numeric_base<'a>(
    base: &'a str,
    flavor: Option<&brass_hir::NumericLayout>,
) -> std::borrow::Cow<'a, str> {
    match flavor {
        Some(_) => std::borrow::Cow::Owned(brass_hir::numeric_instance_base(base, flavor)),
        None => std::borrow::Cow::Borrowed(base),
    }
}

impl Monomorphizer<'_, '_> {
    /// The checker instance of the body being typed: `None` for a module
    /// initializer, the entry, or a body typed outside any instance.
    pub(super) fn current_instance(&self) -> Option<&InstanceKey> {
        self.instance_stack.last()?.as_ref()
    }

    /// Reuse an active callable at identical effective inputs, including its
    /// completed storage contract. Recursion cannot start a second negotiation.
    pub(super) fn recursive_numeric_layout(
        &self,
        key: &InstanceKey,
    ) -> Option<Option<brass_hir::NumericLayout>> {
        self.instance_stack
            .iter()
            .rev()
            .flatten()
            .find(|active| active.callable == key.callable && active.args == key.args)
            .map(|active| active.numeric_layout.clone())
    }

    /// The instance key of free function `base` at `args`.
    pub(super) fn function_instance(&self, base: &str, args: &[Type]) -> Option<InstanceKey> {
        InstanceKey::function(self.program, base, args)
    }

    /// The instance key of method `method` of the type stored as `owner` at
    /// `args` (the receiver first for an instance method).
    pub(super) fn method_instance(
        &self,
        owner: &str,
        method: &str,
        args: &[Type],
    ) -> Option<InstanceKey> {
        InstanceKey::method(self.program, owner, method, args)
    }

    /// The return-origin storage demanded at this call in the active instance.
    pub(super) fn numeric_call_flavor(&self, site: Span) -> Option<brass_hir::NumericLayout> {
        self.numeric_calls
            .get(&(site, self.current_instance().cloned()))
            .or_else(|| self.numeric_calls.get(&(site, None)))
            .cloned()
            .flatten()
    }

    /// The type a local starts from before typing, if any: a seed the
    /// checker recorded for this instance when the instances of the body
    /// disagree at the local's expression ([`LocalDecl::seed_site`]), else
    /// the type lowering fixed (an annotation, or the seed every instance
    /// shares). A per-instance span never falls back to the shared type:
    /// another instance's seed (or a stale shared one, lowered before the
    /// disagreement was known) would type this instance's value at the
    /// wrong representation, while no seed only leaves the local to be
    /// inferred from its uses.
    pub(super) fn local_seed(&self, decl: &LocalDecl) -> Option<Type> {
        if let Some(site) = decl.seed_site {
            self.read_input(dependencies::Read::Seed(site));
        }
        if let Some(site) = decl.seed_site
            && let Some(per_instance) = self.instance_seeds.get(&site)
        {
            return per_instance.get(self.current_instance()?).cloned();
        }
        decl.ty.as_known().cloned()
    }

    /// The specialization the reflective call at `site` (of template
    /// `method`) dispatches to in the instance being typed. A keyed site is
    /// lowered only when the checker recorded per-instance targets for it, so
    /// an instance without one is an instance the checker never elaborated:
    /// an internal error rather than a guess.
    pub(super) fn keyed_target(&self, site: Span, method: &str) -> Result<String, String> {
        self.read_input(dependencies::Read::Dispatch(site));
        self.instance_dispatch
            .get(&site)
            .and_then(|per_instance| per_instance.get(self.current_instance()?))
            .cloned()
            .ok_or_else(|| {
                format!(
                    "internal error: the reflective call `{method}` has no specialization \
                     checked for this instantiation of its generic function"
                )
            })
    }

    /// The specialization of every reflective call site in the blocks of
    /// `body` that `mask` keeps (the instance's live, reachable blocks).
    pub(super) fn keyed_targets(
        &self,
        body: &MirBody,
        mask: &[bool],
    ) -> Result<HashMap<Span, String>, String> {
        let mut targets = HashMap::default();
        for (block, _) in body.blocks.iter().zip(mask).filter(|(_, live)| **live) {
            for stmt in &block.stmts {
                if let MirStmt::Assign(_, Rvalue::Call(Callee::Numeric { site, .. }, _))
                | MirStmt::Eval(Rvalue::Call(Callee::Numeric { site, .. }, _)) = stmt
                    && let Some(target) = self
                        .numeric_targets
                        .get(&(*site, self.current_instance().cloned()))
                {
                    targets.insert(*site, target.clone());
                }
                if let MirStmt::Assign(_, Rvalue::Call(Callee::Keyed { method, site }, _))
                | MirStmt::Eval(Rvalue::Call(Callee::Keyed { method, site }, _)) = stmt
                {
                    targets.insert(*site, self.keyed_target(*site, method)?);
                }
                if let MirStmt::Assign(_, Rvalue::Call(Callee::NumericFree { site, .. }, _))
                | MirStmt::Eval(Rvalue::Call(Callee::NumericFree { site, .. }, _)) = stmt
                    && let Some(target) = self
                        .numeric_targets
                        .get(&(*site, self.current_instance().cloned()))
                {
                    targets.insert(*site, target.clone());
                }
            }
        }
        Ok(targets)
    }
}

#[cfg(test)]
mod tests {
    use super::super::monomorphize;

    /// Polymorphic recursion that reaches monomorphization (the checker
    /// rejects it; this lowers the program unchecked) stops at the nesting
    /// bound with an error instead of exhausting the stack, and quickly: the
    /// failure is not retried by every enclosing frame.
    #[test]
    fn polymorphic_recursion_stops_at_the_nesting_bound() {
        let src = "fun f(x, n: int32) -> int32 {\n  if n == 0 {\n    return 0\n  }\n  \
                   return 1 + f([x], n - 1)\n}\n\
                   fun main() {\n  println(string.from(f(1, 3)))\n}\n";
        // Typing nests one frame per instance; give it the stack the driver
        // gives monomorphization.
        let skip = std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(move || {
                let ast = brass_parser::parse(src).expect("parse");
                let (program, errs) = brass_hir::lower(&[brass_hir::LoadedModule {
                    is_prelude: false,
                    path: vec!["main".into()],
                    ast,
                }]);
                assert!(errs.is_empty(), "lower: {errs:?}");
                let mir = brass_mir::lower_program(&program);
                let mono = monomorphize(&mir, &program).expect("monomorphize");
                mono.main_skip
            })
            .expect("spawn")
            .join()
            .expect("no stack overflow");
        let skip = skip.expect("`main` cannot be monomorphized");
        assert!(skip.contains("nests more than"), "{skip}");
        assert!(skip.contains("instantiating `f`"), "{skip}");
    }
}
