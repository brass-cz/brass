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
    /// initializer or a body typed outside any instance.
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

    /// The type a local starts from before typing. Source-fixed annotations have no
    /// seed site and apply directly. A checker seed inside a callable requires
    /// an observation for that exact instance, even when the span has no
    /// per-instance entries: a shared observation from an open preparation frame
    /// or another instance cannot type this body. Without an exact seed the
    /// local is inferred from its own operands and uses. Shared seeds apply only
    /// outside a callable instance (for example, a module initializer).
    pub(super) fn local_seed(&self, decl: &LocalDecl) -> Option<Type> {
        if let Some(site) = decl.seed_site {
            self.read_input(dependencies::Read::Seed(site));
            if let Some(instance) = self.current_instance() {
                return self.instance_seeds.get(&site)?.get(instance).cloned();
            }
            if self.instance_seeds.contains_key(&site) {
                return None;
            }
        }
        decl.ty.as_known().cloned()
    }

    /// Resolve field-list guards under the current checker instance. Missing entries
    /// are kept absent: only a live loop requires a checked expansion.
    pub(super) fn field_selections(&self, body: &MirBody) -> HashMap<Span, Vec<String>> {
        let mut selected = HashMap::default();
        if self.instance_fields.is_empty() {
            return selected;
        }
        for block in &body.blocks {
            for stmt in &block.stmts {
                if let MirStmt::Assign(_, Rvalue::FieldsTest { site, .. }) = stmt {
                    self.read_input(dependencies::Read::Fields(*site));
                    if let Some(fields) = self
                        .current_instance()
                        .and_then(|key| self.instance_fields.get(site)?.get(key))
                    {
                        selected.insert(*site, fields.clone());
                    }
                }
            }
        }
        selected
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

    #[test]
    fn unobserved_instance_never_uses_a_shared_expression_seed() {
        use super::super::Monomorphizer;
        use brass_hir::{InstanceCallable, InstanceKey, Program, Type};
        use brass_mir::{LocalDecl, TypeRef};
        use brass_parser::Span;

        let program = Program::empty();
        let site = Span::new(1, 2);
        let shared = Type::Slice(Box::new(Type::Str));
        let local = LocalDecl {
            ty: TypeRef::Known(shared.clone()),
            name: None,
            seed_site: Some(site),
        };
        let key = InstanceKey {
            callable: InstanceCallable::Function("collect".into()),
            args: vec![Type::Bool],
            numeric_layout: None,
        };
        let mut mir = brass_mir::lower_program(&program);
        // An open preparation frame can publish a shared type with no exact key.
        let mut mono = Monomorphizer::new(&mir, &program);
        assert_eq!(mono.local_seed(&local), Some(shared.clone()));
        mono.instance_stack.push(Some(key.clone()));
        assert_eq!(mono.local_seed(&local), None);
        // A source annotation remains fixed even in an unobserved instance.
        let annotation = LocalDecl {
            seed_site: None,
            ..local.clone()
        };
        assert_eq!(mono.local_seed(&annotation), Some(shared.clone()));
        drop(mono);

        let other = InstanceKey {
            args: vec![Type::Str],
            ..key.clone()
        };
        mir.instance_seeds
            .entry(site)
            .or_default()
            .insert(other, shared);
        let mut mono = Monomorphizer::new(&mir, &program);
        mono.instance_stack.push(Some(key.clone()));
        assert_eq!(mono.local_seed(&local), None);
        drop(mono);
        let exact = Type::Slice(Box::new(Type::Bool));
        mir.instance_seeds
            .entry(site)
            .or_default()
            .insert(key.clone(), exact.clone());
        let mut mono = Monomorphizer::new(&mir, &program);
        mono.instance_stack.push(Some(key));
        assert_eq!(mono.local_seed(&local), Some(exact));
    }

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
                    source: None,
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
