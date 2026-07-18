//! Runtime JIT compilation: the backend-agnostic orchestration of deferred
//! monomorphization.
//!
//! When a type is fixed by the outside world at runtime (e.g. JSON deserialize),
//! the consumer must be specialized and compiled *then*. This module owns the
//! backend-agnostic half of that: a cache from an instance symbol to its compiled
//! callable address, and `resolve_or_compile`, which returns a cached address or
//! asks the back end to compile the instance once. The actual machine-code
//! generation is delegated through the [`RuntimeJit`] trait, which a target such
//! as `brass_jit_llvm` implements over a live execution engine -- so this crate
//! names no target dependency, exactly as [`crate::Codegen`] does for the static
//! path.

use fxhash::FxHashMap as HashMap;

use crate::mono::{MonoFunction, MonoProgram};

/// A back end that can compile an additional monomorphized instance into its
/// *live* executable form, after the program has started running -- the
/// capability deferred monomorphization needs. A target implements this over the
/// same execution engine that ran the statically-compiled program; the engine
/// drives it without knowing the target.
pub trait RuntimeJit {
    /// Compile one monomorphized instance into the live back end and return its
    /// callable machine address. Calls inside the body reference other instances
    /// by symbol; the back end resolves them against its already-compiled code.
    fn compile_instance(
        &mut self,
        program: &MonoProgram,
        f: &MonoFunction,
    ) -> Result<usize, String>;
}

/// The memory layout of a monomorphized type: its size and alignment in bytes.
/// Cached per concrete (substituted) type so a layout is computed once
/// (the `type_layouts` half of the cache).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypeLayout {
    pub size: u64,
    pub align: u64,
}

/// Monomorphization cache: two memoization tables that make each
/// `(function, concrete types)` instance compiled once and each `(type,
/// substitution)` layout computed once.
///
/// `functions` maps an instance symbol to its compiled callable address. `symbol`
/// already encodes the concrete type tuple (see [`crate::instance_symbol`]), so it
/// is the runtime-spelled `(Symbol, Vec<Type>)` key from the design. `type_layouts`
/// maps a concrete (substituted) type's mangled name -- the runtime spelling of the
/// design's `(TypeId, Substitution)` -- to its [`TypeLayout`].
#[derive(Default)]
pub struct MonomorphCache {
    functions: HashMap<String, usize>,
    type_layouts: HashMap<String, TypeLayout>,
}

impl MonomorphCache {
    pub fn new() -> Self {
        Self::default()
    }

    /// The cached address for an instance symbol, if it has been compiled.
    pub fn get(&self, symbol: &str) -> Option<usize> {
        self.functions.get(symbol).copied()
    }

    /// Record a compiled instance's address.
    pub fn insert(&mut self, symbol: String, addr: usize) {
        self.functions.insert(symbol, addr);
    }

    /// The cached layout for a concrete type's mangled name, if computed.
    pub fn layout(&self, type_name: &str) -> Option<TypeLayout> {
        self.type_layouts.get(type_name).copied()
    }

    /// The layout for `type_name`, computing it via `compute` and caching on first
    /// request so a given monomorphized type's layout is materialized once.
    pub fn layout_or_insert_with(
        &mut self,
        type_name: &str,
        compute: impl FnOnce() -> TypeLayout,
    ) -> TypeLayout {
        if let Some(l) = self.type_layouts.get(type_name) {
            return *l;
        }
        let l = compute();
        self.type_layouts.insert(type_name.to_string(), l);
        l
    }

    /// The number of compiled function instances cached.
    pub fn len(&self) -> usize {
        self.functions.len()
    }

    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }
}

/// Return the callable address of the instance named `symbol`, compiling it
/// through `backend` on first request and caching the result. This is the
/// backend-agnostic core of the runtime service: the cache and lookup live here,
/// the machine-code generation is delegated to [`RuntimeJit`]. The instance must
/// already exist in `program` (it was monomorphized -- statically, or on demand
/// by a future step before this call).
pub fn resolve_or_compile<B: RuntimeJit>(
    cache: &mut MonomorphCache,
    backend: &mut B,
    program: &MonoProgram,
    symbol: &str,
) -> Result<usize, String> {
    if let Some(addr) = cache.get(symbol) {
        return Ok(addr);
    }
    let f = program
        .lookup(symbol)
        .ok_or_else(|| format!("no monomorphized instance `{symbol}` to compile"))?;
    let addr = backend.compile_instance(program, f)?;
    cache.insert(symbol.to_string(), addr);
    Ok(addr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomorphize;

    /// A `RuntimeJit` that records how many instances it was asked to compile and
    /// hands out distinct fake addresses -- enough to test the cache/orchestration
    /// without a real code generator.
    struct CountingBackend {
        compiles: usize,
    }

    impl RuntimeJit for CountingBackend {
        fn compile_instance(
            &mut self,
            _program: &MonoProgram,
            _f: &MonoFunction,
        ) -> Result<usize, String> {
            self.compiles += 1;
            Ok(0x1000 + self.compiles)
        }
    }

    /// `resolve_or_compile` compiles an instance once and serves the cached address
    /// thereafter -- the backend-agnostic orchestration deferred monomorphization
    /// relies on, exercised here with a mock back end.
    #[test]
    fn resolve_or_compile_caches_per_instance() {
        let src = "fun main() {\n  let x = 1 + 2\n}\n";
        let ast = brass_parser::parse(src).expect("parse");
        let (program, errs) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = brass_mir::lower_program(&program);
        let mono = monomorphize(&mir, &program).expect("monomorphize");
        // Pick any existing instance to compile.
        let symbol = mono
            .functions
            .first()
            .map(|f| f.symbol.clone())
            .expect("at least one instance");

        let mut cache = MonomorphCache::new();
        let mut backend = CountingBackend { compiles: 0 };

        let a = resolve_or_compile(&mut cache, &mut backend, &mono, &symbol).expect("compile");
        let b = resolve_or_compile(&mut cache, &mut backend, &mono, &symbol).expect("cached");
        assert_eq!(a, b, "same instance -> same address");
        assert_eq!(backend.compiles, 1, "compiled once, then cached");
        assert_eq!(cache.len(), 1);

        // A missing instance is an error, not a silent miscompile.
        assert!(resolve_or_compile(&mut cache, &mut backend, &mono, "nope$x").is_err());
    }

    /// The `type_layouts` half of the cache computes a concrete
    /// type's layout once and serves it thereafter.
    #[test]
    fn type_layout_is_memoized() {
        let mut cache = MonomorphCache::new();
        let mut computed = 0;
        let mut compute = || {
            computed += 1;
            TypeLayout { size: 16, align: 8 }
        };
        let a = cache.layout_or_insert_with("Point$int32", &mut compute);
        let b = cache.layout_or_insert_with("Point$int32", &mut compute);
        assert_eq!(a, b);
        assert_eq!(computed, 1, "layout computed once, then cached");
        assert_eq!(
            cache.layout("Point$int32"),
            Some(TypeLayout { size: 16, align: 8 })
        );
        assert_eq!(cache.layout("Other"), None);
    }
}
