//! Per-module memo of HIR name resolution over one immutable catalog. Both hits
//! and absences are stable until a body refresh replaces the borrowed program.

use brass_hir::{FunInfo, Program, TypeAlias, TypeInfo};
use fxhash::FxHashMap as HashMap;
use std::{cell::RefCell, rc::Rc};

/// Reuse HIR's decisions; this cache never implements an alternate resolver.
pub(super) struct Names<'a> {
    program: &'a Program,
    module: &'a [String],
    functions: RefCell<HashMap<String, Option<&'a FunInfo>>>,
    types: RefCell<HashMap<String, Option<&'a TypeInfo>>>,
    nominal: RefCell<HashMap<String, Option<&'a TypeInfo>>>,
    aliases: RefCell<HashMap<String, Option<&'a TypeAlias>>>,
    variants: RefCell<HashMap<String, Rc<[&'a TypeInfo]>>>,
}

impl<'a> Names<'a> {
    /// Allocate no entries until a reached body or certificate asks for a name.
    pub(super) fn new(program: &'a Program, module: &'a [String]) -> Self {
        Self {
            program,
            module,
            functions: Default::default(),
            types: Default::default(),
            nominal: Default::default(),
            aliases: Default::default(),
            variants: Default::default(),
        }
    }

    /// Resolve a free function, including qualified imports and shadowing.
    pub(super) fn function(&self, name: &str) -> Option<&'a FunInfo> {
        cached(&self.functions, name, || {
            self.program.resolve_function(self.module, name)
        })
    }

    /// Resolve a nominal name without following an alias.
    pub(super) fn ty(&self, name: &str) -> Option<&'a TypeInfo> {
        cached(&self.types, name, || {
            self.program.resolve_type(self.module, name)
        })
    }

    /// Resolve an alias while retaining its complete target substitution.
    pub(super) fn alias(&self, name: &str) -> Option<&'a TypeAlias> {
        cached(&self.aliases, name, || {
            self.program.resolve_type_alias(self.module, name)
        })
    }

    /// Resolve the nominal declaration behind a name or alias.
    pub(super) fn nominal(&self, name: &str) -> Option<&'a TypeInfo> {
        cached(&self.nominal, name, || {
            self.program.resolve_type_or_alias(self.module, name)
        })
    }

    /// Retain HIR's deterministic visible variant-owner order.
    pub(super) fn variants(&self, name: &str) -> Rc<[&'a TypeInfo]> {
        cached(&self.variants, name, || {
            self.program
                .sums_in_scope_with_variant(self.module, name)
                .into()
        })
    }
}

fn cached<T: Clone>(
    cache: &RefCell<HashMap<String, T>>,
    name: &str,
    resolve: impl FnOnce() -> T,
) -> T {
    if let Some(value) = cache.borrow().get(name) {
        return value.clone();
    }
    let value = resolve();
    cache.borrow_mut().insert(name.into(), value.clone());
    value
}
