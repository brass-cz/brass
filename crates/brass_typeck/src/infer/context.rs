//! The context seed: the cross-module tables a context-only run leaves
//! behind, and how a checker loads them so that only the entry module is
//! checked again.

use super::*;

/// The cross-module tables a CONTEXT-ONLY analysis (every module except the
/// entry) leaves behind, fully resolved against its own solver. Applied to a
/// later run as a seed, they let that run check ONLY the entry module: the
/// context's schemes, inferred returns, and globals are read from here instead
/// of being re-derived, which is where a library-heavy program spends almost
/// all of its inference time.
///
/// An item-selective seed instead certifies only the work listed in `items`;
/// its consumer completes uncovered preparation and retains ordinary body work.
/// It never grants whole-module coverage.
///
/// The tables are span-free by construction (keyed by symbol or
/// module path), so they survive the entry file changing size. Inference
/// VARIABLE ids are not portable -- a consuming run mints its own -- so
/// [`ContextTables::remapped`] renumbers every open variable into the consumer's
/// namespace first, one map across all tables so linked entries stay linked.
///
/// The table fields are the checker's tables of the same names. A complete
/// run's tables serve the same way to check the methods generated from keyed
/// templates afterwards ([`analyze_generated`]).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ContextTables {
    /// The seed satisfied all numeric demands without negotiation.
    pub ordinary_numeric: bool,
    /// Explicit item/shared coverage; partial preparation never covers a module.
    pub items: Option<crate::reachability::AnalysisView>,
    pub schemes: HashMap<String, TypeScheme>,
    pub function_returns: HashMap<String, Type>,
    pub method_returns: HashMap<(String, String), Type>,
    pub method_return_props: HashSet<(String, String)>,
    pub co_method_returns: HashMap<(String, String), Type>,
    pub global_defs: HashMap<Vec<String>, HashMap<String, Type>>,
    /// One past the highest variable id the tables mention.
    pub next_var: u32,
    /// Every bare top-level name the context defines. An entry defining one of
    /// these would QUALIFY the context's symbols in the combined program,
    /// detaching every table key -- the consumer must bail to an unseeded run.
    pub bare_names: HashSet<String>,
    /// The module paths these tables cover. `None` means the whole context
    /// (every module but the entry) -- the full-seed case. `Some` marks a
    /// PARTIAL seed (see [`ContextTables::retain_modules`]): only the listed
    /// modules skip their passes; the rest re-analyze against the seed. An item
    /// seed never grants this module-level coverage.
    pub covered: Option<HashSet<Vec<String>>>,
    /// The program-wide storage symbols and nominal IDs these tables were
    /// built against. Both can change when an otherwise unrelated module
    /// adds a declaration, so partial reuse requires an exact match.
    pub(super) program_identity: ContextProgramIdentity,
}

/// The parts of HIR identity embedded in context table keys and values.
#[derive(Clone, Debug, Default, PartialEq)]
pub(super) struct ContextProgramIdentity {
    functions: std::collections::BTreeMap<String, Vec<String>>,
    types: std::collections::BTreeMap<String, (Vec<String>, i32)>,
}

impl ContextProgramIdentity {
    pub(super) fn of(program: &Program) -> Self {
        Self {
            functions: program
                .functions
                .iter()
                .map(|(symbol, info)| (symbol.clone(), info.module.clone()))
                .collect(),
            types: program
                .types
                .iter()
                .map(|(symbol, info)| (symbol.clone(), (info.module.clone(), info.id)))
                .collect(),
        }
    }
}

impl ContextTables {
    /// Item seeds require the same storage symbols and nominal identities in
    /// the consuming catalog. New declarations may be appended, not renumber old ones.
    pub(crate) fn item_identity_matches(&self, program: &Program) -> bool {
        self.items.is_none()
            || (self
                .program_identity
                .functions
                .iter()
                .all(|(symbol, module)| {
                    program
                        .functions
                        .get(symbol)
                        .is_some_and(|f| &f.module == module)
                })
                && self
                    .program_identity
                    .types
                    .iter()
                    .all(|(symbol, (module, id))| {
                        program
                            .types
                            .get(symbol)
                            .is_some_and(|t| &t.module == module && &t.id == id)
                    }))
    }

    /// Whether this seed covers `module`, whose per-item passes a seeded run
    /// then skips: every module but the entry (`main`) for a full seed, the
    /// listed ones for a partial seed.
    pub(crate) fn covers_module(&self, module: &[String]) -> bool {
        if self.items.is_some() {
            return false;
        }
        match &self.covered {
            Some(covered) => covered.contains(module),
            None => !matches!(module, [name] if name == "main"),
        }
    }

    /// The tables with every inference variable renumbered densely from `base`,
    /// and the first id past them. One mapping is applied across all tables, so
    /// a variable shared between entries (a scheme parameter appearing in a
    /// method return) stays shared.
    pub fn remapped(&self, base: u32) -> (ContextTables, u32) {
        use std::collections::BTreeMap;
        let mut vars: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
        for scheme in self.schemes.values() {
            vars.extend(scheme.params.iter().copied());
            for (_, t) in &scheme.fields {
                vars.extend(brass_hir::type_vars(t));
            }
            for m in scheme.methods.values() {
                for (_, t) in &m.params {
                    vars.extend(brass_hir::type_vars(t));
                }
                vars.extend(brass_hir::type_vars(&m.ret));
            }
        }
        for t in self
            .function_returns
            .values()
            .chain(self.method_returns.values())
            .chain(self.co_method_returns.values())
            .chain(self.global_defs.values().flat_map(|defs| defs.values()))
        {
            vars.extend(brass_hir::type_vars(t));
        }
        let map_id: HashMap<u32, u32> = vars
            .iter()
            .enumerate()
            .map(|(i, v)| (*v, base + i as u32))
            .collect();
        let subst: BTreeMap<u32, Type> = map_id
            .iter()
            .map(|(old, new)| (*old, Type::Unknown(*new)))
            .collect();
        let re = |t: &Type| brass_hir::substitute_vars(t, &subst);
        let out = ContextTables {
            ordinary_numeric: self.ordinary_numeric,
            items: self.items.clone(),
            schemes: self
                .schemes
                .iter()
                .map(|(name, scheme)| {
                    let mut s = scheme.clone();
                    s.params = s.params.iter().map(|v| map_id[v]).collect();
                    s.fields = s.fields.iter().map(|(n, t)| (n.clone(), re(t))).collect();
                    for m in s.methods.values_mut() {
                        m.params = m.params.iter().map(|(n, t)| (n.clone(), re(t))).collect();
                        m.ret = re(&m.ret);
                    }
                    (name.clone(), s)
                })
                .collect(),
            function_returns: self
                .function_returns
                .iter()
                .map(|(k, t)| (k.clone(), re(t)))
                .collect(),
            method_returns: self
                .method_returns
                .iter()
                .map(|(k, t)| (k.clone(), re(t)))
                .collect(),
            method_return_props: self.method_return_props.clone(),
            co_method_returns: self
                .co_method_returns
                .iter()
                .map(|(k, t)| (k.clone(), re(t)))
                .collect(),
            global_defs: self
                .global_defs
                .iter()
                .map(|(m, defs)| {
                    (
                        m.clone(),
                        defs.iter().map(|(n, t)| (n.clone(), re(t))).collect(),
                    )
                })
                .collect(),
            next_var: base + map_id.len() as u32,
            bare_names: self.bare_names.clone(),
            covered: self.covered.clone(),
            program_identity: self.program_identity.clone(),
        };
        let next = out.next_var;
        (out, next)
    }

    /// Restrict these tables to the entries owned by `keep` modules,
    /// attributing each entry through `program` (a context program over the
    /// same modules): a function return by its symbol's defining module, a
    /// scheme and the method tables by the type's, `global_defs` by its own
    /// key. The identity guard below rejects a program whose storage symbols
    /// or nominal IDs changed, so every retained key still names the same HIR
    /// item. `bare_names` is kept WHOLE: the declaration set is unchanged,
    /// and shrinking it would weaken the consumer's collision bail.
    /// `next_var` is kept too -- the retained entries keep
    /// their one coherent variable space, and the re-analysis of the dropped
    /// modules allocates past it. Sound because a retained (clean) module
    /// cannot reference a dropped (dirty) one: references follow imports,
    /// and the dirty closure includes every transitive importer.
    ///
    /// Returns `false` without changing the tables when the current program's
    /// storage symbols or nominal IDs differ. Those identities are global to
    /// lowering rather than module-local, so even an unchanged module cannot
    /// safely retain tables across such a change.
    pub fn retain_modules(&mut self, program: &Program, keep: &HashSet<Vec<String>>) -> bool {
        if self.program_identity != ContextProgramIdentity::of(program) {
            return false;
        }
        // Retention can only narrow an existing partial seed: a module whose
        // tables the seed does not hold is not reclaimed by naming it in
        // `keep`.
        let keep: HashSet<Vec<String>> = match &self.covered {
            Some(covered) => keep.intersection(covered).cloned().collect(),
            None => keep.clone(),
        };
        let fn_kept = |sym: &String| {
            program
                .functions
                .get(sym)
                .is_some_and(|f| keep.contains(&f.module))
        };
        let ty_kept = |name: &String| {
            program
                .types
                .get(
                    name.split_once('.')
                        .map_or(name.as_str(), |(symbol, _)| symbol),
                )
                .is_some_and(|t| keep.contains(&t.module))
        };
        self.function_returns.retain(|sym, _| fn_kept(sym));
        self.schemes.retain(|name, _| ty_kept(name));
        self.method_returns.retain(|(ty, _), _| ty_kept(ty));
        self.co_method_returns.retain(|(ty, _), _| ty_kept(ty));
        self.method_return_props.retain(|(ty, _)| ty_kept(ty));
        self.global_defs.retain(|module, _| keep.contains(module));
        if let Some(items) = &mut self.items {
            items.retain(program, &keep);
        }
        self.covered = Some(keep);
        true
    }
}

impl Checker<'_> {
    /// Load remapped context tables into this checker and confine the per-item
    /// passes to the entry module. The caller has already renumbered the
    /// tables' variables past this checker's counter.
    pub(super) fn apply_seed(&mut self, seed: ContextTables, next_var: u32) -> AppliedSeedMetadata {
        let ContextTables {
            ordinary_numeric,
            items,
            schemes,
            function_returns,
            method_returns,
            method_return_props,
            co_method_returns,
            global_defs,
            next_var: table_next_var,
            bare_names,
            covered,
            program_identity,
        } = seed;
        let scheme_keys = schemes.keys().cloned().collect();
        let function_return_keys = function_returns.keys().cloned().collect();
        let method_return_keys = method_returns.keys().cloned().collect();
        let method_return_prop_keys = method_return_props.clone();
        let co_method_return_keys = co_method_returns.keys().cloned().collect();
        let global_def_keys = global_defs.keys().cloned().collect();
        // Coverage belongs to the producer's storage keys as well as its source
        // IDs. A generated method can share its template's span; projecting a
        // source certificate onto that new key would falsely cover its return.
        self.item_seed = items.map(Rc::new);
        self.numeric_seed_ordinary = ordinary_numeric;
        self.schemes = schemes;
        self.observe_scheme_install();
        self.function_returns = function_returns;
        self.method_returns = method_returns;
        self.method_return_props = method_return_props;
        self.co_method_returns = co_method_returns;
        self.global_defs = global_defs;
        self.seeded_set = covered;
        self.next_unknown = self.next_unknown.max(next_var);
        self.entry_only = true;
        self.assert_item_seed(self.program);
        AppliedSeedMetadata {
            next_var: table_next_var,
            bare_names,
            program_identity,
            scheme_keys,
            function_return_keys,
            method_return_keys,
            method_return_prop_keys,
            co_method_return_keys,
            global_def_keys,
        }
    }

    /// Recover the applied seed after a preliminary checker has read it. Any
    /// entries inferred for uncovered modules are removed before the tables are
    /// transferred to the real checker.
    pub(super) fn take_applied_seed(&mut self, metadata: AppliedSeedMetadata) -> ContextTables {
        let covered = self.seeded_set.take();
        self.schemes
            .retain(|name, _| metadata.scheme_keys.contains(name));
        self.function_returns
            .retain(|symbol, _| metadata.function_return_keys.contains(symbol));
        self.method_returns
            .retain(|key, _| metadata.method_return_keys.contains(key));
        self.method_return_props
            .retain(|key| metadata.method_return_prop_keys.contains(key));
        self.co_method_returns
            .retain(|key, _| metadata.co_method_return_keys.contains(key));
        self.global_defs
            .retain(|module, _| metadata.global_def_keys.contains(module));

        ContextTables {
            ordinary_numeric: self.numeric_seed_ordinary,
            items: self.item_seed.take().map(|v| (*v).clone()),
            schemes: std::mem::take(&mut self.schemes),
            function_returns: std::mem::take(&mut self.function_returns),
            method_returns: std::mem::take(&mut self.method_returns),
            method_return_props: std::mem::take(&mut self.method_return_props),
            co_method_returns: std::mem::take(&mut self.co_method_returns),
            global_defs: std::mem::take(&mut self.global_defs),
            next_var: metadata.next_var,
            bare_names: metadata.bare_names,
            covered,
            program_identity: metadata.program_identity,
        }
    }

    /// Whether `module` was covered by the applied seed: anything but the
    /// entry (whose module path is always `main`) for a full seed, or the
    /// seed's own module list for a partial one (an incremental context
    /// rebuild -- the uncovered modules get real passes here).
    pub(super) fn seeded_module(&self, module: &[String]) -> bool {
        if !self.entry_only || self.item_seed.is_some() {
            return false;
        }
        match &self.seeded_set {
            Some(set) => set.contains(module),
            None => !matches!(module, [m] if m == "main"),
        }
    }
}

/// What `Checker::apply_seed` keeps aside besides the tables it loads: the
/// seed's own fields the checker does not hold, and which table keys came
/// from the seed, so `Checker::take_applied_seed` can hand back exactly the
/// seed.
pub(super) struct AppliedSeedMetadata {
    next_var: u32,
    bare_names: HashSet<String>,
    program_identity: ContextProgramIdentity,
    scheme_keys: HashSet<String>,
    function_return_keys: HashSet<String>,
    method_return_keys: HashSet<(String, String)>,
    method_return_prop_keys: HashSet<(String, String)>,
    co_method_return_keys: HashSet<(String, String)>,
    global_def_keys: HashSet<Vec<String>>,
}
