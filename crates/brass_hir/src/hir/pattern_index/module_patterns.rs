//! Module-visible owners and declaration-only pattern heads.

use std::cell::RefCell;
use std::rc::Rc;

use super::super::{BracedHead, HashMap, Program, TypeInfo};

/// A declaration selected by a written pattern qualifier, before subject typing.
#[derive(Clone, Copy)]
pub enum PatternTypeHead<'p> {
    /// The qualifier resolves to this nominal declaration, including aliases.
    Nominal(&'p TypeInfo),
    /// An alias exists, but its outer type is not a record or sum.
    NonNominalAlias,
    /// No declaration resolves under this spelling in the module.
    Unknown,
}

#[derive(Clone, Copy)]
enum NominalHead {
    Nominal(i32),
    NonNominalAlias,
    Unknown,
}

#[derive(Clone, Copy)]
struct HeadFacts {
    nominal: NominalHead,
    global_variant: bool,
}

struct ScopedOwners {
    ids: Box<[i32]>,
    unit: bool,
}

/// The declaration facts for one module, without subject types or diagnostics.
pub(super) struct ModulePatterns {
    module: Vec<String>,
    owners: HashMap<String, ScopedOwners>,
    heads: RefCell<HashMap<String, HeadFacts>>,
}

impl ModulePatterns {
    /// Filter ordered global owners with the authoritative visibility rule.
    pub(super) fn new(program: &Program, module: &[String]) -> Self {
        let visible: super::super::HashSet<i32> = program
            .types
            .values()
            .filter(|info| info.is_sum() && program.sum_in_scope(module, info))
            .map(|info| info.id)
            .collect();
        let owners = program
            .pattern_index
            .owners
            .iter()
            .filter_map(|(name, ids)| {
                let ids: Box<[i32]> = ids
                    .iter()
                    .copied()
                    .filter(|id| visible.contains(id))
                    .collect();
                if ids.is_empty() {
                    return None;
                }
                let unit = ids.iter().any(|id| {
                    program
                        .type_by_id(*id)
                        .and_then(|info| info.variant(name))
                        .is_some_and(|variant| variant.fields.is_empty())
                });
                Some((name.clone(), ScopedOwners { ids, unit }))
            })
            .collect();
        Self {
            module: module.to_vec(),
            owners,
            heads: RefCell::default(),
        }
    }
}

/// A module's pattern-resolution view, tied to one immutable program topology.
/// Local qualifier shadowing is validated by name resolution before these queries;
/// subject-dependent choices and diagnostics remain with the caller.
pub struct PatternScope<'p> {
    program: &'p Program,
    facts: Rc<ModulePatterns>,
}

impl<'p> PatternScope<'p> {
    /// All visible nominal owners, in global owner order, without allocation.
    pub fn owner_ids(&self, name: &str) -> &[i32] {
        self.facts
            .owners
            .get(name)
            .map_or(&[], |owners| &owners.ids)
    }

    /// The first visible owner, or the first global owner if requested.
    pub fn first_owner(&self, name: &str, global_fallback: bool) -> Option<&'p TypeInfo> {
        let id = self.owner_ids(name).first().copied().or_else(|| {
            global_fallback
                .then(|| {
                    self.program
                        .pattern_index
                        .owners
                        .get(name)?
                        .first()
                        .copied()
                })
                .flatten()
        })?;
        self.program.type_by_id(id)
    }

    /// Whether any visible sum declares a fieldless variant of this spelling.
    pub fn is_unit_variant(&self, name: &str) -> bool {
        self.facts
            .owners
            .get(name)
            .is_some_and(|owners| owners.unit)
    }

    fn head(&self, name: &str) -> HeadFacts {
        if let Some(facts) = self.facts.heads.borrow().get(name) {
            return *facts;
        }
        let nominal = match self.program.resolve_type_or_alias(&self.facts.module, name) {
            Some(info) => NominalHead::Nominal(info.id),
            None if self
                .program
                .resolve_type_alias(&self.facts.module, name)
                .is_some() =>
            {
                NominalHead::NonNominalAlias
            }
            None => NominalHead::Unknown,
        };
        let facts = HeadFacts {
            nominal,
            global_variant: self.program.pattern_index.owners.contains_key(name),
        };
        // Resolution is outside the mutable borrow: alias lookup can consult
        // other program indexes without re-entering an outstanding borrow.
        self.facts
            .heads
            .borrow_mut()
            .insert(name.to_string(), facts);
        facts
    }

    /// Resolve a normalized qualifier. Callers expand receiver-specific `Self`
    /// before querying and retain the written spelling for diagnostics.
    pub fn type_head(&self, name: &str) -> PatternTypeHead<'p> {
        match self.head(name).nominal {
            NominalHead::Nominal(id) => {
                PatternTypeHead::Nominal(self.program.type_by_id(id).expect("indexed nominal"))
            }
            NominalHead::NonNominalAlias => PatternTypeHead::NonNominalAlias,
            NominalHead::Unknown => PatternTypeHead::Unknown,
        }
    }

    /// Resolve a braced head using global variant existence and a visible record.
    /// A record/variant collision stays undecided until the subject is known.
    pub fn braced_head(&self, name: &str) -> BracedHead<'p> {
        if name.contains('.') {
            return BracedHead::Record;
        }
        let facts = self.head(name);
        if !facts.global_variant {
            return BracedHead::Record;
        }
        if let NominalHead::Nominal(id) = facts.nominal
            && let Some(info) = self.program.type_by_id(id)
            && !info.is_sum()
        {
            BracedHead::RecordOrVariant(info)
        } else {
            BracedHead::Variant
        }
    }
}

impl Program {
    /// Reuse declaration facts for a module. The HIR belongs to one analysis
    /// thread; lazy checking and execution lower independent programs and share
    /// channels rather than this cache.
    pub fn pattern_scope(&self, module: &[String]) -> PatternScope<'_> {
        self.pattern_index.assert_consistent(self);
        let cached = self.pattern_index.modules.borrow().get(module).cloned();
        let facts = cached.unwrap_or_else(|| {
            let facts = Rc::new(ModulePatterns::new(self, module));
            self.pattern_index
                .modules
                .borrow_mut()
                .insert(module.to_vec(), Rc::clone(&facts));
            facts
        });
        PatternScope {
            program: self,
            facts,
        }
    }
}
