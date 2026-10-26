//! Declaration indexes shared by pattern checking and lowering.

use std::cell::RefCell;
use std::rc::Rc;

use super::{HashMap, Program, TypeKind};

mod module_patterns;
pub use module_patterns::{PatternScope, PatternTypeHead};

/// Sorted nominal owners of each variant spelling, independent of module scope.
#[derive(Default)]
pub(crate) struct PatternIndex {
    owners: HashMap<String, Box<[i32]>>,
    modules: RefCell<HashMap<Vec<String>, Rc<module_patterns::ModulePatterns>>>,
    #[cfg(debug_assertions)]
    counts: [usize; 10],
}

impl PatternIndex {
    fn new(program: &Program) -> Self {
        let mut owners: HashMap<String, Vec<i32>> = HashMap::default();
        for info in program.types.values() {
            if let TypeKind::Sum { variants } = &info.kind {
                for variant in variants {
                    owners
                        .entry(variant.name.clone())
                        .or_default()
                        .push(info.id);
                }
            }
        }
        for ids in owners.values_mut() {
            ids.sort_by(|a, b| {
                let a = program.type_by_id(*a).expect("collected owner");
                let b = program.type_by_id(*b).expect("collected owner");
                a.name.cmp(&b.name).then_with(|| a.symbol.cmp(&b.symbol))
            });
            // Recovered declarations may repeat a variant name. The scan's
            // membership predicate includes each sum only once.
            ids.dedup();
        }
        Self {
            owners: owners
                .into_iter()
                .map(|(name, ids)| (name, ids.into_boxed_slice()))
                .collect(),
            modules: RefCell::default(),
            #[cfg(debug_assertions)]
            counts: declaration_counts(program),
        }
    }

    fn assert_consistent(&self, program: &Program) {
        #[cfg(debug_assertions)]
        debug_assert_eq!(
            self.counts,
            declaration_counts(program),
            "rebuild resolution indexes after topology changes"
        );
        #[cfg(not(debug_assertions))]
        let _ = program;
    }
}

#[cfg(debug_assertions)]
fn declaration_counts(program: &Program) -> [usize; 10] {
    let (variants, fields) =
        program
            .types
            .values()
            .fold((0, 0), |(count, fields), info| match &info.kind {
                TypeKind::Sum { variants } => (
                    count + variants.len(),
                    fields + variants.iter().map(|v| v.fields.len()).sum::<usize>(),
                ),
                TypeKind::Record { .. } => (count, fields),
            });
    [
        program.types.len(),
        variants,
        fields,
        program.type_aliases.len(),
        program.prelude_modules.len(),
        program.module_imports.values().map(Vec::len).sum(),
        program.import_origins.values().map(HashMap::len).sum(),
        program.import_renames.values().map(HashMap::len).sum(),
        program.module_aliases.values().map(HashMap::len).sum(),
        program.symbol_aliases.len(),
    ]
}

impl Program {
    /// Rebuild declaration indexes after changing nominal identities, variants,
    /// aliases or module visibility. Does not alter inference or method metadata.
    pub fn rebuild_resolution_indexes(&mut self) {
        self.types_by_id = self
            .types
            .iter()
            .map(|(symbol, info)| (info.id, symbol.clone()))
            .collect();
        self.type_names = self
            .types
            .iter()
            .flat_map(|(symbol, info)| [symbol.clone(), info.name.clone()])
            .collect();
        self.pattern_index = PatternIndex::new(self);
    }

    /// Nominal ids of global variant owners, ordered by local name then symbol.
    /// Missing spellings return an empty slice without allocating.
    pub fn variant_owner_ids(&self, variant: &str) -> &[i32] {
        self.pattern_index.assert_consistent(self);
        self.pattern_index
            .owners
            .get(variant)
            .map_or(&[], |ids| ids)
    }
}

#[cfg(test)]
mod tests;
