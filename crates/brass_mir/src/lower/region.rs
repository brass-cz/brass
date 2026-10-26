//! Certified sets of bodies that can be lowered together.

use super::{CheckerChannels, LowerTables, SubsetLowering};
use brass_hir::Program;

/// A closed set of checked bodies with final, clean diagnostics and no keyed calls.
/// The executor supplies the certificate after its checker stream has finished;
/// lowering does not infer diagnostic finality from the absence of errors.
#[derive(Debug)]
pub struct LoweringRegion {
    /// Canonical symbols in deterministic lowering order.
    symbols: Vec<String>,
}

impl LoweringRegion {
    /// Accept the executor's certified set, sorting and deduplicating symbols.
    /// Every referenced free function must also belong to the set. The caller
    /// marks bodies reached by mono needed before compiling their native code.
    pub fn checked(symbols: impl IntoIterator<Item = String>) -> Self {
        let mut symbols: Vec<_> = symbols.into_iter().collect();
        symbols.sort_unstable();
        symbols.dedup();
        Self { symbols }
    }

    /// Whether a free function belongs to this diagnostic certificate.
    pub fn contains(&self, symbol: &str) -> bool {
        self.symbols
            .binary_search_by(|s| s.as_str().cmp(symbol))
            .is_ok()
    }

    /// Number of distinct certified bodies.
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Whether the certificate contains no bodies.
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
}

impl SubsetLowering {
    /// Append certified bodies in sorted order, sharing the closure-id allocator.
    /// Returns the number added; existing bodies retain their MIR and identity.
    /// The next `finish_changes` includes the same session reset as ordinary adds.
    pub fn add_region(
        &mut self,
        region: &LoweringRegion,
        program: &Program,
        tables: &LowerTables,
        channels: &CheckerChannels,
    ) -> usize {
        region
            .symbols
            .iter()
            .filter(|s| self.add_function(program, tables, s, channels))
            .count()
    }
}
