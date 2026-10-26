//! Ordered demand discovery and checker-stream batch identities.

use brass_hir::Type;
use fxhash::FxHashMap as HashMap;

/// A body the executor needs, at the concrete argument types of its call.
#[derive(Clone, Debug)]
pub(crate) struct Demand {
    /// The free-function HIR symbol to check.
    pub symbol: String,
    /// Concrete arguments of the first call that demanded this symbol.
    pub type_args: Vec<Type>,
    /// Whether execution needs MIR rather than only a return contract.
    pub needs_body: bool,
}

/// Demands in discovery order, deduplicated by symbol with `needs_body` ORed.
/// The first argument types suffice: the checker runs one dedicated pass per
/// symbol, so later type arguments for that symbol need no additional request.
#[derive(Default)]
pub(crate) struct DemandFrontier {
    members: Vec<Demand>,
    positions: HashMap<String, usize>,
}

impl DemandFrontier {
    /// Append a new symbol or strengthen its existing body requirement.
    pub fn push(&mut self, demand: Demand) {
        if let Some(&position) = self.positions.get(&demand.symbol) {
            self.members[position].needs_body |= demand.needs_body;
        } else {
            self.positions
                .insert(demand.symbol.clone(), self.members.len());
            self.members.push(demand);
        }
    }

    /// Whether no demands await sealing.
    pub fn is_empty(&self) -> bool {
        self.members.is_empty()
    }

    /// Close the frontier into one batch with a fresh id; `None` when empty.
    pub fn seal(&mut self, ids: &mut BatchIds) -> Option<DemandBatch> {
        if self.is_empty() {
            return None;
        }
        let id = ids.next;
        ids.next = ids.next.checked_add(1).expect("demand batch ids exhausted");
        self.positions.clear();
        Some(DemandBatch {
            id,
            members: std::mem::take(&mut self.members),
        })
    }
}

/// Monotonic ids owned by one lazy state, meaningful only in its checker stream.
/// An id is never reused during a run, including batches settled without requests.
#[derive(Default)]
pub(crate) struct BatchIds {
    next: u64,
}

/// One request set sent to the checker as a unit.
pub(crate) struct DemandBatch {
    /// Unique id allocated by the owning lazy state.
    pub id: u64,
    /// Demands in discovery order, with each symbol appearing once.
    pub members: Vec<Demand>,
}

/// What settling a batch observed.
#[derive(Default)]
pub(crate) struct BatchOutcome {
    /// The seal or `Finished` settled the batch. An interrupted stream keeps
    /// its existing checked-symbol completion verdict.
    pub complete: bool,
    /// Members that required a priority request when the batch was sent.
    pub new_requests: usize,
    /// Requested symbols whose dedicated passes became visible while settling.
    pub newly_settled: usize,
}

#[cfg(test)]
mod tests {
    use super::{BatchIds, Demand, DemandFrontier};
    use brass_hir::Type;

    #[test]
    fn frontier_keeps_first_arguments_and_order_across_duplicates() {
        let mut frontier = DemandFrontier::default();
        let mut ids = BatchIds::default();
        assert!(frontier.seal(&mut ids).is_none());
        for (symbol, type_args, needs_body) in [
            ("a", vec![Type::Bool], false),
            ("b", vec![], true),
            ("a", vec![Type::Str], true),
        ] {
            frontier.push(Demand {
                symbol: symbol.into(),
                type_args,
                needs_body,
            });
        }
        let batch = frontier.seal(&mut ids).unwrap();
        assert_eq!(batch.id, 0);
        assert_eq!(
            batch
                .members
                .iter()
                .map(|d| d.symbol.as_str())
                .collect::<Vec<_>>(),
            ["a", "b"]
        );
        assert_eq!(batch.members[0].type_args, [Type::Bool]);
        assert!(batch.members[0].needs_body);
        assert!(frontier.is_empty());
        frontier.push(Demand {
            symbol: "a".into(),
            type_args: vec![],
            needs_body: false,
        });
        assert_eq!(frontier.seal(&mut ids).unwrap().id, 1);
    }
}
