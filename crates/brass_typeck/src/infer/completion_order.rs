//! Dependency ordering from committed priority elaborations only.

use super::Checker;
use brass_hir::{FunInfo, InstanceCallable, InstanceKey, Program, Type};
use brass_parser::ast::{Expr, Stmt};
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::rc::Rc;

/// Why an observed dependency cannot consume its symbol's dedicated pass early.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum IneligibleReason {
    /// The certified dependency tree contains a cycle, so no deepest-first order exists.
    Recursive,
    /// The requested frame cannot be canonicalized to fully concrete arguments.
    OpenArguments,
    /// A structural argument can take a fallback path instead of a dedicated frame.
    StructuralArgument,
    /// Keyed discovery can contribute effects that the ordinary pass cannot finalize.
    KeyedCall,
    /// The frame or a transitive callee requires numeric negotiation.
    NumericNegotiation,
    /// The body assigns state outside the certified expression-only subset.
    GlobalWrite,
    /// The observed instance is not proven to match the symbol's one dedicated frame.
    SharedSymbolPass,
    /// The conservative expansion charge cannot fit within the elaboration budget.
    BudgetBound,
    /// The body is outside the closed expression subset, including propagation
    /// that could move a warning into an earlier delta.
    UncertifiedBody,
}

/// A closed dependency tree, or the first deterministic reason to keep its order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Eligibility {
    /// Every observed dependency has a compatible frame and a bounded effect certificate.
    Closed,
    /// The first failed certificate keeps this demand in ordinary pass order.
    Ineligible(IneligibleReason),
}

/// Concrete call edges observed during committed priority elaborations, never
/// background passes or probes. Syntax certificates restrict effects but do not
/// add call edges or discover instances. Clones share immutable observations.
#[derive(Clone, Default)]
pub(super) struct CompletionGraph {
    /// Enable observations only while committed priority or completion passes run.
    /// Probe constructors disable this flag even when cloning an active checker.
    pub(super) active: bool,
    data: Rc<GraphData>,
}

#[derive(Clone, Default)]
struct GraphData {
    edge_revision: usize,
    frames: HashMap<String, Vec<Type>>,
    edges: HashMap<InstanceKey, Vec<InstanceKey>>,
    capped: HashSet<InstanceKey>,
    completed: HashMap<String, InstanceKey>,
    eligibility: HashMap<String, Result<u64, IneligibleReason>>,
}

impl CompletionGraph {
    /// Record a committed concrete edge in discovery order, deduplicating repeats.
    /// A capped elaboration marks both endpoints; callers exclude probes and background passes.
    pub(super) fn observe(&mut self, caller: &InstanceKey, callee: &InstanceKey, capped: bool) {
        let data = Rc::make_mut(&mut self.data);
        let edges = data.edges.entry(caller.clone()).or_default();
        if !edges.contains(callee) {
            edges.push(callee.clone());
            data.edge_revision += 1;
        }
        if capped {
            data.capped.insert(caller.clone());
            data.capped.insert(callee.clone());
        }
    }

    /// Changes only when a committed pass adds an edge. Completing a node or
    /// observing an existing edge cannot change the remaining dependency order.
    pub(super) fn edge_revision(&self) -> usize {
        self.data.edge_revision
    }

    /// Whether a committed priority edge marked this instance as depending on a cap.
    /// The observation remains recorded after a later pass supplies an exact return.
    pub(super) fn was_capped(&self, key: &InstanceKey) -> bool {
        self.data.capped.contains(key)
    }

    /// Eligible unresolved dependencies of `demanded`, deepest first. Empty
    /// when any observed dependency is ineligible. Discovery order breaks ties.
    pub(super) fn completion_order(&self, demanded: &InstanceKey) -> Vec<InstanceKey> {
        fn visit(
            graph: &CompletionGraph,
            key: &InstanceKey,
            visiting: &mut HashSet<InstanceKey>,
            seen: &mut HashSet<InstanceKey>,
            order: &mut Vec<InstanceKey>,
        ) -> Option<()> {
            if seen.contains(key) {
                return Some(());
            }
            if !visiting.insert(key.clone())
                || graph.identity_eligibility(key) != Eligibility::Closed
            {
                return None;
            }
            for callee in graph.data.edges.get(key).into_iter().flatten() {
                visit(graph, callee, visiting, seen, order)?;
            }
            visiting.remove(key);
            seen.insert(key.clone());
            if let InstanceCallable::Function(symbol) = &key.callable
                && !graph.data.completed.contains_key(symbol)
            {
                order.push(key.clone());
            }
            Some(())
        }
        let mut order = Vec::new();
        if visit(
            self,
            demanded,
            &mut HashSet::default(),
            &mut HashSet::default(),
            &mut order,
        )
        .is_none()
        {
            return Vec::new();
        }
        order.retain(|key| key != demanded);
        order
    }

    fn identity_eligibility(&self, key: &InstanceKey) -> Eligibility {
        let InstanceCallable::Function(symbol) = &key.callable else {
            return Eligibility::Ineligible(IneligibleReason::SharedSymbolPass);
        };
        if self.data.frames.get(symbol) != Some(&key.args) {
            return Eligibility::Ineligible(IneligibleReason::SharedSymbolPass);
        }
        match self.data.eligibility.get(symbol) {
            Some(Ok(_)) if key.numeric_layout.is_none() => Eligibility::Closed,
            Some(Err(reason)) => Eligibility::Ineligible(*reason),
            _ => Eligibility::Ineligible(IneligibleReason::NumericNegotiation),
        }
    }

    /// Record the frame that consumed a function symbol's dedicated completion pass.
    /// Completed symbols are omitted from future orders, but their edges remain traversable.
    pub(super) fn completed(&mut self, key: InstanceKey) {
        if let InstanceCallable::Function(symbol) = &key.callable {
            Rc::make_mut(&mut self.data)
                .completed
                .insert(symbol.clone(), key);
        }
    }

    /// Debug-check that a later real demand names the completed symbol's exact frame.
    /// Symbols without a completion pass impose no additional demand constraint.
    pub(super) fn assert_demand(&self, program: &Program, symbol: &str, args: &[Type]) {
        if let Some(completed) = self.data.completed.get(symbol) {
            debug_assert_eq!(
                Some(completed.clone()),
                InstanceKey::function(program, symbol, args)
            );
        }
    }
}

impl Checker<'_> {
    /// Certify effects without elaborating, reading background observations, or
    /// discovering concrete dependencies. Only observed edges can be scheduled.
    pub(super) fn completion_eligibility(&mut self, key: &InstanceKey) -> Eligibility {
        let InstanceCallable::Function(symbol) = &key.callable else {
            return Eligibility::Ineligible(IneligibleReason::SharedSymbolPass);
        };
        let result = self.certify_completion(symbol, &mut HashSet::default());
        match result {
            Ok(cost)
                if self
                    .elaborations
                    .saturating_add(cost.saturating_mul(cost) / 2)
                    < super::instantiate::ELABORATION_BUDGET =>
            {
                self.completion.identity_eligibility(key)
            }
            Ok(_) => Eligibility::Ineligible(IneligibleReason::BudgetBound),
            Err(reason) => Eligibility::Ineligible(reason),
        }
    }

    fn certify_completion(
        &mut self,
        symbol: &str,
        visiting: &mut HashSet<String>,
    ) -> Result<u64, IneligibleReason> {
        if let Some(result) = self.completion.data.eligibility.get(symbol) {
            return *result;
        }
        // Even a linear path this long exceeds the conservative expansion
        // bound. Reject it before recursion, not only while unwinding costs.
        let depth = visiting.len() as u64 + 1;
        if depth.saturating_mul(depth).saturating_mul(2) >= super::instantiate::ELABORATION_BUDGET {
            return Err(IneligibleReason::BudgetBound);
        }
        if !visiting.insert(symbol.to_owned()) {
            return Err(IneligibleReason::Recursive);
        }
        let result = (|| {
            let f = self
                .program
                .functions
                .get(symbol)
                .ok_or(IneligibleReason::UncertifiedBody)?;
            if self.keyed_tainted.contains(symbol) {
                return Err(IneligibleReason::KeyedCall);
            }
            if f.signature.params.iter().any(|p| {
                p.resolved_ty
                    .as_ref()
                    .is_none_or(|t| !brass_hir::is_fully_known(t))
            }) {
                return Err(IneligibleReason::SharedSymbolPass);
            }
            let args: Vec<_> = f
                .signature
                .params
                .iter()
                .map(|p| p.resolved_ty.clone().unwrap())
                .collect();
            // A nominal annotation can accept a different structural instance;
            // only scalar signatures prove one frame for every future demand.
            if args
                .iter()
                .any(|ty| !matches!(ty, Type::Int(_) | Type::Float(_) | Type::Bool | Type::Str))
            {
                return Err(IneligibleReason::SharedSymbolPass);
            }
            if args.iter().any(super::driver::contains_structural_record) {
                return Err(IneligibleReason::StructuralArgument);
            }
            let frame = InstanceKey::function(self.program, symbol, &args)
                .ok_or(IneligibleReason::OpenArguments)?;
            Rc::make_mut(&mut self.completion.data)
                .frames
                .insert(symbol.to_owned(), frame.args);
            if !self.numeric_eligibility().transitive(f.decl.body.span) {
                return Err(IneligibleReason::NumericNegotiation);
            }
            let [Stmt::Return(Some(expr), _)] = f.decl.body.stmts.as_slice() else {
                return Err(
                    if f.decl
                        .body
                        .stmts
                        .iter()
                        .any(|s| matches!(s, Stmt::Assign { .. }))
                    {
                        IneligibleReason::GlobalWrite
                    } else {
                        IneligibleReason::UncertifiedBody
                    },
                );
            };
            let mut calls = Vec::new();
            certify_expression(self.program, f, expr, &mut calls)?;
            // A generous upper bound includes repeated full/light walks and
            // dedicated roots for every transitive body, without relying on memo hits.
            let mut cost = 2_u64;
            for callee in calls {
                cost = cost.saturating_add(self.certify_completion(&callee, visiting)?);
            }
            if cost.saturating_mul(cost) / 2 >= super::instantiate::ELABORATION_BUDGET {
                return Err(IneligibleReason::BudgetBound);
            }
            Ok(cost)
        })();
        visiting.remove(symbol);
        Rc::make_mut(&mut self.completion.data)
            .eligibility
            .insert(symbol.to_owned(), result);
        result
    }
}

fn certify_expression(
    program: &Program,
    f: &FunInfo,
    expr: &Expr,
    calls: &mut Vec<String>,
) -> Result<(), IneligibleReason> {
    match expr {
        Expr::Int(_, _) | Expr::Float(_, _) | Expr::Bool(_, _) => Ok(()),
        Expr::Ident(name, _) if f.signature.params.iter().any(|p| p.name == *name) => Ok(()),
        Expr::Binary(_, left, right, _) => {
            certify_expression(program, f, left, calls)?;
            certify_expression(program, f, right, calls)
        }
        Expr::Call(callee, args, _) => {
            let Expr::Ident(name, _) = &**callee else {
                return Err(IneligibleReason::UncertifiedBody);
            };
            if f.signature.params.iter().any(|p| p.name == *name) {
                return Err(IneligibleReason::SharedSymbolPass);
            }
            let callee = program
                .resolve_function(&f.module, name)
                .ok_or(IneligibleReason::UncertifiedBody)?;
            calls.push(callee.symbol.clone());
            for arg in args {
                certify_expression(program, f, &arg.expr, calls)?;
            }
            Ok(())
        }
        _ => Err(IneligibleReason::UncertifiedBody),
    }
}

#[cfg(test)]
mod tests;
