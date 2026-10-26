//! Literal applications independent of a speculative lexical environment.

use super::super::*;
use brass_typesys::NumericLiteral;

/// A statement-indexed inventory of calls and uses. Unclassified uses and
/// control flow force the ordinary light walk instead of guessing scope.
#[derive(Default)]
pub(super) struct ApplicationIndex<'s> {
    calls: HashMap<&'s str, Vec<(usize, &'s [Arg])>>,
    other_uses: HashMap<String, Vec<usize>>,
    declarations: HashMap<&'s str, Vec<usize>>,
    barriers: Vec<usize>,
}

impl<'s> ApplicationIndex<'s> {
    /// Index the whole sequence once. A literal argument has no dependencies
    /// on other local declarations or on an assigned closure's signature.
    pub(super) fn new(stmts: &'s [Stmt]) -> Self {
        let mut result = Self::default();
        for (position, stmt) in stmts.iter().enumerate() {
            let mut recognized = HashSet::default();
            let strict = match stmt {
                Stmt::Let {
                    pat: Pattern::Binding(name, _, _),
                    value,
                    ..
                } => {
                    result.declarations.entry(name).or_default().push(position);
                    value.as_ref().is_none_or(|value| {
                        matches!(value, Expr::Closure(..))
                            || result.strict_expr(value, position, &mut recognized)
                    })
                }
                Stmt::Assign {
                    target: Expr::Ident(_, span),
                    op: AssignOp::Eq,
                    value,
                    ..
                } => {
                    recognized.insert(*span);
                    matches!(value, Expr::Closure(..))
                        || result.strict_expr(value, position, &mut recognized)
                }
                Stmt::Expr(expr) => result.strict_expr(expr, position, &mut recognized),
                _ => false,
            };
            if !strict {
                result.barriers.push(position);
            }
            // Visit nested scopes too: a capture, alias or shadowed call is
            // intentionally not a recognized direct use of this binding.
            let mut reads = OtherReads {
                recognized: &recognized,
                names: Vec::new(),
            };
            crate::walk::walk_stmt(stmt, &mut reads);
            for name in reads.names {
                result.other_uses.entry(name).or_default().push(position);
            }
        }
        result
    }

    /// Calls after one declaration, only when every use can be accounted for
    /// without rebuilding the environment. An alias or nested scope declines.
    pub(super) fn literal_calls(&self, name: &str, after: usize) -> Option<Vec<&'s [Arg]>> {
        // `error` is a language construct handled before local lookup by
        // infer_call_light, so it cannot denote the probe marker.
        if name == "error"
            || self
                .barriers
                .last()
                .is_some_and(|position| *position > after)
            || self
                .other_uses
                .get(name)
                .and_then(|uses| uses.last())
                .is_some_and(|position| *position > after)
            || self
                .declarations
                .get(name)
                .and_then(|uses| uses.last())
                .is_some_and(|position| *position > after)
        {
            return None;
        }
        Some(
            self.calls
                .get(name)
                .into_iter()
                .flatten()
                .filter(|(position, _)| *position > after)
                .map(|(_, args)| *args)
                .collect(),
        )
    }

    fn strict_expr(
        &mut self,
        expr: &'s Expr,
        position: usize,
        recognized: &mut HashSet<Span>,
    ) -> bool {
        match expr {
            Expr::Int(..) | Expr::Float(..) | Expr::Bool(..) | Expr::Null(..) | Expr::Ident(..) => {
                true
            }
            Expr::Unary(_, inner, _) => self.strict_expr(inner, position, recognized),
            Expr::Binary(_, left, right, _) => {
                let left = self.strict_expr(left, position, recognized);
                self.strict_expr(right, position, recognized) && left
            }
            Expr::Call(callee, args, _) => {
                let Expr::Ident(name, span) = &**callee else {
                    return false;
                };
                if args
                    .iter()
                    .all(|arg| NumericLiteral::of_expr(&arg.expr).is_some())
                {
                    self.calls.entry(name).or_default().push((position, args));
                    recognized.insert(*span);
                }
                // The light call checker visits every argument of a direct
                // name call, including nested calls, in argument order.
                let mut strict = true;
                for arg in args {
                    strict &= self.strict_expr(&arg.expr, position, recognized);
                }
                strict
            }
            _ => false,
        }
    }
}

struct OtherReads<'a> {
    recognized: &'a HashSet<Span>,
    names: Vec<String>,
}

impl crate::walk::ExprVisitor for OtherReads<'_> {
    fn visit(&mut self, expr: &Expr) {
        if let Expr::Ident(name, span) = expr
            && !self.recognized.contains(span)
        {
            self.names.push(name.clone());
        }
    }
}
