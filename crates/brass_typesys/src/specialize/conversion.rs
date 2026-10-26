//! `infer.from(x)` inside a reflective decoder: the conversion of `x` to the
//! specialization's key.
//!
//! When the template names the source type -- `x` is bound by a variant
//! pattern of the top `match self` -- the conversion is resolved here, once
//! ([`crate::convert::infer_from`]). Any other source (a local, a field, a
//! literal, a call) only gets its type when the generated body is checked, so
//! the conversion becomes a compile-time type-test dispatch over the source
//! types the key converts from ([`crate::convert::infer_from_dispatch`]):
//!
//! ```text
//! {
//!     const <source> = x
//!     if <source>: int64 { <source> }
//!     else if <source>: int32 { int64.from(<source>) }
//!     ...
//!     else { error("cannot decode this value as `int64`", <location>) }
//! }
//! ```
//!
//! Each instance keeps exactly the arm its source type selects (type tests
//! are decided statically), so both forms resolve a given source type alike.

use brass_hir::{SPAN_SHIFT_UNIT, Span, Type};
use brass_parser::ast::*;

use super::{Bindings, Specializer, type_to_expr};
use crate::convert::{InferFrom, infer_from, infer_from_dispatch};

/// The binding a dispatch holds the converted value in. Source text cannot
/// spell it, so it never shadows a template binding.
const SOURCE: &str = "\u{0}from";

/// The node a synthesized span belongs to within one dispatch lane. Every
/// node of a lane takes a distinct sub-extent of the `infer.from(..)` call it
/// replaces, so the span-keyed sidecars the checker and lowering keep never
/// confuse two of them.
#[derive(Clone, Copy)]
enum Role {
    /// The lane's `if` (lane 0: the dispatch block).
    Whole,
    /// The type test (lane 0: the `const` statement).
    Test,
    /// The tested type (lane 0: the final `else` block).
    Tested,
    /// The tested binding read (lane 0: the `const` pattern).
    Subject,
    /// The arm's `then` block.
    Then,
    /// The conversion call (or the decode error).
    Value,
    /// The conversion's `Q.from` callee.
    Callee,
    /// The conversion's qualifier `Q`.
    Qualifier,
    /// The converted binding read.
    Argument,
    /// The `!` a nullable key puts on a fallible conversion.
    Propagate,
}

impl Specializer<'_> {
    /// Resolve `infer.from(arg)` at the current key.
    pub(super) fn infer_from(&mut self, arg: &Expr, binds: &Bindings, span: Span) -> Expr {
        match self.arg_type(arg, binds) {
            Some(source) => {
                let resolution = infer_from(self.program, &source, self.key);
                self.conversion(resolution, arg.clone(), |_| span)
            }
            None => self.infer_from_dispatch(arg, binds, span),
        }
    }

    /// The source type of `arg` when the template names it: a variable bound
    /// by a variant pattern of the top `match self`.
    fn arg_type(&self, arg: &Expr, binds: &Bindings) -> Option<Type> {
        match arg {
            Expr::Ident(n, _) => binds.get(n).cloned(),
            _ => None,
        }
    }

    /// The expression that applies `resolution` to `source`; `at` gives each
    /// synthesized node its span.
    fn conversion(&self, resolution: InferFrom, source: Expr, at: impl Fn(Role) -> Span) -> Expr {
        match resolution {
            // Identity: the argument already is the target value.
            InferFrom::Identity => source,
            // A named conversion `Q.from(arg)`. At a nullable key a fallible
            // conversion's Result cannot flow into the `T?` result as is: its
            // error propagates and its value promotes.
            InferFrom::Static {
                qualifier,
                fallible,
            } => {
                let call = Expr::Call(
                    Box::new(Expr::Field(
                        Box::new(Expr::Ident(qualifier, at(Role::Qualifier))),
                        "from".into(),
                        at(Role::Callee),
                    )),
                    vec![Arg { expr: source }],
                    at(Role::Value),
                );
                if fallible && matches!(self.key, Type::Nullable(_)) {
                    Expr::ErrorProp(Box::new(call), at(Role::Propagate))
                } else {
                    call
                }
            }
            // No conversion: this source cannot produce the key -- a runtime
            // decode error (e.g. a JSON string decoded as an int).
            InferFrom::Absent(_) => self.error_call(at(Role::Value)),
        }
    }

    /// The type-test dispatch of `infer.from(arg)` over every source type the
    /// key converts from (see the module docs). `call` is the replaced call's
    /// span; the arms take their spans from it, one shift lane per arm.
    fn infer_from_dispatch(&mut self, arg: &Expr, binds: &Bindings, call: Span) -> Expr {
        let initializer = self.expr(arg, binds);
        let dispatch = infer_from_dispatch(self.program, self.key);
        let source = |span| Expr::Ident(SOURCE.into(), span);
        let entry = |role| self.lane_span(call, 0, role);
        let otherwise = self.conversion(dispatch.otherwise, source(entry(Role::Argument)), entry);
        let mut chain = Expr::Block(
            Block {
                stmts: vec![Stmt::Expr(otherwise)],
                span: entry(Role::Tested),
            },
            entry(Role::Tested),
        );
        for (index, (tested, resolution)) in dispatch.arms.into_iter().enumerate().rev() {
            let at = |role| self.lane_span(call, index + 1, role);
            let value = self.conversion(resolution, source(at(Role::Argument)), at);
            let test = Expr::TypeTest(
                Box::new(source(at(Role::Subject))),
                type_to_expr(&tested, at(Role::Tested)),
                false,
                at(Role::Test),
            );
            let then = Block {
                stmts: vec![Stmt::Expr(value)],
                span: at(Role::Then),
            };
            chain = Expr::If(Box::new(test), then, Some(Box::new(chain)), at(Role::Whole));
        }
        let bind = Stmt::Let {
            pat: Pattern::Binding(SOURCE.into(), None, entry(Role::Subject)),
            ty: None,
            value: Some(initializer),
            is_const: true,
            span: entry(Role::Test),
        };
        Expr::Block(
            Block {
                stmts: vec![bind, Stmt::Expr(chain)],
                span: entry(Role::Whole),
            },
            entry(Role::Whole),
        )
    }

    /// The span of a synthesized dispatch node: a sub-extent of the replaced
    /// call's span chosen by `role`, shifted to `lane`.
    ///
    /// Lane `n` sits `n * dispatch_stride` shift units above the call. The
    /// stride exceeds the number of copies the record walk unrolls, so a
    /// dispatch inside one walk copy never lands on another copy's lanes.
    fn lane_span(&self, call: Span, lane: usize, role: Role) -> Span {
        let mut span = call.ungrouped();
        // `infer.from(x)` spans at least 13 bytes, more than there are roles.
        debug_assert!(span.hi - span.lo > Role::Propagate as usize);
        span.hi -= role as usize;
        match lane {
            0 => span,
            lane => span.shifted(lane * self.dispatch_stride * SPAN_SHIFT_UNIT),
        }
    }
}
