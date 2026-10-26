//! Forwarding a parameter into a call through a function VALUE.
//!
//! `fun call(f, b) { f(b) }` mutates the value `b` names when the function
//! passed as `f` takes that argument by `ref(mut(..))`: the parameter-passing
//! rule then makes `b` a private deep copy at `call`'s entry, exactly as for a
//! named callee with a `ref(mut)` parameter. A function value's passing modes
//! are known where its type is written down -- the callable's annotation of
//! the parameter (`f: (ref(mut(Box))) -> void`), or the closure literal a
//! local is bound to. An unannotated function-valued parameter takes its
//! modes from each call site, while the body (and so the entry copy) is
//! compiled once for every passing mode: it is assumed to write through at
//! every position, which keeps a `ref(mut)` callback from reaching the
//! caller's value; for any other callback the copy is unobservable.

use fxhash::FxHashMap as HashMap;

use brass_parser::ast::{Arg, Block, Expr, Param, Pattern, TypeExpr};

use super::{PlaceSink, Roots, root_set, scan_block, tracked_root};
use crate::ParamInfo;

/// A callable parameter as the mutation analysis reads it: its name and its
/// annotation, if any. Implemented by the parsed [`Param`] and the collected
/// [`ParamInfo`], so a body can be analyzed from either.
pub trait ParamDecl {
    /// The parameter's name.
    fn name(&self) -> &str;
    /// The parameter's written annotation; `None` when unannotated.
    fn annotation(&self) -> Option<&TypeExpr>;
}

impl ParamDecl for Param {
    fn name(&self) -> &str {
        &self.name
    }

    fn annotation(&self) -> Option<&TypeExpr> {
        self.ty.as_ref()
    }
}

impl ParamDecl for ParamInfo {
    fn name(&self) -> &str {
        &self.name
    }

    fn annotation(&self) -> Option<&TypeExpr> {
        self.ty.as_ref()
    }
}

/// Which argument positions of a function value take their argument by
/// `ref(mut(..))`, as far as its written type tells.
#[derive(Clone)]
enum WriteThrough {
    /// Unknown modes (an unannotated function-valued parameter, or a local
    /// bound to anything but a closure literal): every position.
    Every,
    /// The flag of each position of a written function type or closure.
    Positions(Vec<bool>),
}

impl WriteThrough {
    fn at(&self, position: usize) -> bool {
        match self {
            WriteThrough::Every => true,
            WriteThrough::Positions(flags) => flags.get(position).copied().unwrap_or(false),
        }
    }
}

/// Whether a parameter annotation is `ref(mut(..))`.
fn annotation_writes_through(annotation: Option<&TypeExpr>) -> bool {
    matches!(annotation, Some(TypeExpr::Ref(inner, _)) if matches!(**inner, TypeExpr::Mut(..)))
}

/// Whether `body` (of a callable with `params`) passes a place rooted at `root`
/// to a function value at a position that value may take by `ref(mut(..))`
/// (see the module docs).
pub(super) fn forwards_to_function_value<P: ParamDecl>(
    params: &[P],
    body: &Block,
    root: &str,
) -> bool {
    let mut sink = FunctionValueSink {
        params: params
            .iter()
            .map(|p| {
                let modes = match p.annotation() {
                    None => Some(WriteThrough::Every),
                    Some(TypeExpr::Fun(positions, _, _)) => Some(WriteThrough::Positions(
                        positions
                            .iter()
                            .map(|t| annotation_writes_through(Some(t)))
                            .collect(),
                    )),
                    Some(_) => None,
                };
                (p.name().to_string(), modes)
            })
            .collect(),
        locals: HashMap::default(),
    };
    scan_block(body, &root_set(root, false), &mut sink)
}

/// Sink that reports a tracked place passed to a function value at a
/// position it may take by `ref(mut(..))`.
struct FunctionValueSink {
    /// The callable's parameters, with the write-through positions of the
    /// function-valued ones (`None` for a parameter that cannot be called).
    params: HashMap<String, Option<WriteThrough>>,
    /// Locals bound so far, with the write-through positions of the closure
    /// literal each was bound to (`Every` for any other value). A local shadows
    /// a same-named parameter.
    locals: HashMap<String, WriteThrough>,
}

impl PlaceSink for FunctionValueSink {
    fn write(&mut self) -> bool {
        // A direct write is `mutates_root`'s concern.
        false
    }

    fn bind(&mut self, pattern: &Pattern, value: Option<&Expr>) {
        let modes = match value {
            Some(Expr::Closure(params, _, _)) => WriteThrough::Positions(
                params
                    .iter()
                    .map(|p| annotation_writes_through(p.ty.as_ref()))
                    .collect(),
            ),
            _ => WriteThrough::Every,
        };
        for name in pattern.bound_names() {
            self.locals.insert(name.to_string(), modes.clone());
        }
    }

    fn call(&mut self, callee: &Expr, args: &[Arg], roots: &Roots) -> bool {
        let Expr::Ident(name, _) = callee else {
            return false;
        };
        let modes = match self.locals.get(name) {
            Some(modes) => modes,
            None => match self.params.get(name) {
                Some(Some(modes)) => modes,
                _ => return false,
            },
        };
        args.iter()
            .enumerate()
            .any(|(i, arg)| modes.at(i) && tracked_root(&arg.expr, roots).is_some())
    }
}
