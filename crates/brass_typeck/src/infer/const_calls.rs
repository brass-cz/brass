//! Const mutation through method calls. Const checking (`crate::constck`)
//! decides lexically which places are const and records the method calls whose
//! receiver or arguments are const-rooted; whether such a call mutates the
//! const depends on the method it dispatches to, so the verdict is made here,
//! on the receiver type this elaboration resolved -- the same resolution the
//! call itself uses. A method is judged by what it does (the program's
//! write-through facts), never by its name or by how the const was
//! initialized.

use super::*;

/// What a method call's receiver dispatches on, for the mutation verdict.
enum MethodOwner {
    /// A growable array: its built-in mutators change it in place.
    Array,
    /// A declared record or sum, by storage symbol.
    Nominal(String),
    /// Not resolved yet (an open generic receiver): each instantiation's
    /// elaboration decides.
    Unknown,
    /// Anything else (scalars, strings, tuples, closures): its methods never
    /// write through the receiver.
    Other,
}

/// The built-in growable-array methods that change their receiver in place.
fn is_array_mutator(method: &str) -> bool {
    matches!(method, "push" | "insert" | "remove" | "pop")
}

impl Checker<'_> {
    /// Reject the method call at `span` when it mutates a const value: its
    /// receiver is rooted in a const binding and `method` -- resolved on
    /// `receiver`, the receiver's type in this elaboration -- writes through
    /// its receiver, or a const-rooted argument lands in a position the method
    /// writes through. An argument whose receiver is not resolved yet is held
    /// against every same-named method (conservatively); a receiver is never
    /// judged before it resolves.
    pub(super) fn check_const_method_call(&mut self, span: Span, method: &str, receiver: &Type) {
        let calls = Rc::clone(&self.const_calls);
        let root = calls.receivers.get(&span);
        let args = calls.args.get(&span);
        if root.is_none() && args.is_none() {
            return;
        }
        let owner = self.method_owner(receiver, method);
        if let Some(root) = root {
            let mutates = match &owner {
                MethodOwner::Array => is_array_mutator(method),
                MethodOwner::Nominal(symbol) => {
                    calls.mutation.method_writes_through_self(symbol, method)
                }
                MethodOwner::Unknown | MethodOwner::Other => false,
            };
            if mutates {
                self.errors.push(TypeError {
                    message: format!(
                        "cannot call mutating method `{method}` on const value `{root}`"
                    ),
                    span,
                });
            }
        }
        let Some(args) = args else {
            return;
        };
        let write_through = match &owner {
            MethodOwner::Nominal(symbol) => {
                calls.mutation.method_write_through_args(symbol, method)
            }
            MethodOwner::Unknown => calls.mutation.method_write_through_args_by_name(method),
            MethodOwner::Array | MethodOwner::Other => return,
        };
        for (index, root, arg_span) in args {
            if write_through.contains(index) {
                self.errors.push(TypeError {
                    message: format!(
                        "cannot pass const value `{root}` to method `{method}`, which requires a mutable parameter"
                    ),
                    span: *arg_span,
                });
            }
        }
    }

    /// Reject a read-only (const-rooted) argument of the call at `span`
    /// through a function value of parameter types `params` when its
    /// parameter takes it by `ref(mut(T))`: the callee would write through to
    /// a value the caller may only read. Const checking records these calls
    /// (it cannot see a function value's parameter modes); the verdict follows
    /// the callee's type in this elaboration, so a generic body is judged per
    /// instantiation, by the function value actually passed.
    pub(super) fn check_read_only_value_args(&mut self, span: Span, params: &[Type]) {
        let calls = Rc::clone(&self.const_calls);
        let Some(args) = calls.value_args.get(&span) else {
            return;
        };
        for (index, root, arg_span) in args {
            let Some(param) = params.get(*index).map(|p| self.resolve(p)) else {
                continue;
            };
            let Type::Ref(referent) = &param else {
                continue;
            };
            if !matches!(self.resolve(referent), Type::Mut(_)) {
                continue;
            }
            self.errors.push(TypeError {
                message: format!(
                    "cannot pass the read-only `{root}` where a write-through `{}` is required",
                    param.display()
                ),
                span: *arg_span,
            });
        }
    }

    /// What a call of `method` on a value of type `receiver` dispatches on. A
    /// narrowed nullable receiver dispatches on its payload, and an anonymous
    /// record on the single in-scope record type declaring the method that it
    /// satisfies (the structural dispatch rule).
    fn method_owner(&mut self, receiver: &Type, method: &str) -> MethodOwner {
        let resolved = self.resolve(receiver);
        let ty = match peel_modes(&resolved) {
            Type::Nullable(inner) => peel_modes(inner),
            other => other,
        };
        match ty {
            Type::Slice(_) | Type::Array(..) => MethodOwner::Array,
            Type::Record(n) if n.id == brass_hir::STRUCTURAL_RECORD_ID => {
                let n = n.clone();
                match self.structural_method_candidates(&n, method).as_slice() {
                    [(_, symbol)] => MethodOwner::Nominal(symbol.clone()),
                    _ => MethodOwner::Other,
                }
            }
            Type::Record(n) | Type::Sum(n) => match self.program.type_by_id(n.id) {
                Some(info) => MethodOwner::Nominal(info.symbol.clone()),
                None => MethodOwner::Other,
            },
            Type::Unknown(_) => MethodOwner::Unknown,
            _ => MethodOwner::Other,
        }
    }
}
