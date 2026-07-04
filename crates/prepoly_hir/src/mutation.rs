//! Parameter-mutation analysis over the collected program.
//!
//! A parameter (or a method's `self`) is *mutated* when the body writes through
//! the reference it names -- a field/element assignment (`p.f = ` / `p[i] = `),
//! a built-in growable-array mutator (`p.push(..)`), or by forwarding the
//! parameter into a callee position already known to mutate it. This is the
//! single signal that decides how an unannotated parameter is passed: a
//! non-mutated parameter is a shared borrow (`ref`), a mutated one is a private
//! deep copy (`mut`), and a mutated `self` is a mutable reference (`ref(mut)`).
//!
//! The analysis is a pure function of the HIR program (bodies are still parser
//! AST) and is shared by const-checking, the back ends' copy machinery, and the
//! language server's type display so all three agree on which arguments are
//! borrowed and which are copied.

use std::collections::{HashMap, HashSet};

use prepoly_parser::ast::{Arg, Block, Expr, Pattern, Stmt, StrSeg, TypeExpr};

use crate::{ParamInfo, Program, Type, TypeInfo, TypeKind};

/// A call a function's body makes through one of its own function-valued
/// parameters (`fun apply(f, v) { f(v) }`), recorded so a call site can check
/// the *actually passed* function's write-through positions against the other
/// arguments -- a const laundered through a higher-order call is still caught.
pub struct ParamCall {
    /// Index of the function's own parameter being called as a function.
    pub fn_param: usize,
    /// For each argument of that inner call, the index of the function's own
    /// parameter the argument is rooted at (`None` for any other expression).
    pub args: Vec<Option<usize>>,
}

/// Precomputed write-through facts for every callable in a program: which
/// parameter positions a `const` value must not be passed into because the
/// callee could mutate it *through the reference* and so change the caller's
/// value. Only a `ref(mut(T))` parameter writes through; an unannotated mutated
/// parameter is a private deep copy (`mut`), so mutating it is const-safe and it
/// is not recorded here.
pub struct MutationInfo {
    /// Free-function storage symbol -> indices of parameters that write through
    /// to the caller: a `ref(mut(T))` parameter, or one that forwards a place
    /// rooted at it into another write-through position. A least fixpoint over
    /// the call graph.
    functions: HashMap<String, HashSet<usize>>,
    /// `(type name, method name)` -> call-site argument indices (the receiver is
    /// excluded, so index 0 is the first non-`self` parameter) that write
    /// through, by the same `ref(mut(T))`-or-forwarding rule as `functions`.
    method_args: HashMap<(String, String), HashSet<usize>>,
    /// `(type name, method name)` pairs whose body mutates `self` *through a
    /// write-through `self`* (an unannotated `self`, inferred `ref(mut(Self))`,
    /// or an explicit `ref(mut(Self))`) -- directly or by forwarding `self` into
    /// another write-through position. A method taking `self: Self`/`mut(Self)`
    /// mutates only its own copy, so it is excluded.
    self_write_through_methods: HashSet<(String, String)>,
    /// Free-function symbol -> the calls its body makes through fn-valued
    /// parameters, for call-site higher-order const checking.
    param_calls: HashMap<String, Vec<ParamCall>>,
}

impl MutationInfo {
    /// Analyze every free function and method in `program`.
    pub fn analyze(program: &Program) -> Self {
        write_through_fixpoint(program)
    }

    /// The indices of free function `symbol`'s write-through parameters, if any.
    /// Passing a `const` value into one of these is rejected.
    pub fn write_through_params(&self, symbol: &str) -> Option<&HashSet<usize>> {
        self.functions.get(symbol)
    }

    /// Whether method `type_name::method` mutates the caller's receiver through a
    /// write-through `self`, so calling it on a `const` receiver is rejected.
    pub fn method_writes_through_self(&self, type_name: &str, method: &str) -> bool {
        self.self_write_through_methods
            .contains(&(type_name.to_string(), method.to_string()))
    }

    /// The union of write-through call-site argument indices of every method
    /// named `method`, across all types. Used when the receiver's type is not
    /// statically known at a call site: passing a const into any of these
    /// positions is (conservatively) rejected.
    pub fn method_write_through_args_by_name(&self, method: &str) -> HashSet<usize> {
        self.method_args
            .iter()
            .filter(|((_, m), _)| m == method)
            .flat_map(|(_, indices)| indices.iter().copied())
            .collect()
    }

    /// Whether any type's method named `method` writes through `self`. Used when
    /// the receiver's type is not statically known (an unannotated parameter used
    /// as a receiver).
    fn any_method_writes_through_self(&self, method: &str) -> bool {
        self.self_write_through_methods
            .iter()
            .any(|(_, m)| m == method)
    }

    /// The calls free function `symbol` makes through its fn-valued parameters.
    pub fn param_calls(&self, symbol: &str) -> Option<&[ParamCall]> {
        self.param_calls.get(symbol).map(Vec::as_slice)
    }
}

/// Whether a `self` parameter writes through to the caller's receiver: an
/// unannotated `self` (a reference by default) or an explicit `ref(mut(Self))`.
/// An immutable `ref(Self)` cannot mutate at all, and `self: Self`/`mut(Self)`
/// mutates only an owned copy -- neither reaches the caller.
fn self_writes_through(self_param: &ParamInfo) -> bool {
    match &self_param.ty {
        None => true,
        Some(TypeExpr::Ref(inner, _)) => matches!(**inner, TypeExpr::Mut(..)),
        Some(_) => false,
    }
}

/// Every method of every type with its owning type name, whether its first
/// parameter is `self`, and the module its body resolves names in.
fn all_methods(
    program: &Program,
) -> impl Iterator<Item = (&TypeInfo, &String, &crate::MethodInfo)> {
    program.types.values().flat_map(|info| {
        let methods: Vec<(&String, &crate::MethodInfo)> = match &info.kind {
            TypeKind::Record { methods, .. } => methods.iter().collect(),
            TypeKind::Sum { variants } => variants.iter().flat_map(|v| v.methods.iter()).collect(),
        };
        methods.into_iter().map(move |(name, m)| (info, name, m))
    })
}

/// The least-fixpoint write-through analysis over the whole call graph:
/// free-function parameters, method (non-`self`) parameters, and method `self`
/// positions. A position writes through when it is annotated `ref(mut(T))`
/// (for `self`: mutated directly through a reference `self`), or the body
/// forwards a place rooted at it into another position already known to write
/// through -- a free-function call, a method call's argument, or the receiver
/// of a self-mutating method. A `const` argument must not be passed into any
/// of these.
///
/// Only `ref(mut(T))` writes through: a directly-mutated unannotated (or `mut`,
/// or bare-aggregate) parameter is a private deep copy, so mutating it never
/// reaches the caller and it is *not* recorded -- passing a `const` into it is
/// safe. Method receivers, in contrast, are references, so a method call on a
/// parameter routes the caller's value into the method's `self`.
///
/// A method call site's receiver type is not statically known here (bodies are
/// unchecked AST), so method facts are matched *by method name* across all
/// types -- conservative: a const may be rejected because a same-named method of
/// an unrelated type mutates. Iteration repeats until no set grows; the sets
/// only gain elements (monotone) and are bounded by the parameter counts, so
/// it terminates.
fn write_through_fixpoint(program: &Program) -> MutationInfo {
    let mut info = MutationInfo {
        functions: HashMap::new(),
        method_args: HashMap::new(),
        self_write_through_methods: HashSet::new(),
        param_calls: collect_param_calls(program),
    };
    // Seed free functions and method args with the explicit `ref(mut(T))`
    // positions, and `self` with the direct through-reference mutations.
    for f in program.functions.values() {
        let indices: HashSet<usize> = f
            .signature
            .params
            .iter()
            .enumerate()
            .filter(|(_, p)| param_is_mut_ref(p))
            .map(|(i, _)| i)
            .collect();
        if !indices.is_empty() {
            info.functions.insert(f.symbol.clone(), indices);
        }
    }
    for (tinfo, mname, m) in all_methods(program) {
        let has_self = method_has_self(m);
        let indices: HashSet<usize> = m
            .signature
            .params
            .iter()
            .skip(usize::from(has_self))
            .enumerate()
            .filter(|(_, p)| param_is_mut_ref(p))
            .map(|(i, _)| i)
            .collect();
        if !indices.is_empty() {
            info.method_args
                .insert((tinfo.name.clone(), mname.clone()), indices);
        }
        if has_self
            && m.signature.params.first().is_some_and(self_writes_through)
            && m.decl
                .body
                .as_ref()
                .is_some_and(|body| mutates_root(body, "self"))
        {
            info.self_write_through_methods
                .insert((tinfo.name.clone(), mname.clone()));
        }
    }
    // Propagate through forwarding calls until the fixpoint is reached.
    loop {
        let mut changed = false;
        for f in program.functions.values() {
            for (param_idx, p) in f.signature.params.iter().enumerate() {
                if param_receives_copy(program, &f.module, p, &f.decl.body) {
                    // A deep-copied parameter's mutation never reaches the caller,
                    // so forwarding it does not make this position mutable.
                    continue;
                }
                if info
                    .functions
                    .get(&f.symbol)
                    .is_some_and(|s| s.contains(&param_idx))
                {
                    continue;
                }
                if forwards_to_mutating(program, &f.module, &f.decl.body, &p.name, &info) {
                    info.functions
                        .entry(f.symbol.clone())
                        .or_default()
                        .insert(param_idx);
                    changed = true;
                }
            }
        }
        for (tinfo, mname, m) in all_methods(program) {
            let Some(body) = m.decl.body.as_ref() else {
                continue;
            };
            let key = (tinfo.name.clone(), mname.clone());
            let has_self = method_has_self(m);
            for (arg_idx, p) in m
                .signature
                .params
                .iter()
                .skip(usize::from(has_self))
                .enumerate()
            {
                if param_receives_copy(program, &tinfo.module, p, body) {
                    continue;
                }
                if info
                    .method_args
                    .get(&key)
                    .is_some_and(|s| s.contains(&arg_idx))
                {
                    continue;
                }
                if forwards_to_mutating(program, &tinfo.module, body, &p.name, &info) {
                    info.method_args
                        .entry(key.clone())
                        .or_default()
                        .insert(arg_idx);
                    changed = true;
                }
            }
            // `self` forwarded into a write-through position also mutates the
            // caller's receiver (only a reference `self` can carry that through).
            if has_self
                && m.signature.params.first().is_some_and(self_writes_through)
                && !info.self_write_through_methods.contains(&key)
                && forwards_to_mutating(program, &tinfo.module, body, "self", &info)
            {
                info.self_write_through_methods.insert(key);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    info
}

fn method_has_self(m: &crate::MethodInfo) -> bool {
    m.signature.params.first().is_some_and(|p| p.name == "self")
}

/// Whether `body` passes a place rooted at `root` into a position some callee
/// already requires to be mutable (per the in-progress `info` tables). This is
/// the interprocedural step of [`write_through_fixpoint`]: `fun f(p) { g(p) }`
/// where `g` mutates its parameter makes `p` mutable too, as does using `p` as
/// the receiver of a self-mutating method.
fn forwards_to_mutating(
    program: &Program,
    module: &[String],
    body: &Block,
    root: &str,
    info: &MutationInfo,
) -> bool {
    let mut sink = ForwardSink {
        program,
        module,
        info,
    };
    scan_block(body, &root_set(root, false), &mut sink)
}

/// Sink that reports a call passing a tracked place into a parameter position
/// already known to write through (per the in-progress fixpoint tables).
struct ForwardSink<'a> {
    program: &'a Program,
    module: &'a [String],
    info: &'a MutationInfo,
}

impl PlaceSink for ForwardSink<'_> {
    fn write(&mut self) -> bool {
        // A direct write is not a forwarding escape; direct mutation makes the
        // parameter a private copy and is handled by `mutates_root`.
        false
    }

    fn call(&mut self, callee: &Expr, args: &[Arg], roots: &Roots) -> bool {
        match callee {
            // A free-function call `g(.., arg_i, ..)`: if `g`'s position `i` is
            // mutable and `arg_i` is a place rooted at the tracked name (or a
            // local alias of it), the parameter escapes into a mutating position.
            Expr::Ident(fname, _) => {
                let Some(symbol) = self.program.resolve_fn_symbol(self.module, fname) else {
                    return false;
                };
                if let Some(indices) = self.info.functions.get(&symbol)
                    && args.iter().enumerate().any(|(i, arg)| {
                        indices.contains(&i) && tracked_root(&arg.expr, roots).is_some()
                    })
                {
                    return true;
                }
                // The callee may relay an argument through a fn-valued parameter
                // (`g(mutate, p)` with `fun g(f, v) { f(v) }`): when the function
                // passed at that position is known and writes through, the
                // argument it receives escapes the same way.
                self.info
                    .param_calls(&symbol)
                    .is_some_and(|calls| self.hof_forwards(calls, args, roots))
            }
            // A method call: the receiver's type is unknown here, so both the
            // receiver and the argument positions are checked by method name
            // across all types (conservative).
            Expr::Field(recv, m, _) => {
                if is_builtin_mutating_method(m) {
                    // A builtin array mutator is a direct write (copy semantics),
                    // not a forwarding escape.
                    return false;
                }
                if tracked_root(recv, roots).is_some()
                    && self.info.any_method_writes_through_self(m)
                {
                    return true;
                }
                let indices = self.info.method_write_through_args_by_name(m);
                !indices.is_empty()
                    && args.iter().enumerate().any(|(i, arg)| {
                        indices.contains(&i) && tracked_root(&arg.expr, roots).is_some()
                    })
            }
            _ => false,
        }
    }
}

impl ForwardSink<'_> {
    /// Whether any recorded fn-param call of the callee routes one of *this*
    /// call's tracked arguments into a write-through position of the function
    /// value passed at the same call.
    fn hof_forwards(&self, calls: &[ParamCall], args: &[Arg], roots: &Roots) -> bool {
        calls.iter().any(|pc| {
            let Some(fn_arg) = args.get(pc.fn_param) else {
                return false;
            };
            let Expr::Ident(gname, _) = &fn_arg.expr else {
                return false;
            };
            let Some(gsym) = self.program.resolve_fn_symbol(self.module, gname) else {
                return false;
            };
            let Some(g_indices) = self.info.functions.get(&gsym) else {
                return false;
            };
            g_indices.iter().any(|k| {
                pc.args.get(*k).copied().flatten().is_some_and(|j| {
                    args.get(j)
                        .is_some_and(|a| tracked_root(&a.expr, roots).is_some())
                })
            })
        })
    }
}

/// For each free function, the calls its body makes through its own fn-valued
/// parameters, with each argument mapped back to the function's own parameter
/// it is rooted at. Shadowed parameter names are respected (a `let f = ..`
/// rebinding hides the parameter).
fn collect_param_calls(program: &Program) -> HashMap<String, Vec<ParamCall>> {
    struct Collector<'a> {
        param_names: &'a [String],
        out: Vec<ParamCall>,
    }
    impl PlaceSink for Collector<'_> {
        fn write(&mut self) -> bool {
            false
        }
        fn call(&mut self, callee: &Expr, args: &[Arg], roots: &Roots) -> bool {
            if let Expr::Ident(name, _) = callee
                && roots.contains_key(name)
                && let Some(fn_param) = self.param_names.iter().position(|p| p == name)
            {
                let arg_params = args
                    .iter()
                    .map(|a| {
                        root_ident(&a.expr)
                            .filter(|r| roots.contains_key(*r))
                            .and_then(|r| self.param_names.iter().position(|p| p == r))
                    })
                    .collect();
                self.out.push(ParamCall {
                    fn_param,
                    args: arg_params,
                });
            }
            false
        }
    }
    let mut map = HashMap::new();
    for f in program.functions.values() {
        let param_names: Vec<String> = f.signature.params.iter().map(|p| p.name.clone()).collect();
        // Track every parameter so shadowing is respected uniformly.
        let roots: Roots = param_names.iter().map(|n| (n.clone(), false)).collect();
        let mut collector = Collector {
            param_names: &param_names,
            out: Vec::new(),
        };
        scan_block(&f.decl.body, &roots, &mut collector);
        if !collector.out.is_empty() {
            map.insert(f.symbol.clone(), collector.out);
        }
    }
    map
}

/// Whether a parameter is a mutable reference (`ref(mut(T))`).
pub fn param_is_mut_ref(p: &ParamInfo) -> bool {
    matches!(&p.resolved_ty, Some(Type::Ref(inner)) if matches!(**inner, Type::Mut(_)))
}

/// Whether a parameter annotated with syntactic type `t` receives a private
/// deep copy at callee entry. This is the single copy predicate shared by the
/// back ends' entry-copy machinery and the write-through fixpoint, so the
/// runtime copy decision and the const checker never disagree.
///
/// A `ref(...)`/`ref(mut(..))` parameter borrows. Every non-reference heap
/// aggregate copies: array/slice, tuple, anonymous structure, a named
/// record/sum, `infer` (resolved per call site, may be any heap value -- the
/// deep copy is type-directed, so a primitive instantiation is a no-op), and
/// `T!` (the built-in `Result`, itself a sum). Wrappers that do not change the
/// underlying value's kind (`mut(T)`, `T?`) recurse.
pub fn annotated_type_passes_by_copy(program: &Program, module: &[String], t: &TypeExpr) -> bool {
    match t {
        TypeExpr::Ref(..) => false,
        TypeExpr::Mut(inner, _) | TypeExpr::Nullable(inner, _) => {
            annotated_type_passes_by_copy(program, module, inner)
        }
        TypeExpr::Array(..) | TypeExpr::Tuple(..) | TypeExpr::Anonymous(..) => true,
        // `T!` is the built-in fallible Result, a sum value whatever `T` is.
        TypeExpr::Fallible(..) => true,
        TypeExpr::Named(n, _) => {
            n == "infer"
                || program.resolve_type(module, n).is_some_and(|info| {
                    matches!(info.kind, TypeKind::Record { .. } | TypeKind::Sum { .. })
                })
        }
        TypeExpr::Fun(..) => false,
        // `typeof(e)`'s underlying kind is unknown without inferring `e`;
        // conservatively treat it as a copied aggregate (never a borrow).
        TypeExpr::TypeOf(..) => true,
        // A refinement is the underlying nominal record: copy like its base.
        TypeExpr::Refine(base, _, _) => annotated_type_passes_by_copy(program, module, base),
        // A `Self.field` slot type's kind is unknown here; a `type` slot never
        // appears as a value parameter. Conservatively treat as a copied aggregate.
        TypeExpr::SelfField(..) | TypeExpr::TypeSlot(..) => true,
    }
}

/// Whether a non-`self` parameter receives a private deep copy at callee
/// entry: an annotated parameter follows its annotation (see
/// [`annotated_type_passes_by_copy`]); an unannotated one copies exactly when
/// the body mutates it (the inferred `mut` mode). A copied parameter's
/// mutations are confined to the callee, so a `const` argument to it is fine
/// and forwarding it never creates a write-through position.
pub fn param_receives_copy(
    program: &Program,
    module: &[String],
    p: &ParamInfo,
    body: &Block,
) -> bool {
    match &p.ty {
        Some(t) => annotated_type_passes_by_copy(program, module, t),
        None => mutates_root(body, &p.name),
    }
}

/// Whether a parameter is an immutable reference (`ref(T)`, not `ref(mut(T))`).
pub fn param_is_immutable_ref(p: &ParamInfo) -> bool {
    matches!(&p.resolved_ty, Some(Type::Ref(inner)) if !matches!(**inner, Type::Mut(_)))
}

/// The built-in growable-array mutators: a method that mutates its receiver in
/// place rather than producing a fresh value. They make their receiver mutable.
fn is_builtin_mutating_method(method: &str) -> bool {
    matches!(method, "push" | "insert" | "remove" | "pop")
}

/// Whether `block` mutates the value behind `root` *through the reference* it
/// names -- a field/element assignment (`root.f = ` / `root[i] = `), a built-in
/// mutating method (`root.push(..)`), a write-back through a loop variable
/// iterating it, or any of these through a local alias (`let q = root` binds
/// another handle to the same heap value). A bare `root = ...` only rebinds the
/// local and is *not* counted -- it does not touch the caller's value, so a
/// `const` argument bound to a copied or rebindable parameter stays valid.
pub fn mutates_root(block: &Block, root: &str) -> bool {
    scan_block(block, &root_set(root, false), &mut WriteSink)
}

/// Sink that reports the first write through a tracked place.
struct WriteSink;

impl PlaceSink for WriteSink {
    fn write(&mut self) -> bool {
        true
    }
}

// ----- shared place-sensitive traversal -----

/// The names currently aliasing the tracked value, each mapped to whether a
/// *bare reassignment* of that name counts as a write. Rebinding counts only
/// for a loop variable (`for e in xs { e = 0 }` writes the element back into
/// the iterated array); for a parameter or a `let` alias a bare reassignment
/// merely rebinds the local and never reaches the tracked value.
type Roots = HashMap<String, bool>;

fn root_set(root: &str, rebind_counts: bool) -> Roots {
    HashMap::from([(root.to_string(), rebind_counts)])
}

/// Events reported by the shared traversal. Each hook returns `true` to stop
/// the scan and report the event to the caller.
trait PlaceSink {
    /// A write through a tracked place: a field/element store (`p.f = ..`,
    /// `p[i] = ..`), a bare reassignment of a rebind-counting name (a loop
    /// variable), or a built-in growable-array mutator (`p.push(..)`).
    fn write(&mut self) -> bool;

    /// Any call expression, with the tracked-alias set in scope, so a sink can
    /// detect a tracked place escaping into a callee.
    fn call(&mut self, _callee: &Expr, _args: &[Arg], _roots: &Roots) -> bool {
        false
    }
}

/// The tracked name a place expression is rooted at (`a.b[c]` -> `a` when `a`
/// is in `roots`). `None` for a non-place expression or an untracked root.
fn tracked_root<'r>(expr: &Expr, roots: &'r Roots) -> Option<(&'r String, &'r bool)> {
    let root = root_ident(expr)?;
    roots.get_key_value(root)
}

/// Names bound by a pattern (destructuring binders and shorthand fields).
fn pattern_names(pat: &Pattern, out: &mut Vec<String>) {
    match pat {
        Pattern::Binding(name, _) => out.push(name.clone()),
        Pattern::Record(_, fields, _) => {
            for f in fields {
                match &f.pat {
                    Some(sub) => pattern_names(sub, out),
                    None => out.push(f.name.clone()),
                }
            }
        }
        Pattern::Array(pats, _) => pats.iter().for_each(|p| pattern_names(p, out)),
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
    }
}

/// Bind a pattern over `source_tracked` data: when the matched value is a place
/// rooted at a tracked name, every bound name is another handle to (part of)
/// the same heap value, so it becomes a tracked alias (bare rebinds of an alias
/// never count). Otherwise the bound names shadow any tracked outer name.
fn bind_pattern(pat: &Pattern, source_tracked: bool, roots: &mut Roots) {
    let mut names = Vec::new();
    pattern_names(pat, &mut names);
    for name in names {
        if source_tracked {
            roots.insert(name, false);
        } else {
            roots.remove(&name);
        }
    }
}

/// Scan a block in statement order, threading alias bindings and shadowing
/// through a local copy of `roots`. Returns `true` as soon as the sink accepts
/// an event.
fn scan_block(block: &Block, roots: &Roots, sink: &mut impl PlaceSink) -> bool {
    let mut roots = roots.clone();
    block
        .stmts
        .iter()
        .any(|stmt| scan_stmt(stmt, &mut roots, sink))
}

fn scan_stmt(stmt: &Stmt, roots: &mut Roots, sink: &mut impl PlaceSink) -> bool {
    match stmt {
        Stmt::Let { pat, value, .. } => {
            if let Some(value) = value {
                if scan_expr(value, roots, sink) {
                    return true;
                }
                // `let q = <place rooted at a tracked name>` binds another handle to
                // the same heap value, so `q` becomes a tracked alias; binding an
                // unrelated value shadows any tracked name of the same name.
                bind_pattern(pat, tracked_root(value, roots).is_some(), roots);
            } else {
                // An uninitialized `let` binds a fresh value (assigned later), so
                // it is never an alias of a tracked name; it shadows like any
                // other unrelated binding.
                bind_pattern(pat, false, roots);
            }
            false
        }
        Stmt::Assign { target, value, .. } => {
            if scan_expr(target, roots, sink) || scan_expr(value, roots, sink) {
                return true;
            }
            if let Some((_, &rebind_counts)) = tracked_root(target, roots) {
                // A projection store (`p.f = ..`, `p[i] = ..`) always writes
                // through; a bare reassignment only when the name is a loop
                // variable (write-back into the iterated array).
                let bare = matches!(target, Expr::Ident(..) | Expr::SelfExpr(..));
                if !bare || rebind_counts {
                    return sink.write();
                }
            }
            false
        }
        Stmt::While { cond, body, .. } => {
            scan_expr(cond, roots, sink) || scan_block(body, roots, sink)
        }
        Stmt::For {
            var, iter, body, ..
        } => {
            if scan_expr(iter, roots, sink) {
                return true;
            }
            let mut inner = roots.clone();
            if tracked_root(iter, roots).is_some() {
                // Iterating a tracked place binds each element by reference of
                // the array's kind, so writing back through the loop variable
                // (`e = ..`, `e.f = ..`, `e.push(..)`) writes the tracked value.
                inner.insert(var.clone(), true);
            } else {
                // The loop variable shadows a like-named tracked binding.
                inner.remove(var);
            }
            body.stmts.iter().any(|s| scan_stmt(s, &mut inner, sink))
        }
        Stmt::Expr(e) | Stmt::Return(Some(e), _) => scan_expr(e, roots, sink),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => false,
    }
}

fn scan_expr(expr: &Expr, roots: &Roots, sink: &mut impl PlaceSink) -> bool {
    match expr {
        Expr::Call(callee, args, _) => {
            // A built-in array mutator on a tracked place mutates it.
            if let Expr::Field(recv, m, _) = &**callee
                && is_builtin_mutating_method(m)
                && tracked_root(recv, roots).is_some()
                && sink.write()
            {
                return true;
            }
            if sink.call(callee, args, roots) {
                return true;
            }
            scan_expr(callee, roots, sink) || args.iter().any(|a| scan_expr(&a.expr, roots, sink))
        }
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) | Expr::Field(inner, _, _) => {
            scan_expr(inner, roots, sink)
        }
        Expr::Binary(_, left, right, _) | Expr::Range(left, right, _) => {
            scan_expr(left, roots, sink) || scan_expr(right, roots, sink)
        }
        Expr::Index(base, idx, _) => scan_expr(base, roots, sink) || scan_expr(idx, roots, sink),
        Expr::Closure(params, body, _) => {
            // Closure parameters shadow like-named tracked bindings; captures
            // keep referring to the tracked value, so the body is scanned.
            let mut inner = roots.clone();
            for p in params {
                inner.remove(&p.name);
            }
            scan_expr(body, &inner, sink)
        }
        Expr::Array(items, _) => items.iter().any(|item| scan_expr(item, roots, sink)),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => fields
            .iter()
            .any(|(_, value)| scan_expr(value, roots, sink)),
        Expr::Str(segs, _) => segs.iter().any(|seg| match seg {
            StrSeg::Expr(e) => scan_expr(e, roots, sink),
            _ => false,
        }),
        Expr::If(cond, then, els, _) => {
            scan_expr(cond, roots, sink)
                || scan_block(then, roots, sink)
                || els.as_ref().is_some_and(|els| scan_expr(els, roots, sink))
        }
        Expr::IfLet(pat, scrut, then, els, _) => {
            if scan_expr(scrut, roots, sink) {
                return true;
            }
            // Pattern binders over a tracked scrutinee alias its contents.
            let mut inner = roots.clone();
            bind_pattern(pat, tracked_root(scrut, roots).is_some(), &mut inner);
            then.stmts.iter().any(|s| scan_stmt(s, &mut inner, sink))
                || els.as_ref().is_some_and(|els| scan_expr(els, roots, sink))
        }
        Expr::Match(scrut, arms, _) => {
            if scan_expr(scrut, roots, sink) {
                return true;
            }
            let scrut_tracked = tracked_root(scrut, roots).is_some();
            arms.iter().any(|arm| {
                let mut inner = roots.clone();
                bind_pattern(&arm.pattern, scrut_tracked, &mut inner);
                scan_expr(&arm.body, &inner, sink)
            })
        }
        Expr::Block(block, _) => scan_block(block, roots, sink),
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => false,
    }
}

/// The base identifier a place expression is rooted at (`a.b[c]` -> `a`).
pub fn root_ident(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Ident(name, _) => Some(name),
        Expr::SelfExpr(_) => Some("self"),
        Expr::Field(base, _, _) | Expr::Index(base, _, _) => root_ident(base),
        _ => None,
    }
}

/// Whether a parameter's passing mode is inferred from whether the body mutates
/// it, rather than fixed by an annotation. Only a truly unannotated parameter
/// qualifies: it becomes a shared borrow (`ref`) when not mutated and a private
/// deep copy (`mut`) when mutated. An explicit `a: infer` is *not* inferred -- it
/// is always a read-only deep copy -- and every other annotation states its own
/// passing mode via its `ref`/`mut` wrapper.
pub fn param_infers_pass_mode(p: &ParamInfo) -> bool {
    p.ty.is_none()
}

/// Whether a parameter is an explicit `infer` (`a: infer`): a read-only deep
/// copy whose contents the body may not mutate.
pub fn param_is_infer(p: &ParamInfo) -> bool {
    matches!(&p.ty, Some(TypeExpr::Named(n, _)) if n == "infer")
}
