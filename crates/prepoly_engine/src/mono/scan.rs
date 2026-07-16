//! Free MIR-scanning helpers of the monomorphizer: pre-passes that walk a
//! body once to recover typing facts -- which locals hold closures and how
//! they are called/passed/stored, which empty array literals are later
//! pushed into, `Use`-copy alias chains, seeds for a returned aggregate's
//! field locals, and `Result`-shape facts (declared Ok payloads, `expr!`
//! propagation returns, whether a body can raise at all) -- plus the shared
//! operand/operator typing lookups built on them.

use super::*;

/// Seed the locals that flow into a body's returned record/variant from the
/// expected return's field types. Used so a constructor's empty array fields take
/// their element type from the result the caller fixed (the witness-free
/// `new()`). Only fills locals still untyped, with supported field types, so it
/// never overrides an inference the body itself can make.
///
/// A field value usually arrives through a `let` binding (`let items = []; Self
/// { items: items }`), which lowers to a temporary holding the empty array and a
/// binding local copied from it. Seeding only the binding would leave the actual
/// empty-array temporary untyped, so the seed is propagated backward along
/// `Use`-copy chains to reach it.
pub(super) fn seed_returned_aggregate(
    body: &MirBody,
    ret_ty: &Type,
    local_types: &mut [Option<Type>],
) {
    let returned: Vec<LocalId> = body
        .blocks
        .iter()
        .filter_map(|b| match &b.term {
            Terminator::Return(Operand::Local(r)) => Some(*r),
            _ => None,
        })
        .collect();
    if returned.is_empty() {
        return;
    }
    // `dest -> src` for every `dest = Use(src)` copy, so a seed on a binding can
    // be carried back to the temporary it copied.
    let mut copy_of: HashMap<LocalId, LocalId> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let MirStmt::Assign(dest, Rvalue::Use(Operand::Local(src))) = stmt {
                copy_of.insert(*dest, *src);
            }
        }
    }
    for block in &body.blocks {
        for stmt in &block.stmts {
            let MirStmt::Assign(dest, rv) = stmt else {
                continue;
            };
            if !returned.contains(dest) {
                continue;
            }
            let fields = match rv {
                Rvalue::Record { fields, .. } | Rvalue::Variant { fields, .. } => fields,
                _ => continue,
            };
            for (fname, op) in fields {
                let Operand::Local(fl) = op else { continue };
                let Some(fty) = aggregate_field_type(ret_ty, fname) else {
                    continue;
                };
                if !is_supported(&fty) {
                    continue;
                }
                // Seed the field operand and every temporary it was copied from.
                let mut cur = *fl;
                loop {
                    if local_types[cur.index()].is_none() {
                        local_types[cur.index()] = Some(fty.clone());
                    }
                    match copy_of.get(&cur) {
                        Some(&src) => cur = src,
                        None => break,
                    }
                }
            }
        }
    }
}

/// A field's resolved type from an aggregate's instance substitution (the
/// checker-resolved record/variant carries each field's concrete type there).
fn aggregate_field_type(ty: &Type, field: &str) -> Option<Type> {
    match ty {
        Type::Record(n) | Type::Sum(n) => n.substitution.get(field).cloned(),
        _ => None,
    }
}

/// The declared return type of a record method, if concrete.
pub(super) fn method_ret_annotation(
    program: &Program,
    type_symbol: &str,
    method: &str,
) -> Option<Type> {
    let info = program.types.get(type_symbol)?;
    let m = match &info.kind {
        TypeKind::Record { methods, .. } => methods.get(method)?,
        // A whole-sum method lives (duplicated) in the variants' tables; the
        // checker keeps the signatures consistent, so the first is canonical.
        TypeKind::Sum { variants } => variants.iter().find_map(|v| v.methods.get(method))?,
    };
    // The RAW annotation (unfiltered): a fallible `T!` resolves to
    // `Result<T, Unknown>` whose open error payload is unsupported, but the Ok
    // payload `T` is still authoritative -- `resolve_callable` needs it to type
    // a mutually recursive call, and separately filters for the provisional.
    m.signature.ret_ty.clone()
}

/// The concrete type of an operand in a fully-typed body.
pub fn operand_type_of(op: &Operand, local_types: &[Type]) -> Type {
    match op {
        Operand::Local(id) => local_types[id.index()].clone(),
        Operand::Const(lit) => const_type(lit).unwrap_or(Type::Void),
    }
}

/// The concrete (supported) Ok payload of a `Result` return type fixed by a `T!`
/// annotation, or `None` if `t` is not such a `Result` or its Ok payload is not
/// yet concrete. Authoritative for the fallible return's Ok payload.
pub(super) fn result_concrete_ok(t: &Type) -> Option<Type> {
    match t {
        Type::Sum(n) if n.id == RESULT_TYPE_ID => n
            .result_payloads()
            .map(|(ok, _)| ok.clone())
            .filter(is_supported),
        _ => None,
    }
}

/// The error arms created by `expr!` return the original Result value unchanged.
/// Those synthetic returns carry only the `Err` payload for the enclosing
/// callable; their `Ok` payload belongs to the callee that produced the Result.
pub(super) fn propagated_result_returns(body: &MirBody) -> HashSet<(usize, LocalId)> {
    let mut tested_results: HashMap<LocalId, LocalId> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let MirStmt::Assign(test, Rvalue::Call(Callee::Builtin(name), args)) = stmt
                && name == "result_is_ok"
                && let Some(Operand::Local(result)) = args.first()
            {
                tested_results.insert(*test, *result);
            }
        }
    }

    let mut returns = HashSet::new();
    for block in &body.blocks {
        if let Terminator::CondBranch {
            cond: Operand::Local(test),
            els,
            ..
        } = &block.term
            && let Some(result) = tested_results.get(test)
            && let Terminator::Return(Operand::Local(returned)) = body.block(*els).term
            && returned == *result
        {
            returns.insert((els.index(), *result));
        }
    }
    returns
}

/// The return blocks created by the null arm of a nullable-operand `expr!`:
/// the else-target of a branch on a `__present` test, returning the `null`
/// constant. Those returns type the enclosing callable's return NULLABLE (an
/// outer `?` around the fallible `Result`); they carry no Ok/Err payload. A
/// USER-written `return null` in a fallible body is not of this shape and
/// keeps its meaning (an Ok payload that may be null).
pub(super) fn null_prop_returns(body: &MirBody) -> HashSet<usize> {
    let mut present_tests: HashSet<LocalId> = HashSet::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let MirStmt::Assign(test, Rvalue::Call(Callee::Builtin(name), _)) = stmt
                && name == "__present"
            {
                present_tests.insert(*test);
            }
        }
    }
    let mut returns = HashSet::new();
    for block in &body.blocks {
        if let Terminator::CondBranch {
            cond: Operand::Local(test),
            els,
            ..
        } = &block.term
            && present_tests.contains(test)
            && matches!(
                body.block(*els).term,
                Terminator::Return(Operand::Const(Literal::Null))
            )
        {
            returns.insert(els.index());
        }
    }
    returns
}

/// Whether every non-propagated, non-null-arm return in `body` returns a
/// value built by an `Err` construction (directly or through `Use` copies):
/// such a body produces no Ok value, so its fallible Ok payload is
/// uninhabited and may default (see `infer_result_ret`). Conservative: any
/// other return operand -- a bare value, or a call the fixpoint has not
/// resolved yet -- keeps the payload open.
pub(super) fn returns_only_err_constructions(
    body: &MirBody,
    propagated: &HashSet<(usize, LocalId)>,
    null_props: &HashSet<usize>,
) -> bool {
    let err_only = err_construction_locals(body);
    let mut any = false;
    for (idx, block) in body.blocks.iter().enumerate() {
        let Terminator::Return(op) = &block.term else {
            continue;
        };
        if null_props.contains(&idx) {
            continue;
        }
        match op {
            Operand::Local(l) if propagated.contains(&(idx, *l)) => {}
            Operand::Local(l) if err_only.contains(l) => {
                any = true;
            }
            _ => return false,
        }
    }
    any
}

/// Locals that only ever hold an `Err`-variant `Result` construction
/// (directly or through `Use` copies of such locals). A return of one can
/// only execute an error path, so it must not define the enclosing
/// callable's Ok payload: the `!` lift arm returns such a rebuild, whose
/// seeded Ok slot is the OPERAND's Ok, not this callable's. Copy chains
/// resolve by iterating to a fixed point (the chains are shallow: a
/// branch-merge result local at most).
pub(super) fn err_construction_locals(body: &MirBody) -> HashSet<LocalId> {
    let mut err_only: HashSet<LocalId> = HashSet::new();
    let mut poisoned: HashSet<LocalId> = HashSet::new();
    loop {
        let mut changed = false;
        for block in &body.blocks {
            for stmt in &block.stmts {
                let MirStmt::Assign(local, rv) = stmt else {
                    continue;
                };
                let is_err = match rv {
                    Rvalue::Variant { ty, variant, .. } => ty == "Result" && variant == "Err",
                    Rvalue::Use(Operand::Local(src)) => {
                        if poisoned.contains(src) {
                            false
                        } else if err_only.contains(src) {
                            true
                        } else {
                            continue; // source not classified yet
                        }
                    }
                    _ => false,
                };
                if is_err {
                    if !poisoned.contains(local) && err_only.insert(*local) {
                        changed = true;
                    }
                } else if poisoned.insert(*local) {
                    err_only.remove(local);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    err_only.retain(|l| !poisoned.contains(l));
    err_only
}

/// Whether a fallible body actually raises an error: an `error(...)` (an `Err`
/// construction) or an `expr!` propagation (a `result_is_ok` test). A body with
/// neither never produces an `Err`, so its `Result` error payload is free.
pub(super) fn body_has_error_source(body: &MirBody) -> bool {
    body.blocks.iter().any(|b| {
        b.stmts.iter().any(|s| match s {
            MirStmt::Assign(_, Rvalue::Variant { ty, variant, .. }) => {
                ty == "Result" && variant == "Err"
            }
            MirStmt::Assign(_, Rvalue::Call(Callee::Builtin(n), _)) => n == "result_is_ok",
            _ => false,
        })
    })
}

/// Scan a body for indirect (closure) calls, mapping each *defining* closure
/// local to the argument operands of *every* call site. Used to type direct-call
/// closures, whose parameter types come from the calls rather than the
/// definition. A `let g = <closure>` binds through a `Use` copy, so callee
/// locals are resolved back through `Use` aliases to the local actually holding
/// the `Closure` rvalue.
///
/// Every site is kept because one parameter has one type across all of them: a
/// closure called once with `null` and once with a `P` takes a `P?`, and typing
/// it from whichever call the scan met first would compile the other against
/// the wrong layout.
pub(super) fn collect_indirect_args(body: &MirBody) -> HashMap<LocalId, Vec<Vec<Operand>>> {
    let alias = use_aliases(body);
    let mut out: HashMap<LocalId, Vec<Vec<Operand>>> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            let (MirStmt::Assign(_, rv) | MirStmt::Eval(rv)) = stmt else {
                continue;
            };
            if let Rvalue::Call(Callee::Indirect(Operand::Local(g)), args) = rv {
                out.entry(resolve_alias(&alias, *g))
                    .or_default()
                    .push(args.clone());
            }
            // `spawn`/`with` call their closure argument: `spawn(f)` invokes a
            // zero-argument `f`; `with(obj, f)` invokes `f(obj)`. Recording the
            // call shape here types the closure through the same path as any other
            // directly-called closure.
            if let Rvalue::Call(Callee::Builtin(name), args) = rv {
                match name.as_str() {
                    "spawn" => {
                        if let Some(Operand::Local(c)) = args.first() {
                            out.entry(resolve_alias(&alias, *c)).or_default();
                        }
                    }
                    "with" => {
                        if let (Some(obj), Some(Operand::Local(c))) = (args.first(), args.get(1)) {
                            out.entry(resolve_alias(&alias, *c))
                                .or_default()
                                .push(vec![obj.clone()]);
                        }
                    }
                    // `_with_all(f, c0, ...)` invokes a zero-argument `f` (the
                    // guarded body references the cowns as captures, not params).
                    "_with_all" => {
                        if let Some(Operand::Local(c)) = args.first() {
                            out.entry(resolve_alias(&alias, *c)).or_default();
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

/// Scan a body for locals stored as record-literal field values, mapping each
/// (alias-resolved) defining local to `(destination local, record type name,
/// field name)`. Used to type a closure that initializes a function-typed
/// field: it is neither called in the body nor passed to a function, so its
/// parameter types come from the field's declared signature, or -- for an
/// unannotated field -- from the constructed instance's checker-seeded
/// substitution on the destination local. Non-closure locals also land in the
/// map; only closure typing consults it, so the extra entries are inert.
pub(super) fn collect_record_field_closures(
    body: &MirBody,
) -> HashMap<LocalId, (LocalId, String, String)> {
    let alias = use_aliases(body);
    let mut out: HashMap<LocalId, (LocalId, String, String)> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            let MirStmt::Assign(dest, Rvalue::Record { ty, fields }) = stmt else {
                continue;
            };
            for (fname, op) in fields {
                if let Operand::Local(l) = op {
                    out.entry(resolve_alias(&alias, *l))
                        .or_insert_with(|| (*dest, ty.clone(), fname.clone()));
                }
            }
        }
    }
    out
}

/// Scan a body for locals passed as arguments to free-function calls, mapping
/// each to `(callee, all call args, its argument index)`. Used to type a closure
/// that is *passed* to a higher-order function (rather than called in place): its
/// parameter types are recovered from how the callee uses that parameter.
#[allow(clippy::type_complexity)]
pub(super) fn collect_closure_passes(
    body: &MirBody,
) -> HashMap<LocalId, (String, Vec<Operand>, usize)> {
    let alias = use_aliases(body);
    let mut out: HashMap<LocalId, (String, Vec<Operand>, usize)> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            let (MirStmt::Assign(_, rv) | MirStmt::Eval(rv)) = stmt else {
                continue;
            };
            // A closure passed to a free function, or to a UFCS method call
            // (`arr.map(closure)` resolves to the free function `map`); both recover
            // the closure's parameter types from the callee's use of it.
            if let Rvalue::Call(Callee::Free(base) | Callee::Method(base), args) = rv {
                for (i, a) in args.iter().enumerate() {
                    if let Operand::Local(g) = a {
                        // Resolve back through `Use` copies to the local that
                        // actually holds the `Closure` (`let g = <closure>`).
                        out.entry(resolve_alias(&alias, *g))
                            .or_insert_with(|| (base.clone(), args.clone(), i));
                    }
                }
            }
        }
    }
    out
}

/// type of an empty array literal `[]` from how it is later filled.
pub(super) fn collect_array_pushes(body: &MirBody) -> HashMap<LocalId, Operand> {
    let alias = use_aliases(body);
    let mut out: HashMap<LocalId, Operand> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            let (MirStmt::Assign(_, rv) | MirStmt::Eval(rv)) = stmt else {
                continue;
            };
            if let Rvalue::Call(Callee::Method(name), args) = rv {
                // `push(arr, elem)` and `insert(arr, idx, elem)` both reveal the
                // element type of an otherwise-unconstrained `[]` literal; the
                // element operand is the last argument in each.
                let elem = match name.as_str() {
                    "push" => args.get(1),
                    "insert" => args.get(2),
                    _ => None,
                };
                if let (Some(Operand::Local(g)), Some(elem)) = (args.first(), elem) {
                    out.entry(resolve_alias(&alias, *g))
                        .or_insert_with(|| elem.clone());
                }
            }
        }
    }
    out
}

/// Map each `dst` of an `Assign(dst, Use(Local(src)))` to `src`.
pub(super) fn use_aliases(body: &MirBody) -> HashMap<LocalId, LocalId> {
    let mut alias: HashMap<LocalId, LocalId> = HashMap::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let MirStmt::Assign(dst, Rvalue::Use(Operand::Local(src))) = stmt {
                alias.insert(*dst, *src);
            }
        }
    }
    alias
}

/// Follow a `Use`-alias chain to its root local.
pub(super) fn resolve_alias(alias: &HashMap<LocalId, LocalId>, mut l: LocalId) -> LocalId {
    for _ in 0..alias.len() + 1 {
        match alias.get(&l) {
            Some(&s) => l = s,
            None => break,
        }
    }
    l
}

/// The source name `local`'s value is bound to, for diagnostics. A value
/// expression lowers to an unnamed temporary that a bare `Use` copy (or a
/// top-level `SetGlobal`) then binds to what the programmer wrote (`let xs =
/// []` is `tmp = []; xs = tmp`), so when the local itself is unnamed the first
/// named binding it flows into names it. `None` for a value that never reaches
/// a named binding.
pub(super) fn binding_name_of(body: &MirBody, local: LocalId) -> Option<String> {
    if let Some(n) = &body.local(local).name {
        return Some(n.clone());
    }
    for block in &body.blocks {
        for stmt in &block.stmts {
            match stmt {
                MirStmt::Assign(dst, Rvalue::Use(Operand::Local(src))) if *src == local => {
                    if let Some(n) = &body.local(*dst).name {
                        return Some(n.clone());
                    }
                }
                MirStmt::SetGlobal(name, Operand::Local(src)) if *src == local => {
                    // A global's storage name is `name@module`; the part before
                    // the qualifier is what the programmer wrote.
                    return Some(name.split('@').next().unwrap_or(name).to_string());
                }
                _ => {}
            }
        }
    }
    None
}
