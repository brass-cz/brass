//! Program-level concurrency facts the back ends consult: whether a batch
//! spawns, which instances a worker thread may run (so the lazy JIT
//! compiles them before a worker starts), which locals a `spawn` moves out
//! of its body, and whether the program uses `with` (and so needs the
//! region write barrier).

use super::*;

/// Whether any instance in `program` spawns a task. The lazy JIT compiles
/// and primes every recorded deferred target before code from such a batch
/// runs: spawned code executes on worker threads, which can only READ the
/// resolved-address cache -- the compiler lives on the main thread.
pub fn batch_spawns(program: &MonoProgram) -> bool {
    let spawns =
        |rv: &Rvalue| matches!(rv, Rvalue::Call(Callee::Builtin(name), _) if name == "spawn");
    program.functions.iter().any(|f| {
        f.body.blocks.iter().any(|b| {
            b.stmts.iter().any(|s| match s {
                MirStmt::Assign(_, rv) | MirStmt::Eval(rv) => spawns(rv),
                _ => false,
            })
        })
    })
}

/// The locals moved out by a `spawn` (their reference is transferred to the new
/// thread, which releases the closure when it finishes). The spawn capture
/// analysis guarantees such a value is not live after the spawn, so excluding it
/// from the spawner's end-of-scope releases is the move itself.
pub(super) fn spawn_moved_locals(f: &MonoFunction) -> fxhash::FxHashSet<LocalId> {
    let mut moved = fxhash::FxHashSet::default();
    let mut scan = |rv: &Rvalue| {
        if let Rvalue::Call(Callee::Builtin(name), args) = rv
            && name == "spawn"
            && let Some(Operand::Local(id)) = args.first()
        {
            moved.insert(*id);
        }
    };
    for block in &f.body.blocks {
        for s in &block.stmts {
            match s {
                MirStmt::Assign(_, rv) | MirStmt::Eval(rv) => scan(rv),
                _ => {}
            }
        }
    }
    moved
}

/// The monomorphized instance symbols a spawned worker thread may execute, or
/// `None` when the program never spawns. For each `spawn` site the operand is
/// traced to the closure instances it can hold; those roots plus everything
/// statically reachable from their bodies -- direct calls, and closures
/// created inside reachable bodies (the only way a function value originates
/// on the worker) -- form the set.
///
/// The walk gives up and returns EVERY instance, the sound fallback, when a
/// function value can cross onto the worker unseen: a spawn operand or a
/// `Fun`-typed capture that cannot be traced to its creations, a capture or a
/// read global whose type carries a function anywhere inside it, or a program
/// with runtime-deferred call sites. Precision only trims the set; soundness
/// never depends on it.
pub fn spawn_precompile(program: &MonoProgram) -> Option<Vec<String>> {
    if !batch_spawns(program) {
        return None;
    }
    spawn_reachable_instances(program)
        .or_else(|| Some(program.functions.iter().map(|f| f.symbol.clone()).collect()))
}

/// The precise half of [`spawn_precompile`]; `None` means the walk gave up.
fn spawn_reachable_instances(program: &MonoProgram) -> Option<Vec<String>> {
    // Deferred sites resolve through the runtime service; their targets are
    // invisible to a static walk.
    if !program.deferred.is_empty() {
        return None;
    }

    // Roots: every closure instance a spawn operand can hold. Closure bodies
    // are instances themselves, so a nested spawn's operand resolves inside
    // its enclosing closure body here as well.
    let mut roots: Vec<String> = Vec::new();
    for f in &program.functions {
        for (_, rv) in body_rvalues(f) {
            let Rvalue::Call(Callee::Builtin(name), args) = rv else {
                continue;
            };
            if name != "spawn" {
                continue;
            }
            let local = args.first().and_then(Operand::as_local)?;
            let mut visiting = fxhash::FxHashSet::default();
            trace_closure_local(program, f, local, &mut roots, &mut visiting)?;
        }
    }

    // Everything statically reachable from the roots. A closure created inside
    // a reachable body is callable there (indirectly), so it joins the walk;
    // any other function value a worker can call was either created in such a
    // body or rejected while resolving the roots' captures.
    let mut seen = std::collections::BTreeSet::new();
    let mut queue = roots;
    while let Some(symbol) = queue.pop() {
        if !seen.insert(symbol.clone()) {
            continue;
        }
        // An uninstantiated closure calls a diagnostic target, so there is
        // no instance body to compile or walk.
        let Some(f) = program.lookup(&symbol) else {
            continue;
        };
        for (dest, rv) in body_rvalues(f) {
            match rv {
                Rvalue::Call(callee, args) => {
                    let arg_types: Vec<Type> = args
                        .iter()
                        .map(|a| operand_type_of(a, &f.local_types))
                        .collect();
                    let dest_ty = dest
                        .map(|d| f.local_types[d.index()].clone())
                        .unwrap_or(Type::Void);
                    match classify_call(program, f, callee, &arg_types, &dest_ty) {
                        CallKind::Instance(target) | CallKind::NullableDisplay(target) => {
                            // The eager path panics when a validated call has no
                            // instance; this walk cannot prove more than it does.
                            program.lookup(&target)?;
                            queue.push(target);
                        }
                        // `print`/`println` of a value rendering through a
                        // USER `display` calls that instance.
                        CallKind::Io(_) => {
                            if let Some(inst) = arg_types.first().and_then(|ty| {
                                display_instance(program, ty)
                                    .or_else(|| nullable_display_instance(program, ty))
                            }) {
                                queue.push(inst.symbol.clone());
                            }
                        }
                        _ => {}
                    }
                }
                Rvalue::Closure { id, captures } => {
                    if let Some(sym) = created_closure_symbol(f, dest, *id, captures) {
                        queue.push(sym);
                    }
                }
                Rvalue::Global(name) => {
                    // A function value read out of module state is invisible
                    // to this walk.
                    let known_fun_free = program
                        .global_type(name)
                        .is_some_and(|t| !type_contains_fun(program.hir, t));
                    if !known_fun_free {
                        return None;
                    }
                }
                _ => {}
            }
        }
    }
    // Only symbols with an instance have a module to materialize.
    Some(
        seen.into_iter()
            .filter(|s| program.lookup(s).is_some())
            .collect(),
    )
}

/// Add every closure instance `local` can hold in `f`'s body to `out`,
/// following local-to-local copies, and trace `Fun`-typed captures to their
/// own creations (they become roots too: the worker can call them). `None`
/// when a producer other than a closure creation or a copy feeds the local,
/// or when a capture's type could smuggle a function value the trace cannot
/// see.
fn trace_closure_local(
    program: &MonoProgram,
    f: &MonoFunction,
    local: LocalId,
    out: &mut Vec<String>,
    visiting: &mut fxhash::FxHashSet<LocalId>,
) -> Option<()> {
    if !visiting.insert(local) {
        return Some(());
    }
    let mut found = false;
    for (dest, rv) in body_rvalues(f) {
        if dest != Some(local) {
            continue;
        }
        match rv {
            Rvalue::Closure { id, captures } => {
                for op in captures {
                    let cty = operand_type_of(op, &f.local_types);
                    if matches!(cty, Type::Fun(..)) {
                        trace_closure_local(program, f, op.as_local()?, out, visiting)?;
                    } else if type_contains_fun(program.hir, &cty) {
                        return None;
                    }
                }
                out.push(created_closure_symbol(f, dest, *id, captures)?);
                found = true;
            }
            // A plain copy: the source's closures are this local's closures.
            Rvalue::Use(op) => {
                trace_closure_local(program, f, op.as_local()?, out, visiting)?;
                found = true;
            }
            // Any other producer (a call result, a load, a global) hides the
            // creation site.
            _ => return None,
        }
    }
    found.then_some(())
}

/// The instance symbol of a closure created by [`Rvalue::Closure`], keyed the
/// way [`Codegen::codegen_rvalue`] keys `make_closure`: capture types from the
/// capture operands, parameter types from the destination local's `Fun` type.
/// `None` when the destination is discarded or not function-typed -- the
/// shared driver never materializes the value then either.
fn created_closure_symbol(
    f: &MonoFunction,
    dest: Option<LocalId>,
    id: ClosureId,
    captures: &[Operand],
) -> Option<String> {
    let Type::Fun(params, _) = &f.local_types[dest?.index()] else {
        return None;
    };
    let capture_types: Vec<Type> = captures
        .iter()
        .map(|op| operand_type_of(op, &f.local_types))
        .collect();
    Some(
        f.closure_targets
            .get(&id)
            .cloned()
            .unwrap_or_else(|| crate::mono::closure_symbol(id, &capture_types, params)),
    )
}

/// Every rvalue in `f`'s body with its destination local (`None` for an
/// evaluated-and-discarded statement).
fn body_rvalues<'a>(
    f: &'a MonoFunction<'_>,
) -> impl Iterator<Item = (Option<LocalId>, &'a Rvalue)> {
    f.body.blocks.iter().flat_map(|b| {
        b.stmts.iter().filter_map(|s| match s {
            MirStmt::Assign(dest, rv) => Some((Some(*dest), rv)),
            MirStmt::Eval(rv) => Some((None, rv)),
            _ => None,
        })
    })
}

/// Whether a value of `ty` can contain a function value anywhere inside it:
/// directly, or through an element, a record field, or a variant payload.
/// Conservative: an unresolvable layout counts as containing one.
fn type_contains_fun(hir: &brass_hir::Program, ty: &Type) -> bool {
    fn walk(hir: &brass_hir::Program, ty: &Type, visiting: &mut Vec<String>) -> bool {
        match ty {
            Type::Fun(..) => true,
            Type::Bool | Type::Int(_) | Type::Float(_) | Type::Str | Type::Void | Type::Never => {
                false
            }
            Type::Array(elem, _) | Type::Slice(elem) => walk(hir, elem, visiting),
            Type::Nullable(inner) | Type::ConstOf(inner) | Type::Mut(inner) | Type::Ref(inner) => {
                walk(hir, inner, visiting)
            }
            Type::Tuple(elems) => elems.iter().any(|e| walk(hir, e, visiting)),
            // A revisited nominal is already being examined higher in the
            // walk; the cycle adds no new field types.
            Type::Record(n) => {
                let key = brass_hir::type_key(ty);
                if visiting.contains(&key) {
                    return false;
                }
                visiting.push(key);
                let contains = match crate::render::render_record_fields(hir, n) {
                    Some(fields) => fields.iter().any(|(_, t)| walk(hir, t, visiting)),
                    None => true,
                };
                visiting.pop();
                contains
            }
            Type::Sum(n) => {
                let key = brass_hir::type_key(ty);
                if visiting.contains(&key) {
                    return false;
                }
                visiting.push(key);
                let contains =
                    match sum_variant_names(hir, n) {
                        Some(names) => names.iter().any(|v| {
                            match crate::render::render_variant_fields(hir, n, v) {
                                Some((_, fields)) => {
                                    fields.iter().any(|(_, t)| walk(hir, t, visiting))
                                }
                                None => true,
                            }
                        }),
                        None => true,
                    };
                visiting.pop();
                contains
            }
            // Neither survives monomorphization; assume the worst.
            Type::Unknown(_) | Type::SelfType => true,
        }
    }
    walk(hir, ty, &mut Vec::new())
}

/// The declared variant names of sum type `n`, or `None` for an unknown
/// nominal.
fn sum_variant_names(hir: &brass_hir::Program, n: &brass_hir::NominalType) -> Option<Vec<String>> {
    let info = hir.type_by_id(n.id)?;
    let brass_hir::TypeKind::Sum { variants } = &info.kind else {
        return None;
    };
    Some(variants.iter().map(|v| v.name.clone()).collect())
}

/// Whether the program uses `with` -- and so opens regions and needs the write
/// barrier on heap stores. A back end consults this so a sequential (region-free)
/// program emits no barriers and pays no barrier cost.
pub fn program_uses_with(program: &MonoProgram) -> bool {
    fn rv_with(rv: &Rvalue) -> bool {
        // `_with_all` is the auto-acquire pass's group form of `with`; a program
        // whose only guards are group wraps still shares cowns across threads, so
        // it needs the same barriers.
        matches!(rv, Rvalue::Call(Callee::Builtin(n), _) if n == "with" || n == "_with_all")
    }
    program.functions.iter().any(|f| {
        f.body.blocks.iter().any(|b| {
            b.stmts.iter().any(|s| match s {
                MirStmt::Assign(_, rv) | MirStmt::Eval(rv) => rv_with(rv),
                _ => false,
            })
        })
    })
}
