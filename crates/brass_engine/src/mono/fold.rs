//! Static-truthiness branch folding: deciding at monomorphization
//! time which conditional edges are dead (e.g. null checks on a
//! non-nullable local) so unreachable blocks are never compiled.

use super::*;

/// The blocks reachable from the entry once statically-known `if` conditions are
/// folded: a `never?` condition (a bare `null`, always null) is taken as false
/// and a non-nullable / non-bool condition (always truthy) as true, so the dead
/// arm is never visited. The typed back end uses this to skip emitting an arm
/// that cannot run -- and the unwrapped `never` values it would otherwise
/// contain (e.g. `a * 2` where `a` is a bare `null`) -- while monomorphization
/// still types both arms so a fallible callable's `Result` payloads infer from
/// whichever arm supplies each.
pub fn reachable_blocks(program: &Program, body: &MirBody, local_types: &[Type]) -> Vec<bool> {
    let mut reached = vec![false; body.blocks.len()];
    let mut stack = vec![body.entry];
    while let Some(id) = stack.pop() {
        if std::mem::replace(&mut reached[id.index()], true) {
            continue;
        }
        match &body.block(id).term {
            Terminator::Goto(b) => stack.push(*b),
            Terminator::CondBranch { cond, then, els } => {
                match cond_static_truthiness(program, body, local_types, cond) {
                    Some(true) => stack.push(*then),
                    Some(false) => stack.push(*els),
                    None => {
                        stack.push(*then);
                        stack.push(*els);
                    }
                }
            }
            Terminator::Return(_) | Terminator::Unreachable => {}
        }
    }
    reached
}

/// The locals no reachable block assigns: the temporaries of an arm a statically
/// known `if` folded away. Nothing reads them and no slot is emitted for them, so
/// monomorphization may leave them untyped rather than failing the instance --
/// which is what lets a generic body hold an arm that only types for a *different*
/// instantiation.
pub fn locals_only_in_dead_blocks(body: &MirBody, reachable: &[bool]) -> Vec<bool> {
    let mut dead = vec![true; body.locals.len()];
    for (block, _) in body.blocks.iter().zip(reachable).filter(|(_, r)| **r) {
        for stmt in &block.stmts {
            if let MirStmt::Assign(local, _) = stmt {
                dead[local.index()] = false;
            }
        }
    }
    dead
}

/// The effective static truthiness of an `if` condition, used to fold a branch.
///
/// Folding decides ONLY on the condition, never on the arm's content. An
/// earlier version also folded a then-arm whose reachable return conflicted
/// with the function's return type, to let a structural `if` degrade for a
/// non-fitting instance -- but every sound degrade is already decided by the
/// condition itself (an absent member reads `never?` -> false, a present
/// non-nullable one -> true), while a runtime-decided branch with a
/// conflicting return is a type error, and deleting the arm turned it into a
/// miscompilation (`HashMap.get_or` silently returned the default on the hit
/// path). The front end now rejects such programs; nothing here may prune a
/// runtime-reachable arm.
pub fn cond_static_truthiness(
    program: &Program,
    body: &MirBody,
    local_types: &[Type],
    cond: &Operand,
) -> Option<bool> {
    // An `if let x = e` presence test folds on the *subject's* nullability, not
    // its truthiness: any non-nullable subject -- including a bool -- is an
    // irrefutable bind (always then), a bare `null` is always absent, and only
    // a real nullable branches at runtime.
    if let Some(subj) = presence_subject_type(body, local_types, cond) {
        return match subj {
            Type::Nullable(inner) if matches!(**inner, Type::Never) => Some(false),
            Type::Nullable(_) | Type::Unknown(_) => None,
            _ => Some(true),
        };
    }
    // A type test (`if v: T`) folds once its subject's type is real: the
    // monomorphized type either satisfies the checker-resolved pattern or it
    // does not -- through the same `brass_typesys::type_test_accepts`
    // (exact/wildcard core plus structural subtyping) the checker selected
    // the arm with, so the pruned arm is exactly the unchecked one. A
    // subject that never resolved (the `Never` stand-in of an untyped local
    // mid-inference) decides nothing.
    if let Some((subj, pattern)) = type_test_of(body, cond) {
        return match operand_type_of(subj, local_types) {
            Type::Never | Type::Unknown(_) => None,
            ty => Some(brass_typesys::type_test_accepts(program, pattern, &ty)),
        };
    }
    operand_type_of(cond, local_types).static_truthiness()
}

/// The blocks an instance reaches once its TYPE TESTS are folded against the
/// seeded (parameter/annotation) types -- before the type fixpoint has run.
/// Only a test whose subject is already fully known decides; every other
/// condition conservatively keeps both successors. Monomorphization uses this
/// to skip typing (and to deny return/fallibility evidence to) the arms other
/// instantiations own: a statement on a type-test-dead path is never compiled
/// for this instance, so nothing about it -- its returns, its `error(...)`
/// sites -- may shape the instance's ABI.
pub fn type_test_live_blocks(
    program: &Program,
    body: &MirBody,
    seeded: &[Option<Type>],
) -> Vec<bool> {
    let mut reached = vec![false; body.blocks.len()];
    let mut stack = vec![body.entry];
    while let Some(id) = stack.pop() {
        if std::mem::replace(&mut reached[id.index()], true) {
            continue;
        }
        match &body.block(id).term {
            Terminator::Goto(b) => stack.push(*b),
            Terminator::CondBranch { cond, then, els } => {
                let decided = type_test_of(body, cond).and_then(|(subj, pattern)| {
                    let ty = match subj {
                        Operand::Local(l) => seeded.get(l.index())?.clone()?,
                        Operand::Const(_) => return None,
                    };
                    brass_hir::is_fully_known(&ty)
                        .then(|| brass_typesys::type_test_accepts(program, pattern, &ty))
                });
                match decided {
                    Some(true) => stack.push(*then),
                    Some(false) => stack.push(*els),
                    None => {
                        stack.push(*then);
                        stack.push(*els);
                    }
                }
            }
            Terminator::Return(_) | Terminator::Unreachable => {}
        }
    }
    reached
}

/// Whether any live block carries a fallibility site, mirroring the AST rule
/// the lowering's `function_fallible` applied to the whole body: a call to
/// the reserved `error(...)` (which lowers as a call to the prelude `error`
/// function, not an inline construction), an explicit `Result.Err`
/// construction (the `!` lift rebuild included), or a `!`-propagation error
/// return. The per-instance fallible ABI keys on this -- an error source on
/// a type-test-dead path belongs to other instantiations.
pub(super) fn live_fallible_site(body: &MirBody, live: &[bool]) -> bool {
    for (i, block) in body.blocks.iter().enumerate() {
        if !live[i] {
            continue;
        }
        for stmt in &block.stmts {
            let rv = match stmt {
                MirStmt::Assign(_, rv) | MirStmt::Eval(rv) => rv,
                _ => continue,
            };
            match rv {
                Rvalue::Call(Callee::Free(sym), _) if sym == "error" => return true,
                Rvalue::Variant { ty, variant, .. } if ty == "Result" && variant == "Err" => {
                    return true;
                }
                _ => {}
            }
        }
    }
    super::scan::propagated_result_returns(body)
        .iter()
        .any(|(idx, _)| live[*idx])
}

/// If `cond` is the result of an `Rvalue::TypeTest` assignment (a type-test
/// `if` condition), the tested operand and the pattern.
fn type_test_of<'b>(body: &'b MirBody, cond: &Operand) -> Option<(&'b Operand, &'b Type)> {
    let Operand::Local(id) = cond else {
        return None;
    };
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let MirStmt::Assign(dest, Rvalue::TypeTest(subj, pattern)) = stmt
                && dest == id
            {
                return Some((subj, pattern));
            }
        }
    }
    None
}

/// If `cond` is the result of a MIR nullable-presence test, the type of its
/// subject. Propagation uses a distinct marker so return inference can identify
/// it, but both tests fold by the same subject type.
fn presence_subject_type<'t>(
    body: &MirBody,
    local_types: &'t [Type],
    cond: &Operand,
) -> Option<&'t Type> {
    let Operand::Local(id) = cond else {
        return None;
    };
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let MirStmt::Assign(dest, Rvalue::Call(Callee::Builtin(name), args)) = stmt
                && dest == id
                && matches!(name.as_str(), "__present" | "__null_prop_present")
                && let Some(Operand::Local(subj)) = args.first()
            {
                return Some(&local_types[subj.index()]);
            }
        }
    }
    None
}
