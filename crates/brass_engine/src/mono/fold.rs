//! Static-truthiness branch folding: deciding at monomorphization
//! time which conditional edges are dead (e.g. null checks on a
//! non-nullable local) so unreachable blocks are never compiled.

use super::*;

/// The blocks reachable from the entry once statically-known `if` conditions are
/// folded: a `never?` condition (a bare `null`, always null) is taken as false
/// and a non-nullable / non-bool condition (always truthy) as true, so the dead
/// arm is never visited. The typed back end uses this to skip emitting an arm
/// that cannot run -- and the unwrapped `never` values it would otherwise
/// contain (e.g. `a * 2` where `a` is a bare `null`) -- and monomorphization
/// joins an instance's returns and infers its `Result` payloads over the
/// reachable blocks only, so a dead arm's returns and `error(..)` sites do not
/// shape the instance.
pub fn reachable_blocks(
    program: &Program,
    body: &MirBody,
    local_types: &[Type],
    fields: &HashMap<brass_parser::Span, Vec<String>>,
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
                match cond_static_truthiness(program, body, local_types, cond, fields) {
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
/// Folding decides ONLY on the condition, never on the arm's content: every
/// sound fold is decided by the condition itself (an absent member reads
/// `never?` -> false, a present non-nullable one -> true), while a
/// runtime-decided branch whose return conflicts with the function's return
/// type is a type error the checker rejects. Nothing here may prune a
/// runtime-reachable arm.
pub fn cond_static_truthiness(
    program: &Program,
    body: &MirBody,
    local_types: &[Type],
    cond: &Operand,
    fields: &HashMap<brass_parser::Span, Vec<String>>,
) -> Option<bool> {
    if let Some(selected) = fields_test_of(body, cond, fields) {
        return Some(selected);
    }
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
    // A variant test (`match` arm, `if let` of a variant) of a variant no
    // value of the subject's type can hold.
    if uninhabited_variant_test(program, body, local_types, cond) {
        return Some(false);
    }
    operand_type_of(cond, local_types).static_truthiness()
}

/// Whether `cond` is certainly false because it is a variant test of a
/// variant no value of the subject's type can hold (see
/// [`variant_uninhabited`]). Pattern lowering guards the tag test behind
/// the subject's presence test and joins both outcomes into one condition
/// local (`c = false` when absent, `c = value_matches(..)` when present), so
/// a local is certainly false when every value assigned to it is: a `false`
/// constant, such a variant test, or a copy of a local that is -- at least
/// one of them a variant test.
fn uninhabited_variant_test(
    program: &Program,
    body: &MirBody,
    local_types: &[Type],
    cond: &Operand,
) -> bool {
    /// The answer for one operand: `None` when it may be true, else whether
    /// a variant test was among its sources.
    fn certainly_false(
        program: &Program,
        body: &MirBody,
        local_types: &[Type],
        op: &Operand,
        depth: u8,
    ) -> Option<bool> {
        let id = match op {
            Operand::Const(Literal::Bool(false)) => return Some(false),
            Operand::Local(id) if depth > 0 => id,
            _ => return None,
        };
        let mut assigned = false;
        let mut saw_test = false;
        for block in &body.blocks {
            for stmt in &block.stmts {
                let MirStmt::Assign(dest, rv) = stmt else {
                    continue;
                };
                if dest != id {
                    continue;
                }
                assigned = true;
                match rv {
                    Rvalue::Use(inner) => {
                        saw_test |= certainly_false(program, body, local_types, inner, depth - 1)?;
                    }
                    Rvalue::Call(Callee::Builtin(name), args) if name == "value_matches" => {
                        let [subj, Operand::Const(Literal::Str(variant))] = args.as_slice() else {
                            return None;
                        };
                        let ty = operand_type_of(subj, local_types);
                        if !variant_uninhabited(program, unwrap_nullable(&ty), variant) {
                            return None;
                        }
                        saw_test = true;
                    }
                    _ => return None,
                }
            }
        }
        assigned.then_some(saw_test)
    }
    certainly_false(program, body, local_types, cond, 4) == Some(true)
}

/// Whether no value of the sum type `ty` can be the variant `variant`: the
/// variant has a member its declaration leaves open (unannotated), and `ty`
/// does not pin it. A construction of the variant records its open members
/// in the instance type it produces, and joining instances keeps them, so
/// a type that leaves one unpinned was never built as that variant -- an
/// `Opt.Nothing` handed to `show(o: Opt)` makes an instance whose `Some { v }`
/// arm would read a `v` of no type. That arm is dead for the instance (the
/// JIT's variant layout already answers such a test `false`). The generic
/// `Result` is not judged here: an unpinned payload of it is spelled `void`.
fn variant_uninhabited(program: &Program, ty: &Type, variant: &str) -> bool {
    let Type::Sum(n) = ty else {
        return false;
    };
    if n.is_result_type() {
        return false;
    }
    let Some(TypeKind::Sum { variants }) = program.type_by_id(n.id).map(|info| &info.kind) else {
        return false;
    };
    let Some(v) = variants.iter().find(|v| v.name == variant) else {
        return false;
    };
    v.fields.iter().any(|field| {
        field.resolved_ty.as_ref().is_none_or(Type::is_unknown)
            && n.substitution
                .get(&format!("{variant}.{}", field.name))
                .is_none_or(Type::is_unknown)
    })
}

/// The blocks an instance reaches after selecting its checked field expansions
/// and folding its TYPE TESTS against the
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
    fields: &HashMap<brass_parser::Span, Vec<String>>,
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
                let decided = fields_test_of(body, cond, fields).or_else(|| {
                    type_test_of(body, cond).and_then(|(subj, pattern)| {
                        let ty = match subj {
                            Operand::Local(l) => seeded.get(l.index())?.clone()?,
                            Operand::Const(_) => return None,
                        };
                        brass_hir::is_fully_known(&ty)
                            .then(|| brass_typesys::type_test_accepts(program, pattern, &ty))
                    })
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

/// The checker-selected truth of a field-list guard. An absent observation leaves
/// it undecided; monomorphization rejects a live guard without a selection.
fn fields_test_of(
    body: &MirBody,
    cond: &Operand,
    selected: &HashMap<brass_parser::Span, Vec<String>>,
) -> Option<bool> {
    if selected.is_empty() {
        return None;
    }
    let Operand::Local(id) = cond else {
        return None;
    };
    body.blocks
        .iter()
        .flat_map(|block| &block.stmts)
        .find_map(|stmt| {
            if let MirStmt::Assign(dest, Rvalue::FieldsTest { site, fields }) = stmt
                && dest == id
            {
                selected.get(site).map(|names| names == fields)
            } else {
                None
            }
        })
}
