//! Promotion of constant array literals to once-initialized module globals.
//!
//! An array literal whose elements are all constant scalars (`[1, 2, 3]`)
//! costs two heap allocations (object + element buffer) every time it is
//! evaluated. When such a literal is only ever *read* -- indexed, measured,
//! or passed to parameters that never write through or leak it -- the value
//! each evaluation produces is indistinguishable from a single shared one, so
//! the literal is rewritten into a read of a synthetic global constructed
//! once by a dedicated init body that runs before every other init. The
//! rewrite happens on the shared MIR, so the JIT and the REPL interpreter
//! behave identically; the JIT's immutable-global auto-freeze then makes the
//! promoted arrays safely shareable across threads.
//!
//! Soundness rests on two analyses over the lowered program:
//!
//! - **Callee parameter safety** (interprocedural fixpoint): a parameter is
//!   safe when its body only reads it. A parameter the body mutates is
//!   received as a private deep copy (`bind_params` emits `__deep_copy`), so
//!   its formal's only use IS the copy call and it classifies safe; only an
//!   explicit write-through `ref(mut(T))` parameter mutates the formal
//!   directly and classifies unsafe. Escapes (returned, stored, captured,
//!   spawned, forwarded to an unsafe position) are unsafe, because an alias
//!   stored into mutable structure could later be written through
//!   (`g[0][0] = 5` must not corrupt a shared literal).
//! - **Use-site safety** (per body): every use of the literal's local, traced
//!   through `Use`-copy aliases, must be one of the whitelisted read forms.
//!   Anything unrecognized keeps the per-evaluation allocation.

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use crate::builder::BodyBuilder;
use crate::cfg::{MirBody, MirStmt, Terminator};
use crate::ids::LocalId;
use crate::program::{MirInit, MirProgram};
use crate::ty::TypeRef;
use crate::value::{Callee, Literal, Operand, Place, Rvalue};

/// Rewrite every safely promotable constant array literal in `program` into a
/// read of a synthetic global, and prepend the init body that constructs the
/// globals. Bodies are left untouched when nothing promotes.
pub fn promote_const_array_literals(program: &mut MirProgram) {
    let safe = safe_params(program);
    let mut globals = PromotedGlobals::default();

    for f in &mut program.functions {
        promote_in_body(&mut f.body, &safe, &mut globals);
    }
    for m in &mut program.methods {
        promote_in_body(&mut m.body, &safe, &mut globals);
    }
    for init in &mut program.inits {
        promote_in_body(&mut init.body, &safe, &mut globals);
    }

    if globals.order.is_empty() {
        return;
    }
    // The construction init must run before any body that reads the globals:
    // init symbols are positional ($init0..), so it is prepended. Its module
    // is `main` so a typed-subset failure inside it (impossible for
    // const-scalar arrays, but load-bearing if the subset ever shrinks)
    // surfaces as a hard error instead of being skipped best-effort.
    let mut b = BodyBuilder::new();
    for name in &globals.order {
        let (elems, known) = &globals.defs[name];
        let elems = elems.iter().cloned().map(Operand::Const).collect();
        // The literal's checker-seeded type (a non-default element width such
        // as `int64[]`) must carry over, or monomorphization would type the
        // global at the elements' default width while call sites read it at
        // the seeded one.
        let value = match known {
            Some(t) => b.emit_known(Rvalue::Array(elems), t.clone()),
            None => b.emit(Rvalue::Array(elems)),
        };
        b.push(MirStmt::SetGlobal(name.clone(), value));
    }
    b.terminate(Terminator::Return(Operand::void()));
    program.inits.insert(
        0,
        MirInit {
            module: vec!["main".to_string()],
            body: b.finish(Vec::new(), crate::ids::BlockId(0)),
        },
    );
}

/// The promoted globals: definition per synthetic name, in first-seen order
/// (kept for deterministic init layout). Identical literals share one global.
#[derive(Default)]
struct PromotedGlobals {
    defs: HashMap<String, (Vec<Literal>, Option<brass_hir::Type>)>,
    keys: HashMap<String, String>,
    order: Vec<String>,
}

impl PromotedGlobals {
    /// The global holding `elems` at `known` type, allocating a name on first
    /// use. The `@consts` suffix cannot collide with user globals, which are
    /// always keyed `name@<module path>`.
    fn global_for(&mut self, elems: &[Literal], known: Option<&brass_hir::Type>) -> String {
        let key = format!(
            "{elems:?}|{}",
            known.map(|t| t.display()).unwrap_or_default()
        );
        if let Some(name) = self.keys.get(&key) {
            return name.clone();
        }
        let name = format!("__arr{}@consts", self.order.len());
        self.keys.insert(key, name.clone());
        self.defs
            .insert(name.clone(), (elems.to_vec(), known.cloned()));
        self.order.push(name.clone());
        name
    }
}

/// Per-function parameter safety: `safe[symbol][i]` is true when a value
/// passed as argument `i` is only read by the callee (directly and through
/// everything the callee forwards it to). Computed as a falling fixpoint:
/// every parameter starts safe and loses safety when its body uses it outside
/// the read whitelist under the current assumptions.
fn safe_params(program: &MirProgram) -> HashMap<String, Vec<bool>> {
    let mut safe: HashMap<String, Vec<bool>> = program
        .functions
        .iter()
        .map(|f| (f.symbol.clone(), vec![true; f.body.params.len()]))
        .collect();
    loop {
        let mut changed = false;
        for f in &program.functions {
            for (i, &param) in f.body.params.iter().enumerate() {
                if !safe[&f.symbol][i] {
                    continue;
                }
                if !uses_are_read_only(&f.body, param, &safe) {
                    safe.get_mut(&f.symbol).unwrap()[i] = false;
                    changed = true;
                }
            }
        }
        if !changed {
            return safe;
        }
    }
}

/// Whether every use of `root` in `body` is a whitelisted read. Copies made
/// with `Assign(x, Use(root))` (a `let` binding, `make_local`) extend the
/// tracked set to `x`; each tracked local must be written by exactly one
/// `Assign` statement (its defining one), because a slot reassigned elsewhere
/// would alias a different value at some uses.
fn uses_are_read_only(body: &MirBody, root: LocalId, safe: &HashMap<String, Vec<bool>>) -> bool {
    // Grow the alias set to a fixpoint before classifying uses.
    let mut tracked: HashSet<LocalId> = HashSet::from_iter([root]);
    loop {
        let mut grew = false;
        for block in &body.blocks {
            for stmt in &block.stmts {
                if let MirStmt::Assign(x, Rvalue::Use(Operand::Local(a))) = stmt
                    && tracked.contains(a)
                    && tracked.insert(*x)
                {
                    grew = true;
                }
            }
        }
        if !grew {
            break;
        }
    }

    let tracked_op = |op: &Operand| matches!(op, Operand::Local(a) if tracked.contains(a));
    let mut assigns: HashMap<LocalId, usize> = HashMap::default();
    for block in &body.blocks {
        for stmt in &block.stmts {
            match stmt {
                MirStmt::Assign(x, rv) => {
                    if tracked.contains(x) {
                        *assigns.entry(*x).or_insert(0) += 1;
                    }
                    if !rvalue_reads_only(rv, &tracked_op, safe) {
                        return false;
                    }
                }
                MirStmt::Eval(rv) => {
                    if !rvalue_reads_only(rv, &tracked_op, safe) {
                        return false;
                    }
                }
                // Stored as a value: escapes into mutable structure. Stored
                // into: an element write-through.
                MirStmt::Store(place, value) => {
                    if tracked_op(value)
                        || tracked.contains(&place.local)
                        || place_mentions_tracked_index(place, &tracked_op)
                    {
                        return false;
                    }
                }
                MirStmt::SetGlobal(_, op) => {
                    if tracked_op(op) {
                        return false;
                    }
                }
            }
        }
        match &block.term {
            Terminator::Return(op) => {
                if tracked_op(op) {
                    return false;
                }
            }
            Terminator::CondBranch { cond, .. } => {
                if tracked_op(cond) {
                    return false;
                }
            }
            Terminator::Goto(_) | Terminator::Unreachable => {}
        }
    }
    // A tracked local written by more than one statement holds a different
    // value at some program points; a root that is a parameter has no
    // defining Assign, so any write to it is a reassignment.
    for (local, count) in assigns {
        let limit = if local == root && body.params.contains(&root) {
            0
        } else {
            1
        };
        if count > limit {
            return false;
        }
    }
    true
}

/// Whether an rvalue's uses of tracked locals are all reads. Rvalues that do
/// not mention a tracked local are vacuously fine.
fn rvalue_reads_only(
    rv: &Rvalue,
    tracked_op: &dyn Fn(&Operand) -> bool,
    safe: &HashMap<String, Vec<bool>>,
) -> bool {
    match rv {
        // The alias-extending copy: its target local joined the tracked set,
        // so its own uses are classified like the root's.
        Rvalue::Use(_) => true,
        // An indexed element read. A tracked local can only be the base;
        // an index is scalar, so a tracked local showing up there means the
        // analysis lost track -- refuse.
        Rvalue::Load(place) => !place_mentions_tracked_index(place, tracked_op),
        // Forwarding to a parameter that is itself read-only, at every
        // position the tracked value occupies.
        Rvalue::Call(Callee::Free(sym), args) => args.iter().enumerate().all(|(i, a)| {
            !tracked_op(a)
                || safe
                    .get(sym)
                    .and_then(|params| params.get(i))
                    .copied()
                    .unwrap_or(false)
        }),
        // Reading the length is pure; `__deep_copy` (a mutated parameter's
        // entry copy) produces an independent value, leaving the original
        // untouched.
        Rvalue::Call(Callee::Builtin(b), args) if b == "array_len" || b == "__deep_copy" => {
            let _ = args;
            true
        }
        // `.len()` in method form (`a.len()`, what user code lowers to; the
        // `for` desugar uses the `array_len` builtin above) reads only its
        // receiver.
        Rvalue::Call(Callee::Method(m), args) if m == "len" && args.len() == 1 => true,
        // Everything else -- methods (push/insert/user), builtins, indirect
        // calls, aggregate construction, views, closures, operators -- is
        // conservatively a leak or a write when it mentions a tracked local.
        Rvalue::Call(_, args) => !args.iter().any(tracked_op),
        Rvalue::Bin(_, a, b) => !tracked_op(a) && !tracked_op(b),
        Rvalue::Un(_, a) => !tracked_op(a),
        Rvalue::Global(_) => true,
        Rvalue::Array(ops) => !ops.iter().any(tracked_op),
        Rvalue::Record { fields, .. } => !fields.iter().any(|(_, v)| tracked_op(v)),
        Rvalue::Variant { fields, .. } => !fields.iter().any(|(_, v)| tracked_op(v)),
        Rvalue::RecordFrom { source, .. } | Rvalue::RecordView { source, .. } => {
            !tracked_op(source)
        }
        Rvalue::Closure { captures, .. } => !captures.iter().any(tracked_op),
        // `typeof(x)` consults only the operand's type, never its value.
        Rvalue::TypeName(_) => true,
    }
}

/// Whether `place` uses a tracked local anywhere it must not appear: as a
/// non-Index projection base is fine (the base read is the whitelisted form),
/// but a tracked local inside an Index operand is out of model.
fn place_mentions_tracked_index(place: &Place, tracked_op: &dyn Fn(&Operand) -> bool) -> bool {
    place.proj.iter().any(|p| match p {
        crate::value::Projection::Index(op) => tracked_op(op),
        crate::value::Projection::Field(_) => false,
    })
}

/// Promote every eligible literal in one body, rewriting its defining assign
/// into a global read.
fn promote_in_body(
    body: &mut MirBody,
    safe: &HashMap<String, Vec<bool>>,
    globals: &mut PromotedGlobals,
) {
    // Collect first (the safety scan borrows the body immutably).
    let mut promotions: Vec<(usize, usize, LocalId, String)> = Vec::new();
    for (bi, block) in body.blocks.iter().enumerate() {
        for (si, stmt) in block.stmts.iter().enumerate() {
            let MirStmt::Assign(local, Rvalue::Array(elems)) = stmt else {
                continue;
            };
            let Some(consts) = const_scalar_elems(elems) else {
                continue;
            };
            if !uses_are_read_only(body, *local, safe) {
                continue;
            }
            let known = match &body.locals[local.index()].ty {
                TypeRef::Known(t) => Some(t.clone()),
                TypeRef::Var(_) => None,
            };
            let name = globals.global_for(&consts, known.as_ref());
            promotions.push((bi, si, *local, name));
        }
    }
    for (bi, si, local, name) in promotions {
        body.blocks[bi].stmts[si] = MirStmt::Assign(local, Rvalue::Global(name));
    }
}

/// The element literals when every element is a constant scalar (int, float,
/// bool) and there is at least one. Strings are heap values and `null`/`void`
/// have no scalar layout, so they keep the per-evaluation path; an empty
/// literal is a growable-array seed, never worth sharing.
fn const_scalar_elems(elems: &[Operand]) -> Option<Vec<Literal>> {
    if elems.is_empty() {
        return None;
    }
    elems
        .iter()
        .map(|op| match op {
            Operand::Const(l @ (Literal::Int(_) | Literal::Float(_) | Literal::Bool(_))) => {
                Some(l.clone())
            }
            _ => None,
        })
        .collect()
}
