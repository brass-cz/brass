//! Null narrowing: where a nullable binding is known to be non-null, and what
//! ends that knowledge.
//!
//! Only a binding narrows: a local, a parameter or a module global. A
//! `ref(T?)`, `mut(T?)` or `ref(mut(T?))` parameter narrows like any `T?`, to
//! the same wrapper around `T`. A field path never narrows, since a field can
//! be reassigned through any alias of its record; a condition that tests one
//! only records the path, so the diagnostic for a later unchecked read of the
//! field can suggest binding it with `if let` (see
//! `Checker::report_nullable_use`).
//!
//! A test (`if x`, `if x != null`, `while x`, `while x != null`) or a guard
//! (`if !x { .. }` or `if x == null { .. }` with no `else`, whose block leaves
//! through a direct `return`, `break` or `continue`) proves a `T?` binding
//! non-null for a REGION: the then-arm or loop body, or the rest of the
//! guard's block. The proof is a [`Narrowing`] recorded in the innermost scope
//! frame of that region -- never in the frame that declares the binding -- so
//! it ends exactly when the region's frame is popped, whatever the enclosing
//! construct does with its scope stack.
//!
//! A narrowing also ends early, on the path that continues after
//!
//! - an assignment of a possibly-null value to the binding (the assignment is
//!   checked against the DECLARED `T?`; assigning a non-null value keeps the
//!   narrowing),
//! - a call that may run user code, when the callee could rebind the binding:
//!   a module global, a reference parameter, or a local some closure assigns.
//!   Rendering a value whose type declares `display` is such a call, and
//! - a call that takes the binding itself as a `ref(mut(T?))` argument.
//!
//! A null test of a narrowed binding (`if x`, `!x`, `x == null`) tests its
//! declared `T?`: it is always allowed, is no value use of the narrowing, and
//! is never folded statically.
//!
//! Ended narrowings are kept in a per-callable log (`Checker::narrowing_kills`)
//! rather than erased from the frames, because branches check their arms on
//! CLONES of the scope stack: the log is what carries an end out of an arm.
//! A branch join keeps the ends of every arm that falls through (a `break` or
//! `continue` arm's ends go to its loop instead). A narrowing in force at a
//! loop head that the body can end before the next iteration does not hold on
//! that iteration, so its uses inside the loop are reported. A closure literal
//! only trusts a narrowing nothing can end while the closure is alive.

use super::*;

/// Identity of one narrowing: one test or guard that proved a binding
/// non-null. Unique per checker, so an id never aliases across callables.
pub(super) type NarrowId = u32;

/// A nullable binding proven non-null for the region its scope frame covers.
#[derive(Clone)]
pub(super) struct Narrowing {
    name: String,
    id: NarrowId,
    /// The binding's non-null type inside the region.
    ty: Type,
    /// Whether code outside this body can rebind the binding during a call: a
    /// module global (frame 0) or a reference parameter, whose storage is the
    /// caller's.
    aliased: bool,
}

impl Narrowing {
    /// The narrowed binding's source name.
    pub(super) fn name(&self) -> &str {
        &self.name
    }
}

/// What a narrowing lookup found for one name.
struct BindingState {
    /// The type the binding was declared with (the frame's value entry).
    declared: Type,
    /// The live narrowings of that binding, innermost first.
    live: Vec<NarrowId>,
}

/// Syntactic facts about one callable body (a function or method body, or a
/// module's top-level statements) that bound how long a narrowing survives
/// calls and closure capture.
#[derive(Default)]
pub(super) struct NarrowingFacts {
    /// Names assigned anywhere inside a closure literal of the body. A closure
    /// captures by reference, so any call can run one and rebind the name.
    /// Shadowing is not tracked: a closure-local binding of the same name
    /// over-approximates, which only ends narrowings early, never late.
    closure_writes: HashSet<String>,
    /// Source spans of every plain `name = value` statement, by name.
    assignments: HashMap<String, Vec<Span>>,
    /// Source spans of every `while` and `for` statement.
    loops: Vec<Span>,
}

impl NarrowingFacts {
    /// Collect the facts of a callable body's statements.
    pub(super) fn of_stmts(stmts: &[Stmt]) -> Self {
        let mut facts = Self::default();
        for s in stmts {
            facts.stmt(s, false);
        }
        facts
    }

    fn block(&mut self, b: &Block, in_closure: bool) {
        for s in &b.stmts {
            self.stmt(s, in_closure);
        }
    }

    fn stmt(&mut self, stmt: &Stmt, in_closure: bool) {
        match stmt {
            Stmt::Let { value, .. } => {
                if let Some(value) = value {
                    self.expr(value, in_closure);
                }
            }
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => {
                if let Expr::Ident(name, _) = target {
                    if in_closure {
                        self.closure_writes.insert(name.clone());
                    }
                    if matches!(op, AssignOp::Eq) {
                        self.assignments
                            .entry(name.clone())
                            .or_default()
                            .push(span.source_span());
                    }
                }
                self.expr(target, in_closure);
                self.expr(value, in_closure);
            }
            Stmt::Expr(e) => self.expr(e, in_closure),
            Stmt::While { cond, body, span } => {
                self.loops.push(span.source_span());
                self.expr(cond, in_closure);
                self.block(body, in_closure);
            }
            Stmt::For {
                iter, body, span, ..
            } => {
                self.loops.push(span.source_span());
                self.expr(iter, in_closure);
                self.block(body, in_closure);
            }
            Stmt::Return(value, _) => {
                if let Some(e) = value {
                    self.expr(e, in_closure);
                }
            }
            Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }

    fn expr(&mut self, expr: &Expr, in_closure: bool) {
        match expr {
            Expr::Closure(_, body, _) => self.expr(body, true),
            Expr::Block(b, _) => self.block(b, in_closure),
            Expr::Unary(_, inner, _)
            | Expr::ErrorProp(inner, _)
            | Expr::TypeTest(inner, _, _, _)
            | Expr::Field(inner, _, _) => self.expr(inner, in_closure),
            Expr::Binary(_, a, b, _) | Expr::Range(a, b, _) | Expr::Index(a, b, _) => {
                self.expr(a, in_closure);
                self.expr(b, in_closure);
            }
            Expr::Call(callee, args, _) => {
                self.expr(callee, in_closure);
                for a in args {
                    self.expr(&a.expr, in_closure);
                }
            }
            Expr::Array(items, _) => {
                for e in items {
                    self.expr(e, in_closure);
                }
            }
            Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
                for (_, e) in fields {
                    self.expr(e, in_closure);
                }
            }
            Expr::Str(segs, _) => {
                for seg in segs {
                    if let StrSeg::Expr(e) = seg {
                        self.expr(e, in_closure);
                    }
                }
            }
            Expr::If(cond, then, els, _) => {
                self.expr(cond, in_closure);
                self.block(then, in_closure);
                if let Some(e) = els {
                    self.expr(e, in_closure);
                }
            }
            Expr::IfLet(_, scrut, then, els, _) => {
                self.expr(scrut, in_closure);
                self.block(then, in_closure);
                if let Some(e) = els {
                    self.expr(e, in_closure);
                }
            }
            Expr::Match(scrut, arms, _) => {
                self.expr(scrut, in_closure);
                for arm in arms {
                    self.expr(&arm.body, in_closure);
                }
            }
            Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(_)
            | Expr::Ident(..)
            | Expr::SelfExpr(_) => {}
        }
    }

    /// Whether some assignment to `name` can run after a closure created at
    /// `closure` (a source span): one written after it, or one sharing a loop
    /// with it (the next iteration runs it after the closure exists).
    fn assigned_after(&self, name: &str, closure: Span) -> bool {
        let Some(sites) = self.assignments.get(name) else {
            return false;
        };
        let contains = |outer: &Span, inner: &Span| outer.lo <= inner.lo && inner.hi <= outer.hi;
        sites.iter().any(|site| {
            site.lo >= closure.lo
                || self
                    .loops
                    .iter()
                    .any(|l| contains(l, site) && contains(l, &closure))
        })
    }
}

/// Whether `a OP b` compares a plain name with `null`, a null test whose
/// operand is no value use of a narrowing.
pub(super) fn is_null_test(op: BinOp, a: &Expr, b: &Expr) -> bool {
    matches!(op, BinOp::Eq | BinOp::Ne)
        && matches!(
            (a, b),
            (Expr::Ident(..), Expr::Null(_)) | (Expr::Null(_), Expr::Ident(..))
        )
}

/// Whether the block leaves unconditionally through a direct `return`,
/// `break` or `continue` statement, so nothing after the enclosing statement
/// runs on its path. Narrowing after a guard relies on this.
fn block_always_leaves(block: &Block) -> bool {
    block
        .stmts
        .iter()
        .any(|s| matches!(s, Stmt::Return(..) | Stmt::Break(_) | Stmt::Continue(_)))
}

impl<'a> Checker<'a> {
    /// The type of `name` at this point: the innermost live narrowing of the
    /// binding when one is in force, else the binding's declared type.
    pub(super) fn lookup(&self, scopes: &ScopeStack, name: &str) -> Option<Type> {
        scopes.iter().rev().find_map(|frame| {
            frame
                .narrowings
                .iter()
                .rev()
                .find(|n| n.name == name && self.narrowing_live(n.id))
                .map(|n| n.ty.clone())
                .or_else(|| frame.get(name).cloned())
        })
    }

    fn narrowing_live(&self, id: NarrowId) -> bool {
        !self.narrowing_kills.contains(&id)
    }

    /// The declared type of the binding `name` resolves to here, with its
    /// live narrowings. A frame's narrowings always postdate its value entry
    /// (a new binding drops them, see `Scope::insert`), so collecting them
    /// before reading the entry is correct.
    fn binding_state(&self, scopes: &ScopeStack, name: &str) -> Option<(BindingState, usize)> {
        let mut live = Vec::new();
        for (index, frame) in scopes.iter().enumerate().rev() {
            live.extend(
                frame
                    .narrowings
                    .iter()
                    .rev()
                    .filter(|n| n.name == name && self.narrowing_live(n.id))
                    .map(|n| n.id),
            );
            if let Some(declared) = frame.get(name) {
                let declared = declared.clone();
                return Some((BindingState { declared, live }, index));
            }
        }
        None
    }

    /// The type a plain `name = value` stores into when `name` is narrowed
    /// here: its declared nullable type. `None` when it is not narrowed.
    pub(super) fn narrowed_declared_type(&self, scopes: &ScopeStack, name: &str) -> Option<Type> {
        let (state, _) = self.binding_state(scopes, name)?;
        (!state.live.is_empty()).then_some(state.declared)
    }

    /// End the narrowings of `name` after `name = value` stored a value of
    /// type `stored`, unless that value is certainly non-null (then the
    /// binding stays narrowed).
    pub(super) fn after_rebinding(&mut self, scopes: &ScopeStack, name: &str, stored: &Type) {
        if !self.may_be_null(stored) {
            return;
        }
        if let Some((state, _)) = self.binding_state(scopes, name) {
            self.narrowing_kills.extend(state.live);
        }
    }

    /// The declared type of a narrowed binding passed as the argument `expr`
    /// to a write-through `ref(mut(T))` parameter (`want`). The parameter
    /// refers to the binding itself, not to its narrowed view, so the argument
    /// is the declared `T?`; and since the callee holds a mutable reference to
    /// the binding, the narrowing ends with the call, as it does for any
    /// binding a call can reach through a reference. `None` when `expr` is not
    /// a narrowed binding or `want` is not a mutable reference.
    pub(super) fn narrowed_ref_mut_argument(
        &mut self,
        expr: &Expr,
        want: &Type,
        scopes: &ScopeStack,
    ) -> Option<Type> {
        let Expr::Ident(name, _) = expr else {
            return None;
        };
        let Type::Ref(referent) = self.resolve(want) else {
            return None;
        };
        if !matches!(self.resolve(&referent), Type::Mut(_)) {
            return None;
        }
        let declared = self.narrowed_declared_type(scopes, name)?;
        self.after_rebinding(scopes, name, &declared);
        Some(declared)
    }

    /// Whether a stored value of type `ty` can be null. A still-open type is
    /// not: a generic body is checked again for each instantiation, where the
    /// value's real type decides.
    fn may_be_null(&self, ty: &Type) -> bool {
        matches!(peel_ref_mut(&self.resolve(ty)), Type::Nullable(_))
    }

    /// `if x` / `if x != null` (or `while`): the binding `x` is non-null for
    /// the region of the innermost frame, which the caller pushed for the
    /// then-arm or loop body. A tested field path is only noted there (see
    /// `Scope::tested_fields`).
    pub(super) fn apply_truthy_narrowing(&mut self, cond: &Expr, scopes: &mut ScopeStack) {
        if let Some(name) = narrow::truthy_narrows(cond) {
            self.narrow_non_null(name, scopes);
        }
        if let Some(path) = narrow::truthy_field_path(cond)
            && let Some(frame) = scopes.last_mut()
        {
            frame.tested_fields.push(path);
        }
    }

    /// `if !x { return }` (or `break`/`continue`, or `x == null`): the rest of
    /// the enclosing block runs only when `x` is non-null. A tested field path
    /// is only noted, as in [`Self::apply_truthy_narrowing`].
    pub(super) fn apply_guard_narrowing(&mut self, stmt: &Stmt, scopes: &mut ScopeStack) {
        let Stmt::Expr(Expr::If(cond, then, None, _)) = stmt else {
            return;
        };
        if !block_always_leaves(then) {
            return;
        }
        if let Some(name) = narrow::falsy_narrows(cond) {
            self.narrow_non_null(name, scopes);
        }
        if let Some(path) = narrow::falsy_field_path(cond)
            && let Some(frame) = scopes.last_mut()
        {
            frame.tested_fields.push(path);
        }
    }

    /// Note a read of the field `expr` (of type `ty`) when it is nullable and
    /// a condition of an enclosing region tested the same field path (see
    /// [`Checker::tested_field_reads`]).
    pub(super) fn note_tested_field_read(&mut self, expr: &Expr, ty: &Type, scopes: &ScopeStack) {
        if !matches!(self.resolve(ty), Type::Nullable(_)) {
            return;
        }
        let Some(path) = narrow::field_path(expr) else {
            return;
        };
        if scopes
            .iter()
            .any(|frame| frame.tested_fields.contains(&path))
        {
            self.tested_field_reads.insert(expr.span(), path);
        }
    }

    /// Record that `name` is non-null for the region of the innermost frame.
    /// A `ref(T?)`, `mut(T?)` or `ref(mut(T?))` parameter narrows to the same
    /// wrapper around `T`.
    fn narrow_non_null(&mut self, name: &str, scopes: &mut ScopeStack) {
        // A test of an already-narrowed name still records a narrowing of its
        // own: the region's uses then belong to this test, not to an outer
        // one a loop may end.
        let Some((state, decl_frame)) = self.binding_state(scopes, name) else {
            return;
        };
        let declared = self.resolve(&state.declared);
        let Some(ty) = non_null_view(&declared) else {
            return;
        };
        tracing::debug!(name, to = %ty.display(), "narrowing nullable to non-null");
        // A `mut(T?)` parameter is the callee's own deep copy: no callee can
        // rebind it, unlike a module global or a `ref` parameter.
        let aliased = decl_frame == 0 || matches!(declared, Type::Ref(_));
        let id = self.next_narrowing;
        self.next_narrowing += 1;
        if let Some(frame) = scopes.last_mut() {
            frame.narrowings.push(Narrowing {
                name: name.to_string(),
                id,
                ty,
                aliased,
            });
        }
    }

    /// End the narrowings a call may invalidate: those of bindings a callee
    /// can rebind (a global or reference parameter, see
    /// [`Narrowing::aliased`]) and of locals some closure of this body
    /// assigns (the call may run that closure). Plain locals stay narrowed:
    /// no callee can rebind them.
    pub(super) fn invalidate_narrowed_after_call(&mut self, scopes: &ScopeStack) {
        let ended: Vec<NarrowId> = scopes
            .iter()
            .flat_map(|frame| &frame.narrowings)
            .filter(|n| {
                self.narrowing_live(n.id)
                    && (n.aliased || self.narrowing_facts.closure_writes.contains(&n.name))
            })
            .map(|n| n.id)
            .collect();
        if !ended.is_empty() {
            tracing::debug!(
                count = ended.len(),
                "re-widening narrowed bindings after call"
            );
            self.narrowing_kills.extend(ended);
        }
    }

    /// Rendering can invoke a top-level display or debug methods at any
    /// structural depth. Those calls invalidate mutable narrowings like explicit calls.
    pub(super) fn invalidate_after_rendering(&mut self, ty: &Type, scopes: &ScopeStack) {
        self.invalidate_after_rendering_form(ty, brass_hir::rendering::RenderForm::Display, scopes);
    }

    /// Apply the same call-effect rule to explicit structural debug rendering.
    pub(super) fn invalidate_after_rendering_form(
        &mut self,
        ty: &Type,
        form: brass_hir::rendering::RenderForm,
        scopes: &ScopeStack,
    ) {
        if brass_hir::rendering::rendering_runs_code(self.program, &self.resolve(ty), form) {
            self.invalidate_narrowed_after_call(scopes);
        }
    }

    /// The scope stack a closure literal at `closure` captures: the current
    /// one, keeping only the narrowings nothing can end while the closure is
    /// alive. The closure may run at any later point, so a binding that is
    /// reassigned after the literal (or anywhere in a loop around it), that
    /// some closure assigns, or that a callee can rebind, is seen with its
    /// declared nullable type inside the closure.
    pub(super) fn closure_capture_scopes(&self, scopes: &ScopeStack, closure: Span) -> ScopeStack {
        let at = closure.source_span();
        let facts = &self.narrowing_facts;
        let mut captured = scopes.clone();
        for frame in &mut captured {
            frame.narrowings.retain(|n| {
                self.narrowing_live(n.id)
                    && !n.aliased
                    && !facts.closure_writes.contains(&n.name)
                    && !facts.assigned_after(&n.name, at)
            });
        }
        captured
    }

    /// A position in the narrowing-end log, taken before a branch arm or a
    /// speculative walk (see [`Self::narrowing_ends_since`]).
    pub(super) fn narrowing_mark(&self) -> usize {
        self.narrowing_kills.len()
    }

    /// Remove and return the narrowing ends recorded since `mark`, so a
    /// sibling arm starts from the state before the branch. The caller routes
    /// each arm's ends with [`Self::route_arm_ends`], or drops those of a
    /// speculative walk.
    pub(super) fn narrowing_ends_since(&mut self, mark: usize) -> Vec<NarrowId> {
        self.narrowing_kills.split_off(mark)
    }

    /// Carry the narrowings one branch arm ended to where its path continues:
    /// the join after the branch when the arm falls through, the code after
    /// the innermost loop when it `break`s, that loop's next iteration when it
    /// `continue`s, and nowhere when it returns or is statically dead.
    pub(super) fn route_arm_ends(&mut self, ends: Vec<NarrowId>, exit: ArmExit) {
        match exit {
            ArmExit::FallsThrough => self.narrowing_kills.extend(ends),
            ArmExit::Breaks => {
                if let Some(frame) = self.loop_frames.last_mut() {
                    frame.exit_ends.extend(ends);
                }
            }
            ArmExit::Continues => {
                if let Some(frame) = self.loop_frames.last_mut() {
                    frame.next_ends.extend(ends);
                }
            }
            ArmExit::Returns | ArmExit::Dead => {}
        }
    }

    /// Check one loop (its condition, when it has one, and its body, through
    /// `pass`). A narrowing in force at the loop head that the body can end
    /// before a later iteration does not hold on that iteration, so every use
    /// of it inside the loop -- typed non-null while checking -- is reported.
    /// The loop is checked once; a variable it may null must be checked again
    /// inside the loop.
    pub(super) fn check_loop(
        &mut self,
        scopes: &mut ScopeStack,
        pass: impl FnOnce(&mut Self, &mut ScopeStack),
    ) {
        let head: Vec<NarrowId> = scopes
            .iter()
            .flat_map(|frame| &frame.narrowings)
            .filter(|n| self.narrowing_live(n.id))
            .map(|n| n.id)
            .collect();
        self.loop_frames.push(LoopFrame {
            head,
            ..LoopFrame::default()
        });
        let mark = self.narrowing_mark();
        pass(self, scopes);
        let frame = self.loop_frames.pop().expect("the loop frame pushed above");
        // The ends that reach the next iteration: those of the paths running
        // off the end of the body, and of the paths that `continue`.
        let reaches_head = |id: &NarrowId| {
            self.narrowing_kills[mark..].contains(id) || frame.next_ends.contains(id)
        };
        let ended: Vec<NarrowId> = frame.head.iter().copied().filter(reaches_head).collect();
        for (id, name, span) in &frame.uses {
            if ended.contains(id) {
                self.report_stale_narrowing(name, *span);
            }
        }
        // After the loop, the ends of every path that leaves it hold.
        self.narrowing_kills.extend(frame.next_ends);
        self.narrowing_kills.extend(frame.exit_ends);
    }

    fn report_stale_narrowing(&mut self, name: &str, span: Span) {
        let message = format!(
            "nullable value must be checked for null before use: `{name}` was checked before \
             this loop, but the loop can make it null again before a later iteration; check \
             it inside the loop"
        );
        if !self
            .errors
            .iter()
            .any(|e| e.span == span && e.message == message)
        {
            self.errors.push(TypeError { message, span });
        }
    }

    /// Note a value use of `name` at `span` for the loops being checked: a
    /// use of a narrowing from a loop's head is reported if the loop turns out
    /// to end it (see [`Self::check_loop`]). A null-test operand (`if x`,
    /// `!x`, `x == null`) is no such use: its meaning does not depend on the
    /// narrowing.
    pub(super) fn note_narrowed_use(&mut self, scopes: &ScopeStack, name: &str, span: Span) {
        if self.loop_frames.is_empty() || self.null_test_operand || self.discarded_walks > 0 {
            return;
        }
        let Some(id) = self.narrowing_in_force(scopes, name) else {
            return;
        };
        for frame in &mut self.loop_frames {
            if frame.head.contains(&id) {
                frame.uses.push((id, name.to_string(), span));
            }
        }
    }

    /// The innermost live narrowing `name` resolves to here, if any.
    fn narrowing_in_force(&self, scopes: &ScopeStack, name: &str) -> Option<NarrowId> {
        for frame in scopes.iter().rev() {
            if let Some(n) = frame
                .narrowings
                .iter()
                .rev()
                .find(|n| n.name == name && self.narrowing_live(n.id))
            {
                return Some(n.id);
            }
            if frame.contains_key(name) {
                return None;
            }
        }
        None
    }

    /// Type the operand of a null test (`if x`, `!x`, `x == null`): a plain
    /// name there is not a value use for [`Self::note_narrowed_use`].
    pub(super) fn check_null_test_operand(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        if !matches!(e, Expr::Ident(..)) {
            return self.check_expr(e, scopes);
        }
        let saved = std::mem::replace(&mut self.null_test_operand, true);
        let ty = self.check_expr(e, scopes);
        self.null_test_operand = saved;
        ty
    }

    /// Whether `cond` is a plain name whose non-null-ness here comes from a
    /// narrowing. Such a test is not decided by the variable's type, and the
    /// back end, which only sees the declared `T?`, emits both arms; the
    /// checker must not fold it statically either.
    pub(super) fn is_narrowed_test(&self, cond: &Expr, scopes: &ScopeStack) -> bool {
        matches!(cond, Expr::Ident(name, _) if self.narrowing_in_force(scopes, name).is_some())
    }

    /// Run a walk whose diagnostics are discarded when `discard` is set (a
    /// statically dead arm, a speculative probe): the uses it makes are not
    /// uses of the program that loop verification judges.
    pub(super) fn discarded_walk<T>(
        &mut self,
        discard: bool,
        walk: impl FnOnce(&mut Self) -> T,
    ) -> T {
        if !discard {
            return walk(self);
        }
        self.discarded_walks += 1;
        let out = walk(self);
        self.discarded_walks -= 1;
        out
    }

    /// Run `check` with no enclosing loop or narrowing-end state: a closure
    /// body or another callable's body is not part of the current path.
    pub(super) fn with_detached_flow<T>(&mut self, check: impl FnOnce(&mut Self) -> T) -> T {
        let saved_loops = std::mem::take(&mut self.loop_frames);
        let saved_test = std::mem::replace(&mut self.null_test_operand, false);
        let mark = self.narrowing_mark();
        let out = check(self);
        self.narrowing_kills.truncate(mark);
        self.null_test_operand = saved_test;
        self.loop_frames = saved_loops;
        out
    }
}

/// The narrowing bookkeeping of one loop being checked.
#[derive(Clone, Default)]
pub(super) struct LoopFrame {
    /// The narrowings in force when the loop is entered.
    head: Vec<NarrowId>,
    /// Value uses of head narrowings inside the loop: id, name and span.
    uses: Vec<(NarrowId, String, Span)>,
    /// Narrowings ended on paths that `break` out of the loop.
    exit_ends: Vec<NarrowId>,
    /// Narrowings ended on paths that `continue` with the next iteration.
    next_ends: Vec<NarrowId>,
}

/// How a branch arm leaves, which decides where the narrowings it ends
/// matter (see [`Checker::route_arm_ends`]).
#[derive(Clone, Copy)]
pub(super) enum ArmExit {
    FallsThrough,
    Returns,
    Breaks,
    Continues,
    /// The arm is statically unreachable.
    Dead,
}

impl ArmExit {
    /// How a block arm leaves: through its first direct `return`, `break`
    /// or `continue` statement (the statements after it are unreachable), or
    /// by falling through.
    pub(super) fn of_block(b: &Block) -> Self {
        b.stmts
            .iter()
            .find_map(|s| match s {
                Stmt::Return(..) => Some(Self::Returns),
                Stmt::Break(_) => Some(Self::Breaks),
                Stmt::Continue(_) => Some(Self::Continues),
                _ => None,
            })
            .unwrap_or(Self::FallsThrough)
    }

    /// As [`Self::of_block`] for an arm written as an expression (an `else`
    /// or `match` arm): only a braced block is inspected.
    pub(super) fn of_expr(e: &Expr) -> Self {
        match e {
            Expr::Block(b, _) => Self::of_block(b),
            _ => Self::FallsThrough,
        }
    }

    /// `exit` unless `dead`, in which case the arm never runs.
    pub(super) fn unless_dead(self, dead: bool) -> Self {
        if dead { Self::Dead } else { self }
    }
}

/// The non-null view of a nullable binding type, seeing through reference
/// wrappers (a `ref(mut(T?))` parameter narrows to `ref(mut(T))`). `None` when
/// the type is not nullable.
fn non_null_view(ty: &Type) -> Option<Type> {
    match ty {
        Type::Nullable(inner) => Some((**inner).clone()),
        Type::Ref(inner) => non_null_view(inner).map(|t| Type::Ref(Box::new(t))),
        Type::Mut(inner) => non_null_view(inner).map(|t| Type::Mut(Box::new(t))),
        _ => None,
    }
}
