//! Row inference: what a callable body requires of each unannotated parameter
//! that may receive an anonymous (structural) value.
//!
//! For every unannotated, non-`self` parameter of every free function, the body
//! is scanned for field accesses and the way each field is used, producing a
//! [`Row`]: the set of field names with, per field,
//!
//! - a [`Presence`]: `Required` when the body reads/writes the field
//!   unguarded (rendering a field is a read too), `Guarded` when every access
//!   is dominated by a truthiness / `if let` test of that same field;
//! - a [`RowTy`]: `Forced(T)` when an unambiguous use pins a primitive type
//!   (the field flows into a `T`-annotated parameter, `let x: T =`, or a
//!   declared primitive return), otherwise `Open` (the argument's own field
//!   type flows through).
//!
//! A parameter forwarded whole into another unannotated free-function
//! parameter unions that callee's row (an interprocedural least fixpoint, the
//! same shape as `brass_hir::mutation`); forwarding into an ineligible one
//! makes it ineligible too. Any use that a reduced field set could not honor
//! -- method receiver use, escaping into a store / return / closure capture,
//! being passed to an annotated or unknown position -- marks the parameter
//! *view-ineligible*: its row is still derived for diagnostics, but the call
//! boundary must keep the argument's full value.
//!
//! Consumers: the checker validates each anonymous argument to a free
//! function's parameter against the callee row at the argument's own span,
//! and (for eligible parameters) both the checker's body elaboration and
//! monomorphization use the argument's *view* (see [`view_type`]), collapsing
//! every argument shape with the same view into one compiled instance.

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::collections::BTreeMap;

use brass_hir::{Program, Type};
use brass_parser::ast::{Arg, Block, Expr, Pattern, Stmt, StrSeg, TypeExpr};

use crate::flow::{Flow, numeric_flow};

/// Whether a field may be absent at the call site.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Presence {
    /// Every access is dominated by a truthiness/`if let` test of the field
    /// itself; an absent field takes the fallback path.
    Guarded,
    /// The body uses the field unguarded; the caller must supply it.
    Required,
}

/// What the body requires of a field's type.
#[derive(Clone, Debug, PartialEq)]
pub enum RowTy {
    /// An unambiguous use pins this primitive type; the argument's field must
    /// flow into it (identity or value-preserving widening).
    Forced(Type),
    /// The body only moves/renders/tests the field; the argument's own field
    /// type flows through and becomes part of the instance key.
    Open,
}

/// One field of a row.
#[derive(Clone, Debug, PartialEq)]
pub struct RowField {
    pub presence: Presence,
    pub ty: RowTy,
}

/// The field requirements one parameter's uses impose.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Row {
    /// Field name -> requirement. A `BTreeMap` so iteration (and the derived
    /// view layout) is canonical.
    pub fields: BTreeMap<String, RowField>,
}

/// A parameter's derived row plus whether the call boundary may replace the
/// argument with its view.
#[derive(Clone, Debug, PartialEq)]
pub struct ParamRow {
    pub row: Row,
    pub eligible: bool,
}

/// Interprocedural row table over a whole program: free-function parameters
/// keyed by storage symbol.
/// Only unannotated non-`self` parameters carry an entry.
pub struct RowInfo {
    functions: HashMap<String, Vec<Option<ParamRow>>>,
}

impl RowInfo {
    /// Analyze every free function of `program` (least fixpoint over
    /// whole-parameter forwarding; rows only grow and eligibility only flips to
    /// false over a finite field universe, so it terminates).
    pub fn analyze(program: &Program) -> Self {
        analyze_rows(program)
    }

    /// The row of free function `symbol`'s parameter `idx`, if that parameter
    /// is unannotated (annotated parameters keep their declared checking).
    pub fn function_param(&self, symbol: &str, idx: usize) -> Option<&ParamRow> {
        self.functions.get(symbol)?.get(idx)?.as_ref()
    }
}

/// Whether a source field of type `have` can stand in a position requiring
/// `want`: identical after peeling passing modes, or a value-preserving numeric
/// widening. Shared by the checker's value-site test and the back ends' view
/// construction so the two never disagree on what satisfies a forced type.
pub fn field_satisfies(have: &Type, want: &Type) -> bool {
    let have = brass_hir::peel_modes(have);
    have == want || matches!(numeric_flow(have, want), Flow::Identity | Flow::Widen)
}

/// Check a structural value's resolved fields against `row`, returning rendered
/// issues (empty = the value fits). Only `Required` fields reject: a `Guarded`
/// field may be absent (the view then carries null and the body's fallback
/// path runs, the specified graceful degradation), and its type is judged by
/// the body re-elaboration at the argument's own field type.
pub fn check_row(row: &Row, fields: &[(String, Type)]) -> Vec<String> {
    let mut issues = Vec::new();
    for (name, rf) in &row.fields {
        if rf.presence != Presence::Required {
            continue;
        }
        let Some((_, have)) = fields.iter().find(|(n, _)| n == name) else {
            issues.push(format!("missing field `{name}`"));
            continue;
        };
        if let RowTy::Forced(want) = &rf.ty {
            // A not-yet-resolved field type stays flexible (the checker defers).
            if brass_hir::is_fully_known(have) && !field_satisfies(have, want) {
                issues.push(format!(
                    "field `{name}`: cannot use `{}` where `{}` is required",
                    have.display(),
                    want.display()
                ));
            }
        }
    }
    issues
}

/// The canonical *view* type of `row` for a concrete structural `source`: a
/// structural record with exactly the row's fields, each at the SOURCE's own
/// field type. A `Guarded` field the source lacks -- or carries at a type that
/// cannot serve the field's `Forced` use even once narrowed to non-null -- is
/// the always-null `never?`, exactly what an absent field reads as: every use
/// of a guarded field sits behind a presence test, so the body takes its
/// fallback path (the graceful degradation of an open field).
///
/// The view drops the fields the body never touches but never changes the
/// type of one it does. Both the checker (which elaborates the callee body for
/// this argument at the view) and the back ends (which compile the body at the
/// view) see the same field types, and those are the argument's own: a
/// `Forced` row type is a requirement on the argument (see [`check_row`]),
/// never a representation change. Widening the slot would change the body's
/// arithmetic (`p.n / 2` on an `int32` field would divide as `float64`), and
/// wrapping a guarded `bool` slot into `bool?` would turn `if p.flag` into a
/// presence test.
///
/// Errors when a required field is missing from the source. The checker
/// rejects such an argument ([`check_row`]), so monomorphization meets this
/// only as an internal inconsistency.
pub fn view_type(row: &Row, source: &brass_hir::NominalType) -> Result<Type, String> {
    let mut fields: Vec<(String, Type)> = Vec::with_capacity(row.fields.len());
    for (name, rf) in &row.fields {
        let ty = match (source.substitution.get(name), rf.presence) {
            (Some(have), Presence::Guarded) if !guarded_field_fits(have, &rf.ty) => Type::null(),
            (Some(have), _) => have.clone(),
            (None, Presence::Guarded) => Type::null(),
            (None, Presence::Required) => {
                return Err(format!("view source is missing required field `{name}`"));
            }
        };
        fields.push((name.clone(), ty));
    }
    Ok(brass_hir::structural_record(fields))
}

/// Whether a guarded field the source carries at `have` can serve the row's
/// use of it. Every use sits behind a presence test, so a nullable source is
/// judged by its non-null payload. A type that is not fully known yet stays
/// flexible, as in [`check_row`].
fn guarded_field_fits(have: &Type, ty: &RowTy) -> bool {
    let RowTy::Forced(want) = ty else {
        return true;
    };
    let payload = match brass_hir::peel_modes(have) {
        Type::Nullable(inner) => inner,
        other => other,
    };
    !brass_hir::is_fully_known(payload) || field_satisfies(payload, want)
}

// ----- derivation -----

/// The per-parameter facts one body scan produces, before the interprocedural
/// union: the locally-derived row, local eligibility, and the (callee symbol,
/// parameter index) positions the whole parameter is forwarded into.
struct LocalScan {
    row: Row,
    eligible: bool,
    forwards: Vec<(String, usize)>,
}

fn analyze_rows(program: &Program) -> RowInfo {
    // Phase 1: scan every body once, collecting local rows and forward edges.
    let mut fn_scans: HashMap<String, Vec<Option<LocalScan>>> = HashMap::default();
    for f in program.functions.values() {
        let scans = scan_params(
            program,
            &f.module,
            &f.signature.params,
            Some(&f.decl.body),
            f.signature.ret_ty.as_ref(),
        );
        fn_scans.insert(f.symbol.clone(), scans);
    }
    // Phase 2: least fixpoint. Each parameter's row is its local row unioned
    // with every forward target's current row; forwarding into a missing or
    // ineligible target makes the parameter ineligible too (the callee may use
    // the value in ways the view cannot honor). Rows grow monotonically and
    // eligibility only decreases, so iteration terminates.
    let mut info = RowInfo {
        functions: fn_scans
            .iter()
            .map(|(sym, scans)| (sym.clone(), seed_rows(scans)))
            .collect(),
    };
    loop {
        let mut changed = false;
        for (sym, scans) in &fn_scans {
            for (idx, scan) in scans.iter().enumerate() {
                let Some(scan) = scan else { continue };
                let merged = merge_forwards(&info, scan, &info.functions[sym][idx]);
                if let Some(next) = merged {
                    info.functions.get_mut(sym).unwrap()[idx] = Some(next);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    info
}

/// The initial table entry for each scanned parameter: its local row.
fn seed_rows(scans: &[Option<LocalScan>]) -> Vec<Option<ParamRow>> {
    scans
        .iter()
        .map(|s| {
            s.as_ref().map(|s| ParamRow {
                row: s.row.clone(),
                eligible: s.eligible,
            })
        })
        .collect()
}

/// One fixpoint step for one parameter: union every forward target's current
/// row into the current entry. Returns the changed entry, or `None` when
/// already stable.
fn merge_forwards(
    info: &RowInfo,
    scan: &LocalScan,
    current: &Option<ParamRow>,
) -> Option<ParamRow> {
    let current = current.as_ref()?;
    let mut next = current.clone();
    for (callee, idx) in &scan.forwards {
        match info.function_param(callee, *idx) {
            Some(target) => {
                if !target.eligible {
                    next.eligible = false;
                }
                for (name, rf) in &target.row.fields {
                    union_field(&mut next, name, rf.presence, &rf.ty);
                }
            }
            // The callee parameter is annotated (or unknown): a typed position
            // the row cannot summarize -- the parameter keeps the full-value
            // path.
            None => next.eligible = false,
        }
    }
    (next != *current).then_some(next)
}

/// Union one field fact into a row (shared by the body scan and the fixpoint):
/// `Required` beats `Guarded`; a forced type replaces `Open`, and two different
/// forced types keep the *narrower* (a value satisfying it satisfies both). Two
/// incomparable forced types cannot both hold, so the parameter is marked
/// ineligible (the body itself will fail to type; the view must not guess).
fn union_field(pr: &mut ParamRow, name: &str, presence: Presence, ty: &RowTy) {
    let entry = pr
        .row
        .fields
        .entry(name.to_string())
        .or_insert_with(|| RowField {
            presence,
            ty: RowTy::Open,
        });
    entry.presence = entry.presence.max(presence);
    match (&entry.ty, ty) {
        (_, RowTy::Open) => {}
        (RowTy::Open, RowTy::Forced(t)) => entry.ty = RowTy::Forced(t.clone()),
        (RowTy::Forced(a), RowTy::Forced(b)) => {
            if a == b || field_satisfies(a, b) {
                // `a` is the narrower (or equal) requirement; keep it.
            } else if field_satisfies(b, a) {
                entry.ty = RowTy::Forced(b.clone());
            } else {
                pr.eligible = false;
            }
        }
    }
}

/// Scan every unannotated, non-`self` parameter of one body. `None` per slot
/// for annotated parameters (their declared type governs) and when the body is
/// absent (interface method declarations).
fn scan_params(
    program: &Program,
    module: &[String],
    params: &[brass_hir::ParamInfo],
    body: Option<&Block>,
    ret_ty: Option<&Type>,
) -> Vec<Option<LocalScan>> {
    params
        .iter()
        .map(|p| {
            if p.ty.is_some() || p.name == "self" {
                return None;
            }
            let body = body?;
            let mut scan = ParamScan {
                program,
                module,
                param: &p.name,
                forced_ret: ret_ty.and_then(forced_return_type),
                guarded: HashSet::default(),
                aliases: Vec::new(),
                locals: vec![params.iter().map(|q| q.name.clone()).collect()],
                out: LocalScan {
                    row: Row::default(),
                    eligible: true,
                    forwards: Vec::new(),
                },
            };
            scan.walk_block(body, true);
            Some(scan.out)
        })
        .collect()
}

/// The primitive type a declared return annotation forces on a directly
/// returned field. A fallible `T!` return forces its Ok payload `T`: a bare
/// `return e` there is the Ok value, so the same constraint applies.
fn forced_return_type(ret: &Type) -> Option<Type> {
    let ret = match ret.result_payloads() {
        Some((ok, _)) => ok,
        None => ret,
    };
    forced_primitive(ret)
}

/// Only a concrete primitive is an unambiguous forcing type: records/sums carry
/// per-instance substitutions that an annotation does not fix, nullables defer
/// to the guarded machinery, and literals adapt across numeric widths. Anything
/// else leaves the field `Open` (the body re-elaboration still checks it).
fn forced_primitive(t: &Type) -> Option<Type> {
    match brass_hir::peel_modes(t) {
        t @ (Type::Int(_) | Type::Float(_) | Type::Bool | Type::Str) => Some(t.clone()),
        _ => None,
    }
}

/// The primitive type named by a `let` annotation, for `let x: T = p.f` forcing.
fn forced_primitive_annotation(t: &TypeExpr) -> Option<Type> {
    match t {
        TypeExpr::Named(name, _) => {
            if let Some(k) = brass_hir::IntKind::from_name(name) {
                return Some(Type::Int(k));
            }
            match name.as_str() {
                "float32" => Some(Type::Float(brass_hir::FloatKind::F32)),
                "float64" => Some(Type::Float(brass_hir::FloatKind::F64)),
                "string" => Some(Type::Str),
                "bool" => Some(Type::Bool),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The single-parameter body walker. `active` tracks whether the source name
/// still denotes the parameter (a shadowing binder or a bare reassignment turns
/// it off for the rest of that scope); `guarded` holds the fields currently
/// proven present by an enclosing truthiness/`if let` test.
struct ParamScan<'p> {
    program: &'p Program,
    module: &'p [String],
    param: &'p str,
    /// The primitive the declared return type forces on `return p.f`.
    forced_ret: Option<Type>,
    guarded: HashSet<String>,
    /// The bindings of `if let v = p.f` presence tests whose then-arm is being
    /// walked: `(v, f, depth)`, `depth` being the index of the pattern's own
    /// scope in `locals`. A use of `v` there is a guarded use of `f`, so a
    /// type it pins (`let s: string = v`) constrains the field exactly as
    /// `let s: string = p.f` behind `if p.f` does.
    aliases: Vec<(String, String, usize)>,
    /// The lexical scopes of local value names (the callable's parameters,
    /// `let` / `for` / pattern binders), innermost last. A call through a
    /// local name calls that value, never a same-named function, exactly as
    /// MIR lowering resolves it.
    locals: Vec<HashSet<String>>,
    out: LocalScan,
}

/// Presence tests in a condition are distinct from fields that the condition
/// proves present in one arm. In particular, both operands of `a || b` tolerate
/// absence while neither operand is necessarily present when the result is true.
#[derive(Default)]
struct GuardSubjects {
    tested: Vec<String>,
    then_present: Vec<String>,
    else_present: Vec<String>,
}

fn union_fields(mut left: Vec<String>, right: Vec<String>) -> Vec<String> {
    for field in right {
        if !left.contains(&field) {
            left.push(field);
        }
    }
    left
}

fn intersect_fields(left: Vec<String>, right: &[String]) -> Vec<String> {
    left.into_iter()
        .filter(|field| right.contains(field))
        .collect()
}

impl ParamScan<'_> {
    fn ineligible(&mut self) {
        self.out.eligible = false;
    }

    /// Record one field access. `presence` is the access's own tolerance
    /// (`Required` for a plain read/write, `Guarded` for a guard-test or
    /// rendering use); an enclosing guard of the same field downgrades a
    /// required access to guarded.
    fn access(&mut self, field: &str, presence: Presence, forced: Option<&Type>) {
        let presence = if self.guarded.contains(field) {
            Presence::Guarded
        } else {
            presence
        };
        let ty = match forced.and_then(forced_primitive) {
            Some(t) => RowTy::Forced(t),
            None => RowTy::Open,
        };
        // Reuse the shared union so a scan's own accesses combine exactly like
        // the interprocedural fixpoint's.
        let mut pr = ParamRow {
            row: std::mem::take(&mut self.out.row),
            eligible: self.out.eligible,
        };
        union_field(&mut pr, field, presence, &ty);
        self.out.row = pr.row;
        self.out.eligible = pr.eligible;
    }

    /// The parameter field the local `name` stands for here: an `if let`
    /// presence binding of it (see `aliases`) that no deeper scope shadows.
    fn field_alias(&self, name: &str) -> Option<&str> {
        let (_, field, depth) = self.aliases.iter().rev().find(|(n, _, _)| n == name)?;
        let shadowed = self
            .locals
            .get(depth + 1..)
            .is_some_and(|scopes| scopes.iter().any(|scope| scope.contains(name)));
        (!shadowed).then_some(field.as_str())
    }

    /// Whether `e` is the bare parameter itself.
    fn is_param(&self, e: &Expr, active: bool) -> bool {
        active && matches!(e, Expr::Ident(name, _) if name == self.param)
    }

    /// Whether `name` is bound by an enclosing local scope (shadowing any
    /// function of that name).
    fn is_local(&self, name: &str) -> bool {
        self.locals.iter().any(|scope| scope.contains(name))
    }

    /// Bind every name `pat` introduces in the innermost local scope.
    fn bind_pattern(&mut self, pat: &Pattern) {
        let names: Vec<String> = pat.bound_names().into_iter().map(str::to_string).collect();
        if let Some(scope) = self.locals.last_mut() {
            scope.extend(names);
        }
    }

    /// Run `walk` inside a fresh local scope holding the names `pat` binds.
    fn with_pattern_scope(&mut self, pat: Option<&Pattern>, walk: impl FnOnce(&mut Self)) {
        self.locals.push(HashSet::default());
        if let Some(pat) = pat {
            self.bind_pattern(pat);
        }
        walk(self);
        self.locals.pop();
    }

    /// The field name when `e` is a direct field access `p.f`.
    fn param_field<'e>(&self, e: &'e Expr, active: bool) -> Option<&'e str> {
        match e {
            Expr::Field(base, f, _) if self.is_param(base, active) => Some(f),
            _ => None,
        }
    }

    /// Walk a block in statement order, threading shadowing through `active`.
    fn walk_block(&mut self, block: &Block, active: bool) {
        self.with_pattern_scope(None, |s| {
            let mut active = active;
            for stmt in &block.stmts {
                active = s.walk_stmt(stmt, active);
            }
        });
    }

    /// Walk one statement; returns the parameter's `active` state for the
    /// statements that follow it in the same block.
    fn walk_stmt(&mut self, stmt: &Stmt, active: bool) -> bool {
        match stmt {
            Stmt::Let { pat, ty, value, .. } => {
                if let Some(value) = value {
                    let forced = ty.as_ref().and_then(forced_primitive_annotation);
                    self.walk_value(value, active, forced.as_ref());
                }
                self.bind_pattern(pat);
                // A binder of the same name shadows the parameter from here on.
                if pattern_binds(pat, self.param) {
                    return false;
                }
                active
            }
            Stmt::Assign { target, value, .. } => {
                self.walk_value(value, active, None);
                // Rebinding a presence binding ends its standing for the field.
                if let Expr::Ident(name, _) = target {
                    self.aliases.retain(|(n, _, _)| n != name);
                }
                if self.is_param(target, active) {
                    // A bare reassignment rebinds the local: later uses are the
                    // new value, not the argument.
                    return false;
                }
                if let Some(f) = self.assigned_param_field(target, active) {
                    let f = f.to_string();
                    self.access(&f, Presence::Required, None);
                } else {
                    self.walk_value(target, active, None);
                }
                active
            }
            Stmt::While { cond, body, .. } => {
                self.walk_guarding_cond(cond, active, |s| s.walk_block(body, active));
                active
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                self.walk_value(iter, active, None);
                // A loop variable that shadows the parameter hides it in the body.
                let shadows = pat.bound_names().contains(&self.param);
                self.with_pattern_scope(Some(pat), |s| s.walk_block(body, active && !shadows));
                active
            }
            Stmt::Expr(e) => {
                self.walk_value(e, active, None);
                active
            }
            Stmt::Return(Some(e), _) => {
                let forced = self.forced_ret.clone();
                self.walk_value(e, active, forced.as_ref());
                active
            }
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => active,
        }
    }

    /// The parameter field a store targets (`p.f = ..`, `p.f.g = ..`,
    /// `p.f[i] = ..` all touch `f`). A store *through* the parameter itself
    /// with no field (`p[i] = ..`) has no row representation.
    fn assigned_param_field<'e>(&mut self, target: &'e Expr, active: bool) -> Option<&'e str> {
        match target {
            Expr::Field(base, f, _) if self.is_param(base, active) => Some(f),
            Expr::Field(base, _, _) | Expr::Index(base, _, _) => {
                if self.is_param(base, active) {
                    // `p[i] = ..`: an indexing use of the whole parameter.
                    self.ineligible();
                    None
                } else {
                    self.assigned_param_field(base, active)
                }
            }
            _ => None,
        }
    }

    /// Walk an expression in a *value* position. `forced` is the concrete type
    /// this position pins (an annotated argument slot, an annotated `let`, a
    /// declared return); it applies only to a direct `p.f` here -- arithmetic
    /// and nested expressions never force (their operands adapt).
    fn walk_value(&mut self, e: &Expr, active: bool, forced: Option<&Type>) {
        if self.is_param(e, active) {
            // A bare use of the whole parameter in a generic value position:
            // it escapes or aliases, which a reduced view must not do.
            self.ineligible();
            return;
        }
        if let Some(f) = self.param_field(e, active) {
            let f = f.to_string();
            self.access(&f, Presence::Required, forced);
            return;
        }
        if let Expr::Ident(name, _) = e
            && let Some(f) = self.field_alias(name)
        {
            let f = f.to_string();
            self.access(&f, Presence::Guarded, forced);
            return;
        }
        match e {
            Expr::Call(callee, args, _) => self.walk_call(callee, args, active),
            Expr::Field(base, _, _) => self.walk_value(base, active, None),
            Expr::Index(base, idx, _) => {
                self.walk_value(base, active, None);
                self.walk_value(idx, active, None);
            }
            Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) => {
                self.walk_value(inner, active, forced)
            }
            // A type test reads its subject; the annotation names no value.
            Expr::TypeTest(subject, _, _, _) => self.walk_value(subject, active, None),
            Expr::Binary(_, a, b, _) | Expr::Range(a, b, _) => {
                self.walk_value(a, active, None);
                self.walk_value(b, active, None);
            }
            Expr::Array(items, _) => {
                for item in items {
                    self.walk_value(item, active, None);
                }
            }
            Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
                for (_, v) in fields {
                    self.walk_value(v, active, None);
                }
            }
            Expr::Str(segs, _) => {
                for seg in segs {
                    if let StrSeg::Expr(inner) = seg {
                        self.walk_render_arg(inner, active);
                    }
                }
            }
            Expr::Closure(params, body, _) => {
                // A capture outlives the call frame (and may escape through the
                // closure value), so any un-shadowed mention of the parameter
                // inside the body makes it ineligible.
                let shadowed = params.iter().any(|p| p.name == self.param);
                if active && !shadowed && expr_mentions(body, self.param) {
                    self.ineligible();
                }
            }
            Expr::If(cond, then, els, _) => {
                self.walk_guarding_cond(cond, active, |s| s.walk_block(then, active));
                if let Some(els) = els {
                    self.walk_else(cond, active, els);
                }
            }
            Expr::IfLet(pat, scrut, then, els, _) => {
                let mut then_guard = None;
                if let Some(f) = self.param_field(scrut, active) {
                    // `if let x = p.f` is a presence test of `f`: the test
                    // itself tolerates absence, and the then-arm is guarded.
                    let f = f.to_string();
                    self.access(&f, Presence::Guarded, None);
                    then_guard = Some(f);
                } else {
                    self.walk_value(scrut, active, None);
                }
                let inner_active = active && !pattern_binds(pat, self.param);
                let alias = match (pat, &then_guard) {
                    (Pattern::Binding(name, None, _), Some(f)) => Some((name.clone(), f.clone())),
                    _ => None,
                };
                let added = then_guard
                    .map(|f| self.guarded.insert(f.clone()).then_some(f))
                    .unwrap_or(None);
                self.with_pattern_scope(Some(pat), |s| {
                    let depth = s.locals.len() - 1;
                    if let Some((name, f)) = alias {
                        s.aliases.push((name, f, depth));
                    }
                    s.walk_block(then, inner_active);
                    s.aliases.retain(|(_, _, d)| *d != depth);
                });
                if let Some(f) = added {
                    self.guarded.remove(&f);
                }
                if let Some(els) = els {
                    self.walk_value(els, active, None);
                }
            }
            Expr::Match(scrut, arms, _) => {
                self.walk_value(scrut, active, None);
                for arm in arms {
                    let inner_active = active && !pattern_binds(&arm.pattern, self.param);
                    self.with_pattern_scope(Some(&arm.pattern), |s| {
                        s.walk_value(&arm.body, inner_active, None)
                    });
                }
            }
            Expr::Block(block, _) => self.walk_block(block, active),
            Expr::Ident(..)
            | Expr::SelfExpr(_)
            | Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(_) => {}
        }
    }

    /// Walk a call. Whole-parameter arguments are the interesting case: into an
    /// unannotated free-function parameter they forward (row union); into any
    /// annotated, method, builtin, or indirect position they make the parameter
    /// ineligible -- except the pure rendering builtins, which the view serves.
    fn walk_call(&mut self, callee: &Expr, args: &[Arg], active: bool) {
        // `string.from(x)` renders its argument exactly like `"{x}"`.
        if let Expr::Field(base, method, _) = callee
            && method == "from"
            && matches!(&**base, Expr::Ident(t, _) if t == "string" && !self.is_local(t))
        {
            for a in args {
                self.walk_render_arg(&a.expr, active);
            }
            return;
        }
        if let Expr::Field(base, _method, _) = callee {
            if self.is_param(base, active) {
                // The parameter is a method receiver (or a function-typed field
                // is called through it): dispatch needs the full value.
                self.ineligible();
            } else {
                self.walk_value(base, active, None);
            }
            for a in args {
                if self.is_param(&a.expr, active) {
                    // A method's receiver type is unknown at this AST-only
                    // stage, so its parameter rows cannot be resolved; keep the
                    // full value.
                    self.ineligible();
                } else {
                    self.walk_value(&a.expr, active, None);
                }
            }
            return;
        }
        if let Expr::Ident(fname, _) = callee {
            // A local value of the callee's name (a closure parameter, a
            // `let`-bound closure, a pattern binder) is what the call invokes:
            // it shadows any same-named function, and its parameter rows are
            // unknown, so the whole parameter passed to it keeps its full
            // value. `error` is reserved in call position and never shadowed.
            if self.is_param(callee, active) || (fname != "error" && self.is_local(fname)) {
                for a in args {
                    if self.is_param(&a.expr, active) {
                        self.ineligible();
                    } else {
                        self.walk_value(&a.expr, active, None);
                    }
                }
                if self.is_param(callee, active) {
                    // The parameter itself is called as a function value.
                    self.ineligible();
                }
                return;
            }
            if let Some(finfo) = self.program.resolve_function(self.module, fname) {
                let params = finfo.signature.params.clone();
                let symbol = finfo.symbol.clone();
                if is_prelude_print(self.program, finfo) {
                    // The prelude print/println only render their argument
                    // (the typed back ends intercept them as typed I/O, and
                    // the bodies themselves just format it), so despite
                    // resolving to real functions they are rendering
                    // positions, exactly like interpolation. Identified by
                    // the resolved declaration: a module's own `println`
                    // shadows the prelude's and is an ordinary callee.
                    for a in args {
                        self.walk_render_arg(&a.expr, active);
                    }
                    return;
                }
                for (j, a) in args.iter().enumerate() {
                    if self.is_param(&a.expr, active) {
                        match params.get(j) {
                            Some(p) if p.ty.is_none() && p.name != "self" => {
                                self.out.forwards.push((symbol.clone(), j));
                            }
                            // An annotated (or missing) parameter is a typed
                            // position the row cannot summarize.
                            _ => self.ineligible(),
                        }
                        continue;
                    }
                    let forced = params
                        .get(j)
                        .filter(|p| p.ty.is_some())
                        .and_then(|p| p.resolved_ty.clone());
                    self.walk_value(&a.expr, active, forced.as_ref());
                }
                return;
            }
            // A name that resolves to no function: a runtime builtin or a
            // module-level callable value. Rendering builtins only format the
            // value, which the view is specified to serve; anything else needs
            // the full value.
            let rendering = matches!(fname.as_str(), "print" | "println");
            for a in args {
                if rendering {
                    self.walk_render_arg(&a.expr, active);
                } else if self.is_param(&a.expr, active) {
                    self.ineligible();
                } else {
                    self.walk_value(&a.expr, active, None);
                }
            }
            return;
        }
        // An arbitrary callee expression (an immediately-called closure).
        self.walk_value(callee, active, None);
        for a in args {
            self.walk_value(&a.expr, active, None);
        }
    }

    /// A rendering position (`println(x)`, `string.from(x)`, `"{x}"`): the whole
    /// parameter may be rendered (the view renders instead -- specified), and a
    /// direct field access renders null when absent, so it is a Guarded access.
    fn walk_render_arg(&mut self, e: &Expr, active: bool) {
        if self.is_param(e, active) {
            return;
        }
        if let Some(f) = self.param_field(e, active) {
            // A field READ in a rendering position (`println("{obj.x}")`) is
            // an unguarded read like any other: the caller promised the field.
            // `access` still downgrades it to Guarded inside an enclosing
            // truthiness guard of the same field, which is where the
            // render-null degradation lives. Rendering the WHOLE parameter
            // (handled above) contributes nothing: it shows whatever the view
            // carries.
            let f = f.to_string();
            self.access(&f, Presence::Required, None);
            return;
        }
        self.walk_value(e, active, None);
    }

    /// Walk `cond` recording its bare `p.f` truthiness subjects as Guarded
    /// accesses, then run `then` with those fields added to the guard set.
    fn walk_guarding_cond(&mut self, cond: &Expr, active: bool, then: impl FnOnce(&mut Self)) {
        let subjects = self.guard_subjects(cond, active);
        for f in &subjects.tested {
            self.access(f, Presence::Guarded, None);
        }
        self.walk_cond_rest(cond, active);
        let added: Vec<String> = subjects
            .then_present
            .into_iter()
            .filter(|f| self.guarded.insert(f.clone()))
            .collect();
        then(self);
        for f in added {
            self.guarded.remove(&f);
        }
    }

    /// Walk an `if`'s else arm: a negated test (`if !p.f { .. } else { .. }`)
    /// proves the field present in the else arm.
    fn walk_else(&mut self, cond: &Expr, active: bool, els: &Expr) {
        let added: Vec<String> = self
            .guard_subjects(cond, active)
            .else_present
            .into_iter()
            .filter(|f| self.guarded.insert(f.clone()))
            .collect();
        self.walk_value(els, active, None);
        for f in added {
            self.guarded.remove(&f);
        }
    }

    /// The parameter fields tested for truthiness and the fields proven present
    /// in each arm. `&&` unions then-proofs, while `||` only retains proofs shared
    /// by both alternatives; every bare operand remains a tolerant presence test.
    fn guard_subjects(&self, cond: &Expr, active: bool) -> GuardSubjects {
        match cond {
            Expr::Field(..) => match self.param_field(cond, active) {
                Some(f) => GuardSubjects {
                    tested: vec![f.to_string()],
                    then_present: vec![f.to_string()],
                    else_present: Vec::new(),
                },
                None => GuardSubjects::default(),
            },
            Expr::Unary(brass_parser::ast::UnaryOp::Not, inner, _) => {
                let subjects = self.guard_subjects(inner, active);
                GuardSubjects {
                    tested: subjects.tested,
                    then_present: subjects.else_present,
                    else_present: subjects.then_present,
                }
            }
            Expr::Binary(brass_parser::ast::BinOp::And, a, b, _) => {
                let left = self.guard_subjects(a, active);
                let right = self.guard_subjects(b, active);
                GuardSubjects {
                    tested: union_fields(left.tested, right.tested),
                    then_present: union_fields(left.then_present, right.then_present),
                    else_present: intersect_fields(left.else_present, &right.else_present),
                }
            }
            Expr::Binary(brass_parser::ast::BinOp::Or, a, b, _) => {
                let left = self.guard_subjects(a, active);
                let right = self.guard_subjects(b, active);
                GuardSubjects {
                    tested: union_fields(left.tested, right.tested),
                    then_present: intersect_fields(left.then_present, &right.then_present),
                    else_present: union_fields(left.else_present, right.else_present),
                }
            }
            _ => GuardSubjects::default(),
        }
    }

    /// Walk the parts of a guard condition that are not bare `p.f` truthiness
    /// subjects (those were already recorded as Guarded accesses).
    fn walk_cond_rest(&mut self, cond: &Expr, active: bool) {
        if self.param_field(cond, active).is_some() {
            return;
        }
        match cond {
            Expr::Unary(brass_parser::ast::UnaryOp::Not, inner, _) => {
                self.walk_cond_rest(inner, active)
            }
            Expr::Binary(brass_parser::ast::BinOp::And | brass_parser::ast::BinOp::Or, a, b, _) => {
                self.walk_cond_rest(a, active);
                self.walk_cond_rest(b, active);
            }
            other => self.walk_value(other, active, None),
        }
    }
}

/// Whether `f` is the implicit prelude's `print` or `println`.
fn is_prelude_print(program: &Program, f: &brass_hir::FunInfo) -> bool {
    matches!(f.decl.name.as_str(), "print" | "println")
        && program.prelude_modules.contains(&f.module)
}

/// Whether a pattern binds `name` (shadowing the tracked parameter).
fn pattern_binds(pat: &Pattern, name: &str) -> bool {
    match pat {
        Pattern::Binding(n, _, _) => n == name,
        Pattern::Record(_, _, fields, _) => fields.iter().any(|f| match &f.pat {
            Some(sub) => pattern_binds(sub, name),
            None => f.name == name,
        }),
        Pattern::Array(pats, _) => pats.iter().any(|p| pattern_binds(p, name)),
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => false,
    }
}

/// Whether `e` mentions identifier `name` anywhere (shadowing-unaware on
/// purpose: used only to detect a closure capturing the parameter, where a
/// conservative answer keeps the full value).
fn expr_mentions(e: &Expr, name: &str) -> bool {
    let mut found = false;
    visit(e, &mut |x| {
        if let Expr::Ident(n, _) = x
            && n == name
        {
            found = true;
        }
    });
    found
}

/// Pre-order visit of every sub-expression of `e` (including statements of
/// nested blocks).
fn visit(e: &Expr, f: &mut impl FnMut(&Expr)) {
    f(e);
    match e {
        Expr::Unary(_, a, _)
        | Expr::ErrorProp(a, _)
        | Expr::Field(a, _, _)
        | Expr::TypeTest(a, _, _, _) => visit(a, f),
        Expr::Binary(_, a, b, _) | Expr::Range(a, b, _) | Expr::Index(a, b, _) => {
            visit(a, f);
            visit(b, f);
        }
        Expr::Call(c, args, _) => {
            visit(c, f);
            for a in args {
                visit(&a.expr, f);
            }
        }
        Expr::Array(items, _) => items.iter().for_each(|i| visit(i, f)),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            fields.iter().for_each(|(_, v)| visit(v, f))
        }
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(inner) = seg {
                    visit(inner, f);
                }
            }
        }
        Expr::Closure(_, body, _) => visit(body, f),
        Expr::If(c, then, els, _) => {
            visit(c, f);
            visit_block(then, f);
            if let Some(els) = els {
                visit(els, f);
            }
        }
        Expr::IfLet(_, scrut, then, els, _) => {
            visit(scrut, f);
            visit_block(then, f);
            if let Some(els) = els {
                visit(els, f);
            }
        }
        Expr::Match(scrut, arms, _) => {
            visit(scrut, f);
            arms.iter().for_each(|a| visit(&a.body, f));
        }
        Expr::Block(b, _) => visit_block(b, f),
        Expr::Ident(..)
        | Expr::SelfExpr(_)
        | Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_) => {}
    }
}

fn visit_block(b: &Block, f: &mut impl FnMut(&Expr)) {
    for s in &b.stmts {
        match s {
            Stmt::Let {
                value: Some(value), ..
            } => visit(value, f),
            Stmt::Let { value: None, .. } => {}
            Stmt::Assign { target, value, .. } => {
                visit(target, f);
                visit(value, f);
            }
            Stmt::While { cond, body, .. } => {
                visit(cond, f);
                visit_block(body, f);
            }
            Stmt::For { iter, body, .. } => {
                visit(iter, f);
                visit_block(body, f);
            }
            Stmt::Expr(e) | Stmt::Return(Some(e), _) => visit(e, f),
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }
}
