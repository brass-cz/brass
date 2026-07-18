//! Row inference: what a callable body requires of each unannotated parameter
//! that may receive an anonymous (structural) value.
//!
//! For every unannotated, non-`self` parameter of every free function and
//! method, the body is scanned for field accesses and the way each field is
//! used, producing a [`Row`]: the set of field names with, per field,
//!
//! - a [`Presence`]: `Required` when the body reads/writes the field
//!   unguarded, `Guarded` when every access is dominated by a truthiness /
//!   `if let` test of that same field (or only rendered, which tolerates
//!   absence);
//! - a [`RowTy`]: `Forced(T)` when an unambiguous use pins a primitive type
//!   (the field flows into a `T`-annotated parameter, `let x: T =`, or a
//!   declared primitive return), otherwise `Open` (the argument's own field
//!   type flows through).
//!
//! A parameter forwarded whole into another *eligible* unannotated free-function
//! parameter unions that callee's row (an interprocedural least fixpoint, the
//! same shape as `brass_hir::mutation`). Any use that a reduced field set
//! could not honor -- method receiver use, escaping into a store / return /
//! closure capture, being passed to an annotated or unknown position -- marks
//! the parameter *view-ineligible*: its row is still derived for diagnostics,
//! but the call boundary must keep the argument's full value.
//!
//! Consumers: the checker validates each anonymous argument against the callee
//! row at the argument's own span, and (for eligible parameters) the back end
//! converts the argument into the row's *view* (see [`view_type`]), collapsing
//! every argument shape with the same view into one compiled instance.

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::collections::BTreeMap;

use brass_hir::{Program, Type, TypeKind};
use brass_parser::ast::{Arg, Block, Expr, Pattern, Stmt, StrSeg, TypeExpr};

use crate::flow::{Flow, numeric_flow};

/// Whether a field may be absent at the call site.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Presence {
    /// Every access is dominated by a truthiness/`if let` test of the field
    /// itself (or is a rendering use); an absent field takes the fallback path.
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
/// keyed by storage symbol, method parameters keyed by (type symbol, method).
/// Only unannotated non-`self` parameters carry an entry.
pub struct RowInfo {
    functions: HashMap<String, Vec<Option<ParamRow>>>,
    methods: HashMap<(String, String), Vec<Option<ParamRow>>>,
}

impl RowInfo {
    /// Analyze every free function and method of `program` (least fixpoint over
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

    /// The row of method `(type symbol, method)`'s call-site argument `idx`
    /// (the receiver is excluded; index 0 is the first non-`self` parameter).
    pub fn method_param(&self, type_symbol: &str, method: &str, idx: usize) -> Option<&ParamRow> {
        self.methods
            .get(&(type_symbol.to_string(), method.to_string()))?
            .get(idx)?
            .as_ref()
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
/// field that is absent or type-mismatched degrades to null at the view (the
/// body's fallback path runs), which is the specified graceful degradation.
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
/// structural record with exactly the row's fields. A `Required` field carries
/// its forced type (or the source's own type when open); a `Guarded` field is
/// nullable -- its forced type wrapped, or the source's type wrapped when open
/// (`never?` when absent), so absence/mismatch materializes as null at run
/// time. Errors when a required field is missing from the source (the checker
/// prevents this for checked calls; the deferred boundary surfaces it).
pub fn view_type(row: &Row, source: &brass_hir::NominalType) -> Result<Type, String> {
    let mut fields: Vec<(String, Type)> = Vec::with_capacity(row.fields.len());
    for (name, rf) in &row.fields {
        let have = source.substitution.get(name);
        let ty = match (&rf.presence, &rf.ty) {
            (Presence::Required, RowTy::Forced(t)) => t.clone(),
            (Presence::Required, RowTy::Open) => have
                .cloned()
                .ok_or_else(|| format!("view source is missing required field `{name}`"))?,
            // A guarded field's slot always exists in the view; whether the
            // value or null lands in it is decided per field at construction.
            (Presence::Guarded, RowTy::Forced(t)) => nullable_of(t.clone()),
            (Presence::Guarded, RowTy::Open) => match have {
                Some(t) => nullable_of(t.clone()),
                None => Type::Nullable(Box::new(Type::Never)),
            },
        };
        fields.push((name.clone(), ty));
    }
    Ok(brass_hir::structural_record(fields))
}

/// Wrap `t` nullable unless it already is (a chained view's guarded field is
/// already `T?`; double-wrapping would change its representation).
fn nullable_of(t: Type) -> Type {
    match t {
        Type::Nullable(_) => t,
        other => Type::Nullable(Box::new(other)),
    }
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
    let mut method_scans: HashMap<(String, String), Vec<Option<LocalScan>>> = HashMap::default();
    for info in program.types.values() {
        let methods: Vec<(&String, &brass_hir::MethodInfo)> = match &info.kind {
            TypeKind::Record { methods, .. } => methods.iter().collect(),
            TypeKind::Sum { variants } => variants.iter().flat_map(|v| v.methods.iter()).collect(),
        };
        for (mname, m) in methods {
            let has_self = m.signature.params.first().is_some_and(|p| p.name == "self");
            let params = &m.signature.params[usize::from(has_self)..];
            let scans = scan_params(
                program,
                &info.module,
                params,
                m.decl.body.as_ref(),
                m.signature.ret_ty.as_ref(),
            );
            method_scans.insert((info.symbol.clone(), mname.clone()), scans);
        }
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
        methods: method_scans
            .iter()
            .map(|(key, scans)| (key.clone(), seed_rows(scans)))
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
        for (key, scans) in &method_scans {
            for (idx, scan) in scans.iter().enumerate() {
                let Some(scan) = scan else { continue };
                let merged = merge_forwards(&info, scan, &info.methods[key][idx]);
                if let Some(next) = merged {
                    info.methods.get_mut(key).unwrap()[idx] = Some(next);
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
            // the row cannot summarize -- the parameter keeps today's full-value
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
    out: LocalScan,
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

    /// Whether `e` is the bare parameter itself.
    fn is_param(&self, e: &Expr, active: bool) -> bool {
        active && matches!(e, Expr::Ident(name, _) if name == self.param)
    }

    /// The field name when `e` is a direct field access `p.f`.
    fn param_field<'e>(&self, e: &'e Expr, active: bool) -> Option<&'e str> {
        match e {
            Expr::Field(base, f, _) if self.is_param(base, active) => Some(f),
            _ => None,
        }
    }

    /// Walk a block in statement order, threading shadowing through `active`.
    fn walk_block(&mut self, block: &Block, mut active: bool) {
        for stmt in &block.stmts {
            active = self.walk_stmt(stmt, active);
        }
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
                // A binder of the same name shadows the parameter from here on.
                if pattern_binds(pat, self.param) {
                    return false;
                }
                active
            }
            Stmt::Assign { target, value, .. } => {
                self.walk_value(value, active, None);
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
                self.walk_block(body, active && !shadows);
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
                let added = then_guard
                    .map(|f| self.guarded.insert(f.clone()).then_some(f))
                    .unwrap_or(None);
                self.walk_block(then, inner_active);
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
                    self.walk_value(&arm.body, inner_active, None);
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
            if self.is_param(callee, active) {
                // The parameter itself is called as a function value.
                self.ineligible();
                for a in args {
                    self.walk_value(&a.expr, active, None);
                }
                return;
            }
            if let Some(finfo) = self.program.resolve_function(self.module, fname) {
                let params = finfo.signature.params.clone();
                let symbol = finfo.symbol.clone();
                if symbol == "print" || symbol == "println" {
                    // The stdlib print/println bodies are never instantiated by
                    // the typed back ends (both intercept these calls as typed
                    // I/O), so despite resolving to real functions they are
                    // rendering positions, exactly like interpolation.
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
            // A runtime builtin or a local closure. Rendering builtins only
            // format the value, which the view is specified to serve; anything
            // else (spawn, error, len, a closure...) needs the full value.
            let rendering = matches!(fname.as_str(), "print" | "println" | "to_string");
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

    /// A rendering position (`println(x)`, `to_string(x)`, `"{x}"`): the whole
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
        let (then_guards, _else_guards) = self.guard_subjects(cond, active);
        for f in &then_guards {
            self.access(f, Presence::Guarded, None);
        }
        self.walk_cond_rest(cond, active);
        let added: Vec<String> = then_guards
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
        let (_then_guards, else_guards) = self.guard_subjects(cond, active);
        for f in &else_guards {
            self.access(f, Presence::Guarded, None);
        }
        let added: Vec<String> = else_guards
            .into_iter()
            .filter(|f| self.guarded.insert(f.clone()))
            .collect();
        self.walk_value(els, active, None);
        for f in added {
            self.guarded.remove(&f);
        }
    }

    /// The parameter fields a condition tests for truthiness, split by which
    /// arm the test proves them present in: `p.f` proves `f` in the then arm,
    /// `!p.f` in the else arm, `a && b` proves both sides' then-fields. `||`
    /// proves nothing (either side may have failed).
    fn guard_subjects(&self, cond: &Expr, active: bool) -> (Vec<String>, Vec<String>) {
        match cond {
            Expr::Field(..) => match self.param_field(cond, active) {
                Some(f) => (vec![f.to_string()], Vec::new()),
                None => (Vec::new(), Vec::new()),
            },
            Expr::Unary(brass_parser::ast::UnaryOp::Not, inner, _) => {
                let (t, e) = self.guard_subjects(inner, active);
                (e, t)
            }
            Expr::Binary(brass_parser::ast::BinOp::And, a, b, _) => {
                let (ta, _) = self.guard_subjects(a, active);
                let (tb, _) = self.guard_subjects(b, active);
                (ta.into_iter().chain(tb).collect(), Vec::new())
            }
            _ => (Vec::new(), Vec::new()),
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
            Expr::Binary(brass_parser::ast::BinOp::And, a, b, _) => {
                self.walk_cond_rest(a, active);
                self.walk_cond_rest(b, active);
            }
            other => self.walk_value(other, active, None),
        }
    }
}

/// Whether a pattern binds `name` (shadowing the tracked parameter).
fn pattern_binds(pat: &Pattern, name: &str) -> bool {
    match pat {
        Pattern::Binding(n, _) => n == name,
        Pattern::Record(_, fields, _) => fields.iter().any(|f| match &f.pat {
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
        Expr::Unary(_, a, _) | Expr::ErrorProp(a, _) | Expr::Field(a, _, _) => visit(a, f),
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
