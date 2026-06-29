//! JIT-time constraint-based type inference over a MIR body (DESIGN.md 1,
//! "deferred monomorphization"; PLAN.md R1/R9).
//!
//! Where `mono.rs` forward-propagates concrete types per instance, this derives a
//! body's types by *constraint generation + unification*: each MIR local becomes
//! a type variable in the shared `prepoly_solver`, the body is walked emitting
//! equality constraints (a local equals its rvalue, a binary operator's operands
//! agree, a `return` operand equals the callable's result type, ...), and the
//! solver resolves them. A unification conflict is a JIT-time type error -- the
//! check the deferred model needs. Because the IR is type-independent, the same
//! body instantiates at different entry types simply by seeding its parameter
//! variables differently, which is exactly per-call monomorphization.
//!
//! This module is the constraint core: it covers the parts that need no program
//! or callee information -- operands, `Use`/`Bin`/`Un`/`Array`, index load/store,
//! and `return`. Calls, field access, record/variant construction, and closures
//! need callee/type resolution; they are supplied by a [`Resolver`] so the same
//! engine serves both an isolated unit test (a trivial resolver) and, when wired
//! into monomorphization, the real program lookups. Unresolved positions bind a
//! fresh variable so the surrounding constraints still solve.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use prepoly_hir::{FloatKind, IntKind, Program, Type, TypeInfo, TypeKind};
use prepoly_mir::{Literal, MirBody, MirStmt, Operand, Place, Projection, Rvalue, Terminator};
use prepoly_parser::ast::{BinOp, UnaryOp};
use prepoly_solver::solver::{InferenceVarKind, Solver};

/// A JIT-time type error found while solving a body's constraints. The MIR
/// carries no source spans, so a failure is reported against the offending
/// local, with the solver's unification message.
#[derive(Debug, Clone, PartialEq)]
pub struct MirTypeError {
    pub message: String,
}

/// What a deferred (runtime-typed) value must structurally provide, gathered from
/// how a body uses it: the fields it reads (with their inferred types) and the
/// methods it calls. For deferred monomorphization (DESIGN.md 7.3), the dispatch
/// trampoline checks a JSON-built runtime type against this before specializing
/// the consumer -- a runtime type missing a required field is rejected at the
/// boundary rather than miscompiled.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct StructuralReq {
    pub fields: BTreeMap<String, Type>,
    pub methods: BTreeSet<String>,
}

/// Resolution of the program-dependent rvalues the constraint core cannot type on
/// its own: a call's result, a field/element's type, a named nominal type, a
/// global's type. Returning `None` leaves the position open (a fresh variable),
/// which the integration layer fills with the real lookup.
pub trait Resolver {
    /// The result type of a call, given its already-resolved argument types.
    fn call_type(&mut self, callee: &prepoly_mir::Callee, args: &[Type]) -> Option<Type>;
    /// The declared type of `field` read from a base of type `base`.
    fn field_type(&self, base: &Type, field: &str) -> Option<Type>;
    /// The nominal type a record/variant literal `name` constructs.
    fn nominal(&self, name: &str) -> Option<Type>;
    /// The type of a module-level global by source name.
    fn global_type(&self, name: &str) -> Option<Type>;
}

/// A [`Resolver`] that resolves nothing -- every program-dependent position stays
/// open. Used to exercise the constraint core in isolation.
pub struct NullResolver;

impl Resolver for NullResolver {
    fn call_type(&mut self, _: &prepoly_mir::Callee, _: &[Type]) -> Option<Type> {
        None
    }
    fn field_type(&self, _: &Type, _: &str) -> Option<Type> {
        None
    }
    fn nominal(&self, _: &str) -> Option<Type> {
        None
    }
    fn global_type(&self, _: &str) -> Option<Type> {
        None
    }
}

/// A [`Resolver`] backed by the HIR program: it resolves record/sum field types
/// and the nominal type a literal constructs from the program's type definitions.
/// Calls and globals are left open here -- typing a call requires instantiating
/// its callee, which only the monomorphizer can drive (the deep integration).
pub struct ProgramResolver<'p> {
    program: &'p Program,
    /// The module the body being typed belongs to, for name resolution.
    module: Vec<String>,
}

impl<'p> ProgramResolver<'p> {
    pub fn new(program: &'p Program, module: Vec<String>) -> Self {
        Self { program, module }
    }

    /// The program type definition a nominal `ty` resolves to, if any.
    fn type_def(&self, ty: &Type) -> Option<&TypeInfo> {
        match ty {
            Type::Record(n) | Type::Sum(n) => self.program.type_by_id(n.id),
            _ => None,
        }
    }
}

impl Resolver for ProgramResolver<'_> {
    /// A direct call to a function with a fully concrete annotated return type
    /// yields that type. A callee whose return is inferred (unannotated) needs
    /// its body instantiated at the argument types, which only the monomorphizer
    /// can drive, so it is left open here.
    fn call_type(&mut self, callee: &prepoly_mir::Callee, _args: &[Type]) -> Option<Type> {
        match callee {
            prepoly_mir::Callee::Free(sym) => self
                .program
                .functions
                .get(sym)
                .and_then(|f| f.signature.ret_ty.clone())
                .filter(is_concrete),
            _ => None,
        }
    }

    /// A record's named field, or a field common to every variant of a sum
    /// (DESIGN.md 13.4) -- the same rule the AST checker uses.
    fn field_type(&self, base: &Type, field: &str) -> Option<Type> {
        match &self.type_def(base)?.kind {
            TypeKind::Record { fields, .. } => fields
                .iter()
                .find(|f| f.name == field)
                .and_then(|f| f.resolved_ty.clone()),
            // A variant-qualified field (`Variant.field`, from a variant pattern
            // binding) resolves in that variant; a bare name must be common to every
            // variant of the sum (DESIGN.md 13.4).
            TypeKind::Sum { variants } => match field.split_once('.') {
                Some((variant, fname)) => variants
                    .iter()
                    .find(|v| v.name == variant)
                    .and_then(|v| v.fields.iter().find(|f| f.name == fname))
                    .and_then(|f| f.resolved_ty.clone()),
                None => {
                    let mut common = None;
                    for v in variants {
                        let f = v.fields.iter().find(|f| f.name == field)?;
                        common = f.resolved_ty.clone();
                    }
                    common
                }
            },
        }
    }

    fn nominal(&self, name: &str) -> Option<Type> {
        self.program
            .resolve_type(&self.module, name)
            .map(TypeInfo::type_ref)
    }

    fn global_type(&self, _: &str) -> Option<Type> {
        None
    }
}

/// Infer the concrete type of every local in `body`, given its concrete parameter
/// types and (optional) declared return type. Returns the locals' resolved types
/// in `LocalId` order, or the type errors found while solving.
pub fn infer_body<R: Resolver>(
    body: &MirBody,
    params: &[Type],
    captures: &[(prepoly_mir::LocalId, Type)],
    ret: Option<&Type>,
    fallible: bool,
    resolver: &mut R,
) -> Result<Vec<Type>, Vec<MirTypeError>> {
    let mut t = BodyTyper::new();
    // One fresh type variable per local.
    for _ in 0..body.locals.len() {
        let v = t.solver.fresh(InferenceVarKind::Source);
        t.locals.push(v);
    }
    // Seed parameters with their concrete instance types.
    for (i, p) in body.params.iter().enumerate() {
        if let Some(pty) = params.get(i) {
            let pv = t.locals[p.index()].clone();
            t.unify(&pv, pty);
        }
    }
    // Seed a closure's captured locals (not parameters) with their types.
    for (local, ty) in captures {
        let cv = t.locals[local.index()].clone();
        t.unify(&cv, ty);
    }
    // In a fallible callable the result is `Result<ok, err>`, but a bare
    // `return v` yields the *Ok payload* `v` (codegen wraps it), while an
    // `error(x)`/`expr!` return yields a `Result`. So a non-`Result` return
    // operand is checked against the Ok payload, a `Result` one against the whole
    // result type.
    let ok_payload = ret
        .filter(|_| fallible)
        .and_then(|r| result_ok_payload(&t.solver.resolve(r)));
    // Generate constraints over every block.
    for block in &body.blocks {
        for stmt in &block.stmts {
            t.stmt(stmt, resolver);
        }
        if let Terminator::Return(op) = &block.term
            && let Some(r) = ret
        {
            let ot = t.operand_type(op);
            let ot_resolved = t.solver.resolve(&ot);
            let target = match &ok_payload {
                Some(ok) if !is_result(&ot_resolved) => ok.clone(),
                _ => r.clone(),
            };
            // Skip an implicit/empty `return` (a void operand) in a value-
            // returning callable: lowering inserts a trailing `Return(void)`
            // for fall-through, which is not a real value return.
            let skip = matches!(ot_resolved, Type::Void)
                && !matches!(t.solver.resolve(&target), Type::Void);
            if !skip {
                t.unify(&ot, &target);
            }
        }
    }
    t.default_literals();
    if t.errors.is_empty() {
        Ok(t.locals.iter().map(|v| t.solver.resolve(v)).collect())
    } else {
        Err(t.errors)
    }
}

/// Gather the structural requirement a body places on its `deferred` parameter --
/// the fields it reads and the methods it calls on that value -- by typing the
/// body with `deferred` left as a fresh, unseeded type variable. This is the
/// consumer side of deferred monomorphization (DESIGN.md 7.3): the runtime
/// dispatch checks a boundary value's runtime-built type against this requirement
/// before specializing the consumer, so a type missing a required field is
/// rejected at the boundary rather than miscompiled.
pub fn gather_requirements(body: &MirBody, deferred: prepoly_mir::LocalId) -> StructuralReq {
    let mut t = BodyTyper::new();
    for _ in 0..body.locals.len() {
        let v = t.solver.fresh(InferenceVarKind::Source);
        t.locals.push(v);
    }
    let deferred_var = t.locals[deferred.index()].clone();
    let mut resolver = NullResolver;
    for block in &body.blocks {
        for stmt in &block.stmts {
            t.stmt(stmt, &mut resolver);
        }
    }
    // A field used only in a numeric-literal context (`p.age + 1`) defaults like
    // any literal, so the requirement records its concrete class.
    t.default_literals();
    // The deferred parameter's accesses were recorded under its variable's id.
    let id = match t.solver.resolve(&deferred_var) {
        Type::Unknown(id) => id,
        _ => return StructuralReq::default(),
    };
    let mut req = t.requirements.remove(&id).unwrap_or_default();
    // Resolve each required field to its final inferred type.
    for fty in req.fields.values_mut() {
        *fty = t.solver.resolve(fty);
    }
    req
}

struct BodyTyper {
    solver: Solver,
    locals: Vec<Type>,
    /// Numeric-literal variables to default after solving: `(var_id, is_int)`.
    lits: Vec<(u32, bool)>,
    /// Structural requirements accumulated per *unresolved* type variable: the
    /// fields/methods a still-deferred value is used with. Keyed by the variable's
    /// (resolved) id at the point of access.
    requirements: HashMap<u32, StructuralReq>,
    errors: Vec<MirTypeError>,
}

impl BodyTyper {
    fn new() -> Self {
        Self {
            solver: Solver::new(),
            locals: Vec::new(),
            lits: Vec::new(),
            requirements: HashMap::new(),
            errors: Vec::new(),
        }
    }

    /// Record that a deferred value (an unresolved variable `id`) is read with
    /// field `name` of type `fty`.
    fn note_field(&mut self, id: u32, name: &str, fty: Type) {
        self.requirements
            .entry(id)
            .or_default()
            .fields
            .insert(name.to_string(), fty);
    }

    /// Record that a deferred value (an unresolved variable `id`) has method
    /// `name` called on it.
    fn note_method(&mut self, id: u32, name: &str) {
        self.requirements
            .entry(id)
            .or_default()
            .methods
            .insert(name.to_string());
    }

    /// Unify two types in a value-flow context, recording a JIT-time type error on
    /// conflict. Uses Prepoly's flow leniency (see [`BodyTyper::flow_unify`]) so a
    /// value flowing into a nullable or a slice/array position is accepted the
    /// same way the AST checker accepts it.
    fn unify(&mut self, a: &Type, b: &Type) {
        if self.flow_unify(a, b) {
            return;
        }
        let ra = self.solver.resolve(a);
        let rb = self.solver.resolve(b);
        let message =
            self.solver.unify(&ra, &rb).err().unwrap_or_else(|| {
                format!("cannot unify `{}` with `{}`", ra.display(), rb.display())
            });
        self.errors.push(MirTypeError { message });
    }

    /// Unify with value-flow leniency: a top-level nullable is stripped from each
    /// side (`T` flows into `T?` and a guarded `T?` into `T`), and a slice/fixed
    /// array reconcile by element type. This mirrors the AST checker's
    /// `flow_unify`, so the JIT-time check does not reject a flow the front end
    /// already accepted.
    fn flow_unify(&mut self, a: &Type, b: &Type) -> bool {
        let a = strip_nullable(self.solver.resolve(a));
        let b = strip_nullable(self.solver.resolve(b));
        if let (Some(x), Some(y)) = (array_elem(&a), array_elem(&b)) {
            return self.flow_unify(&x, &y);
        }
        self.solver.unify(&a, &b).is_ok()
    }

    fn fresh(&mut self) -> Type {
        self.solver.fresh(InferenceVarKind::Source)
    }

    /// The type of an operand. A numeric constant becomes a fresh variable
    /// recorded for kind defaulting, so a contextual use (`let x: int64 = 5`)
    /// can pin its exact kind before it defaults.
    fn operand_type(&mut self, op: &Operand) -> Type {
        match op {
            Operand::Local(id) => self.locals[id.index()].clone(),
            Operand::Const(lit) => match lit {
                Literal::Int(_) => self.literal(true),
                Literal::Float(_) => self.literal(false),
                Literal::Bool(_) => Type::Bool,
                Literal::Str(_) => Type::Str,
                Literal::Void => Type::Void,
                Literal::Null => Type::Nullable(Box::new(self.fresh())),
            },
        }
    }

    fn literal(&mut self, is_int: bool) -> Type {
        let ty = self.solver.fresh(InferenceVarKind::Source);
        if let Type::Unknown(id) = ty {
            self.lits.push((id, is_int));
        }
        ty
    }

    fn stmt<R: Resolver>(&mut self, stmt: &MirStmt, resolver: &mut R) {
        match stmt {
            MirStmt::Assign(local, rv) => {
                let rt = self.rvalue_type(rv, resolver);
                let lt = self.locals[local.index()].clone();
                self.unify(&lt, &rt);
            }
            MirStmt::Eval(rv) => {
                self.rvalue_type(rv, resolver);
            }
            // `arr[i] = v`: the element type equals the stored value's type. A
            // field store needs the record's field type from the resolver.
            MirStmt::Store(place, value) => {
                let vt = self.operand_type(value);
                if let Some(target) = self.place_type(place, resolver) {
                    self.unify(&target, &vt);
                }
            }
            MirStmt::SetGlobal(_, _) => {}
        }
    }

    /// The type a place projection reads/writes, when derivable from the core
    /// (an array element) or the resolver (a record field).
    fn place_type<R: Resolver>(&mut self, place: &Place, resolver: &mut R) -> Option<Type> {
        let base = self.locals[place.local.index()].clone();
        match place.proj.as_slice() {
            [Projection::Index(_)] => match self.solver.resolve(&base) {
                Type::Slice(e) | Type::Array(e, _) => Some(*e),
                _ => None,
            },
            [Projection::Field(name)] => {
                let rb = self.solver.resolve(&base);
                // A deferred base (an unresolved variable) records a field
                // requirement; the field's type is a fresh variable refined by use.
                if let Type::Unknown(id) = rb {
                    let fv = self.fresh();
                    self.note_field(id, name, fv.clone());
                    Some(fv)
                } else {
                    resolver.field_type(&rb, name)
                }
            }
            _ => None,
        }
    }

    fn rvalue_type<R: Resolver>(&mut self, rv: &Rvalue, resolver: &mut R) -> Type {
        match rv {
            Rvalue::Use(op) => self.operand_type(op),
            Rvalue::Bin(op, a, b) => {
                let ta = self.operand_type(a);
                let tb = self.operand_type(b);
                if is_comparison(*op) {
                    self.unify(&ta, &tb);
                    Type::Bool
                } else if matches!(op, BinOp::And | BinOp::Or) {
                    self.unify(&ta, &Type::Bool);
                    self.unify(&tb, &Type::Bool);
                    Type::Bool
                } else {
                    // Arithmetic/bitwise/string-concat: both operands and the
                    // result share one type.
                    self.unify(&ta, &tb);
                    ta
                }
            }
            Rvalue::Un(UnaryOp::Not, _) => Type::Bool,
            Rvalue::Un(_, a) => self.operand_type(a),
            Rvalue::Array(elems) => {
                let elem = self.fresh();
                for e in elems {
                    let et = self.operand_type(e);
                    self.unify(&elem, &et);
                }
                Type::Slice(Box::new(elem))
            }
            Rvalue::Load(place) => self
                .place_type(place, resolver)
                .unwrap_or_else(|| self.fresh()),
            Rvalue::Global(name) => resolver.global_type(name).unwrap_or_else(|| self.fresh()),
            Rvalue::Call(callee, args) => {
                let arg_types: Vec<Type> = args.iter().map(|a| self.operand_type(a)).collect();
                // A method call on a deferred receiver records a method requirement.
                if let prepoly_mir::Callee::Method(m) = callee
                    && let Some(Type::Unknown(id)) =
                        arg_types.first().map(|t| self.solver.resolve(t))
                {
                    self.note_method(id, m);
                }
                resolver
                    .call_type(callee, &arg_types)
                    .unwrap_or_else(|| self.fresh())
            }
            Rvalue::Record { ty, .. } | Rvalue::Variant { ty, .. } => {
                resolver.nominal(ty).unwrap_or_else(|| self.fresh())
            }
            Rvalue::Closure { .. } => self.fresh(),
        }
    }

    /// A numeric literal whose kind context never pinned defaults to its class's
    /// canonical type (int32 / float64), matching the rest of the pipeline.
    fn default_literals(&mut self) {
        let lits = std::mem::take(&mut self.lits);
        for (id, is_int) in lits {
            let resolved = self.solver.resolve(&Type::Unknown(id));
            if matches!(resolved, Type::Unknown(_)) {
                let default = if is_int {
                    Type::Int(IntKind::I32)
                } else {
                    Type::Float(FloatKind::F64)
                };
                let _ = self.solver.unify(&resolved, &default);
            }
        }
    }
}

fn is_comparison(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge
    )
}

/// Whether a (resolved) type is the built-in `Result`.
fn is_result(ty: &Type) -> bool {
    matches!(ty, Type::Sum(n) if n.is_result_type())
}

/// The `Ok` payload of a `Result<ok, err>` type, if `ty` is one.
fn result_ok_payload(ty: &Type) -> Option<Type> {
    match ty {
        Type::Sum(n) => n.result_payloads().map(|(ok, _)| ok.clone()),
        _ => None,
    }
}

/// A nullable's element type (one level), else the type unchanged -- so value
/// flow treats `T` and `T?` as compatible.
fn strip_nullable(ty: Type) -> Type {
    match ty {
        Type::Nullable(inner) => *inner,
        other => other,
    }
}

/// The element type of a slice or fixed array, letting value flow reconcile
/// slices, fixed arrays, and array literals by their elements.
fn array_elem(ty: &Type) -> Option<Type> {
    match ty {
        Type::Slice(e) | Type::Array(e, _) => Some((**e).clone()),
        _ => None,
    }
}

/// Whether a type is fully concrete -- safe to use as a fixed call return type
/// without instantiating the callee. Excludes inference variables and `Self`; a
/// nominal type's own name is concrete (its monomorphized payloads are handled by
/// the monomorphizer, not this fast path).
fn is_concrete(ty: &Type) -> bool {
    match ty {
        Type::Unknown(_) | Type::SelfType => false,
        Type::Nullable(t)
        | Type::Slice(t)
        | Type::ConstOf(t)
        | Type::Mut(t)
        | Type::Ref(t)
        | Type::Array(t, _) => is_concrete(t),
        Type::Fun(params, ret) => params.iter().all(is_concrete) && is_concrete(ret),
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use prepoly_mir::{BasicBlock, BlockId, LocalDecl, LocalId, TypeRef};

    /// A local declaration with a fresh type variable, as lowering produces.
    fn local(id: u32) -> LocalDecl {
        LocalDecl {
            ty: TypeRef::var(id),
            name: None,
        }
    }

    /// `fun add(a, b) { return a + b }`: locals _0=a, _1=b, _2=a+b.
    fn add_body() -> MirBody {
        MirBody {
            locals: vec![local(0), local(1), local(2)],
            blocks: vec![BasicBlock {
                stmts: vec![MirStmt::Assign(
                    LocalId(2),
                    Rvalue::Bin(
                        BinOp::Add,
                        Operand::Local(LocalId(0)),
                        Operand::Local(LocalId(1)),
                    ),
                )],
                term: Terminator::Return(Operand::Local(LocalId(2))),
            }],
            entry: BlockId(0),
            params: vec![LocalId(0), LocalId(1)],
        }
    }

    #[test]
    fn binary_operands_and_result_share_one_type() {
        // Seeding both parameters as int32 forces the sum local to int32 through
        // the operand-equality constraint -- the inferred instance type.
        let body = add_body();
        let locals = infer_body(
            &body,
            &[Type::Int(IntKind::I32), Type::Int(IntKind::I32)],
            &[],
            Some(&Type::Int(IntKind::I32)),
            false,
            &mut NullResolver,
        )
        .expect("well-typed");
        assert_eq!(locals[2], Type::Int(IntKind::I32));
    }

    #[test]
    fn mismatched_operands_are_a_jit_time_error() {
        // `a + b` with a:int32, b:string cannot unify -- the JIT-time check the
        // deferred model needs (mono's forward propagation would just stall).
        let body = add_body();
        let errs = infer_body(
            &body,
            &[Type::Int(IntKind::I32), Type::Str],
            &[],
            None,
            false,
            &mut NullResolver,
        )
        .expect_err("operand mismatch must be rejected");
        assert!(!errs.is_empty());
    }

    #[test]
    fn return_operand_must_match_declared_result() {
        // Returning the int32 sum where the body is declared to yield `string`
        // is a conflict at the return constraint.
        let body = add_body();
        let errs = infer_body(
            &body,
            &[Type::Int(IntKind::I32), Type::Int(IntKind::I32)],
            &[],
            Some(&Type::Str),
            false,
            &mut NullResolver,
        )
        .expect_err("return type mismatch must be rejected");
        assert!(!errs.is_empty());
    }

    #[test]
    fn numeric_literals_default_when_context_is_absent() {
        // `_0 = 1 + 2; return _0` with no declared return: the literals default
        // to int32 and the result follows.
        let body = MirBody {
            locals: vec![local(0)],
            blocks: vec![BasicBlock {
                stmts: vec![MirStmt::Assign(
                    LocalId(0),
                    Rvalue::Bin(
                        BinOp::Add,
                        Operand::Const(Literal::Int(1)),
                        Operand::Const(Literal::Int(2)),
                    ),
                )],
                term: Terminator::Return(Operand::Local(LocalId(0))),
            }],
            entry: BlockId(0),
            params: vec![],
        };
        let locals = infer_body(&body, &[], &[], None, false, &mut NullResolver).expect("ok");
        assert_eq!(locals[0], Type::Int(IntKind::I32));
    }

    #[test]
    fn infers_a_real_lowered_function() {
        // The constraint core works on MIR produced by the real lowering, not just
        // hand-built bodies: lowering `add` and seeding its parameters at int32
        // forces every temporary (and the return) to int32 with no conflict. The
        // function is call-free, so the NullResolver suffices.
        let ast =
            prepoly_parser::parse("fun add(a: int32, b: int32) -> int32 {\n  return a + b\n}\n")
                .expect("parse");
        let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = prepoly_mir::lower_program(&program);
        let f = mir
            .functions
            .iter()
            .find(|f| f.name == "add")
            .expect("add lowered");
        let i32 = Type::Int(IntKind::I32);
        let locals = infer_body(
            &f.body,
            &[i32.clone(), i32.clone()],
            &[],
            Some(&i32),
            false,
            &mut NullResolver,
        )
        .expect("well-typed real body");
        // No local is left as a string/bool/etc.; every concrete local is int32.
        for ty in &locals {
            assert!(
                *ty == i32 || matches!(ty, Type::Unknown(_) | Type::Void),
                "unexpected local type {ty:?} in {locals:?}"
            );
        }
        // The parameters definitely resolved to int32.
        assert_eq!(locals[f.body.params[0].index()], i32);
        assert_eq!(locals[f.body.params[1].index()], i32);
    }

    #[test]
    fn program_resolver_types_a_record_field_access() {
        // `p.x` lowers to a field load; the ProgramResolver types it from the
        // record definition, so seeding `p` as `Point` and declaring `int32`
        // checks clean, while declaring `string` is a JIT-time conflict.
        let src = "type Point = {\n  x: int32\n  y: int32\n}\n\
                   fun get_x(p: Point) -> int32 {\n  return p.x\n}\n";
        let ast = prepoly_parser::parse(src).expect("parse");
        let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let point = program
            .resolve_type(&["main".into()], "Point")
            .map(TypeInfo::type_ref)
            .expect("Point type");
        let mir = prepoly_mir::lower_program(&program);
        let f = mir
            .functions
            .iter()
            .find(|f| f.name == "get_x")
            .expect("get_x lowered");
        let i32 = Type::Int(IntKind::I32);

        let mut ok_res = ProgramResolver::new(&program, vec!["main".into()]);
        infer_body(
            &f.body,
            std::slice::from_ref(&point),
            &[],
            Some(&i32),
            false,
            &mut ok_res,
        )
        .expect("field access types to int32");

        let mut bad_res = ProgramResolver::new(&program, vec!["main".into()]);
        let errs = infer_body(
            &f.body,
            &[point],
            &[],
            Some(&Type::Str),
            false,
            &mut bad_res,
        )
        .expect_err("int32 field cannot satisfy a string return");
        assert!(!errs.is_empty());
    }

    #[test]
    fn program_resolver_types_a_direct_call_by_annotated_return() {
        // A call to a function with a concrete annotated return is typed by that
        // return: `caller` returning `helper(n)` (helper -> string) checks against
        // a `string` result and conflicts with an `int32` one.
        let src = "fun helper(n: int32) -> string {\n  return \"x\"\n}\n\
                   fun caller(n: int32) -> string {\n  return helper(n)\n}\n";
        let ast = prepoly_parser::parse(src).expect("parse");
        let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = prepoly_mir::lower_program(&program);
        let f = mir
            .functions
            .iter()
            .find(|f| f.name == "caller")
            .expect("caller lowered");
        let i32 = Type::Int(IntKind::I32);

        let mut ok_res = ProgramResolver::new(&program, vec!["main".into()]);
        infer_body(
            &f.body,
            std::slice::from_ref(&i32),
            &[],
            Some(&Type::Str),
            false,
            &mut ok_res,
        )
        .expect("call result is string");

        let mut bad_res = ProgramResolver::new(&program, vec!["main".into()]);
        let errs = infer_body(
            &f.body,
            std::slice::from_ref(&i32),
            &[],
            Some(&i32),
            false,
            &mut bad_res,
        )
        .expect_err("string call result cannot satisfy an int32 return");
        assert!(!errs.is_empty());
    }

    #[test]
    fn gathers_structural_requirement_of_a_deferred_parameter() {
        // `describe` reads `p.age` (used with `+ 1`, so int32) and `p.label`, so a
        // deferred `p` must structurally provide both -- the requirement runtime
        // dispatch checks a JSON-built type against (DESIGN.md 7.3).
        let src = "fun describe(p) {\n  let next = p.age + 1\n  let l = p.label\n}\n";
        let ast = prepoly_parser::parse(src).expect("parse");
        let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = prepoly_mir::lower_program(&program);
        let f = mir
            .functions
            .iter()
            .find(|f| f.name == "describe")
            .expect("describe lowered");
        let req = gather_requirements(&f.body, f.body.params[0]);
        assert!(
            req.fields.contains_key("age") && req.fields.contains_key("label"),
            "requirement must include both accessed fields: {req:?}"
        );
        // `age` is used in a numeric-literal context, so its required type is int32.
        assert_eq!(req.fields.get("age"), Some(&Type::Int(IntKind::I32)));
        assert!(req.methods.is_empty());
    }
}
