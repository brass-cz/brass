//! Type checking for Prepoly. The passes that have high value
//! and low false-positive risk run statically: type-name resolution, interface
//! enforcement, match exhaustiveness, const checking, and the
//! no-implicit-numeric-conversion check. Remaining type errors are caught at
//! runtime by the typed runtime, matching the design's deferred checking.

pub mod constck;
pub mod constraint;
pub mod exhaustive;
pub mod flow;
pub mod globals;
pub mod hm;
pub mod infer;
pub mod interface;
pub mod narrow;
pub mod structural;
mod walk;

// The constraint solver lives in `prepoly_solver` (shared with the JIT-time MIR
// inference); re-export it so `crate::solver` / `crate::unify` keep resolving.
pub use prepoly_solver::{solver, unify};

use std::collections::HashMap;

use prepoly_hir::{MethodInfo, NominalInfo, Program, TypeKind, TypedProgram, resolve};
use prepoly_lexer::Span;
use prepoly_parser::ast::*;

#[derive(Clone, Debug, PartialEq)]
pub struct TypeError {
    pub message: String,
    pub span: Span,
}

/// Static checking result plus typed expression information.
#[derive(Clone, Debug, PartialEq)]
pub struct Analysis {
    pub errors: Vec<TypeError>,
    pub typed: TypedProgram,
    /// Fully-concrete call instances per free-function symbol, the input to
    /// static monomorphization.
    pub fn_instances: std::collections::HashMap<String, Vec<Vec<prepoly_hir::Type>>>,
    /// Per record-type generalized scheme (inferred type parameters and the
    /// field/method signatures over them), keyed by the type's source name. The
    /// language server renders a method generically from this.
    pub schemes: std::collections::HashMap<String, prepoly_hir::TypeScheme>,
}

/// Run all static checks. Returns the errors found (sorted by position).
pub fn check(program: &Program) -> Vec<TypeError> {
    analyze(program).errors
}

/// Run all static checks and collect the typed-expression sidecar.
pub fn analyze(program: &Program) -> Analysis {
    let mut errors = Vec::new();
    errors.extend(resolve_annotations(program));
    errors.extend(check_constructions(program));
    errors.extend(interface::check(program));
    errors.extend(exhaustive::check(program));
    errors.extend(flow::check(program));
    errors.extend(globals::check(program));
    errors.extend(check_reserved_names(program));
    errors.extend(constck::check(program));
    // Hindley-Milner inference runs as the principled type-checking pass before
    // monomorphization: it infers principal types for the
    // functional core and rejects unification conflicts the ad-hoc pass may miss.
    errors.extend(hm::check(program));
    tracing::debug!(after_hm = errors.len(), "errors after Hindley-Milner pass");
    let infer = infer::analyze(program);
    errors.extend(infer.errors);
    errors.sort_by_key(|e| e.span.lo);
    errors.dedup();
    tracing::debug!(
        total = errors.len(),
        fn_instances = infer.fn_instances.len(),
        "type analysis finished"
    );
    Analysis {
        errors,
        typed: infer.typed,
        fn_instances: infer.fn_instances,
        schemes: infer.schemes,
    }
}

/// Reject user definitions that shadow a runtime builtin free function
/// or the `error` sugar. These names are
/// provided by the runtime/compiler rather than by a `.pp` file, so a user
/// definition would silently capture the standard library's internal calls
/// (e.g. `len(s)`) or, in the case of `error`, become dead code because
/// `error(x)` is always desugared to `Result.Err { error: x }`.
fn check_reserved_names(program: &Program) -> Vec<TypeError> {
    const RESERVED: &[&str] = &["len", "open", "spawn", "with", "sync", "error"];
    let mut errors = Vec::new();
    for name in RESERVED {
        if let Some(info) = program.functions.get(*name) {
            errors.push(TypeError {
                message: format!("`{name}` is a builtin and cannot be redefined"),
                span: info.signature.span,
            });
        }
    }
    errors
}

/// Verify record/variant literals name a known type and variant. Without this,
/// an unknown constructor silently produces a void value at runtime.
fn check_constructions(program: &Program) -> Vec<TypeError> {
    struct V<'a> {
        program: &'a Program,
        errors: Vec<TypeError>,
    }
    impl walk::ExprVisitor for V<'_> {
        fn visit(&mut self, e: &Expr) {
            match e {
                // These validation passes have no module context. For a unique
                // type name (a direct table key) the precise checks run; a name
                // defined in several modules is only checked for existence here
                // and resolved precisely by module-aware inference.
                // An empty name is an anonymous structure literal `{ f: v }`
                // (a structural record), not a named-type construction.
                Expr::TypeLit(name, _, span) if name != "Self" && !name.is_empty() => match self.program.types.get(name) {
                    Some(info) if info.is_sum() => self.errors.push(TypeError {
                        message: format!("`{name}` is a sum type; construct a variant with `{name}.Variant {{ ... }}`"),
                        span: *span,
                    }),
                    Some(_) => {}
                    None if self.program.has_type_named(name) => {}
                    None => self.errors.push(TypeError {
                        message: format!("unknown type `{name}`"),
                        span: *span,
                    }),
                },
                Expr::VariantLit(t, v, _, span) if t != "Self" => match self.program.types.get(t) {
                    Some(info) if info.variant(v).is_none() => self.errors.push(TypeError {
                        message: format!("`{t}` has no variant `{v}`"),
                        span: *span,
                    }),
                    Some(_) => {}
                    None if self.program.has_type_named(t) => {}
                    None => self.errors.push(TypeError {
                        message: format!("unknown type `{t}`"),
                        span: *span,
                    }),
                },
                _ => {}
            }
        }
    }
    let mut v = V {
        program,
        errors: Vec::new(),
    };
    walk::walk_program_exprs(program, &mut v);
    v.errors
}

/// Verify every syntactic type annotation names a type visible from the module
/// it appears in. Nominal names are keyed by the
/// type's unique symbol, and each annotation is resolved from its declaring
/// module (own/unique, this module's qualified definition, or an imported one).
fn resolve_annotations(program: &Program) -> Vec<TypeError> {
    let kinds: HashMap<String, NominalInfo> = program
        .types
        .iter()
        .map(|(symbol, info)| {
            let nominal = match &info.kind {
                TypeKind::Record { .. } => NominalInfo::record(info.id),
                TypeKind::Sum { .. } => NominalInfo::sum(info.id),
            };
            (symbol.clone(), nominal)
        })
        .collect();
    // A type annotation may only name a type visible from its module: this
    // module's own definition, a built-in, the standard-library prelude, or one
    // brought in by `import`. Colliding names resolve
    // through the module-qualified symbol; a unique name additionally checks
    // visibility so a public-but-not-imported type from another module does not
    // leak into annotations.
    let resolve_nominal = |module: &[String], name: &str| -> Option<NominalInfo> {
        if let Some(n) = kinds.get(&prepoly_hir::qualify(name, module)) {
            return Some(*n);
        }
        if let Some(origin) = program.import_origins.get(module).and_then(|o| o.get(name))
            && let Some(n) = kinds.get(&prepoly_hir::qualify(name, origin))
        {
            return Some(*n);
        }
        let info = program.types.get(name)?;
        let def = &info.module;
        let visible = def == module
            || def.is_empty()
            || def.first().map(String::as_str) == Some("std")
            || program
                .module_imports
                .get(module)
                .is_some_and(|names| names.iter().any(|n| n == name));
        visible.then(|| kinds.get(name).copied()).flatten()
    };

    // Annotations tagged with the module they appear in, so a bare type name
    // resolves against that module's visible types.
    let mut tes: Vec<(Vec<String>, TypeExpr)> = Vec::new();
    let push_decl =
        |module: &[String], local: Vec<TypeExpr>, out: &mut Vec<(Vec<String>, TypeExpr)>| {
            out.extend(local.into_iter().map(|te| (module.to_vec(), te)));
        };
    for info in program.types.values() {
        let mut local = Vec::new();
        match &info.kind {
            TypeKind::Record { fields, methods } => {
                for f in fields {
                    if let Some(t) = &f.ty {
                        local.push(t.clone());
                    }
                }
                for m in methods.values() {
                    collect_method(m, &mut local);
                }
            }
            TypeKind::Sum { variants } => {
                for v in variants {
                    for f in &v.fields {
                        if let Some(t) = &f.ty {
                            local.push(t.clone());
                        }
                    }
                    for m in v.methods.values() {
                        collect_method(m, &mut local);
                    }
                }
            }
        }
        push_decl(&info.module, local, &mut tes);
    }
    for f in program.functions.values() {
        let mut local = Vec::new();
        for p in &f.signature.params {
            if let Some(t) = &p.ty {
                local.push(t.clone());
            }
        }
        if let Some(r) = &f.signature.ret {
            local.push(r.clone());
        }
        collect_block(&f.decl.body, &mut local);
        push_decl(&f.module, local, &mut tes);
    }
    for init in &program.inits {
        let mut local = Vec::new();
        for stmt in &init.stmts {
            collect_stmt(stmt, &mut local);
        }
        push_decl(&init.path, local, &mut tes);
    }
    let mut errors = Vec::new();
    for (module, te) in &tes {
        if let Err(msg) = resolve(te, |n| resolve_nominal(module, n)) {
            errors.push(TypeError {
                message: msg,
                span: te.span(),
            });
        }
    }
    errors
}

fn collect_method(m: &MethodInfo, out: &mut Vec<TypeExpr>) {
    for p in &m.signature.params {
        if let Some(t) = &p.ty {
            out.push(t.clone());
        }
    }
    if let Some(r) = &m.signature.ret {
        out.push(r.clone());
    }
    if let Some(b) = &m.decl.body {
        collect_block(b, out);
    }
}

fn collect_block(b: &Block, out: &mut Vec<TypeExpr>) {
    for s in &b.stmts {
        collect_stmt(s, out);
    }
}

fn collect_stmt(stmt: &Stmt, out: &mut Vec<TypeExpr>) {
    match stmt {
        Stmt::Let { ty, value, .. } => {
            if let Some(t) = ty {
                out.push(t.clone());
            }
            collect_expr(value, out);
        }
        Stmt::Assign { target, value, .. } => {
            collect_expr(target, out);
            collect_expr(value, out);
        }
        Stmt::Expr(expr) => collect_expr(expr, out),
        Stmt::While { cond, body, .. } => {
            collect_expr(cond, out);
            collect_block(body, out);
        }
        Stmt::For { iter, body, .. } => {
            collect_expr(iter, out);
            collect_block(body, out);
        }
        Stmt::Return(Some(expr), _) => collect_expr(expr, out),
        Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

fn collect_expr(expr: &Expr, out: &mut Vec<TypeExpr>) {
    match expr {
        Expr::Str(segs, _) => {
            for seg in segs {
                if let StrSeg::Expr(expr) = seg {
                    collect_expr(expr, out);
                }
            }
        }
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) => collect_expr(inner, out),
        Expr::Binary(_, left, right, _) | Expr::Range(left, right, _) => {
            collect_expr(left, out);
            collect_expr(right, out);
        }
        Expr::Call(callee, args, _) => {
            collect_expr(callee, out);
            for arg in args {
                collect_expr(&arg.expr, out);
            }
        }
        Expr::Field(base, _, _) => collect_expr(base, out),
        Expr::Index(base, index, _) => {
            collect_expr(base, out);
            collect_expr(index, out);
        }
        Expr::Closure(params, body, _) => {
            for param in params {
                if let Some(ty) = &param.ty {
                    out.push(ty.clone());
                }
            }
            collect_expr(body, out);
        }
        Expr::Array(items, _) => {
            for item in items {
                collect_expr(item, out);
            }
        }
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
            for (_, value) in fields {
                collect_expr(value, out);
            }
        }
        Expr::If(cond, then, els, _) => {
            collect_expr(cond, out);
            collect_block(then, out);
            if let Some(els) = els {
                collect_expr(els, out);
            }
        }
        Expr::IfLet(_, scrutinee, then, els, _) => {
            collect_expr(scrutinee, out);
            collect_block(then, out);
            if let Some(els) = els {
                collect_expr(els, out);
            }
        }
        Expr::Match(scrutinee, arms, _) => {
            collect_expr(scrutinee, out);
            for arm in arms {
                collect_expr(&arm.body, out);
            }
        }
        Expr::Block(block, _) => collect_block(block, out),
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::{Analysis, analyze, check};
    use prepoly_hir::{Constness, IntKind, LoadedModule, Type, TypedExprKind, lower};
    use prepoly_parser::ast::BinOp;
    use prepoly_parser::parse;

    fn errs(src: &str) -> Vec<String> {
        let ast = parse(src).expect("parse");
        let (prog, lerr) = lower(&[LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(lerr.is_empty(), "lower errors: {lerr:?}");
        check(&prog).into_iter().map(|e| e.message).collect()
    }

    fn analysis(src: &str) -> Analysis {
        let ast = parse(src).expect("parse");
        let (prog, lerr) = lower(&[LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(lerr.is_empty(), "lower errors: {lerr:?}");
        analyze(&prog)
    }

    #[test]
    fn witness_free_container_element_is_resolved_from_use() {
        // A constructor that builds an empty array field (`items = []`, no
        // element pushed) leaves the field's element open. A later mutating
        // call on the binding pins it: `b.add("a", 1)` stores a `Pair` into
        // `self.items[i]`, and the indexed-place store (Stage 1) commits that
        // through the binding's element variable. So `b.first_k()` is known to
        // return `string` -- accepted into a `string`, rejected into an
        // `int32`. This is the checker-side resolution the witness-free
        // constructor relies on.
        let pair_box = "type Pair = {\n    k\n    v\n}\n\
             type Box = {\n    items\n}\n\
             fun Box.new() {\n    let items = []\n    return Self { items: items }\n}\n\
             fun Box.add(self, k, v) {\n    self.items[0] = Pair { k: k, v: v }\n}\n\
             fun Box.first_k(self) {\n    return self.items[0].k\n}\n";
        let ok = errs(&format!(
            "{pair_box}fun main() {{\n    let b = Box.new()\n    b.add(\"a\", 1)\n    let x: string = b.first_k()\n}}\n"
        ));
        assert!(ok.is_empty(), "{ok:?}");
        let bad = errs(&format!(
            "{pair_box}fun main() {{\n    let b = Box.new()\n    b.add(\"a\", 1)\n    let x: int32 = b.first_k()\n}}\n"
        ));
        assert!(
            bad.iter()
                .any(|m| m.contains("`string`") && m.contains("`int32`")),
            "{bad:?}"
        );
    }

    #[test]
    fn scheme_generalizes_a_generic_container_over_shared_params() {
        // `Box`'s element type is inferred. Co-checking its methods links the
        // `items` element to the `add` parameters through the indexed store of a
        // `Pair { k, v }` (the unification edge the type and its methods share),
        // so the scheme has two inferred parameters and `add`'s `k`/`v` are
        // expressed over them -- the user's "type and methods share one type
        // environment" generalization.
        let a = analysis(
            "type Pair = {\n    k\n    v\n}\n\
             type Box = {\n    items\n}\n\
             fun Box.add(self, k, v) {\n    self.items[0] = Pair { k: k, v: v }\n}\n",
        );
        assert!(a.errors.is_empty(), "{:?}", a.errors);
        let scheme = a.schemes.get("Box").expect("Box scheme");
        assert_eq!(scheme.params.len(), 2, "two inferred params: {scheme:?}");
        let add = scheme.methods.get("add").expect("add in scheme");
        // `self` is the bare type; `k` and `v` are inferred parameters that are
        // exactly the scheme's quantified variables.
        let param_var = |name: &str| -> Option<u32> {
            add.params
                .iter()
                .find(|(n, _)| n == name)
                .and_then(|(_, t)| match t {
                    Type::Unknown(id) => Some(*id),
                    _ => None,
                })
        };
        let k = param_var("k").expect("k is an inference var");
        let v = param_var("v").expect("v is an inference var");
        assert!(
            scheme.params.contains(&k),
            "k is a scheme param: {scheme:?}"
        );
        assert!(
            scheme.params.contains(&v),
            "v is a scheme param: {scheme:?}"
        );
        assert_ne!(k, v, "k and v are distinct params");
    }

    #[test]
    fn indexed_store_refines_an_open_record_element_from_use() {
        // A store of a concrete record into an array element typed `Pair<?, ?>`
        // refines the element's open key/value through the solver's record-
        // substitution unification, so a later read of `.v` is concretely typed.
        // `add("a", 5)` makes `items` element `Pair<string, int32>`, so `first_v`
        // returns `int32` -- assigning it into a `string` is rejected. Without the
        // record unification + committing store the element would stay `Pair<?,
        // ?>` and the mismatch would go unreported.
        let prog = "type Pair = {\n    k\n    v\n}\n\
             type Box = {\n    items\n}\n\
             fun Box.empty() {\n    let items = []\n    return Self { items: items }\n}\n\
             fun Box.add(self, k, v) {\n    self.items[0] = Pair { k: k, v: v }\n}\n\
             fun Box.first_v(self) {\n    return self.items[0].v\n}\n";
        let bad = errs(&format!(
            "{prog}fun main() {{\n    let b = Box.empty()\n    b.add(\"a\", 5)\n    let x: string = b.first_v()\n}}\n"
        ));
        assert!(
            bad.iter()
                .any(|m| m.contains("`int32`") && m.contains("`string`")),
            "the value type must resolve to int32 from the store: {bad:?}"
        );
        let ok = errs(&format!(
            "{prog}fun main() {{\n    let b = Box.empty()\n    b.add(\"a\", 5)\n    let x: int32 = b.first_v()\n}}\n"
        ));
        assert!(ok.is_empty(), "{ok:?}");
    }

    #[test]
    fn store_refines_a_record_element_already_typed_with_open_fields() {
        // The first store pins `items`' element to `Pair<?, ?>` (its fields come
        // from reading the still-open element, the table's `_grow` witness shape);
        // the second store of a concrete `Pair<string, int32>` then refines those
        // open fields through the solver's record-substitution unification, so
        // `first_v` is `int32`. This is the case `_grow` + `_insert` hits in
        // `HashMap`: without unifying two same-nominal records field-wise the
        // element would stay `Pair<?, ?>` and the value type never resolve.
        let prog = "type Pair = {\n    k\n    v\n}\n\
             type Box = {\n    items\n}\n\
             fun Box.empty() {\n    let items = []\n    return Self { items: items }\n}\n\
             fun Box.add(self, k, v) {\n\
             \x20   let w = self.items[0]\n\
             \x20   self.items[1] = Pair { k: w.k, v: w.v }\n\
             \x20   self.items[2] = Pair { k: k, v: v }\n}\n\
             fun Box.first_v(self) {\n    return self.items[0].v\n}\n";
        let bad = errs(&format!(
            "{prog}fun main() {{\n    let b = Box.empty()\n    b.add(\"a\", 5)\n    let x: string = b.first_v()\n}}\n"
        ));
        assert!(
            bad.iter()
                .any(|m| m.contains("`int32`") && m.contains("`string`")),
            "the value type must resolve to int32 through record unification: {bad:?}"
        );
    }

    #[test]
    fn constructor_inferred_return_reflects_a_nullable_slot_element() {
        // A witness-free slot container: `new()` fills an `infer?[]` field with
        // `null`, and `put` stores a non-null `Pair`. The full check (not the
        // weaker light return inference) observes the `push(null)` and the store,
        // so the constructor's inferred return carries the nullable element type:
        // `value_at` returns the value type (`int32`), nullable. Assigning it into
        // a `string` is rejected; into an `int32?` is accepted.
        let prog = "type Pair = {\n    k\n    v\n}\n\
             type Slots = {\n    items: infer?[]\n}\n\
             fun Slots.new() {\n    let items = []\n    items.push(null)\n    return Self { items: items }\n}\n\
             fun Slots.put(self, k, v) {\n    self.items[0] = Pair { k: k, v: v }\n}\n\
             fun Slots.value_at(self) {\n    if let e = self.items[0] {\n        return e.v\n    }\n    return null\n}\n";
        let bad = errs(&format!(
            "{prog}fun main() {{\n    let s = Slots.new()\n    s.put(\"a\", 7)\n    let x: string = s.value_at()\n}}\n"
        ));
        assert!(
            bad.iter()
                .any(|m| m.contains("int32") || m.contains("nullable")),
            "value type must resolve to int32 (nullable): {bad:?}"
        );
        let ok = errs(&format!(
            "{prog}fun main() {{\n    let s = Slots.new()\n    s.put(\"a\", 7)\n    let x: int32? = s.value_at()\n}}\n"
        ));
        assert!(ok.is_empty(), "{ok:?}");
    }

    #[test]
    fn scheme_of_a_monomorphic_record_has_no_params() {
        // A fully-annotated record infers no type parameters, so its scheme is
        // monomorphic (empty `params`).
        let a = analysis(
            "type Point = {\n    x: int32\n    y: int32\n}\n\
             fun Point.sum(self) -> int32 {\n    return self.x + self.y\n}\n",
        );
        assert!(a.errors.is_empty(), "{:?}", a.errors);
        let scheme = a.schemes.get("Point").expect("Point scheme");
        assert!(scheme.params.is_empty(), "monomorphic: {scheme:?}");
    }

    #[test]
    fn collects_concrete_call_instances_for_monomorphization() {
        // A polymorphic function called with two concrete
        // types records two instances; the input to static monomorphization.
        let a = analysis(
            "fun id(x) {\n    return x\n}\nfun main() {\n    let a: int32 = id(5)\n    let b: string = id(\"s\")\n}\n",
        );
        assert!(a.errors.is_empty(), "{:?}", a.errors);
        let instances = a.fn_instances.get("id").expect("id instances");
        assert!(
            instances.contains(&vec![Type::Int(IntKind::I32)]),
            "{instances:?}"
        );
        assert!(instances.contains(&vec![Type::Str]), "{instances:?}");
        assert_eq!(instances.len(), 2, "two distinct instances: {instances:?}");
    }

    #[test]
    fn analyze_collects_expression_types() {
        let a = analysis("fun main() {\n    let x = 1 + 2\n}\n");
        assert!(a.errors.is_empty(), "{:?}", a.errors);
        assert!(
            a.typed
                .expressions
                .iter()
                .any(|expr| expr.kind == TypedExprKind::Binary(BinOp::Add)
                    && expr.ty == Type::Int(IntKind::I32)),
            "{:?}",
            a.typed.expressions
        );
    }

    #[test]
    fn analyze_records_expected_fixed_array_type() {
        let a = analysis("fun main() {\n    let values: int32[2] = [1, 2]\n}\n");
        assert!(a.errors.is_empty(), "{:?}", a.errors);
        assert!(
            a.typed.expressions.iter().any(|expr| {
                matches!(
                    &expr.ty,
                    Type::Array(inner, 2) if **inner == Type::Int(IntKind::I32)
                )
            }),
            "{:?}",
            a.typed.expressions
        );
    }

    #[test]
    fn indexed_store_pins_open_array_element() {
        // A store `self.items[i] = v` into an unannotated array field pins the
        // field's element type during checking, the way `push` pins it on the
        // read side. So the first store fixes `items` to `int32[]` and the
        // second store of a `string` clashes. Without the store-side pin the
        // element would stay open and the clash would go unreported.
        let e = errs(
            "type Box = {\n    items\n}\n\
             fun Box.fill(self) {\n    self.items[0] = 1\n    self.items[1] = \"x\"\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("`string`") && m.contains("`int32`")),
            "expected an element-type clash, got {e:?}"
        );
    }

    #[test]
    fn indexed_store_of_consistent_type_is_accepted() {
        // Two stores of the same concrete element type leave the field
        // consistently typed and report nothing -- the pin only fires while the
        // element is open, so it does not manufacture a spurious clash.
        let e = errs(
            "type Box = {\n    items\n}\n\
             fun Box.fill(self) {\n    self.items[0] = 1\n    self.items[1] = 2\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn analyze_records_const_expression_constness() {
        let a = analysis("fun main() {\n    const x = 1\n    let y = x\n}\n");
        assert!(a.errors.is_empty(), "{:?}", a.errors);
        assert!(
            a.typed.expressions.iter().any(|expr| {
                expr.ty == Type::ConstOf(Box::new(Type::Int(IntKind::I32)))
                    && expr.constness == Constness::Const
            }),
            "{:?}",
            a.typed.expressions
        );
    }

    #[test]
    fn analyze_uses_distinct_unknowns_for_unannotated_variant_fields() {
        let a = analysis(
            "type Pair =\n    | Both { left, right }\nfun main(pair: Pair) {\n    match pair { Both { left, right } => left == right }\n}\n",
        );
        assert!(a.errors.is_empty(), "{:?}", a.errors);
        let unknown_id_for = |name: &str| {
            a.typed
                .expressions
                .iter()
                .find_map(|expr| match (&expr.kind, &expr.ty) {
                    (TypedExprKind::Ident(ident), Type::Unknown(id)) if ident == name => Some(*id),
                    _ => None,
                })
        };
        let left = unknown_id_for("left").expect("left binding typed as unknown");
        let right = unknown_id_for("right").expect("right binding typed as unknown");
        assert_ne!(left, right, "{:?}", a.typed.expressions);
    }

    #[test]
    fn record_literal_substitutes_unannotated_field_type() {
        let e = errs(
            "type Box = {\n    value\n}\nfun main() {\n    let b = Box { value: 1 }\n    let s: string = b.value\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn method_body_param_unknown_keeps_call_site_argument_type() {
        let e = errs(
            "type Box = {\n    value\n}\nfun Box.set(self, value) {\n    self.value = value\n}\nfun main() {\n    let box = Box { value: 1 }\n    box.set(\"bad\")\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn static_method_body_param_unknown_substitutes_return_field() {
        let e = errs(
            "type Box = {\n    value\n}\nfun Box.new(value) {\n    return Self { value: value }\n}\nfun main() {\n    let box = Box.new(1)\n    let s: string = box.value\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn interface_missing_method_is_reported() {
        let e = errs(
            "type Showable = {\n    to_string(self) -> string\n}\ntype User: Showable = {\n    name: string\n}\n",
        );
        assert!(
            e.iter().any(|m| m.contains("missing method `to_string`")),
            "{e:?}"
        );
    }

    #[test]
    fn interface_satisfied_ok() {
        let e = errs(
            "type Showable = {\n    to_string(self) -> string\n}\ntype User: Showable = {\n    name: string\n}\nfun User.to_string(self) -> string { return self.name }\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn interface_field_covariance_is_rejected() {
        // Fields are mutable, so an interface field overridden with a structural
        // subtype is unsound and must be rejected.
        let e = errs(
            "type Named = { name: string }\ntype HasBreed: Named = { name: string  breed: string }\ntype Box = { value: Named }\ntype DogBox: Box = { value: HasBreed }\n",
        );
        assert!(
            e.iter().any(|m| m.contains("`DogBox` field `value`")),
            "{e:?}"
        );
    }

    #[test]
    fn conflicting_parent_field_types_are_rejected() {
        // Two interfaces declare `name` with different types; a type implementing
        // both inherits a conflict that neither parent's independent check would
        // catch (the implementing field is even unannotated).
        let e = errs(
            "type Person = { name: int32 }\ntype Animal = { name: string }\ntype Family: Person, Animal = { name }\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("conflicting types for field `name`")),
            "{e:?}"
        );
    }

    #[test]
    fn agreeing_parent_field_types_are_ok() {
        // Same field name, same type across both parents is not a conflict.
        let e =
            errs("type A = { id: int32 }\ntype B = { id: int32 }\ntype C: A, B = { id: int32 }\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn interface_method_parameter_covariance_is_rejected() {
        // A narrower method parameter than the interface declares is unsound:
        // a caller could pass an Animal the DogConsumer cannot handle.
        let e = errs(
            "type Animal = { sound: string }\ntype Dog: Animal = { sound: string  breed: string }\ntype Consumer = { consume(self, a: Animal) -> void }\ntype DogConsumer: Consumer = { }\nfun DogConsumer.consume(self, a: Dog) -> void { }\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("method `consume` signature is not compatible")),
            "{e:?}"
        );
    }

    #[test]
    fn interface_method_signature_mismatch_is_reported() {
        let e = errs(
            "type Show = {\n    show(self, x: int32) -> string\n}\ntype Bad: Show = { }\nfun Bad.show(self, x: string) -> int32 { return 1 }\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("method `show` signature is not compatible")),
            "{e:?}"
        );
    }

    #[test]
    fn interface_unknown_field_is_constrained_at_call_site() {
        let e = errs(
            "type Container = {\n    value\n}\ntype IntBox: Container = {\n    value: int32\n}\nfun get(c: Container) -> string {\n    return c.value\n}\nfun main() {\n    let box = IntBox { value: 1 }\n    let value = get(box)\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn interface_unknown_field_is_constrained_in_annotated_binding() {
        let e = errs(
            "type Container = {\n    value\n}\ntype IntBox: Container = {\n    value: int32\n}\nfun main() {\n    let c: Container = IntBox { value: 1 }\n    let s: string = c.value\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn concrete_interface_field_constrains_unannotated_record_field() {
        let e = errs(
            "type Named = {\n    name: string\n}\ntype User: Named = {\n    name\n}\nfun main() {\n    let user = User { name: 1 }\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn concrete_interface_field_constrains_unannotated_sum_variant_field() {
        let e = errs(
            "type Named = {\n    name: string\n}\ntype Pet: Named =\n    | Cat { name }\nfun main() {\n    let pet = Pet.Cat { name: 1 }\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn concrete_interface_method_param_constrains_unannotated_implementation_param() {
        let e = errs(
            "type Setter = {\n    set(self, value: string) -> void\n}\ntype User: Setter = { }\nfun User.set(self, value) {\n    let n: int32 = value\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn concrete_interface_method_return_constrains_inferred_implementation_return() {
        let e = errs(
            "type Show = {\n    show(self) -> string\n}\ntype Bad: Show = { }\nfun Bad.show(self) {\n    return 1\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn interface_unknown_method_param_is_constrained_at_call_site() {
        let e = errs(
            "type Consumer = {\n    consume(self, value)\n}\ntype StringConsumer: Consumer = { }\nfun StringConsumer.consume(self, value: string) {\n}\nfun use(c: Consumer) {\n    c.consume(1)\n}\nfun main() {\n    let c = StringConsumer { }\n    use(c)\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn interface_unknown_method_return_is_constrained_at_call_site() {
        let e = errs(
            "type Getter = {\n    get(self)\n}\ntype IntGetter: Getter = { }\nfun IntGetter.get(self) -> int32 {\n    return 1\n}\nfun use(g: Getter) {\n    let s: string = g.get()\n}\nfun main() {\n    let g = IntGetter { }\n    use(g)\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn non_exhaustive_match_is_reported() {
        let e = errs(
            "type T = | A | B | C\nfun f(x: T) {\n    return match x {\n        A => 1,\n        B => 2,\n    }\n}\n",
        );
        assert!(e.iter().any(|m| m.contains("non-exhaustive")), "{e:?}");
    }

    #[test]
    fn const_assignment_is_reported() {
        let e = errs("fun main() {\n    const p = 1\n    p = 2\n}\n");
        assert!(e.iter().any(|m| m.contains("const")), "{e:?}");
    }

    #[test]
    fn top_level_const_assignment_is_reported() {
        let e = errs("const a = 4\na += 1\n");
        assert!(e.iter().any(|m| m.contains("const")), "{e:?}");
    }

    #[test]
    fn top_level_const_cannot_be_assigned_in_function_body() {
        // A const global is immutable everywhere in the file.
        let e = errs("const value = 1\nfun main() {\n    value = 2\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot assign to const value `value`")),
            "{e:?}"
        );
    }

    #[test]
    fn local_binding_shadows_top_level_const() {
        // A local `let` reusing a const global's name is a distinct, mutable
        // binding, so assigning to it is allowed.
        let e = errs("const value = 1\nfun main() {\n    let value = 2\n    value = 3\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn const_mutating_method_call_is_reported() {
        let e = errs(
            "type Counter = {\n    count: int32\n}\nfun Counter.set(self, value: int32) {\n    self.count = value\n}\nfun main() {\n    const c = Counter { count: 1 }\n    c.set(2)\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot call mutating method `set` on const value `c`")),
            "{e:?}"
        );
    }

    #[test]
    fn const_array_mutating_method_is_rejected() {
        // A const array is immutable: the growable-array mutators
        // (`push`/`insert`/`remove`/`pop`) modify it in place, so they are rejected
        // -- the same rule as element assignment and a const record's mutators.
        for method in ["push(2)", "insert(0, 2)", "remove(0)", "pop()"] {
            let src = format!("const a = [1]\nfun main() {{\n    a.{method}\n}}\n");
            let e = errs(&src);
            assert!(
                e.iter().any(|m| m.contains("on const value `a`")),
                "`a.{method}` on a const array should be rejected: {e:?}"
            );
        }
        // A mutable array still accepts them.
        let ok = errs("fun main() {\n    let a = [1]\n    a.push(2)\n}\n");
        assert!(ok.is_empty(), "mutable array push must be allowed: {ok:?}");
    }

    #[test]
    fn const_array_reachable_from_a_const_root_is_immutable() {
        // An array reachable from a const struct/array root is itself immutable.
        let e = errs("const m = [[1], [2]]\nfun main() {\n    m[0].push(3)\n}\n");
        assert!(
            e.iter().any(|m| m.contains("on const value `m`")),
            "pushing into an element of a const array should be rejected: {e:?}"
        );
    }

    #[test]
    fn const_to_an_unannotated_mutating_function_is_allowed() {
        // An unannotated parameter the body mutates is a private deep copy (an
        // inferred `mut`), so the mutation never reaches the caller. Passing a
        // const array is therefore allowed -- only a `ref(mut(T))` write-through
        // parameter rejects a const.
        let ok =
            errs("fun f(arr) {\n    arr.push(99)\n}\nconst a = [1]\nfun main() {\n    f(a)\n}\n");
        assert!(
            ok.is_empty(),
            "a const to an unannotated (copied) mutating parameter must be allowed: {ok:?}"
        );
        // A `ref(mut(int32[]))` parameter writes through, so a const is rejected.
        let e = errs(
            "fun f(arr: ref(mut(int32[]))) {\n    arr.push(99)\n}\nconst a = [1]\nfun main() {\n    f(a)\n}\n",
        );
        assert!(
            e.iter().any(|m| m.contains("`a`") && m.contains("mutable")),
            "passing a const array to a `ref(mut(T))` parameter should be rejected: {e:?}"
        );
    }

    #[test]
    fn const_through_a_transitive_write_through_function_is_rejected() {
        // Write-through is interprocedural: `g` takes `ref(mut(P))` and writes
        // through it, and `f` only forwards its parameter to `g`, so `f`'s
        // parameter is a write-through position too. Passing a const through the
        // forwarding `f` must be rejected, and the chain holds at any depth.
        let two = errs(
            "type P = { x: int32 }\nfun g(p: ref(mut(P))) { p.x = 5 }\nfun f(p) { g(p) }\nconst c = P { x: 1 }\nfun main() {\n    f(c)\n}\n",
        );
        assert!(
            two.iter()
                .any(|m| m.contains("`c`") && m.contains("mutable")),
            "a const forwarded one level into a write-through parameter should be rejected: {two:?}"
        );
        let three = errs(
            "type P = { x: int32 }\nfun deep(p: ref(mut(P))) { p.x = 9 }\nfun mid(p) { deep(p) }\nfun top(p) { mid(p) }\nconst c = P { x: 1 }\nfun main() {\n    top(c)\n}\n",
        );
        assert!(
            three
                .iter()
                .any(|m| m.contains("`c`") && m.contains("mutable")),
            "a const forwarded three levels into a write-through parameter should be rejected: {three:?}"
        );
        // Forwarding a const into a parameter that only *copies* it (an
        // unannotated mutating callee) places no write-through requirement, so the
        // const argument is accepted -- the mutation hits the callee's own copy.
        let copied = errs(
            "type P = { x: int32 }\nfun g(p) { p.x = 5 }\nfun f(p) { g(p) }\nconst c = P { x: 1 }\nfun main() {\n    f(c)\n}\n",
        );
        assert!(
            copied.is_empty(),
            "a const forwarded into a copying mutator must be allowed: {copied:?}"
        );
        // A function that only reads its forwarded parameter places no requirement
        // either, so a const argument is accepted.
        let ok = errs(
            "type P = { x: int32 }\nfun read(p) -> int32 { return p.x }\nfun fwd(p) -> int32 { return read(p) }\nconst c = P { x: 7 }\nfun main() {\n    println(fwd(c))\n}\n",
        );
        assert!(
            ok.is_empty(),
            "a const forwarded only into a reader must be allowed: {ok:?}"
        );
    }

    #[test]
    fn mut_ref_annotation_requires_a_mutable_argument() {
        // A `ref(mut(T))` parameter is a mutable reference: it requires a mutable
        // argument even with no mutation in the body (a const is rejected, a `let`
        // accepted). A bare `mut(T)` is passed by copy, so it has no such
        // requirement -- the next case checks a const is accepted there.
        let e = errs(
            "fun f(arr: ref(mut(int32[]))) {\n    println(arr.len())\n}\nconst a = [1]\nfun main() {\n    f(a)\n}\n",
        );
        assert!(
            e.iter().any(|m| m.contains("`a`") && m.contains("mutable")),
            "a const argument to a `ref(mut(T))` parameter should be rejected: {e:?}"
        );
        let ok = errs(
            "fun f(arr: ref(mut(int32[]))) {\n    arr.push(2)\n}\nfun main() {\n    let a = [1]\n    f(a)\n}\n",
        );
        assert!(
            ok.is_empty(),
            "a `let` argument to a `ref(mut(T))` parameter must be allowed: {ok:?}"
        );
    }

    #[test]
    fn const_to_a_copied_array_parameter_is_allowed() {
        // A non-reference array parameter is passed by deep copy, so a const
        // argument is fine even though the callee mutates its (own) copy.
        let ok = errs(
            "fun f(arr: int32[]) {\n    arr.push(2)\n}\nconst a = [1]\nfun main() {\n    f(a)\n}\n",
        );
        assert!(
            ok.is_empty(),
            "a const argument to a copied array parameter must be allowed: {ok:?}"
        );
    }

    #[test]
    fn mutating_an_infer_parameter_is_rejected() {
        // `a: infer` receives a read-only deep copy, so mutating it through its
        // reference is rejected; reading it is fine.
        let e = errs("fun f(a: infer) {\n    a.push(1)\n}\nfun main() {\n    f([1, 2])\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot mutate parameter `a`") && m.contains("infer")),
            "mutating an `infer` parameter should be rejected: {e:?}"
        );
        let ok = errs(
            "fun f(a: infer) -> int32 {\n    return a[0]\n}\nfun main() {\n    let v: int32 = f([1, 2])\n}\n",
        );
        assert!(
            ok.is_empty(),
            "reading an `infer` parameter must be allowed: {ok:?}"
        );
        // Writing back through a loop variable (`e *= 2`) mutates the iterated
        // array, so it is rejected on a read-only `infer` parameter too.
        let loop_e = errs(
            "fun f(a: infer) {\n    for e in a {\n        e *= 2\n    }\n}\nfun main() {\n    f([1, 2])\n}\n",
        );
        assert!(
            loop_e
                .iter()
                .any(|m| m.contains("cannot mutate parameter `a`")),
            "mutating an `infer` parameter through a loop variable should be rejected: {loop_e:?}"
        );
    }

    #[test]
    fn mutating_an_unannotated_parameter_is_allowed() {
        // An unannotated parameter the body mutates is inferred as a private `mut`
        // copy, so mutating it is fine (the caller is unaffected at runtime).
        let ok =
            errs("fun f(a) {\n    a.push(1)\n}\nfun main() {\n    let xs = [1]\n    f(xs)\n}\n");
        assert!(
            ok.is_empty(),
            "mutating an unannotated parameter must be allowed: {ok:?}"
        );
    }

    #[test]
    fn const_primitive_to_a_reassigning_function_is_allowed() {
        // Reassigning a parameter (`x = ...`) only rebinds the local; it is not a
        // through-reference mutation, so the parameter is not mutable and a copied
        // const primitive argument stays valid.
        let ok = errs("fun f(x) {\n    x = 5\n}\nconst c = 1\nfun main() {\n    f(c)\n}\n");
        assert!(
            ok.is_empty(),
            "a const primitive to a reassigning function must be allowed: {ok:?}"
        );
    }

    #[test]
    fn const_readonly_method_call_is_allowed() {
        let e = errs(
            "type Counter = {\n    count: int32\n}\nfun Counter.get(self) -> int32 {\n    return self.count\n}\nfun main() {\n    const c = Counter { count: 1 }\n    let value: int32 = c.get()\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn const_alias_field_mutation_is_rejected() {
        // Aliasing a const record shares the same value, so mutating through the
        // alias must be rejected.
        let e = errs(
            "type Point = { x: int32 }\nfun main() {\n    const p = Point { x: 1 }\n    let q = p\n    q.x = 2\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot assign to const value `q`")),
            "{e:?}"
        );
    }

    #[test]
    fn const_alias_mutating_method_is_rejected() {
        let e = errs(
            "type Counter = {\n    n: int32\n}\nfun Counter.bump(self) { self.n = self.n + 1 }\nfun main() {\n    const c = Counter { n: 0 }\n    let alias = c\n    alias.bump()\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot call mutating method `bump` on const value `alias`")),
            "{e:?}"
        );
    }

    #[test]
    fn nested_const_field_mutating_method_is_rejected() {
        // A mutating method on a field of a const value mutates the const, so it
        // is rejected even though the field is reached through a projection.
        let e = errs(
            "type Inner = {\n    n: int32\n}\nfun Inner.bump(self) { self.n = self.n + 1 }\ntype Outer = { inner: Inner }\nfun main() {\n    const o = Outer { inner: Inner { n: 0 } }\n    o.inner.bump()\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot call mutating method `bump`")),
            "{e:?}"
        );
    }

    #[test]
    fn nested_const_field_readonly_method_is_allowed() {
        let e = errs(
            "type Inner = {\n    n: int32\n}\nfun Inner.get(self) -> int32 { return self.n }\ntype Outer = { inner: Inner }\nfun main() {\n    const o = Outer { inner: Inner { n: 0 } }\n    let x: int32 = o.inner.get()\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn const_argument_to_write_through_function_is_rejected() {
        // Passing a const record into a `ref(mut(P))` parameter would mutate a
        // value declared immutable at the call site, through the reference.
        let e = errs(
            "type P = { x: int32 }\nfun f(p: ref(mut(P))) { p.x = 5 }\nfun main() {\n    const q = P { x: 1 }\n    f(q)\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot pass const value `q` to `f`")),
            "{e:?}"
        );
        // A bare-record parameter is a deep copy, so the same const is accepted:
        // the callee mutates its own copy, not the caller's const.
        let ok = errs(
            "type P = { x: int32 }\nfun f(p: P) { p.x = 5 }\nfun main() {\n    const q = P { x: 1 }\n    f(q)\n}\n",
        );
        assert!(
            ok.is_empty(),
            "a const to a copied record parameter must be allowed: {ok:?}"
        );
    }

    #[test]
    fn const_argument_to_readonly_function_is_allowed() {
        let e = errs(
            "type P = { x: int32 }\nfun f(p: P) -> int32 { return p.x }\nfun main() {\n    const q = P { x: 1 }\n    let v: int32 = f(q)\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn primitive_const_copy_is_mutable() {
        // A primitive const is copied on binding, so the copy is an independent
        // mutable local; this must not be a false positive.
        let e = errs("fun main() {\n    const MAX = 100\n    let x = MAX\n    x = 5\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn unknown_type_name_is_reported() {
        let e = errs("fun f(x: Nope) {\n}\n");
        assert!(e.iter().any(|m| m.contains("unknown type `Nope`")), "{e:?}");
    }

    #[test]
    fn top_level_binding_is_visible_in_function_body() {
        // A top-level `let` is in scope inside functions.
        let e = errs("let value = 1\nfun main() {\n    let s: string = value\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn top_level_binding_participates_in_function_return_inference() {
        // The global feeds the inferred return type of `get`, which then flows
        // to the annotated binding in `main`.
        let e = errs(
            "let value = 1\nfun get() {\n    return value\n}\nfun main() {\n    let s: string = get()\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn top_level_annotation_is_resolved() {
        let e = errs("let value: Nope = 1\n");
        assert!(e.iter().any(|m| m.contains("unknown type `Nope`")), "{e:?}");
    }

    #[test]
    fn incompatible_branch_returns_are_rejected() {
        // Two branches return incompatible concrete types, so the inferred
        // return type must be an error, not a fresh Unknown that satisfies the
        // `int32` annotation downstream.
        let e = errs(
            "fun f(flag: bool) {\n    if flag { return 1 } else { return \"x\" }\n}\nfun main() {\n    let y: int32 = f(false)\n}\n",
        );
        assert!(
            e.iter().any(|m| m.contains("incompatible return types")),
            "{e:?}"
        );
    }

    #[test]
    fn missing_return_in_non_void_function_is_rejected() {
        // The `if` has no `else`, so the function can fall through to its end
        // without returning the declared `int32`.
        let e = errs("fun f(b: bool) -> int32 {\n    if b { return 1 }\n}\n");
        assert!(
            e.iter().any(|m| m.contains("without returning a value")),
            "{e:?}"
        );
    }

    #[test]
    fn fallthrough_non_void_function_is_rejected() {
        let e = errs("fun f() -> int32 {\n    let x = 1\n}\n");
        assert!(
            e.iter().any(|m| m.contains("without returning a value")),
            "{e:?}"
        );
    }

    #[test]
    fn exhaustive_returns_are_accepted() {
        // Both branches return, and an infinite loop with no break never falls
        // through, so neither function is flagged.
        let e = errs(
            "fun f(b: bool) -> int32 {\n    if b { return 1 } else { return 2 }\n}\nfun g() -> int32 {\n    while true { }\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn break_outside_loop_is_rejected() {
        let e = errs("fun main() {\n    break\n}\n");
        assert!(
            e.iter().any(|m| m.contains("`break` outside of a loop")),
            "{e:?}"
        );
    }

    #[test]
    fn break_inside_loop_is_accepted() {
        let e = errs("fun main() {\n    while true {\n        break\n    }\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn assignment_to_non_place_is_rejected() {
        let e = errs("fun main() {\n    5 = 3\n}\n");
        assert!(
            e.iter().any(|m| m.contains("invalid assignment target")),
            "{e:?}"
        );
    }

    #[test]
    fn self_outside_method_is_rejected() {
        let e = errs("fun f() {\n    let x = self\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`self` is only valid inside a method")),
            "{e:?}"
        );
    }

    #[test]
    fn void_function_may_fall_through() {
        let e = errs("fun f() {\n    let x = 1\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn float_from_string_is_rejected() {
        // `from` is a numeric conversion; a string source is a static error
        // instead of silently producing 0.0 at runtime.
        let e = errs("fun main() {\n    let f = float64.from(\"abc\")\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`float64.from` expects a numeric value")),
            "{e:?}"
        );
    }

    #[test]
    fn int_parse_non_string_is_rejected() {
        let e = errs("fun main() {\n    let n = int32.parse(5)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`int32.parse` expects a string")),
            "{e:?}"
        );
    }

    #[test]
    fn numeric_from_and_parse_accept_valid_sources() {
        let e = errs(
            "fun main() {\n    let i: int32 = 3\n    let f = float64.from(i)\n    let n = int32.parse(\"42\")!\n    let s = string.from(true)\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn static_method_called_through_instance_is_rejected() {
        let e = errs(
            "type P = {\n    x: int32\n}\nfun P.make() -> P { return P { x: 0 } }\nfun main() {\n    let p = P { x: 1 }\n    p.make()\n}\n",
        );
        assert!(e.iter().any(|m| m.contains("is a static method")), "{e:?}");
    }

    #[test]
    fn method_call_on_primitive_is_rejected() {
        let e = errs("fun main() {\n    let x: int32 = 5\n    x.speak()\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`int32` has no method `speak`")),
            "{e:?}"
        );
    }

    #[test]
    fn field_access_on_primitive_is_rejected() {
        let e = errs("fun main() {\n    let x: int32 = 5\n    let y = x.foo\n}\n");
        assert!(
            e.iter().any(|m| m.contains("`int32` has no field `foo`")),
            "{e:?}"
        );
    }

    #[test]
    fn generic_method_use_rejects_primitive_argument() {
        // The body's `x.speak()` imposes a structural requirement that int32
        // cannot satisfy, caught when the call binds x to int32.
        let e = errs("fun f(x) {\n    x.speak()\n}\nfun main() {\n    f(1)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`int32` has no method `speak`")),
            "{e:?}"
        );
    }

    #[test]
    fn structural_method_use_accepts_matching_record() {
        let e = errs(
            "type Dog = {\n    name: string\n}\nfun Dog.speak(self) { println(self.name) }\nfun greet(a) {\n    a.speak()\n}\nfun main() {\n    greet(Dog { name: \"Rex\" })\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn array_push_wrong_element_is_rejected() {
        let e = errs("fun main() {\n    let xs = [1]\n    xs.push(\"x\")\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn annotated_empty_array_constrains_push() {
        // The annotation fixes the element type, so a wrong push is rejected
        // while a matching push passes.
        let bad = errs("fun main() {\n    let xs: string[] = []\n    xs.push(1)\n}\n");
        assert!(
            bad.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{bad:?}"
        );
        let ok = errs("fun main() {\n    let xs: string[] = []\n    xs.push(\"a\")\n}\n");
        assert!(ok.is_empty(), "{ok:?}");
    }

    #[test]
    fn array_index_assignment_checks_element_type() {
        let e = errs("fun main() {\n    let xs: int32[] = [1, 2]\n    xs[0] = \"bad\"\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn array_len_is_int64() {
        let e = errs("fun main() {\n    let xs: int32[] = [1]\n    let n: int64 = xs.len()\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn unit_variant_is_typed_as_its_sum() {
        // `Color.Red` is a value of `Color`, so assigning it to `int32` fails
        // instead of collapsing to a fresh Unknown.
        let e = errs("type Color = Red | Blue\nfun main() {\n    let n: int32 = Color.Red\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `Color` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn unknown_variant_access_is_rejected() {
        // `C.Z` where Z is not a variant must be an error rather than a fresh
        // Unknown produced by a bare field access on the type name.
        let e = errs("type C = A | B\nfun main() {\n    let c = C.Z\n}\n");
        assert!(
            e.iter().any(|m| m.contains("`C` has no variant `Z`")),
            "{e:?}"
        );
    }

    #[test]
    fn fielded_variant_without_braces_is_rejected() {
        let e = errs("type C =\n    | A { n: int32 }\n    | B\nfun main() {\n    let c = C.A\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("has fields; construct it with")),
            "{e:?}"
        );
    }

    #[test]
    fn unit_variant_keeps_nominal_sum_identity() {
        // A unit variant of one sum type is not assignable to an unrelated sum.
        let e = errs(
            "type A = P | Q\ntype B = P | Q\nfun take(a: A) { }\nfun main() {\n    take(B.P)\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `B` where `A` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn unit_variant_assignment_to_its_sum_is_accepted() {
        let e = errs("type Color = Red | Blue\nfun main() {\n    let c: Color = Color.Red\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn non_nullable_condition_is_accepted() {
        // A condition of any type is accepted; a non-nullable, non-bool type
        // (here an integer) is unconditionally truthy at runtime, so the type
        // checker reports nothing.
        let e = errs("fun main() {\n    let x: int32 = 3\n    if x { println(\"x\") }\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn nullable_identifier_condition_is_accepted() {
        let e = errs("fun main() {\n    let x: int32? = null\n    if x { println(\"has\") }\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn statically_dead_if_arm_with_bare_null_is_tolerated() {
        // Calling an unannotated `if`-branching function with a bare `null`
        // monomorphizes its parameter to `never?` (only ever null), making the
        // truthy arm statically unreachable -- narrowing there yields `never`, so
        // `a * 2` cannot type. That dead arm's errors are tolerated rather than
        // rejecting the program; the value call exercises the opposite arm.
        let src = "fun double(a) {\n    if a {\n        return a * 2\n    } else {\n        return error(\"null\")\n    }\n}\nfun main() {\n    let x = double(2)\n    let y = double(null)\n}\n";
        let e = errs(src);
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn circular_global_initializers_are_rejected() {
        let e = errs("let a = b\nlet b = a\n");
        assert!(
            e.iter()
                .any(|m| m.contains("global `b` is used before it is initialized")),
            "{e:?}"
        );
    }

    #[test]
    fn forward_global_reference_is_rejected() {
        let e = errs("let a = b\nlet b = 1\n");
        assert!(
            e.iter()
                .any(|m| m.contains("global `b` is used before it is initialized")),
            "{e:?}"
        );
    }

    #[test]
    fn backward_global_reference_is_accepted() {
        // A global may reference an earlier global and any function, regardless
        // of where the function is defined.
        let e = errs("let a = 1\nlet b = a\nfun compute() -> int32 {\n    return a\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn local_shadow_is_not_a_forward_global_reference() {
        // The local `b` introduced inside the closure shadows the later global,
        // so referencing it is not a forward reference to the global.
        let e = errs("let a = (b: int32) -> b\nlet b = 1\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn matching_branch_returns_are_accepted() {
        // Same-typed returns across branches stay valid.
        let e =
            errs("fun f(flag: bool) -> int32 {\n    if flag { return 1 } else { return 2 }\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn unknown_closure_param_type_is_reported() {
        let e = errs("fun main() {\n    let f = (x: Nope) -> x\n}\n");
        assert!(e.iter().any(|m| m.contains("unknown type `Nope`")), "{e:?}");
    }

    #[test]
    fn redefining_a_builtin_is_rejected() {
        // `len` is a runtime builtin used internally by the standard library;
        // a user definition would silently capture those calls.
        let e = errs("fun len(x) -> int32 {\n    return 0\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`len` is a builtin and cannot be redefined")),
            "{e:?}"
        );
    }

    #[test]
    fn redefining_the_error_sugar_is_rejected() {
        // `error(x)` is always desugared to `Result.Err { error: x }`, so a user
        // `fun error` would be dead code; reject it instead.
        let e = errs("fun error(x) {\n    return x\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`error` is a builtin and cannot be redefined")),
            "{e:?}"
        );
    }

    #[test]
    fn duplicate_function_parameter_is_reported() {
        let e = errs("fun f(x: int32, x: int32) {\n    return x\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("duplicate parameter `x` in function `f`")),
            "{e:?}"
        );
    }

    #[test]
    fn duplicate_method_parameter_is_reported() {
        let e = errs(
            "type Box = {\n    value: int32\n}\nfun Box.set(self, value: int32, value: int32) {\n    return value\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("duplicate parameter `value` in method `Box.set`")),
            "{e:?}"
        );
    }

    #[test]
    fn duplicate_closure_parameter_is_reported() {
        let e = errs("fun main() {\n    let f = (x, x) -> x\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("duplicate parameter `x` in closure")),
            "{e:?}"
        );
    }

    #[test]
    fn integer_literal_comparison_uses_contextual_integer_type() {
        let e = errs(
            "fun main() {\n    let x: uint8 = 10\n    if x == 10 { return }\n    if 10 == x { return }\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn integer_literal_comparison_converts_to_a_common_type() {
        // A `uint8` compared with an int literal converts both to a common int
        // type (the comparison is valid even if the literal is out of `uint8`'s
        // range -- it is simply never equal).
        let e = errs("fun main() {\n    let x: uint8 = 1\n    if x == 300 { return }\n}\n");
        assert!(
            e.is_empty(),
            "uint8 == int literal should compare via a common type: {e:?}"
        );
    }

    #[test]
    fn string_ordering_comparison_is_rejected() {
        // Strings have no ordering: `<`/`>`/`<=`/`>=` are numeric
        // only. Equality (`==`/`!=`) on strings still type-checks.
        let e = errs("fun main() {\n    let r = \"a\" < \"b\"\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("operator `<` is not defined for `string` and `string`")),
            "{e:?}"
        );
        let ok = errs("fun main() {\n    if \"a\" == \"b\" { return }\n}\n");
        assert!(ok.is_empty(), "string equality should type-check: {ok:?}");
    }

    #[test]
    fn int_float_mix_converts_to_float() {
        // An int operand with a float operand implicitly converts to that float.
        let e = errs("fun main() {\n    let a = 1\n    let b = 2.0\n    let c = a + b\n}\n");
        assert!(e.is_empty(), "int + float should convert to float: {e:?}");
    }

    #[test]
    fn annotation_mismatch_is_reported() {
        let e = errs("fun main() {\n    let a: int32 = 3.5\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `float64` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn record_literal_fields_are_checked() {
        let e = errs(
            "type Point = {\n    x: float64\n    y: float64\n}\nfun main() {\n    let p = Point { x: \"hello\" }\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `float64` is required")),
            "{e:?}"
        );
        assert!(
            e.iter()
                .any(|m| m.contains("`Point` literal is missing field `y`")),
            "{e:?}"
        );
    }

    #[test]
    fn duplicate_record_literal_field_is_reported() {
        let e = errs(
            "type Point = {\n    x: int32\n}\nfun main() {\n    let p = Point { x: 1, x: 2 }\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("`Point` literal repeats field `x`")),
            "{e:?}"
        );
    }

    #[test]
    fn missing_record_field_access_is_nullable_not_an_error() {
        // Accessing a field a structure does not have is not an error: it yields a
        // nullable (null at runtime), so the access is allowed but the result must
        // be null-checked before use as a non-null value.
        let e = errs(
            "type Point = {\n    x: int32\n}\nfun main() {\n    let p = Point { x: 1 }\n    let q = p.y\n    if q {\n        return 1\n    }\n    return 0\n}\n",
        );
        assert!(
            !e.iter().any(|m| m.contains("has no field")),
            "missing field access should not be an error: {e:?}"
        );
    }

    #[test]
    fn nullable_must_be_checked_before_use() {
        let e = errs("fun main() {\n    let x: int32? = null\n    let y = x + 1\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("nullable value must be checked for null before use")),
            "{e:?}"
        );
    }

    #[test]
    fn nullable_guard_narrows_after_return() {
        let e = errs(
            "fun f(x: int32?) -> int32 {\n    if !x {\n        return 0\n    }\n    return x + 1\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn nullable_not_null_test_narrows_truthy_branch() {
        let e = errs(
            "fun f(x: int32?) -> int32 {\n    if x != null {\n        return x + 1\n    }\n    return 0\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn null_branch_can_flow_to_nullable_annotation() {
        let e = errs(
            "fun f(flag: bool) -> int32? {\n    return if flag {\n        null\n    } else {\n        1\n    }\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn null_branch_infers_nullable_value() {
        let e = errs(
            "fun main() {\n    let x = if true {\n        null\n    } else {\n        1\n    }\n    let y = x + 1\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("nullable value must be checked for null before use")),
            "{e:?}"
        );
    }

    #[test]
    fn if_branch_type_mismatch_is_reported() {
        let e = errs("fun main() {\n    let x: int32 = if true { 1 } else { \"one\" }\n}\n");
        assert!(
            e.iter().any(|m| {
                m.contains("`if` branches have incompatible types `int32` and `string`")
            }),
            "{e:?}"
        );
    }

    #[test]
    fn match_arm_type_mismatch_is_reported() {
        let e = errs(
            "fun main() {\n    let x: int32 = match true { true => 1, false => \"one\" }\n}\n",
        );
        assert!(
            e.iter().any(|m| {
                m.contains("`match` branches have incompatible types `int32` and `string`")
            }),
            "{e:?}"
        );
    }

    #[test]
    fn literal_pattern_type_mismatch_is_reported() {
        let e = errs("fun main() {\n    match 1 { \"one\" => 1, _ => 0 }\n}\n");
        assert!(
            e.iter()
                .any(|m| { m.contains("literal pattern of type `string` cannot match `int32`") }),
            "{e:?}"
        );
    }

    #[test]
    fn integer_literal_pattern_uses_contextual_integer_type() {
        let e = errs("fun main() {\n    let x: uint8 = 1\n    match x { 1 => 1, _ => 0 }\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn integer_literal_pattern_rejects_out_of_range_context() {
        let e = errs("fun main() {\n    let x: uint8 = 1\n    match x { 300 => 1, _ => 0 }\n}\n");
        assert!(
            e.iter()
                .any(|m| { m.contains("literal pattern of type `int32` cannot match `uint8`") }),
            "{e:?}"
        );
    }

    #[test]
    fn variant_pattern_unknown_field_is_reported() {
        let e = errs(
            "type Shape =\n    | Circle { radius: int32 }\nfun main(s: Shape) {\n    match s { Circle { diameter } => 1 }\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("pattern `Circle` has no field `diameter`")),
            "{e:?}"
        );
    }

    #[test]
    fn variant_pattern_field_subpattern_is_checked() {
        let e = errs(
            "type Shape =\n    | Circle { radius: int32 }\nfun main(s: Shape) {\n    match s { Circle { radius: \"large\" } => 1 }\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| { m.contains("literal pattern of type `string` cannot match `int32`") }),
            "{e:?}"
        );
    }

    #[test]
    fn mixed_integer_widths_convert_to_the_wider() {
        // Two integers of different widths implicitly convert to the wider.
        let e =
            errs("fun main() {\n    let a: int8 = 1\n    let b: int32 = 2\n    let c = a + b\n}\n");
        assert!(e.is_empty(), "int8 + int32 should convert to int32: {e:?}");
    }

    #[test]
    fn generic_function_allows_mixed_integer_kinds() {
        // The function body is checked again with the concrete call-site types;
        // `uint8 + int32` implicitly converts to the wider signed int.
        let e = errs(
            "fun add(x, y) {\n    return x + y\n}\nfun main() {\n    let r = add(uint8.from(1)!, 2)\n}\n",
        );
        assert!(e.is_empty(), "uint8 + int32 should convert: {e:?}");
    }

    #[test]
    fn remainder_rejects_floats() {
        let e = errs("fun main() {\n    let x = 5.0 % 2.0\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("operator `%` is not defined for `float64` and `float64`")),
            "{e:?}"
        );
    }

    #[test]
    fn generic_function_rejects_float_remainder() {
        let e = errs(
            "fun rem(x, y) {\n    return x % y\n}\nfun main() {\n    let r = rem(5.0, 2.0)\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("operator `%` is not defined for `float64` and `float64`")),
            "{e:?}"
        );
    }

    #[test]
    fn fallible_integer_conversion_must_be_unwrapped() {
        let e = errs("fun main() {\n    let x: int32 = int32.from(1)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `Result<int32, string>` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn fallible_integer_conversion_can_be_propagated() {
        let e = errs("fun main() {\n    let x: int32 = int32.from(1)!\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn fallible_float_parse_can_be_propagated() {
        let e = errs("fun main() {\n    let x: float64 = float64.parse(\"1.5\")!\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn fallible_float_parse_must_be_unwrapped() {
        let e = errs("fun main() {\n    let x: float64 = float64.parse(\"1.5\")\n}\n");
        assert!(
            e.iter()
                .any(|m| m
                    .contains("cannot use `Result<float64, string>` where `float64` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn error_propagation_preserves_ok_payload_type() {
        // The unwrapped payload keeps its own type through `!`: a `uint8` payload
        // in a `string` position is reported as a `uint8` (numeric-to-numeric
        // positions convert implicitly, so a non-numeric target shows the
        // preserved type).
        let e = errs("fun main() {\n    let x: string = uint8.from(1)!\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `uint8` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn incompatible_inferred_error_payloads_are_rejected() {
        // One fallible body cannot mix a
        // propagated `string` error payload with a locally constructed `int32`
        // one; the inferred `Err` type must be single.
        let e = errs(
            "fun a() {\n    return error(\"text\")\n}\nfun b() {\n    let x = a()!\n    return error(1)\n}\nfun main() {\n    let _ = b()\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("incompatible error payloads: `string` and `int32`")),
            "{e:?}"
        );
    }

    #[test]
    fn consistent_inferred_error_payloads_are_accepted() {
        let e = errs(
            "fun a() {\n    return error(\"text\")\n}\nfun b() {\n    let x = a()!\n    return error(\"other\")\n}\nfun main() {\n    let _ = b()\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn error_only_function_ok_payload_in_required_position_is_rejected() {
        // A function that only returns error(...) has
        // no inferable Ok payload; using it at a concrete type is an error.
        let e = errs(
            "fun a() {\n    return error(\"text\")\n}\nfun main() {\n    let x: int32 = a()!\n}\n",
        );
        assert!(
            e.iter().any(|m| m.contains(
                "cannot infer the Ok payload type of a function that only returns errors"
            )),
            "{e:?}"
        );
    }

    #[test]
    fn error_only_function_ok_payload_unused_is_accepted() {
        // If the Ok payload never reaches a required position, the function is a
        // legal deferred contract (it can still be matched in the Err arm).
        let e = errs(
            "fun a() {\n    return error(\"text\")\n}\nfun main() {\n    match a() {\n        Ok { value } => println(\"ok\"),\n        Err { error } => println(error),\n    }\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn result_pattern_binds_substituted_ok_payload_type() {
        // Matching `Ok { value }` binds `value` at the inferred Ok
        // payload type (int32 here), so using it as a string is rejected.
        let e = errs(
            "fun parse(s: string) {\n    return int32.parse(s)!\n}\nfun main() {\n    match parse(\"5\") {\n        Ok { value } => {\n            let bad: string = value\n            println(bad)\n        },\n        Err { error } => println(error),\n    }\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn error_propagation_requires_result() {
        let e = errs("fun main() {\n    let x = 1!\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("error propagation requires `Result`, found `int32`")),
            "{e:?}"
        );
    }

    #[test]
    fn error_propagation_requires_result_return_context() {
        let e = errs("fun f() -> int32 {\n    return int32.parse(\"1\")!\n}\n");
        assert!(
            e.iter().any(|m| {
                m.contains("error propagation requires `Result` return type, found `int32`")
            }),
            "{e:?}"
        );
    }

    #[test]
    fn error_propagation_is_rejected_at_top_level() {
        let e = errs("let x = int32.parse(\"1\")!\n");
        assert!(
            e.iter()
                .any(|m| m
                    .contains("error propagation cannot be used outside a function or closure")),
            "{e:?}"
        );
    }

    #[test]
    fn fallible_closure_returns_result_type() {
        let e = errs(
            "fun main() {\n    let f = () -> int32.parse(\"1\")!\n    let x: int32 = f()\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m
                    .contains("cannot use `Result<int32, string>` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn result_match_binds_ok_payload_type() {
        // The match binds `value` at the Ok payload type (`uint8`): using it where
        // a string is required is rejected, confirming the payload type.
        let e = errs(
            "fun main() {\n    let r = uint8.from(1)\n    let z = match r {\n        Ok { value } => {\n            let s: string = value\n            0\n        },\n        Err { error } => 0,\n    }\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `uint8` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn inferred_function_result_keeps_ok_payload_type() {
        // The inferred `Result` Ok payload survives a second propagation: a
        // `uint8` payload used at a non-numeric type still names `uint8`
        // (numeric positions now convert implicitly, so `string` is the probe).
        let e = errs(
            "fun get_u8() {\n    return uint8.from(1)!\n}\nfun main() {\n    let x: string = get_u8()!\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `uint8` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn instantiated_function_return_type_is_used() {
        let e = errs("fun id(x) {\n    return x\n}\nfun main() {\n    let x: string = id(1)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn inferred_fallible_function_returns_result_type() {
        let e = errs(
            "fun get_value(fail: bool) {\n    if fail {\n        return error(\"bad\")\n    }\n    return 1\n}\nfun main() {\n    let x: int32 = get_value(false)\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `Result<int32, string>` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn inferred_instance_method_return_is_used() {
        let e = errs(
            "type Counter = {\n    count: int32\n}\nfun Counter.get(self) {\n    return self.count\n}\nfun main() {\n    let c = Counter { count: 1 }\n    let x: string = c.get()\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn inferred_static_method_return_is_used() {
        let e = errs(
            "type Counter = {\n    count: int32\n}\nfun Counter.make() {\n    return Self { count: 0 }\n}\nfun main() {\n    let x: int32 = Counter.make()\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `Counter` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn variant_instance_method_return_is_used() {
        let e = errs(
            "type Shape =\n    | Circle {\n        radius: float64\n    }\n    | Square {\n        side: float64\n    }\nfun Shape.area(self) -> float64 {\n    return self.radius * self.radius\n}\nfun main() {\n    let shape = Shape.Circle { radius: 2.0 }\n    let x: string = shape.area()\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `float64` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn variant_static_method_return_is_used() {
        let e = errs(
            "type Token =\n    | Ident\nfun Token.make() {\n    return 1\n}\nfun main() {\n    let x: string = Token.Ident.make()\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn missing_common_variant_method_is_reported() {
        let e = errs(
            "type Shape =\n    | Circle {\n        area(self) -> float64\n    }\n    | Point\nfun f(shape: Shape) {\n    return shape.area()\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("`Shape` has no common method `area`")),
            "{e:?}"
        );
    }

    #[test]
    fn sum_common_field_access_is_allowed() {
        let e = errs(
            "type Pet =\n    | Cat {\n        name: string\n    }\n    | Dog {\n        name: string\n    }\nfun name(pet: Pet) -> string {\n    return pet.name\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn sum_common_field_access_uses_variant_literal_substitution() {
        let e = errs(
            "type Wrapper =\n    | Empty {\n        value\n    }\n    | Some {\n        value\n    }\nfun main() {\n    let w = Wrapper.Some { value: 1 }\n    let s: string = w.value\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn sum_common_field_access_uses_static_method_return_substitution() {
        let e = errs(
            "type Wrapper =\n    | Empty {\n        value\n    }\n    | Some {\n        value\n    }\ntype Maker = { }\nfun Maker.make(value) {\n    return Wrapper.Some { value: value }\n}\nfun main() {\n    let w = Maker.make(1)\n    let s: string = w.value\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn sum_non_common_field_access_is_reported() {
        let e = errs(
            "type Shape =\n    | Circle {\n        radius: float64\n    }\n    | Point\nfun radius(shape: Shape) {\n    return shape.radius\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("`Shape` has no common field `radius`")),
            "{e:?}"
        );
    }

    #[test]
    fn variant_method_can_access_variant_specific_self_field() {
        let e = errs(
            "type Shape =\n    | Circle {\n        radius: float64\n    }\n    | Point\nfun Shape.radius_value(self) -> float64 {\n    return self.radius\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn local_binding_shadows_global_function_in_calls() {
        // A parameter named like a global function must be called as the local
        // value, not type-checked against the global's signature.
        let e = errs(
            "fun g() -> int32 {\n    return 0\n}\nfun call_it(g) {\n    return g(1)\n}\nfun main() {\n    let r = call_it((x) -> x + 1)\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn closure_arity_mismatch_is_reported() {
        let e =
            errs("fun main() {\n    let f = (x: int32, y: int32) -> x + y\n    let r = f(1)\n}\n");
        assert!(
            e.iter().any(|m| m.contains("expects 2 argument(s), got 1")),
            "{e:?}"
        );
    }

    #[test]
    fn identity_closure_result_is_instantiated_at_call_site() {
        // `(x) -> x` applied to an `int32` yields `int32`, so binding the
        // result to `string` must be rejected. Without per-call instantiation
        // the closure return collapsed to an unconstrained unknown that
        // satisfied any annotation (an unsound laundering of the value type).
        let e = errs("fun main() {\n    let f = (x) -> x\n    let s: string = f(1)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn identity_closure_valid_use_is_accepted() {
        // The matching-typed use must still type-check: instantiation should
        // recover the concrete result, not over-reject polymorphic closures.
        let e = errs(
            "fun main() {\n    let f = (x) -> x\n    let n: int32 = f(1)\n    let s: string = f(\"a\")\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn self_applied_identity_closure_does_not_diverge() {
        // `id(id)` unifies the parameter variable with a function type that
        // mentions it, which the occurs check must reject as an infinite type
        // rather than looping forever while resolving the substitution. The
        // call must still type-check overall (the result is instantiated to
        // `int32`), so the binding to `int32` is accepted.
        let e = errs("fun main() {\n    let id = (x) -> x\n    let n: int32 = id(id)(1)\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn for_over_non_iterable_is_reported() {
        let e = errs("fun main() {\n    for x in 5 {\n        let y = x\n    }\n}\n");
        assert!(
            e.iter().any(|m| m.contains("cannot iterate over `int32`")),
            "{e:?}"
        );
    }

    #[test]
    fn indexing_non_indexable_is_reported() {
        let e = errs("fun main() {\n    let n = 5\n    let x = n[0]\n}\n");
        assert!(
            e.iter().any(|m| m.contains("cannot index `int32`")),
            "{e:?}"
        );
    }

    #[test]
    fn fixed_array_literal_matches_annotation() {
        let e = errs("fun main() {\n    let values: int32[2] = [1, 2]\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn numeric_values_convert_implicitly_at_flow_positions() {
        // Automatic numeric conversion: a numeric value flows into a numeric
        // position of a different type -- assignments, arguments, returns, and
        // compound assignments alike. Narrowing int -> int is allowed (lossy by
        // design); int -> float is allowed.
        for (label, src) in [
            (
                "assignment widens",
                "fun main() {\n    let a: int32 = 5\n    let b: int64 = a\n}\n",
            ),
            (
                "assignment narrows (lossy)",
                "fun main() {\n    let a: int64 = 5\n    let b: int32 = a\n}\n",
            ),
            (
                "argument widens",
                "fun f(x: int64) -> int64 {\n    return x\n}\nfun main() {\n    let a: int32 = 5\n    f(a)\n}\n",
            ),
            (
                "return widens",
                "fun g() -> int64 {\n    let a: int32 = 5\n    return a\n}\nfun main() {\n    g()\n}\n",
            ),
            (
                "compound assign widens the operand",
                "fun main() {\n    let t: int64 = 1\n    let x: int32 = 2\n    t += x\n}\n",
            ),
            (
                "int flows into a float position",
                "fun main() {\n    let a: int32 = 5\n    let f: float64 = a\n}\n",
            ),
            (
                "int flows into a nullable numeric position",
                "fun main() {\n    let a: int32 = 5\n    let m: int64? = a\n}\n",
            ),
        ] {
            let e = errs(src);
            assert!(e.is_empty(), "{label}: {e:?}");
        }
    }

    #[test]
    fn float_does_not_convert_to_int_implicitly() {
        // float -> int stays explicit (int32.from): the compound write-back would
        // silently truncate the fraction.
        let assign = errs("fun main() {\n    let f: float64 = 1.5\n    let n: int32 = f\n}\n");
        assert!(
            assign
                .iter()
                .any(|m| m.contains("cannot use `float64` where `int32` is required")),
            "{assign:?}"
        );
        let compound =
            errs("fun main() {\n    let t: int32 = 1\n    let x: float64 = 2.5\n    t += x\n}\n");
        assert!(
            compound
                .iter()
                .any(|m| m.contains("cannot use `float64` where `int32` is required")),
            "{compound:?}"
        );
    }

    #[test]
    fn integer_literal_defaults_to_its_magnitude() {
        // A literal that does not fit int32 defaults to int64 instead of
        // truncating (the stdlib's `const INT64_MAX = 9223372036854775807`).
        let e = errs("const BIG = 9223372036854775807\nfun main() {\n    let x: int64 = BIG\n}\n");
        assert!(e.is_empty(), "{e:?}");
        // An in-range literal still defaults to int32: it flows into an int8
        // position numerically, and a string position names int32.
        let small = errs("fun main() {\n    let x = 5\n    let s: string = x\n}\n");
        assert!(
            small
                .iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{small:?}"
        );
    }

    #[test]
    fn nullable_slice_annotation_flows_into_array_literal() {
        // A `T?[]` annotation propagates the nullable element type to each element,
        // so a `null` element and a plain integer are both accepted (a `null`
        // element would otherwise force a heterogeneous, rejected literal).
        let with_null = errs("const a: int32?[] = [4, 1, null, 65]\n");
        assert!(
            with_null.is_empty(),
            "a null element in an int32?[] literal must be accepted: {with_null:?}"
        );
        let all_present = errs("const a: int32?[] = [4, 1, 65]\n");
        assert!(
            all_present.is_empty(),
            "an all-present int32?[] literal must be accepted: {all_present:?}"
        );
    }

    #[test]
    fn unannotated_null_containing_array_is_a_nullable_sequence() {
        // Without an annotation, a `null` element does not force a tuple: null
        // unifies with any element type, so the literal is a nullable-element
        // sequence and its elements narrow like any nullable.
        for src in [
            // const binding (a fixed-length array) and element narrowing.
            "const a = [4, 1, null, 65]\nfun main() {\n    let x = a[0]\n    if x {\n        println(x + 1)\n    }\n}\n",
            // let binding (a growable slice) accepts further pushes of both kinds.
            "fun main() {\n    let a = [4, null]\n    a.push(null)\n    a.push(7)\n}\n",
            // all-null literal is a nullable sequence with an open element.
            "fun main() {\n    let a = [null, null]\n    a.push(5)\n}\n",
        ] {
            let e = errs(src);
            assert!(e.is_empty(), "{src}: {e:?}");
        }
        // Genuinely ununifiable elements still form a tuple, null or not.
        let hetero = errs(
            "fun main() {\n    let t = [1, null, \"s\"]\n    let s: string = t[2]\n    let n: int32 = t[0]\n}\n",
        );
        assert!(hetero.is_empty(), "{hetero:?}");
    }

    #[test]
    fn const_array_literal_is_fixed_length_and_flows_into_slices() {
        // An unannotated const literal is a fixed-length array; it is still
        // usable where a slice is required (same storage, static length).
        let e = errs(
            "fun total(xs: int32[]) -> int32 {\n    return xs[0]\n}\nconst nums = [10, 20, 30]\nfun main() {\n    println(total(nums))\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
        // A let binding stays growable: push is accepted.
        let grow = errs("fun main() {\n    let xs = [1, 2]\n    xs.push(3)\n}\n");
        assert!(grow.is_empty(), "{grow:?}");
    }

    #[test]
    fn nullable_slice_annotation_works_inside_a_function() {
        // The in-function `let` exercises the HM engine too (it skips top-level
        // init values): a null-containing literal is classified a tuple there and
        // must flow element-wise into the annotated sequence, and the same literal
        // must flow into a nullable-element parameter at a call site.
        let with_null = errs("fun main() {\n    let a: int32?[] = [4, 1, null, 65]\n}\n");
        assert!(
            with_null.is_empty(),
            "a null element in an int32?[] let binding must be accepted: {with_null:?}"
        );
        let all_present = errs("fun main() {\n    let a: int32?[] = [1, 2, 3]\n}\n");
        assert!(
            all_present.is_empty(),
            "an all-present int32?[] let binding must be accepted: {all_present:?}"
        );
        let argument =
            errs("fun take(xs: int32?[]) {\n}\nfun main() {\n    take([7, null, 8])\n}\n");
        assert!(
            argument.is_empty(),
            "a null-containing literal must flow into an int32?[] parameter: {argument:?}"
        );
        // The element type still holds: a string element does not flow into
        // `int32?` even via the element-wise tuple rule.
        let bad = errs("fun main() {\n    let a: int32?[] = [1, \"s\", 3]\n}\n");
        assert!(
            !bad.is_empty(),
            "a string element must not flow into an int32?[] literal"
        );
    }

    #[test]
    fn fixed_array_literal_length_is_checked() {
        let e = errs("fun main() {\n    let values: int32[2] = [1, 2, 3]\n}\n");
        assert!(
            e.iter().any(|m| m.contains("array literal has length 3")),
            "{e:?}"
        );
    }

    #[test]
    fn fixed_array_literal_can_be_function_argument() {
        let e =
            errs("fun take_pair(values: int32[2]) {\n}\nfun main() {\n    take_pair([1, 2])\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn fixed_array_pattern_length_is_checked() {
        let e = errs(
            "fun main() {\n    let values: int32[2] = [1, 2]\n    let [a, b, c] = values\n}\n",
        );
        assert!(
            e.iter().any(|m| m.contains("array pattern has length 3")),
            "{e:?}"
        );
    }

    #[test]
    fn ufcs_free_function_on_record_is_accepted() {
        let e = errs(
            "type Vec2 = {\n    x: float64\n    y: float64\n}\nfun length_sq(v: Vec2) -> float64 {\n    return v.x * v.x + v.y * v.y\n}\nfun main() {\n    let v = Vec2 { x: 3.0, y: 4.0 }\n    let r: float64 = length_sq(v)\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn ufcs_receiver_type_is_checked() {
        let e = errs(
            "type Vec2 = {\n    x: float64\n}\ntype Other = {\n    z: float64\n}\nfun length_sq(v: Vec2) -> float64 {\n    return v.x\n}\nfun main() {\n    let o = Other { z: 1.0 }\n    let r = length_sq(o)\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `Other` where `Vec2` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn structural_record_argument_accepts_superset() {
        let e = errs(
            "type Point = {\n    x: int32\n}\ntype LabeledPoint = {\n    x: int32\n    label: string\n}\nfun get_x(p: Point) -> int32 {\n    return p.x\n}\nfun main() {\n    let p = LabeledPoint { x: 1, label: \"p\" }\n    let x: int32 = get_x(p)\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn generic_method_constraint_is_checked_at_call_site() {
        let e = errs(
            "type Silent = {\n    name: string\n}\nfun speak_twice(x) {\n    x.speak()\n    x.speak()\n}\nfun main() {\n    let s = Silent { name: \"s\" }\n    speak_twice(s)\n}\n",
        );
        assert!(e.iter().any(|m| m.contains("no method `speak`")), "{e:?}");
    }

    #[test]
    fn foreign_variant_pattern_is_reported() {
        let e = errs(
            "type Color = Red | Green\ntype Shape = Circle | Square\nfun f(c: Color) {\n    return match c {\n        Red => 1,\n        Circle => 2,\n        _ => 0,\n    }\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("pattern variant `Circle` belongs to `Shape`, not `Color`")),
            "{e:?}"
        );
    }

    #[test]
    fn variant_pattern_on_non_sum_is_reported() {
        let e = errs(
            "type Color = Red | Green\nfun main() {\n    let n = 5\n    let r = match n { Red => 1, _ => 0 }\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("pattern variant `Red` belongs to `Color`, not `int32`")),
            "{e:?}"
        );
    }

    #[test]
    fn builtin_file_methods_are_typed_as_result() {
        let e = errs(
            "fun write(path: string) {\n    let f = open(path, \"w\")!\n    f.write(_string_bytes(\"x\"))!\n    f.close()!\n}\nfun main() {\n    let r = write(\"out.txt\")\n    match r {\n        Ok { value } => 0,\n        Err { error } => 1,\n    }\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn unknown_numeric_parameter_can_be_compared_to_literal() {
        let e = errs("fun abs(x) {\n    if x < 0 {\n        return -x\n    }\n    return x\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn result_builtin_is_exhaustive() {
        let e = errs(
            "fun f(r) {\n    return match r {\n        Ok { value } => value,\n        Err { error } => 0,\n    }\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    // --- Milestone R5a: unresolved identifiers are name-resolution errors ---

    #[test]
    fn unknown_name_in_call_argument_is_rejected() {
        // An undeclared value name must not silently collapse to a fresh
        // unknown that runs as `void`; name resolution is a hard pre-execution
        // check.
        let e = errs("fun main() {\n    println(zzz)\n}\n");
        assert!(e.iter().any(|m| m.contains("unknown name `zzz`")), "{e:?}");
    }

    #[test]
    fn unknown_name_in_arithmetic_is_rejected() {
        let e = errs("fun main() {\n    let n: int32 = zzz + 1\n}\n");
        assert!(e.iter().any(|m| m.contains("unknown name `zzz`")), "{e:?}");
    }

    #[test]
    fn unknown_name_as_function_argument_to_known_function_is_rejected() {
        let e = errs("fun g(a: int32) -> int32 {\n    return a\n}\nfun main() {\n    g(zzz)\n}\n");
        assert!(e.iter().any(|m| m.contains("unknown name `zzz`")), "{e:?}");
    }

    #[test]
    fn unknown_callee_is_rejected() {
        let e = errs("fun main() {\n    nope(1)\n}\n");
        assert!(
            e.iter().any(|m| m.contains("unknown function `nope`")),
            "{e:?}"
        );
    }

    #[test]
    fn in_scope_local_resolves() {
        // A name bound earlier in the same scope still resolves and runs.
        let e = errs("fun main() {\n    let zzz = 1\n    println(zzz)\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn prelude_builtin_names_remain_callable_without_stdlib() {
        // Runtime builtins resolve without an explicit stdlib definition, so
        // the name-resolution check must keep treating them as known even when
        // only the user module is loaded.
        let e = errs("fun main() {\n    println(\"x\")\n    let n = len(\"abc\")\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn runtime_builtins_have_static_return_types() {
        // These names are runtime builtins even when stdlib wrappers are not
        // loaded. Their return types must not collapse to unconstrained
        // unknowns that satisfy arbitrary annotations.
        let e = errs(
            "fun main() {\n    let p: int32 = println(\"x\")\n    let t: int32 = input()\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `void` where `int32` is required")),
            "{e:?}"
        );
        // Without the stdlib, `input` falls back to the same `string!` the real
        // definition infers.
        assert!(
            e.iter().any(
                |m| m.contains("cannot use `Result<string, string>` where `int32` is required")
            ),
            "{e:?}"
        );
    }

    #[test]
    fn type_of_is_no_longer_a_builtin() {
        // `type_of`/`_type_name` were removed: a call without a definition is an
        // unknown function rather than a recognized runtime builtin.
        let e = errs("fun main() {\n    let _ = type_of(1)\n}\n");
        assert!(
            e.iter().any(|m| m.contains("unknown function `type_of`")),
            "{e:?}"
        );
    }

    #[test]
    fn runtime_input_builtin_is_typed_as_string() {
        // `input` reads a line fallibly: its type is `string!`, so the bare
        // value binds only after `!` (or a `match`).
        let e = errs("fun main() {\n    let s: string = input()!\n}\n");
        assert!(e.is_empty(), "{e:?}");
        let bare = errs("fun main() {\n    let s: string = input()\n}\n");
        assert!(
            bare.iter()
                .any(|m| m
                    .contains("cannot use `Result<string, string>` where `string` is required")),
            "{bare:?}"
        );
    }

    #[test]
    fn runtime_assert_builtin_is_a_recognized_prelude_name() {
        // `assert` resolves as a prelude builtin even without the stdlib loaded,
        // so a call is not reported as an unknown function. The bool-condition
        // contract is carried by the stdlib signature
        // `assert(cond: bool, msg: string?)`, exercised by the running examples.
        let e = errs("fun main() {\n    assert(true)\n}\n");
        assert!(
            !e.iter().any(|m| m.contains("unknown function `assert`")),
            "{e:?}"
        );
    }

    #[test]
    fn string_runtime_builtins_check_arguments_and_returns() {
        let e = errs(
            "fun main() {\n    let part: string = _string_slice(\"abc\", 0, 1)\n    let bytes: uint8[] = _string_bytes(\"abc\")\n    let back: string = _string_from_bytes(bytes)!\n    let pos: int64? = _string_find(\"abc\", \"b\")\n    let cmp: int32 = _string_cmp(\"a\", \"b\")\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn string_runtime_builtin_argument_mismatch_is_rejected() {
        let e = errs("fun main() {\n    let x = _string_slice(1, 0, 1)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn array_runtime_builtins_check_element_contracts() {
        let e = errs(
            "fun main() {\n    let xs = [1]\n    _array_push(xs, 2)\n    let x: int32? = _array_pop(xs)\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn array_runtime_push_rejects_wrong_element() {
        let e = errs("fun main() {\n    let xs = [1]\n    _array_push(xs, \"x\")\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn array_runtime_pop_return_type_is_checked() {
        let e = errs("fun main() {\n    let xs = [1]\n    let x: string? = _array_pop(xs)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32?` where `string?` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn numeric_helper_builtins_have_static_contracts() {
        // The numeric runtime helpers map onto LLVM primitives, so their return
        // types are first-class and their argument classes are enforced.
        let e = errs(
            "fun main() {\n    let s: string = _int_to_string(1)\n    let f: float64 = _int_to_float(1, 64)\n    let n: int64 = _int_parse(\"7\")!\n    let g: float64 = _float_sqrt(2.0)\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn numeric_helper_rejects_wrong_value_class() {
        // `_int_to_string` reads its argument as an integer payload; a float
        // would be reinterpreted, so a concrete float is a static error.
        let e = errs("fun main() {\n    let s = _int_to_string(1.0)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`_int_to_string` expects an integer")),
            "{e:?}"
        );
    }

    #[test]
    fn float_parse_helper_requires_a_string() {
        let e = errs("fun main() {\n    let f = _float_parse(1)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`_float_parse` expects a string")),
            "{e:?}"
        );
    }

    #[test]
    fn open_requires_string_arguments() {
        let e = errs("fun main() {\n    let f = open(1, \"r\")\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn spawn_requires_zero_argument_closure() {
        let e = errs("fun main() {\n    spawn((x) -> x)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`spawn` expects a zero-argument closure")),
            "{e:?}"
        );
    }

    #[test]
    fn spawn_rejects_non_closure_argument() {
        let e = errs("fun main() {\n    spawn(1)\n}\n");
        assert!(
            e.iter().any(|m| m.contains("`spawn` expects a closure")),
            "{e:?}"
        );
    }

    #[test]
    fn with_returns_callback_result_type() {
        // `with(c, f)` returns the closure's result type, so a string callback
        // result cannot satisfy an int annotation.
        let e = errs("fun main() {\n    let n: int32 = with(1, (c) -> \"x\")\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn with_rejects_non_closure_second_argument() {
        let e = errs("fun main() {\n    with(1, 2)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`with` expects a closure as its second argument")),
            "{e:?}"
        );
    }

    // --- Milestone R5b: declared return types hold on every return path ---

    #[test]
    fn nested_if_return_violating_declared_type_is_rejected() {
        // A `return` inside an `if` evaluated as a statement-expression must
        // still be checked against the declared return type; previously the
        // expression-position path passed no declared type and accepted it.
        let e =
            errs("fun f(n: int32) -> int32 {\n    if n <= 0 { return \"x\" }\n    return n\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn bare_block_return_violating_declared_type_is_rejected() {
        let e = errs("fun f(n: int32) -> int32 {\n    { return \"x\" }\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn deeply_nested_return_violating_declared_type_is_rejected() {
        let e = errs("fun f() -> int32 {\n    if true { { return \"x\" } }\n    return 0\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn valid_nested_return_of_correct_type_is_accepted() {
        let e = errs("fun f(n: int32) -> int32 {\n    if n <= 0 { return 1 }\n    return n\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn return_of_match_expression_is_accepted() {
        let e = errs("fun g() -> string {\n    return match 1 { _ => \"x\" }\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn closure_return_is_checked_against_closure_not_outer_function() {
        // A `return` inside a closure body has the closure's own inferred
        // return context, so it must not be checked against the enclosing
        // function's declared type.
        let e = errs("fun f() -> int32 {\n    let g = () -> { return \"x\" }\n    return 0\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    // --- Milestone R4: fixed arrays T[n] cannot grow; slices T[] can ---

    #[test]
    fn push_on_fixed_array_is_rejected() {
        // A fixed array has a statically fixed length, so push is not a method
        // on it.
        let e = errs("fun main() {\n    let xs: int32[1] = [1]\n    xs.push(2)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("fixed array type `int32[1]` has no method `push`")),
            "{e:?}"
        );
    }

    #[test]
    fn pop_on_fixed_array_is_rejected() {
        let e = errs("fun main() {\n    let xs: int32[1] = [1]\n    xs.pop()\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("fixed array type `int32[1]` has no method `pop`")),
            "{e:?}"
        );
    }

    #[test]
    fn push_on_slice_is_accepted() {
        let e = errs("fun main() {\n    let xs: int32[] = [1]\n    xs.push(2)\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn index_assignment_to_fixed_array_is_accepted() {
        // Element replacement keeps the length, so it is allowed on a fixed
        // array; only length-changing operations are rejected.
        let e = errs("fun main() {\n    let xs: int32[2] = [1, 2]\n    xs[1] = 3\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn len_works_for_both_fixed_array_and_slice() {
        let e = errs(
            "fun main() {\n    let a: int32[2] = [1, 2]\n    let b: int32[] = [1]\n    let m = len(a)\n    let n = len(b)\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    // --- Milestone R2: closure body constraints are verified at call sites ---

    #[test]
    fn closure_numeric_constraint_is_enforced() {
        // `(x) -> x + 1` uses `x` numerically, so applying it to a `string`
        // must be rejected even though the parameter type is only known at the
        // call site.
        let e = errs("fun main() {\n    let f = (x) -> x + 1\n    f(\"x\")\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn closure_numeric_constraint_accepts_matching_argument() {
        let e = errs("fun main() {\n    let f = (x) -> x + 1\n    let n: int32 = f(2)\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn closure_method_constraint_is_enforced() {
        // `(x) -> x.speak()` requires a receiver with a `speak` method; an
        // `int32` has none.
        let e = errs("fun main() {\n    let f = (x) -> x.speak()\n    f(1)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`int32` has no method `speak`")),
            "{e:?}"
        );
    }

    #[test]
    fn closure_index_constraint_is_enforced() {
        let e = errs("fun main() {\n    let f = (x) -> x[0]\n    f(1)\n}\n");
        assert!(
            e.iter().any(|m| m.contains("cannot index `int32`")),
            "{e:?}"
        );
    }

    #[test]
    fn closure_field_constraint_accepts_matching_record() {
        let e = errs(
            "type P = { name: string }\nfun main() {\n    let f = (x) -> x.name\n    let p = P { name: \"a\" }\n    let s: string = f(p)\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn closure_field_constraint_rejects_record_without_field() {
        let e = errs(
            "type P = { other: string }\nfun main() {\n    let f = (x) -> x.name\n    let p = P { other: \"a\" }\n    f(p)\n}\n",
        );
        assert!(e.iter().any(|m| m.contains("has no field `name`")), "{e:?}");
    }

    #[test]
    fn closure_typed_field_with_self_typechecks() {
        // A field may hold a closure whose type names the enclosing type via
        // `self` (`apply: (self, int32) -> int32`). The closure literal is checked
        // against that type, with `self` bound to the record -- including inside a
        // function, where the HM pass must resolve `self` from the closure's
        // parameter scope rather than only a method receiver.
        let e = errs(
            "type Calc = {\n    base: int32\n    apply: (self, int32) -> int32\n}\nfun main() {\n    let c = Calc { base: 10, apply: (self, n) -> { return self.base + n } }\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn closure_typed_field_body_return_mismatch_is_rejected() {
        // The closure body is checked against the field's declared return type, so
        // returning an int where `-> string` is required is an error.
        let e = errs(
            "type Obj = {\n    transform: (self, string) -> string\n}\nfun main() {\n    let o = Obj { transform: (self, s) -> { return 1 } }\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int32` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn closure_constraint_survives_being_stored_in_array() {
        // The constraint is keyed by the parameter's inference variable, which
        // travels with the closure value into an array, so it is still verified
        // when the closure is taken back out and applied.
        let e = errs("fun main() {\n    let fs = [(x) -> x + 1]\n    fs[0](\"x\")\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn higher_order_closure_argument_is_checked() {
        // A closure passed to a function and applied inside its body is still
        // constrained: `apply` calls `f(x)`, so the numeric closure rejects a
        // string actual argument flowing through.
        let e = errs(
            "fun apply2(f, x) {\n    return f(x)\n}\nfun main() {\n    apply2((x) -> x + 1, \"s\")\n}\n",
        );
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    // --- Milestone R3: empty arrays pin their element type from first use ---

    #[test]
    fn empty_array_element_type_is_pinned_by_first_push() {
        // `let xs = []` starts with an unconstrained element type; the first
        // push fixes it, so a later push of a different type is rejected.
        let e = errs("fun main() {\n    let xs = []\n    xs.push(1)\n    xs.push(\"x\")\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `string` where `int32` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn empty_array_pinned_element_is_readable_at_its_type() {
        let e =
            errs("fun main() {\n    let xs = []\n    xs.push(1)\n    let y: int32 = xs[0]\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn empty_array_pinned_to_string_reads_as_string() {
        let e = errs(
            "fun main() {\n    let xs = []\n    xs.push(\"x\")\n    let y: string = xs[0]\n}\n",
        );
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn empty_array_consistent_pushes_are_accepted() {
        let e = errs("fun main() {\n    let xs = []\n    xs.push(1)\n    xs.push(2)\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn unconstrained_empty_array_in_required_position_is_rejected() {
        // A bare empty array whose element type
        // is never pinned must not silently satisfy a concrete required position.
        let e = errs("fun main() {\n    let xs = []\n    let first: int32 = xs[0]\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot infer element type of empty array")),
            "{e:?}"
        );
    }

    #[test]
    fn annotated_empty_array_satisfies_required_position() {
        // Annotating the array supplies the element type, so reading it into a
        // concrete position is fine.
        let e = errs("fun main() {\n    let xs: int32[] = []\n    let first: int32 = xs[0]\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }

    // --- Milestone R1: the free `len` builtin has a static int64 contract ---

    #[test]
    fn free_len_call_is_typed_as_int64() {
        // `len(arr)` used as a free function must type as int64, like the
        // method form `arr.len()`, so a wrong annotation is rejected statically.
        let e = errs("fun main() {\n    let xs = [1, 2, 3]\n    let n: string = len(xs)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("cannot use `int64` where `string` is required")),
            "{e:?}"
        );
    }

    #[test]
    fn free_len_on_non_collection_is_rejected() {
        let e = errs("fun main() {\n    let n = len(1)\n}\n");
        assert!(
            e.iter()
                .any(|m| m.contains("`len` expects an array or string")),
            "{e:?}"
        );
    }

    #[test]
    fn free_len_on_string_is_accepted() {
        let e = errs("fun main() {\n    let n: int64 = len(\"abc\")\n}\n");
        assert!(e.is_empty(), "{e:?}");
    }
}
