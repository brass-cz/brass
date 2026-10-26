mod name_resolution;

use super::{Analysis, analyze, check, context_seed};
use brass_hir::{Constness, IntKind, LoadedModule, Program, Type, TypedExprKind, lower};
use brass_parser::ast::{BinOp, Pattern, TopLevel};
use brass_parser::{Span, parse};
use fxhash::FxHashSet as HashSet;

fn errs(src: &str) -> Vec<String> {
    let ast = parse(src).expect("parse");
    let (prog, lerr) = lower(&[LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(lerr.is_empty(), "lower errors: {lerr:?}");
    check(&prog).into_iter().map(|e| e.message).collect()
}

fn infer_errs(src: &str) -> Vec<String> {
    let ast = parse(src).expect("parse");
    let (prog, lerr) = lower(&[LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(lerr.is_empty(), "lower errors: {lerr:?}");
    super::infer::analyze(&prog)
        .errors
        .into_iter()
        .map(|e| e.message)
        .collect()
}

fn prelude_infer_errs(src: &str) -> Vec<String> {
    let core = parse(include_str!("../../../core/error.cz")).expect("parse core error module");
    let main = parse(src).expect("parse main module");
    let (prog, lerr) = lower(&[
        LoadedModule {
            is_prelude: true,
            path: vec!["core".into(), "error".into()],
            ast: core,
        },
        LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast: main,
        },
    ]);
    assert!(lerr.is_empty(), "lower errors: {lerr:?}");
    super::infer::analyze(&prog)
        .errors
        .into_iter()
        .map(|e| e.message)
        .collect()
}

fn analysis(src: &str) -> Analysis {
    let ast = parse(src).expect("parse");
    let (prog, lerr) = lower(&[LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(lerr.is_empty(), "lower errors: {lerr:?}");
    analyze(&prog)
}

fn module_errs(modules: &[(&[&str], &str)]) -> Vec<String> {
    let loaded = modules
        .iter()
        .map(|(path, src)| LoadedModule {
            is_prelude: false,
            path: path.iter().map(|part| (*part).to_string()).collect(),
            ast: parse(src).expect("parse"),
        })
        .collect::<Vec<_>>();
    let (program, lower_errors) = lower(&loaded);
    assert!(lower_errors.is_empty(), "lower errors: {lower_errors:?}");
    check(&program)
        .into_iter()
        .map(|error| error.message)
        .collect()
}

fn module_program(modules: &[(&[&str], &str)]) -> Program {
    let loaded = modules
        .iter()
        .map(|(path, src)| LoadedModule {
            is_prelude: false,
            path: path.iter().map(|part| (*part).to_string()).collect(),
            ast: parse(src).expect("parse"),
        })
        .collect::<Vec<_>>();
    let (program, lower_errors) = lower(&loaded);
    assert!(lower_errors.is_empty(), "lower errors: {lower_errors:?}");
    program
}

#[test]
fn qualified_pattern_errors_do_not_bind_or_cover_variants() {
    // A typo must fail at the pattern, never become a binding named Typo
    // or make an otherwise non-exhaustive match exhaustive.
    let a = analysis("type A = X { v: int32 } | Y\nfun f(a: A) { match a { A.Typo => Typo } }\n");
    let messages: Vec<_> = a.errors.iter().map(|e| e.message.as_str()).collect();
    assert!(
        messages.contains(&"`A` has no variant `Typo`"),
        "{messages:?}"
    );
    assert!(
        messages.iter().any(|m| m.contains("non-exhaustive")),
        "{messages:?}"
    );
    assert!(
        messages.iter().any(|m| m.contains("unknown name `Typo`")),
        "{messages:?}"
    );

    let src =
        "type A = X { v: int32 } | Y\nfun f(a: A) { match a { Nope.X { v } => v, _ => 0 } }\n";
    let a = analysis(src);
    let error = a
        .errors
        .iter()
        .find(|e| e.message == "unknown type `Nope`")
        .expect("qualifier diagnostic");
    assert_eq!(&src[error.span.lo..error.span.hi], "Nope");

    // Bodies are checked even after a rejected pattern. The unknown name
    // confirms that the qualified typo was never introduced as a binding.
    for body in [
        "if let A.Typo = a { Typo } else { 0 }",
        "for A.Typo in [a] { Typo }",
    ] {
        let e = errs(&format!("type A = X | Y\nfun f(a: A) {{ {body} }}\n"));
        assert!(e.iter().any(|e| e == "`A` has no variant `Typo`"), "{e:?}");
        assert!(e.iter().any(|e| e.contains("unknown name `Typo`")), "{e:?}");
    }
}

#[test]
fn rejected_pattern_bodies_still_record_nested_calls() {
    // Call evidence is needed even in bodies whose diagnostics are later
    // discarded by static dead-branch checking.
    for body in [
        "match a { A.Typo => nested(1), _ => 0 }",
        "if let A.Typo = a { nested(1) } else { 0 }",
        "for A.Typo in [a] { nested(1) }",
    ] {
        for dead in [false, true] {
            let body = if dead {
                format!("if null {{ {body} }}")
            } else {
                body.to_string()
            };
            let src = format!(
                "type A = X | Y\nfun nested(x: int32) -> int32 {{ return x }}\nfun f(a: A) {{ {body} }}\n"
            );
            let a = analysis(&src);
            let lo = src.find("nested(1)").expect("call site");
            assert!(
                a.typed.expressions.iter().any(|expr| {
                    matches!(expr.kind, TypedExprKind::Call)
                        && expr.span.lo == lo
                        && expr.span.hi == lo + "nested(1)".len()
                }),
                "body call was not checked: {body}; {:?}",
                a.errors
            );
        }
    }
}

#[test]
fn module_record_markers_are_not_sum_variant_patterns() {
    // A same-named variant must not turn the qualified record into a
    // sum tag test for exhaustiveness or control-flow analysis.
    let program = module_program(&[(&["main"], "type Collision = | P { x: int32 }\n")]);
    let record = Pattern::Record("pt.P".into(), None, Vec::new(), Span::new(0, 4));
    assert!(!crate::exhaustive::pattern_names_sum_variant(
        &program,
        &["main".to_string()],
        &record
    ));
}

#[test]
fn qualified_patterns_check_every_pattern_position() {
    // Each entry reaches a different pattern-checking path. The nested
    // case ensures recursive field checking retains the written type.
    for body in [
        "match a { B.X { v } => v, _ => 0 }",
        "if let B.X { v } = a { v } else { 0 }",
        "let B.X { v } = a",
        "for B.X { v } in [a] { v }",
        "let box = Box.Wrap { item: a }\nif let Box.Wrap { item: B.X { v } } = box { v } else { 0 }",
    ] {
        let src = format!(
            "type A = X {{ v: int32 }} | Y\ntype B = X {{ v: int32 }} | Z\ntype Box = | Wrap {{ item: A }}\nfun f(a: A) {{ {body} }}\n"
        );
        let e = errs(&src);
        assert!(
            e.iter()
                .any(|e| e == "pattern `B.X` names `B`, but the matched value has type `A`"),
            "{body}: {e:?}"
        );
    }
}

#[test]
fn qualified_unit_pattern_is_not_a_reflection_loop_binding() {
    // Reflective for-loops expand a binding into field names; a qualified
    // variant head must still be checked before that special path runs.
    let e = errs("type A = X | Y\nfun f() { let r = { v: 1 }\nfor A.X in fields(r) { X } }\n");
    assert!(
        e.iter()
            .any(|e| e == "pattern `A.X` names `A`, but the matched value has type `string`"),
        "{e:?}"
    );
    assert!(!e.iter().any(|e| e.contains("unknown name")), "{e:?}");
}

#[test]
fn qualified_patterns_use_nominal_identity_across_modules() {
    // Both declarations display as Shape. Import renaming must not erase
    // the distinction between their nominal IDs.
    let e = module_errs(&[
        (&["left"], "type Shape = X { v: int32 } | Y\n"),
        (&["right"], "type Shape = X { v: int32 } | Y\n"),
        (
            &["main"],
            "import left.{ Shape as L }\nimport right.{ Shape as R }\nfun f(x: L) { match x { R.X { v } => v, R.Y => 0 } }\n",
        ),
    ]);
    assert!(
        e.iter()
            .any(|e| e.contains("pattern `R.X` names `R`, but the matched value has type")),
        "{e:?}"
    );
}

#[test]
fn qualified_pattern_aliases_select_the_underlying_sum() {
    // Aliases, including module markers and renamed alias imports, name
    // the same declaration without creating a new nominal identity.
    let e = module_errs(&[
        (
            &["shapes"],
            "type Shape = X { v: int32 } | Y\ntype Alias = Shape\n",
        ),
        (
            &["main"],
            "import shapes as shapes\nimport shapes.{ Shape, Alias as Renamed }\nfun f(x: Shape) { match x { shapes.Alias.X { v } => v, Renamed.Y => 0 } }\n",
        ),
    ]);
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn partial_context_seed_rejects_shifted_nominal_ids() {
    // Adding a type in an earlier module renumbers the unchanged module's
    // nominal. Its old table values must not be retained under the new ID.
    let old = module_program(&[
        (&["a"], "type A = { value: int32 }\n"),
        (
            &["b"],
            "type B = { value: string }\nfun make() { return B { value: \"b\" } }\n",
        ),
    ]);
    let mut seed = context_seed(&old).expect("clean context");
    let current = module_program(&[
        (
            &["a"],
            "type Added = { flag: bool }\ntype A = { value: int32 }\n",
        ),
        (
            &["b"],
            "type B = { value: string }\nfun make() { return B { value: \"b\" } }\n",
        ),
    ]);
    let keep = HashSet::from_iter([vec!["b".to_string()]]);

    assert!(!seed.retain_modules(&current, &keep));
    assert_eq!(seed.covered, None);
}

#[test]
fn partial_context_seed_rejects_changed_symbol_qualification() {
    // A new same-named function qualifies the unchanged definition's
    // storage symbol. Dropping its old entry while skipping its module is
    // not a valid partial seed.
    let old = module_program(&[
        (&["a"], "fun other() { return 0 }\n"),
        (&["b"], "fun helper() { return 1 }\n"),
    ]);
    let mut seed = context_seed(&old).expect("clean context");
    let current = module_program(&[
        (&["a"], "fun helper() { return 0 }\n"),
        (&["b"], "fun helper() { return 1 }\n"),
    ]);
    let keep = HashSet::from_iter([vec!["b".to_string()]]);

    assert!(!seed.retain_modules(&current, &keep));
    assert_eq!(seed.covered, None);
}

#[test]
fn partial_context_seed_cannot_regain_dropped_modules() {
    // A partial seed may be passed through another incremental selection;
    // retaining a wider set cannot recreate tables that were never kept.
    let program = module_program(&[
        (&["a"], "fun a() { return 1 }\n"),
        (&["b"], "fun b() { return 2 }\n"),
    ]);
    let mut seed = context_seed(&program).expect("clean context");
    let only_a = HashSet::from_iter([vec!["a".to_string()]]);
    assert!(seed.retain_modules(&program, &only_a));
    let all = HashSet::from_iter([vec!["a".to_string()], vec!["b".to_string()]]);

    assert!(seed.retain_modules(&program, &all));
    assert_eq!(seed.covered, Some(only_a));
}

#[test]
fn structural_records_resolve_declarations_by_nominal_id() {
    // Both modules declare `Target`, so the type table keys are qualified.
    // Looking fields up by the bare display name would make both records
    // appear fieldless and accept this unrelated argument.
    let errors = module_errs(&[
        (
            &["a"],
            "type Target = { x: int32 }\nfun read(t: Target) -> int32 { return t.x }\n",
        ),
        (
            &["b"],
            "type Target = { y: string }\nfun make() -> Target { return Target { y: \"bad\" } }\n",
        ),
        (
            &["main"],
            "import a.{ read }\nimport b.{ make }\nfun main() { read(make()) }\n",
        ),
    ]);
    assert!(
        errors
            .iter()
            .any(|message| message.contains("cannot use") && message.contains("Target")),
        "{errors:?}"
    );
}

#[test]
fn row_rejection_reports_once_at_the_value() {
    // A row-rejected anonymous argument must produce exactly the value-site
    // error: the callee body is not re-elaborated for that call, so no
    // duplicate or interior-span variant of the same failure leaks out.
    let msgs = errs(
        "fun get_x(p) -> int32 {\n    return p.x\n}\n\
             fun main() {\n    println(get_x({ y: 1 }))\n}\n",
    );
    assert_eq!(
        msgs,
        vec!["this value does not fit `get_x`'s parameter: missing field `x`".to_string()],
    );
}

#[test]
fn row_pass_keeps_reelaboration_clean_and_records_the_view_argument() {
    // A fitting anonymous argument passes the row check, the body still
    // re-elaborates without errors, and the argument span is recorded for
    // the view conversion (the `view_args` lowering channel).
    let a = analysis(
        "fun get_x(p) -> int32 {\n    return p.x\n}\n\
             fun main() {\n    println(get_x({ x: 1 }))\n}\n",
    );
    assert!(a.errors.is_empty(), "{:?}", a.errors);
    assert_eq!(a.view_args.len(), 1, "one viewable argument expected");
}

#[test]
fn witness_free_container_element_is_resolved_from_use() {
    // A constructor that builds an empty array field (`items = []`, no
    // element pushed) leaves the field's element open. A later mutating
    // call on the binding pins it: `b.add("a", 1)` stores a `Pair` into
    // `self.items[i]`, and the indexed-place store commits that
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
    // expressed over them: the type and its methods share one type
    // environment.
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

/// A closure value is monomorphic: its application (here through a
/// generic callee) commits the parameter in the solver, so the sidecar
/// shows the concrete type directly. A generalized binding applied at
/// exactly one type keeps its scheme variable open in the sidecar and
/// gets a display-only observation of the one instantiation instead.
#[test]
fn closure_binding_observed_at_single_application() {
    let a = analysis(
        "fun apply(f, x) {\n    return f(x)\n}\n\
             fun main() {\n    let y = apply((v) -> v, 3)\n    let id = (w) -> w\n    \
             let z = apply(id, 4)\n}\n",
    );
    assert!(a.errors.is_empty(), "{:?}", a.errors);
    let ident = |name: &str| {
        a.typed
            .expressions
            .iter()
            .find(|e| matches!(&e.kind, brass_hir::TypedExprKind::Ident(n) if n == name))
            .unwrap_or_else(|| panic!("typed entry for {name}"))
            .ty
            .clone()
    };
    assert_eq!(ident("v"), brass_hir::Type::Int(IntKind::I32));
    let brass_hir::Type::Unknown(id) = ident("w") else {
        panic!("w stays the scheme's open variable in the sidecar");
    };
    let observed = a.closure_bindings.get(&id).expect("observation for w");
    assert_eq!(observed, &brass_hir::Type::Int(IntKind::I32));
}

/// The same closure applied at two different types is genuinely
/// polymorphic: the observation is poisoned and dropped, so display falls
/// back to the open variable (and neither application errors).
#[test]
fn closure_binding_poisoned_on_conflicting_applications() {
    let a = analysis(
        "fun apply(f, x) {\n    return f(x)\n}\n\
             fun main() {\n    let id = (v) -> v\n    let a = apply(id, 3)\n    let b = apply(id, \"s\")\n}\n",
    );
    assert!(a.errors.is_empty(), "{:?}", a.errors);
    for e in &a.typed.expressions {
        if let (brass_hir::TypedExprKind::Ident(n), brass_hir::Type::Unknown(id)) = (&e.kind, &e.ty)
            && n == "v"
        {
            assert!(
                !a.closure_bindings.contains_key(id),
                "conflicting observations must poison var {id}"
            );
        }
    }
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
fn annotated_generic_record_is_instantiated_under_composite_types() {
    // A passing wrapper must not hide the actual record field type from the
    // callee body. Otherwise this write would change an integer field into a
    // string while callers continue to observe it as an integer.
    let wrapped = errs(
        "type Box = { value }\nfun smash(b: ref(mut(Box))) { b.value = \"bad\" }\nfun main() {\n  let b = Box { value: 1 }\n  smash(b)\n}\n",
    );
    assert!(
        wrapped
            .iter()
            .any(|m| m.contains("cannot use `string` where `int32` is required")),
        "{wrapped:?}"
    );

    // Tuple and nullable positions use the same recursive instantiation,
    // including promotion from a non-null actual into `Box?`.
    let tuple = errs(
        "type Box = { value }\nfun get(p: [Box, int32]) -> string { return p[0].value }\nfun main() { get([Box { value: 1 }, 0]) }\n",
    );
    assert!(
        tuple
            .iter()
            .any(|m| m.contains("cannot use `int32` where `string` is required")),
        "{tuple:?}"
    );
    let nullable = errs(
        "type Box = { value }\nfun get(b: Box?) -> string {\n  if b { return b.value }\n  return \"\"\n}\nfun main() { get(Box { value: 1 }) }\n",
    );
    assert!(
        nullable
            .iter()
            .any(|m| m.contains("cannot use `int32` where `string` is required")),
        "{nullable:?}"
    );
}

#[test]
fn annotated_nominal_instantiation_stops_at_concrete_method_types() {
    // The inferred return type of `copy` contains `Box` again. Instantiating
    // an annotated `Box` argument must reuse that concrete method type
    // instead of recursively expanding the same nominal declaration.
    let e = errs(
        "type Box = { value }\nfun Box.copy(self) { return Self { value: self.value } }\nfun take(b: Box) {}\nfun main() { take(Box { value: 1 }) }\n",
    );
    assert!(e.is_empty(), "{e:?}");
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
        "type Named = { name: string }\ntype HasBreed: Named = { name: string, breed: string }\ntype Box = { value: Named }\ntype DogBox: Box = { value: HasBreed }\n",
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
    let e = errs("type A = { id: int32 }\ntype B = { id: int32 }\ntype C: A, B = { id: int32 }\n");
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn interface_method_parameter_covariance_is_rejected() {
    // A narrower method parameter than the interface declares is unsound:
    // a caller could pass an Animal the DogConsumer cannot handle.
    let e = errs(
        "type Animal = { sound: string }\ntype Dog: Animal = { sound: string, breed: string }\ntype Consumer = { consume(self, a: Animal) -> void }\ntype DogConsumer: Consumer = { }\nfun DogConsumer.consume(self, a: Dog) -> void { }\n",
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

// ----- variance of function types -----
//
// A function value is compiled once, for its own signature, and nothing
// converts the arguments it receives or the result it returns. So a
// function value only flows where its parameter and result types name the
// SAME records as the required function type: `Dog` declaring `Animal`
// (and structurally satisfying it) does not make `(Animal) -> void` usable
// as `(Dog) -> void`, nor the reverse.

const VARIANCE_BASE: &str =
    "type Animal = { sound: string }\ntype Dog: Animal = { sound: string, breed: string }\n";

const FUNCTION_VALUE_HINT: &str = "a function value is compiled for its own signature";

#[test]
fn function_value_parameter_of_another_record_is_rejected() {
    // An `(Animal) -> void` value would be called with `Dog` values laid
    // out for `Dog`.
    let e = errs(&format!(
        "{VARIANCE_BASE}fun main() {{\n  let f: (Dog) -> void = (a: Animal) -> {{ let s = a.sound }}\n}}\n"
    ));
    assert!(
        e.iter().any(|m| m.contains(FUNCTION_VALUE_HINT)
            && m.contains("`(Animal) -> void`")
            && m.contains("`(Dog) -> void`")),
        "{e:?}"
    );
}

#[test]
fn function_value_with_narrower_parameter_is_rejected() {
    // Unsound direction: a `(Dog) -> void` value into an `(Animal) -> void`
    // slot. The holder may call it with a bare Animal, but the body reads
    // `.breed`. A covariant rule would accept this; the invariant rule
    // rejects it like the reverse direction.
    let e = errs(&format!(
        "{VARIANCE_BASE}fun main() {{\n  let g = (d: Dog) -> {{ let s = d.breed }}\n  let f: (Animal) -> void = g\n}}\n"
    ));
    // A block closure without a value `return` is `void`.
    assert!(
        e.iter()
            .any(|m| m.contains("`(Dog) -> void`") && m.contains("`(Animal) -> void`")),
        "{e:?}"
    );
}

#[test]
fn function_value_with_narrower_parameter_is_rejected_as_argument() {
    // Same rule at a consumed argument position: passing a `(Dog) -> void`
    // where the parameter is `(Animal) -> void` is rejected -- the callee
    // will invoke the callback with a bare Animal.
    let e = errs(&format!(
        "{VARIANCE_BASE}fun run(cb: (Animal) -> void) -> void {{ cb(Animal {{ sound: \"x\" }}) }}\nfun main() {{\n  run((d: Dog) -> {{ let s = d.breed }})\n}}\n"
    ));
    // A block closure without a value `return` is `void`.
    assert!(
        e.iter()
            .any(|m| m.contains("`(Dog) -> void`") && m.contains("`(Animal) -> void`")),
        "{e:?}"
    );
}

#[test]
fn anonymous_literal_closure_body_is_built_as_the_declared_result() {
    // An expression body is the closure's result: a record literal with
    // exactly the declared result record's fields is built as it, one
    // with another field set is a storage error.
    let base = "type Named = { name: string, id: int32 }\n";
    let ok = errs(&format!(
        "{base}fun main() {{\n  let f: () -> Named = () -> ({{ id: 1, name: \"x\" }})\n  let n = f()\n}}\n"
    ));
    assert!(ok.is_empty(), "{ok:?}");
    let bad = errs(&format!(
        "{base}fun main() {{\n  let f: () -> Named = () -> ({{ id: 1 }})\n  let n = f()\n}}\n"
    ));
    assert!(
        bad.iter()
            .any(|m| m.contains("cannot store this record literal") && m.contains("`name`")),
        "{bad:?}"
    );
}

#[test]
fn function_value_result_of_another_record_is_rejected() {
    // A closure checked against `(int32) -> Animal` returns into an
    // `Animal` result slot, so a `Dog` result is a representation change;
    // the reverse direction is not even usable.
    let widened = errs(&format!(
        "{VARIANCE_BASE}fun main() {{\n  let f: (int32) -> Animal = (n: int32) -> Dog {{ sound: \"woof\", breed: \"x\" }}\n}}\n"
    ));
    assert!(
        widened
            .iter()
            .any(|m| m.contains("cannot store a `Dog` in a slot of type `Animal`")),
        "{widened:?}"
    );
    // A closure LITERAL is checked against the annotation it flows into,
    // so the mismatch is its result value; a closure VALUE is compared as
    // a whole function type.
    let bad = errs(&format!(
        "{VARIANCE_BASE}fun main() {{\n  let f: (int32) -> Dog = (n: int32) -> Animal {{ sound: \"woof\" }}\n}}\n"
    ));
    assert!(
        bad.iter()
            .any(|m| m.contains("`Animal`") && m.contains("`Dog` is required")),
        "{bad:?}"
    );
    let bad = errs(&format!(
        "{VARIANCE_BASE}fun main() {{\n  let g = (n: int32) -> Animal {{ sound: \"woof\" }}\n  let f: (int32) -> Dog = g\n}}\n"
    ));
    assert!(
        bad.iter()
            .any(|m| m.contains("`(int32) -> Animal`") && m.contains("`(int32) -> Dog`")),
        "{bad:?}"
    );
}

#[test]
fn higher_order_function_values_keep_their_callback_types() {
    // A callback parameter of a function value is itself a function
    // value: it must name the same records in either direction.
    let widened = errs(&format!(
        "{VARIANCE_BASE}fun main() {{\n  let f: ((Animal) -> void) -> void = (cb: (Dog) -> void) -> {{}}\n}}\n"
    ));
    assert!(
        widened.iter().any(|m| m.contains(FUNCTION_VALUE_HINT)),
        "{widened:?}"
    );
    let bad = errs(&format!(
        "{VARIANCE_BASE}fun main() {{\n  let f: ((Dog) -> void) -> void = (cb: (Animal) -> void) -> {{}}\n}}\n"
    ));
    assert!(
        bad.iter()
            .any(|m| m.contains("`((Animal) -> void) -> void`")
                && m.contains("`((Dog) -> void) -> void`")),
        "{bad:?}"
    );
}

#[test]
fn function_value_passing_mode_cannot_change() {
    // Parameter variance applies to value types, not to the calling
    // convention. Hiding a mutable reference behind a copied parameter
    // would let a caller-owned value be changed through the function slot.
    let direct = errs(
        "fun main() {\n  let f: (int32[]) -> void = (x: ref(mut(int32[]))) -> { x.push(2) }\n}\n",
    );
    assert!(
        direct
            .iter()
            .any(|m| m.contains("ref(mut(int32[]))") && m.contains("int32[]")),
        "{direct:?}"
    );

    // The same rule must hold after the closure has first been inferred and
    // then flows through a separately annotated function-value binding.
    let indirect = errs(
        "fun main() {\n  let g = (x: ref(mut(int32[]))) -> { x.push(2) }\n  let f: (int32[]) -> void = g\n}\n",
    );
    assert!(
        indirect
            .iter()
            .any(|m| m.contains("ref(mut(int32[]))") && m.contains("int32[]")),
        "{indirect:?}"
    );
}

#[test]
fn function_typed_field_is_invariant_through_interface() {
    // A function-typed field is mutable storage, hence invariant: neither a
    // contravariantly-wider nor a covariantly-narrower parameter is allowed
    // to override the interface's field type, because a write through the
    // interface alias could install an incompatible callback.
    let widen = errs(&format!(
        "{VARIANCE_BASE}type Handler = {{ on: (Animal) -> void }}\ntype DogHandler: Handler = {{ on: (Dog) -> void }}\n"
    ));
    assert!(
        widen.iter().any(|m| m.contains("`DogHandler` field `on`")),
        "{widen:?}"
    );
    let narrow = errs(&format!(
        "{VARIANCE_BASE}type Handler = {{ on: (Dog) -> void }}\ntype AniHandler: Handler = {{ on: (Animal) -> void }}\n"
    ));
    assert!(
        narrow.iter().any(|m| m.contains("`AniHandler` field `on`")),
        "{narrow:?}"
    );
}

#[test]
fn method_function_typed_parameter_is_invariant() {
    // A method parameter is invariant (a caller reaching the type through
    // the interface must be able to pass everything the interface allows),
    // so a function-typed method parameter must match the interface's
    // parameter type exactly in BOTH directions.
    let widen = errs(&format!(
        "{VARIANCE_BASE}type C = {{ run(self, cb: (Dog) -> void) -> void }}\ntype D: C = {{ }}\nfun D.run(self, cb: (Animal) -> void) -> void {{ }}\n"
    ));
    assert!(
        widen
            .iter()
            .any(|m| m.contains("method `run` signature is not compatible")),
        "{widen:?}"
    );
    let narrow = errs(&format!(
        "{VARIANCE_BASE}type C = {{ run(self, cb: (Animal) -> void) -> void }}\ntype D: C = {{ }}\nfun D.run(self, cb: (Dog) -> void) -> void {{ }}\n"
    ));
    assert!(
        narrow
            .iter()
            .any(|m| m.contains("method `run` signature is not compatible")),
        "{narrow:?}"
    );
}

#[test]
fn method_function_typed_return_is_covariant() {
    // A method's return type is covariant: an implementation returning a
    // contravariantly-wider callback (`(Animal) -> void`) satisfies an
    // interface returning `(Dog) -> void`, but the reverse is rejected.
    let ok = errs(&format!(
        "{VARIANCE_BASE}type C = {{ make(self) -> (Dog) -> void }}\ntype D: C = {{ }}\nfun D.make(self) -> (Animal) -> void {{ return (a: Animal) -> {{}} }}\n"
    ));
    assert!(ok.is_empty(), "{ok:?}");
    let bad = errs(&format!(
        "{VARIANCE_BASE}type C = {{ make(self) -> (Animal) -> void }}\ntype D: C = {{ }}\nfun D.make(self) -> (Dog) -> void {{ return (d: Dog) -> {{}} }}\n"
    ));
    assert!(
        bad.iter()
            .any(|m| m.contains("method `make` signature is not compatible")),
        "{bad:?}"
    );
}

#[test]
fn debug_protocol_accepts_every_type() {
    // Every type satisfies `Debug` (the built-in renderer provides the
    // member), so a `Debug`-annotated parameter takes records, scalars,
    // and literals alike, and `type T: Debug` conformance holds. The body
    // is checked at each argument's own type, where a scalar's `debug` is
    // its standard-library primitive method.
    let library = parse(
        "type Debug = {\n    debug: (Self) -> string\n}\n\
             fun int32.debug(self) -> string {\n    return \"int\"\n}\n\
             fun string.debug(self) -> string {\n    return self\n}\n",
    )
    .expect("parse library module");
    let main = parse(
            "type Plain: Debug = {\n    n: int32\n}\nfun debug_it(v: Debug) {\n    println(v.debug())\n}\nfun main() {\n    debug_it(Plain { n: 1 })\n    debug_it(1)\n    debug_it(\"s\")\n}\n",
        )
        .expect("parse main module");
    let (prog, lerr) = lower(&[
        LoadedModule {
            is_prelude: true,
            path: vec!["core".into(), "show".into()],
            ast: library,
        },
        LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast: main,
        },
    ]);
    assert!(lerr.is_empty(), "lower errors: {lerr:?}");
    let e: Vec<String> = check(&prog).into_iter().map(|e| e.message).collect();
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn display_protocol_rejects_types_without_display() {
    let e = errs(
        "type Display = {\n    display: (Self) -> string\n}\ntype Plain = {\n    n: int32\n}\nfun show(v: Display) {\n    println(v.display())\n}\nfun main() {\n    show(Plain { n: 1 })\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("cannot use `Plain` where `Display` is required")),
        "{e:?}"
    );
}

#[test]
fn method_provides_function_typed_interface_member() {
    // A `b: (Self) -> string` member is provided by a declared method
    // `fun B.b(self)`, and calling `a.b()` through the interface binds
    // the receiver implicitly.
    let e = errs(
        "type A = {\n    a\n    b: (Self) -> string\n}\ntype B = {\n    a\n}\nfun B.b(self) {\n    return self.a\n}\nfun f(a: A) {\n    println(a.b())\n}\nfun main() {\n    f(B { a: \"s\" })\n}\n",
    );
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn function_typed_interface_member_rejects_incompatible_method_parameter() {
    // Same arity is insufficient: the implementing method must accept the
    // parameter type promised by the function-typed protocol member.
    let e = errs(
        "type Parser = {\n    parse: (Self, string) -> string\n}\ntype IntParser: Parser = {\n}\nfun IntParser.parse(self, value: int32) -> string {\n    return \"parsed\"\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("`IntParser` does not satisfy `Parser`: missing field `parse`")),
        "{e:?}"
    );
}

#[test]
fn function_typed_interface_member_accepts_compatible_method_parameter() {
    // A method with the protocol's receiver, parameter, and return types
    // provides the function-typed member without a stored closure field.
    let e = errs(
        "type Parser = {\n    parse: (Self, string) -> string\n}\ntype StringParser: Parser = {\n}\nfun StringParser.parse(self, value: string) -> string {\n    return value\n}\n",
    );
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn function_typed_interface_member_rejects_method_passing_mode_change() {
    // Function-member substitution cannot turn a copied parameter into a
    // mutable reference that aliases caller-owned state.
    let e = errs(
        "type Applier = {\n    apply: (Self, int32[]) -> void\n}\ntype BorrowingApplier: Applier = {\n}\nfun BorrowingApplier.apply(self, values: ref(mut(int32[]))) -> void {\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m
                .contains("`BorrowingApplier` does not satisfy `Applier`: missing field `apply`")),
        "{e:?}"
    );
}

#[test]
fn builtin_debug_types_as_string() {
    // Every type satisfies `Debug`: a record without a user `debug` gets
    // the built-in renderer, typed `string` (the mismatch against int32
    // proves the call resolved rather than deferring open).
    let e = errs(
        "type Point = {\n    x: int32\n}\nfun main() {\n    let p = Point { x: 1 }\n    let n: int32 = p.debug()\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("cannot use `string` where `int32` is required")),
        "{e:?}"
    );
}

#[test]
fn builtin_debug_rejects_arguments() {
    let e = errs(
        "type Point = {\n    x: int32\n}\nfun main() {\n    let p = Point { x: 1 }\n    println(p.debug(1))\n}\n",
    );
    assert!(
        e.iter().any(|m| m.contains("`debug` takes no arguments")),
        "{e:?}"
    );
}

#[test]
fn slotted_record_instances_are_independent() {
    // Two literals of a slotted record pin their slots independently: each
    // literal (and each field access on it) takes its own instantiation of
    // the declaration's slot variables. Unifying through the shared
    // declaration variables would make the first instance's element type
    // reject every differently-typed instance in the program.
    let e = errs(
        "type Stack = {\n    type item\n    items: Self.item[]\n}\nfun main() {\n    let a = Stack { items: [1] }\n    let b = Stack { items: [\"x\"] }\n    a.items.push(2)\n    b.items.push(\"y\")\n}\n",
    );
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn slotted_record_same_instance_mismatch_is_rejected() {
    // Independence is per instance, not per use: a second store into ONE
    // instance still checks against the type its first store pinned.
    let e = errs(
        "type Stack = {\n    type item\n    items: Self.item[]\n}\nfun main() {\n    let a = Stack { items: [1] }\n    a.items.push(\"y\")\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("cannot use `string` where `int32` is required")),
        "{e:?}"
    );
}

#[test]
fn alias_static_call_resolves_the_target_type() {
    // A static call through a `type Alias = Target` binding dispatches on
    // the target: the result is a `Widget`, so binding it to a string is
    // the target type's mismatch, not a silent open unknown.
    let e = errs(
        "type Widget = {\n    n: int64\n}\nfun Widget.new(n: int64) {\n    return Self { n: n }\n}\ntype B = Widget\nfun main() {\n    let s: string = B.new(3)\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("cannot use `Widget` where `string` is required")),
        "{e:?}"
    );
}

#[test]
fn alias_static_call_resolves_across_modules_and_renames() {
    // A re-export chain: a module imports a type under a
    // rename, aliases it, and a third module imports the alias and calls a
    // static through it. The mismatch against the TARGET type proves the
    // whole chain resolved.
    let e = module_errs(&[
        (
            &["lower"],
            "type Widget = {\n    n: int64\n}\nfun Widget.new(n: int64) {\n    return Self { n: n }\n}\n",
        ),
        (&["mid"], "import lower.{ Widget as W }\n\ntype Alias = W\n"),
        (
            &["main"],
            "import mid.{ Alias }\n\nfun main() {\n    let s: string = Alias.new(3)\n}\n",
        ),
    ]);
    assert!(
        e.iter()
            .any(|m| m.contains("cannot use `Widget` where `string` is required")),
        "{e:?}"
    );
}

#[test]
fn unresolvable_static_call_is_reported() {
    // A static call nothing declares must be a check error, not a silent
    // open unknown that only the back end trips over.
    let e = errs(
        "type Widget = {\n    n: int64\n}\nfun Widget.new(n: int64) {\n    return Self { n: n }\n}\nfun main() {\n    println(Widget.nope(3))\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("`Widget` has no static method `nope`")),
        "{e:?}"
    );
}

#[test]
fn refinement_alias_static_call_pins_slots() {
    // `Names.new()` builds the instance the refinement alias pins, exactly
    // like the annotated `let s: Names = Stack.new()` form: a later store
    // of the wrong element type is rejected.
    let e = errs(
        "type Stack = {\n    type item\n    items: Self.item[]\n}\nfun Stack.new() {\n    return Self { items: [] }\n}\nfun Stack.add(self, v) {\n    self.items.push(v)\n}\ntype Names = Stack { item: string }\nfun main() {\n    let s = Names.new()\n    s.add(1)\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("cannot use `int32` where `string` is required")),
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
fn exhaustiveness_uses_the_scrutinee_nominal_type() {
    // `X` belongs to both sums. Coverage must be computed from `b: B`, not
    // from the smaller `A` that happens to make the written arm exhaustive.
    let e = errs(
        "type A = | X\ntype B = | X | Y\nfun f(b: B) -> int32 {\n  return match b { X => 1 }\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("non-exhaustive match on `B`") && m.contains("Y")),
        "{e:?}"
    );

    let ok = errs(
        "type A = | X\ntype B = | X | Y\nfun f(a: A) -> int32 {\n  return match a { X => 1 }\n}\n",
    );
    assert!(ok.is_empty(), "{ok:?}");
}

#[test]
fn const_assignment_is_reported() {
    let e = errs("fun main() {\n    const p = 1\n    p = 2\n}\n");
    assert!(e.iter().any(|m| m.contains("const")), "{e:?}");
}

#[test]
fn const_mutations_in_assignment_values_and_interpolation_are_reported() {
    // Both positions evaluate their embedded call and therefore enforce the
    // same receiver immutability as a standalone call.
    let e = errs(
        "type Counter = { n: int32 }\nfun Counter.bump(self) -> int32 { self.n += 1\n return self.n }\nfun main() {\n const c = Counter { n: 0 }\n let n = 0\n n = c.bump()\n let text = \"{c.bump()}\"\n}\n",
    );
    let mutations = e
        .iter()
        .filter(|message| message.contains("mutating method `bump` on const value `c`"))
        .count();
    assert_eq!(mutations, 2, "{e:?}");
}

#[test]
fn closure_and_pattern_bindings_shadow_outer_consts() {
    // Each binding is lexical and fresh; none resolves to the same-named
    // global const while its body is checked.
    let e = errs(
        "const value = 1\nfun main() {\n let closure = (value) -> { value = 2 }\n if let value = 2 { value = 3 }\n match 2 { value => { value = 4 } }\n}\n",
    );
    assert!(
        !e.iter()
            .any(|message| message.contains("const value `value`")),
        "{e:?}"
    );
}

#[test]
fn pattern_binding_from_a_const_scrutinee_is_const() {
    // A matched aggregate aliases the const scrutinee instead of becoming a
    // mutable route to the same storage.
    let e = errs("const source = [1]\nfun main() {\n if let item = source { item[0] = 2 }\n}\n");
    assert!(
        e.iter()
            .any(|message| message.contains("cannot assign to const value `item`")),
        "{e:?}"
    );
}

#[test]
fn global_const_resolution_is_module_local() {
    // Same-named globals in unrelated modules cannot change the constness a
    // function observes in its own module.
    let e = module_errs(&[
        (
            &["a"],
            "const shared = [1]\nfun mutate_shared() { shared.push(2) }\n",
        ),
        (&["b"], "let shared = [1]\n"),
        (
            &["c"],
            "let other = [1]\nfun mutate_other() { other.push(2) }\n",
        ),
        (&["d"], "const other = [1]\n"),
    ]);
    assert!(
        e.iter()
            .any(|message| message.contains("const value `shared`")),
        "{e:?}"
    );
    assert!(
        !e.iter()
            .any(|message| message.contains("const value `other`")),
        "{e:?}"
    );
}

#[test]
fn imported_global_const_uses_its_local_name() {
    // Import renames participate in const lookup just like function and
    // type resolution.
    let e = module_errs(&[
        (&["values"], "const source = [1]\n"),
        (
            &["main"],
            "import values.{ source as local }\nfun main() { local.push(2) }\n",
        ),
    ]);
    assert!(
        e.iter()
            .any(|message| message.contains("const value `local`")),
        "{e:?}"
    );
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
fn const_mutation_is_judged_on_the_resolved_receiver() {
    // The const's type comes from an unannotated call and from an alias:
    // only inference knows the receiver is a `V`, whose `bump` writes
    // through `self`.
    let e = errs(
        "type V = { x: int32 }\nfun V.bump(self) {\n    self.x += 1\n}\n\
             fun mk() {\n    return V { x: 1 }\n}\n\
             fun main() {\n    const w = mk()\n    w.bump()\n\
             \x20   let v = V { x: 2 }\n    const a = v\n    a.bump()\n}\n",
    );
    for root in ["w", "a"] {
        assert!(
            e.iter().any(|m| m.contains(&format!(
                "cannot call mutating method `bump` on const value `{root}`"
            ))),
            "`{root}.bump()` must be rejected: {e:?}"
        );
    }
    // A user `push` that builds a new value is not a mutator, whatever its
    // name.
    let ok = errs(
        "type L = | Cons { head: int32, tail: L } | Nil\n\
             fun L.push(self, v: int32) -> L {\n    return L.Cons { head: v, tail: self }\n}\n\
             fun main() {\n    const n = L.Nil\n    let m = n.push(1)\n}\n",
    );
    assert!(ok.is_empty(), "a non-mutating `push` is allowed: {ok:?}");
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
    // parameter rejects a const. (The global is annotated growable: an
    // unannotated `const` array literal is fixed-length, which has no
    // `push` at all.)
    let ok = errs(
        "fun f(arr) {\n    arr.push(99)\n}\nconst a: int32[] = [1]\nfun main() {\n    f(a)\n}\n",
    );
    assert!(
        ok.is_empty(),
        "a const to an unannotated (copied) mutating parameter must be allowed: {ok:?}"
    );
    // A `ref(mut(int32[]))` parameter writes through, so a const is rejected.
    let e = errs(
        "fun f(arr: ref(mut(int32[]))) {\n    arr.push(99)\n}\nconst a: int32[] = [1]\nfun main() {\n    f(a)\n}\n",
    );
    assert!(
        e.iter().any(|m| m.contains("`a`") && m.contains("mutable")),
        "passing a const array to a `ref(mut(T))` parameter should be rejected: {e:?}"
    );
}

#[test]
fn const_through_a_transitive_write_through_function_is_rejected() {
    // Write-through is interprocedural through explicit references: `g`
    // takes `ref(mut(P))` and writes through it, and `f` passes its own
    // `ref(mut(P))` parameter on, so a const through the chain must be
    // rejected, at any depth.
    let two = errs(
        "type P = { x: int32 }\nfun g(p: ref(mut(P))) { p.x = 5 }\nfun f(p: ref(mut(P))) { g(p) }\nconst c = P { x: 1 }\nfun main() {\n    f(c)\n}\n",
    );
    assert!(
        two.iter()
            .any(|m| m.contains("`c`") && m.contains("mutable")),
        "a const forwarded one level into a write-through parameter should be rejected: {two:?}"
    );
    let three = errs(
        "type P = { x: int32 }\nfun deep(p: ref(mut(P))) { p.x = 9 }\nfun mid(p: ref(mut(P))) { deep(p) }\nfun top(p: ref(mut(P))) { mid(p) }\nconst c = P { x: 1 }\nfun main() {\n    top(c)\n}\n",
    );
    assert!(
        three
            .iter()
            .any(|m| m.contains("`c`") && m.contains("mutable")),
        "a const forwarded three levels into a write-through parameter should be rejected: {three:?}"
    );
    // An UNANNOTATED parameter that forwards into a write-through position
    // is a private deep copy (forwarding counts as mutation), so a const
    // argument is accepted -- the mutation hits the forwarder's own copy.
    let unannotated = errs(
        "type P = { x: int32 }\nfun g(p: ref(mut(P))) { p.x = 5 }\nfun f(p) { g(p) }\nconst c = P { x: 1 }\nfun main() {\n    f(c)\n}\n",
    );
    assert!(
        unannotated.is_empty(),
        "a const into an unannotated (copying) forwarder must be allowed: {unannotated:?}"
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
    // `a: infer` receives a read-only deep copy, so mutating it is
    // rejected; reading it is fine.
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
fn infer_parameter_rebinding_is_found_in_nested_expression_positions() {
    // The assignment is inside a call argument's block expression, not at
    // statement position.
    let e = errs("fun f(x: infer) { println({ x = 2\n x }) }\n");
    assert!(
        e.iter()
            .any(|message| message.contains("cannot mutate parameter `x`")),
        "{e:?}"
    );
}

#[test]
fn nested_shadow_does_not_rebind_an_infer_parameter() {
    // A lexical let hides the parameter for all later statements in the
    // block expression.
    let e = errs("fun f(x: infer) { println({ let x = 1\n x = 2\n x }) }\n");
    assert!(
        !e.iter()
            .any(|message| message.contains("cannot mutate parameter `x`")),
        "{e:?}"
    );
}

#[test]
fn mutating_an_unannotated_parameter_is_allowed() {
    // An unannotated parameter the body mutates is inferred as a private `mut`
    // copy, so mutating it is fine (the caller is unaffected at runtime).
    let ok = errs("fun f(a) {\n    a.push(1)\n}\nfun main() {\n    let xs = [1]\n    f(xs)\n}\n");
    assert!(
        ok.is_empty(),
        "mutating an unannotated parameter must be allowed: {ok:?}"
    );
}

#[test]
fn const_primitive_to_a_reassigning_function_is_allowed() {
    // Reassigning a parameter (`x = ...`) only rebinds the local; it is not a
    // through-reference mutation, so the parameter does not write through and
    // a const primitive argument stays valid.
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
    // Signature annotations are resolved during HIR lowering, so the
    // diagnostic is available before the type checker starts.
    let ast = parse("fun f(x: Nope) {\n}\n").expect("parse");
    let (_, errors) = lower(&[LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("unknown type `Nope`")),
        "{errors:?}"
    );
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
fn branch_local_tracking_does_not_escape_its_scope() {
    // Rewinding an if branch must discard both the branch-local descriptor
    // and its state slot before later locals receive ids.
    let e = errs(
        "fun main(flag: bool) {\n if flag {\n  let branch: int32\n  branch = 1\n  println(branch)\n }\n let later: int32\n later = 2\n println(later)\n}\n",
    );
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn indexed_store_requires_an_initialized_aggregate() {
    // An element store projects through the aggregate and cannot construct
    // an ordinary uninitialized binding wholesale.
    let e = errs("fun main() {\n let values: int32[]\n values[0] = 1\n}\n");
    assert!(
        e.iter()
            .any(|message| message.contains("`values` is used before it is fully initialized")),
        "{e:?}"
    );
}

#[test]
fn fields_loop_exits_do_not_prove_full_initialization() {
    // Break reaches the code after the loop without visiting later fields;
    // continue can skip the current field. Both remain live uninitialized paths.
    let e = errs(
        "type Pair = { left: int32, right: int32 }\nfun with_break(stop: bool) {\n let pair: Pair\n for field in fields(pair) {\n  if stop { break }\n  pair[field] = 1\n }\n println(pair)\n}\nfun with_continue(skip: bool) {\n let pair: Pair\n for field in fields(pair) {\n  if skip { continue }\n  pair[field] = 1\n }\n println(pair)\n}\n",
    );
    let uses = e
        .iter()
        .filter(|message| message.contains("`pair` is used before it is fully initialized"))
        .count();
    assert_eq!(uses, 2, "{e:?}");
}

#[test]
fn returning_fields_loop_paths_do_not_reach_the_summary() {
    // A return path needs no initialized post-loop value; every path that
    // does reach the final return has assigned the current field.
    let e = errs(
        "type Pair = { left: int32, right: int32 }\nfun build(stop: bool) -> Pair {\n let pair: Pair\n for field in fields(pair) {\n  if stop { return Pair { left: 0, right: 0 } }\n  pair[field] = 1\n }\n return pair\n}\n",
    );
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn closure_body_checks_its_own_uninitialized_locals() {
    // Closure-local storage has its own definite-assignment analysis even
    // though constructing the closure does not execute the body.
    let e =
        errs("fun main() {\n let closure = () -> {\n  let local: int32\n  println(local)\n }\n}\n");
    assert!(
        e.iter()
            .any(|message| message.contains("`local` is used before it is fully initialized")),
        "{e:?}"
    );
}

#[test]
fn closure_parameter_is_not_an_outer_capture() {
    // The parameter shadows the not-yet-initialized outer binding, so the
    // closure captures no `value` from its surrounding function.
    let e = errs(
        "fun main() {\n let value: int32\n let closure = (value: int32) -> value + 1\n value = 2\n println(closure(value))\n}\n",
    );
    assert!(
        !e.iter()
            .any(|message| message.contains("captured by a closure")),
        "{e:?}"
    );
}

#[test]
fn module_initializer_uses_definite_assignment() {
    // Top-level statement sequences obey the same uninitialized-let rule as
    // callable bodies.
    let e = errs("let value: int32\nprintln(value)\n");
    assert!(
        e.iter()
            .any(|message| message.contains("`value` is used before it is fully initialized")),
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
fn divergence_in_evaluated_subexpressions_satisfies_return_flow() {
    // Each function returns from a position that is unconditionally
    // evaluated before its enclosing statement could fall through.
    let e = errs(
        "fun consume(value: int32) {}\nfun from_initializer() -> int32 {\n let value = { return 1 }\n}\nfun from_assignment() -> int32 {\n let value = 0\n value = { return 2 }\n}\nfun from_condition() -> int32 {\n if { return 3 } {}\n}\nfun from_operand() -> int32 {\n let value = 1 + { return 4 }\n}\nfun from_argument() -> int32 {\n consume({ return 5 })\n}\n",
    );
    assert!(
        !e.iter()
            .any(|message| message.contains("may finish without returning")),
        "{e:?}"
    );
}

#[test]
fn module_qualified_reserved_functions_are_rejected() {
    // Duplicate bare names force qualified HIR symbols, but the declaration
    // name remains reserved in every user module.
    let e = module_errs(&[
        (&["a"], "fun len(value) { return value }\n"),
        (&["b"], "fun len(value) { return value }\n"),
    ]);
    assert!(
        e.iter()
            .any(|message| message.contains("`len` is a builtin and cannot be redefined")),
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

/// A RECORD `T.from(v)` accepts an argument of any type: it is a fallible
/// structural conversion whose result is `T?`, and an argument that is not a
/// record simply lands in the null path. (The numeric `T.from` below is a
/// different conversion and stays strict.) Accepting it is what lets one
/// function branch on "is this a T?" for a value whose type differs per call
/// site -- `fs.create_dir` takes a string or a `Path` that way.
#[test]
fn record_from_accepts_any_argument_type() {
    let src = "type P = { x: int32 }\nfun main() {\n    let a = P.from(\"s\")\n    let b = P.from(1)\n    let c = P.from([1])\n    let d = P.from(P { x: 1 })\n}\n";
    let e = errs(src);
    assert!(
        e.is_empty(),
        "a non-record argument must not be an error: {e:?}"
    );
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
fn absent_primitive_member_reads_null_but_cannot_be_used() {
    // An unknown member on a scalar is the null member-presence value
    // (`never?`), not a hard error -- that is what lets one generic body
    // presence-dispatch over scalars. Consuming it as a value still fails.
    let e = errs("fun main() {\n    let x: int32 = 5\n    let y: int32 = x.foo\n}\n");
    assert!(e.iter().any(|m| m.contains("cannot use")), "{e:?}");
}

#[test]
fn absent_member_on_a_string_or_array_prunes_the_arm() {
    // On a string or array receiver too, an absent member is a presence
    // test: it reads as the always-null `never?`, the `if` folds statically
    // false, and the arm that could not type for this receiver is never
    // checked.
    let e = errs(concat!(
        "fun f(x) -> int64 {\n",
        "    if x.no_such_member {\n",
        "        return x.no_such_member(1, 2)\n",
        "    }\n",
        "    return 0\n",
        "}\n",
        "fun main() {\n",
        "    let a = f(\"s\")\n",
        "    let b = f([1, 2])\n",
        "}\n",
    ));
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn a_present_primitive_member_is_a_truthy_name_string() {
    // `push` is a growable-array builtin, so `xs.push` (uncalled) decays to
    // its own name -- a non-null string, hence a statically true condition
    // whose else-arm is pruned rather than checked.
    let e = errs(concat!(
        "fun f(xs) -> string {\n",
        "    if xs.push {\n",
        "        return xs.push\n",
        "    }\n",
        "    return xs.anything_at_all(0)\n",
        "}\n",
        "fun main() {\n",
        "    let a = f([1, 2])\n",
        "}\n",
    ));
    assert!(e.is_empty(), "{e:?}");
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
    // Reported once, as an initialization-order error -- not also as an
    // unknown name.
    let e = errs("let a = b\nlet b = 1\n");
    assert_eq!(e, ["global `b` is used before it is initialized"], "{e:?}");
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
    let e = errs("fun f(flag: bool) -> int32 {\n    if flag { return 1 } else { return 2 }\n}\n");
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
    // `error(..)` is the prelude function the checker types as the
    // fallibility sugar's Err constructor; a user `fun error` would detach
    // `error(..)` from the sugar, so it is rejected.
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
            .any(|m| m.contains("cannot implicitly convert `float64` to `int32`")),
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
fn unresolved_literal_recovery_checks_every_field_expression() {
    let e = infer_errs(
        "type Choice = A | B\n\
             fun main() {\n\
                 Missing { value: missing_record_value }\n\
                 Choice.Nope { value: missing_variant_value }\n\
                 Choice { value: missing_sum_value }\n\
             }\n",
    );
    // Construction recovery must not hide independent failures nested in
    // unknown records, missing variants, or direct sum constructions.
    for name in [
        "missing_record_value",
        "missing_variant_value",
        "missing_sum_value",
    ] {
        assert!(
            e.iter()
                .any(|m| m.contains(&format!("unknown name `{name}`"))),
            "{name}: {e:?}"
        );
    }
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
fn call_invalidation_widens_the_exact_shadowed_global_binding() {
    let e = errs(
        "let state: string? = \"ready\"\n\
             fun clear() { state = null }\n\
             fun main() {\n\
                 if state {\n\
                     { let state = \"shadow\"\n clear() }\n\
                     state.len()\n\
                 }\n\
             }\n",
    );
    // The inner `state` must not hide the narrowed global from call
    // invalidation: `clear` can re-null the global before the final use.
    assert!(
        e.iter()
            .any(|m| m.contains("nullable value must be checked for null before use")),
        "{e:?}"
    );
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
        e.iter()
            .any(|m| { m.contains("`if` branches have incompatible types `int32` and `string`") }),
        "{e:?}"
    );
}

#[test]
fn match_arm_type_mismatch_is_reported() {
    let e =
        errs("fun main() {\n    let x: int32 = match true { true => 1, false => \"one\" }\n}\n");
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
    let e = errs("fun main() {\n    let a: int8 = 1\n    let b: int32 = 2\n    let c = a + b\n}\n");
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
    let e =
        errs("fun rem(x, y) {\n    return x % y\n}\nfun main() {\n    let r = rem(5.0, 2.0)\n}\n");
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
        e.iter().any(|m| m
            .contains("cannot infer the Ok payload type of a function that only returns errors")),
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
                .any(|m| m
                    .contains("error propagation requires `Result` or a nullable, found `int32`")),
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
fn error_propagation_is_allowed_at_top_level() {
    // A failed `!` at the module top level aborts the program at runtime
    // (there is no enclosing callable to return a `Result` from), so it
    // is not a compile error, and the binding takes the Ok payload type.
    let e = errs("let x = int32.parse(\"1\")!\nlet y: int64 = x\n");
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn error_propagation_on_nullable_makes_return_nullable() {
    // `!` on a nullable operand unwraps the value type; the null case
    // returns null itself, so the enclosing function's inferred return is
    // the operand's inner type made nullable -- using it without a null
    // check is rejected like any nullable.
    let e = errs(
        "fun find(s: string) -> int32? {\n    if s == \"a\" { return 1 }\n    return null\n}\nfun use_it() {\n    let v = find(\"a\")!\n    return v + 1\n}\nfun main() {\n    let bad: int32 = use_it()\n    println(bad)\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("nullable value must be checked for null before use")),
        "{e:?}"
    );
}

#[test]
fn mixed_error_and_null_propagation_infers_nullable_result() {
    // Bare returns + `error(...)` propagation + a nullable `!` in one body
    // infer `Result<int32, string>?`: narrowing the outer `?` and matching
    // `Ok`/`Err` consumes it without errors.
    let e = errs(
        "fun f(c: int32) {\n    if c == 0 {\n        return 1\n    } else if c == 1 {\n        error(\"a\")!\n    } else {\n        null!\n    }\n}\nfun main() {\n    let r = f(0)\n    if r {\n        match r {\n            Ok { value } => println(value),\n            Err { error } => println(error),\n        }\n    }\n}\n",
    );
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn implicit_nullable_result_warning_uses_signature_span_and_annotation_silences_it() {
    let body = "\n    if c == 1 {\n        error(\"a\")!\n    } else if c == 2 {\n        null!\n    }\n    return 1\n";
    let src = format!("fun mixed(c: int32) {{{body}}}\n");
    let ast = parse(&src).expect("parse");
    let TopLevel::Fun(function) = &ast.items[0] else {
        panic!("expected function");
    };
    let signature_span = function.span;
    let (program, lower_errors) = lower(&[LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(lower_errors.is_empty(), "lower errors: {lower_errors:?}");
    let analyzed = analyze(&program);
    assert!(analyzed.errors.is_empty(), "errors: {:?}", analyzed.errors);
    let [warning] = analyzed.warnings.as_slice() else {
        panic!("expected one warning, got {:?}", analyzed.warnings);
    };
    assert_eq!(warning.span, signature_span);
    let message = super::render_diagnostic_message(&warning.message, |offset| {
        Some(format!("offset:{offset}"))
    });
    assert!(
        message.starts_with(
            "`mixed` returns `Result<int32, string>?`: the body propagates both null (offset:"
        ),
        "{message}"
    );
    assert!(message.contains(") and errors (offset:"), "{message}");

    let explicit = format!("fun mixed(c: int32) -> int32!? {{{body}}}\n");
    let explicit = analysis(&explicit);
    assert!(explicit.errors.is_empty(), "errors: {:?}", explicit.errors);
    assert!(
        explicit.warnings.is_empty(),
        "explicit return annotations opt in to both layers: {:?}",
        explicit.warnings
    );
}

#[test]
fn implicit_nullable_result_warning_counts_a_returned_error_call() {
    // `return error(..)` is an error source like `error(..)!`: mixed with a
    // nullable `!`, the body infers `Result<T, E>?` and warns the same way.
    let analyzed = analysis(
        "fun find(xs: int32[], t: int32) -> int64? {\n\
                 if xs[0] == t { return 0 }\n\
                 return null\n\
             }\n\
             fun both(xs: int32[], t: int32) {\n\
                 const a = find(xs, t)!\n\
                 if a > 1 { return error(\"too far\") }\n\
                 return a\n\
             }\n",
    );
    assert!(analyzed.errors.is_empty(), "errors: {:?}", analyzed.errors);
    let [warning] = analyzed.warnings.as_slice() else {
        panic!("expected one warning, got {:?}", analyzed.warnings);
    };
    assert!(
        warning
            .message
            .starts_with("`both` returns `Result<int64, string>?`: the body propagates both"),
        "{}",
        warning.message
    );
}

#[test]
fn nullable_context_rewrite_infers_one_result_layer_without_warning() {
    let analyzed = analysis(
        "fun maybe(c: int32) -> int32? {\n\
                 if c > 0 { return c }\n\
                 return null\n\
             }\n\
             fun rewritten(c: int32) {\n\
                 if c == 0 { error(\"bad input\")! }\n\
                 return maybe(c).context(\"missing value\")!\n\
             }\n",
    );
    assert!(analyzed.errors.is_empty(), "errors: {:?}", analyzed.errors);
    assert!(
        analyzed.warnings.is_empty(),
        "the suggested rewrite must remove the mixed-propagation warning: {:?}",
        analyzed.warnings
    );
    assert_eq!(
        analyzed.function_returns.get("rewritten"),
        Some(&Type::result(Type::Int(IntKind::I32), Type::Str)),
    );
}

#[test]
fn implicit_nullable_result_warning_covers_methods_but_not_forwarded_or_closure_flows() {
    let method = analysis(
        "type Box = { value: int32 }\n\
             fun Box.mixed(self, c: int32) {\n\
                 if c == 1 { error(\"a\")! } else if c == 2 { null! }\n\
                 return self.value\n\
             }\n",
    );
    assert!(method.errors.is_empty(), "errors: {:?}", method.errors);
    assert_eq!(method.warnings.len(), 1, "warnings: {:?}", method.warnings);

    let forwarded = analysis(
        "fun source(c: int32) -> int32!? {\n\
                 if c == 1 { error(\"a\")! } else if c == 2 { null! }\n\
                 return null\n\
             }\n\
             fun forward(c: int32) -> int32!? { return source(c) }\n",
    );
    assert!(
        forwarded.errors.is_empty(),
        "errors: {:?}",
        forwarded.errors
    );
    assert!(
        forwarded.warnings.is_empty(),
        "an annotation and a forwarded two-layer value are deliberate: {:?}",
        forwarded.warnings
    );

    let closure = analysis(
        "fun outer(c: int32) {\n\
                 let nested = (value: int32) -> {\n\
                     if value == 1 { error(\"a\")! } else if value == 2 { null! }\n\
                     return 1\n\
                 }\n\
                 return nested(c)\n\
             }\n",
    );
    assert!(closure.errors.is_empty(), "errors: {:?}", closure.errors);
    assert!(
        closure.warnings.is_empty(),
        "closure return flows must not warn on the outer function: {:?}",
        closure.warnings
    );
}

#[test]
fn error_propagation_on_nullable_needs_nullable_return() {
    // Outside `main`/top level, a nullable `!` needs a return the null
    // can flow out of: an explicit non-nullable return rejects it.
    let e = errs(
        "fun find() -> int32? {\n    return null\n}\nfun f() -> int32 {\n    return find()!\n}\n",
    );
    assert!(
            e.iter().any(|m| {
                m.contains(
                    "null propagation (`!` on a nullable) requires a nullable return type, found `int32`"
                )
            }),
            "{e:?}"
        );
}

#[test]
fn fallible_closure_returns_result_type() {
    let e =
        errs("fun main() {\n    let f = () -> int32.parse(\"1\")!\n    let x: int32 = f()\n}\n");
    assert!(
        e.iter()
            .any(|m| m.contains("cannot use `Result<int32, string>` where `int32` is required")),
        "{e:?}"
    );
}

/// A block-bodied closure mixing `return error(..)` with a bare return is
/// fallible: the bare value is the Ok payload, so the call result is a
/// `Result` and matches like one. Unwrapping the call with `!` yields the
/// payload.
#[test]
fn fallible_closure_mixed_returns_and_unwrap() {
    let src = concat!(
        "fun main() {\n",
        "    let f = (s: string) -> {\n",
        "        if s == \"\" {\n",
        "            return error(\"empty\")\n",
        "        }\n",
        "        return s\n",
        "    }\n",
        "    let ok: string = f(\"hi\")!\n",
        "}\n",
    );
    let e = errs(src);
    assert!(e.is_empty(), "{e:?}");
}

/// A fallible closure through an UNANNOTATED higher-order parameter: the
/// callee's per-call result is the closure's `Result`, so matching on the
/// `Ok`/`Err` variants type-checks (the closure argument is re-checked at
/// its observed instantiation).
#[test]
fn fallible_closure_through_generic_callee_matches_result() {
    let e = errs(concat!(
        "fun call_it(f) {\n    return f(\"7\")\n}\n",
        "fun main() {\n",
        "    let r = call_it((s: string) -> {\n",
        "        if s == \"7\" {\n",
        "            return error(\"seven\")\n",
        "        }\n",
        "        return s\n",
        "    })\n",
        "    match r {\n",
        "        Ok { value } => println(value),\n",
        "        Err { error } => println(\"e\"),\n",
        "    }\n",
        "}\n",
    ));
    assert!(e.is_empty(), "{e:?}");
}

/// A fallible closure's error sites belong to the CLOSURE alone: the
/// enclosing function's inferred return stays the plain value, not wrapped
/// in the closure's `Result`.
#[test]
fn closure_error_sites_do_not_make_the_parent_fallible() {
    let e = errs(concat!(
        "fun outer() {\n",
        "    let f = (s: string) -> int32.parse(s)!\n",
        "    let r = f(\"xx\")\n",
        "    return \"done\"\n",
        "}\n",
        "fun main() {\n",
        "    let x: string = outer()\n",
        "}\n",
    ));
    assert!(e.is_empty(), "{e:?}");
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
    // (numeric positions convert implicitly, so `string` is the probe).
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
    let e = errs("fun main() {\n    let f = (x: int32, y: int32) -> x + y\n    let r = f(1)\n}\n");
    assert!(
        e.iter().any(|m| m.contains("expects 2 argument(s), got 1")),
        "{e:?}"
    );
}

#[test]
fn identity_closure_result_is_instantiated_at_call_site() {
    // `(x) -> x` applied to an `int32` yields `int32`, so binding the
    // result to `string` must be rejected. Without per-call instantiation
    // the closure return would be an unconstrained unknown that satisfies
    // any annotation (an unsound laundering of the value type).
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
    // `id` is a let-polymorphic binding, so `id(id)` applies one fresh
    // instance to another instead of unifying a parameter variable with a
    // function type that mentions it (the infinite type the occurs check
    // rejects for a monomorphic function value). Resolving terminates and
    // the result applied to `1` is an `int32`, so the binding is accepted.
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
    // compound assignments alike. Only VALUE-PRESERVING widenings convert;
    // narrowing is explicit (see the companion rejection test below).
    for (label, src) in [
        (
            "assignment widens",
            "fun main() {\n    let a: int32 = 5\n    let b: int64 = a\n}\n",
        ),
        (
            "unsigned widens into wider signed",
            "fun main() {\n    let a: uint8 = 5\n    let b: int32 = a\n}\n",
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
fn lossy_numeric_conversions_are_rejected() {
    // Narrowing (width, sign, float precision) is never implicit; the
    // diagnostic names the explicit conversion.
    for (label, src) in [
        (
            "int narrowing",
            "fun main() {\n    let a: int64 = 5\n    let b: int32 = a\n}\n",
        ),
        (
            "sign change",
            "fun main() {\n    let a: int32 = 5\n    let b: uint32 = a\n}\n",
        ),
        (
            "float narrowing",
            "fun main() {\n    let a: float64 = 1.5\n    let b: float32 = a\n}\n",
        ),
        (
            "int64 into float64 (mantissa)",
            "fun main() {\n    let a: int64 = 5\n    let f: float64 = a\n}\n",
        ),
    ] {
        let e = errs(src);
        assert!(
            e.iter().any(|m| m.contains("cannot implicitly convert")),
            "{label}: {e:?}"
        );
    }
}

#[test]
fn float_does_not_convert_to_int_implicitly() {
    // float -> int stays explicit (int32.from): the compound write-back would
    // silently truncate the fraction.
    let assign = errs("fun main() {\n    let f: float64 = 1.5\n    let n: int32 = f\n}\n");
    assert_eq!(
        assign,
        vec![
            "cannot implicitly convert `float64` to `int32`: float to int drops the \
                 fraction; convert explicitly (`int32.from(x)`)"
        ],
    );
    let compound =
        errs("fun main() {\n    let t: int32 = 1\n    let x: float64 = 2.5\n    t += x\n}\n");
    assert_eq!(
        compound,
        vec![
            "cannot implicitly convert `float64` to `int32`: float to int drops the \
                 fraction; convert explicitly (`int32.from(x)`)"
        ],
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
    // A null-containing literal must flow element-wise into the annotated
    // nullable-element sequence of an in-function `let`, and the same
    // literal must flow into a nullable-element parameter at a call site.
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
    let argument = errs("fun take(xs: int32?[]) {\n}\nfun main() {\n    take([7, null, 8])\n}\n");
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
    let e = errs("fun take_pair(values: int32[2]) {\n}\nfun main() {\n    take_pair([1, 2])\n}\n");
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn fixed_array_cannot_become_growable_through_mutable_reference() {
    // Dropping a fixed length is valid for a copied/read-only slice view,
    // but not for an alias through which the callee can grow the storage.
    let e = errs(
        "fun grow(a: ref(mut(int32[]))) { a.push(3) }\nfun main() {\n  let xs: int32[2] = [1, 2]\n  grow(xs)\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("int32[2]") && m.contains("ref(mut(int32[]))")),
        "{e:?}"
    );
}

#[test]
fn fixed_array_pattern_length_is_checked() {
    let e =
        errs("fun main() {\n    let values: int32[2] = [1, 2]\n    let [a, b, c] = values\n}\n");
    assert!(
        e.iter().any(|m| m.contains("array pattern has length 3")),
        "{e:?}"
    );
}

#[test]
fn growable_array_pattern_requires_a_refutable_context() {
    // A growable array does not prove the pattern's fixed arity, so a plain
    // `let` could leave one of its bindings uninitialized.
    let e = errs("fun main() {\n  let values = [1]\n  let [a, b] = values\n}\n");
    assert!(
        e.iter()
            .any(|m| m.contains("fixed-length array pattern") && m.contains("growable array")),
        "{e:?}"
    );

    // A literal supplies the exact arity even though a `let`-bound array is
    // growable after construction.
    let literal = errs("fun main() {\n  let [a, b] = [1, 2]\n}\n");
    assert!(literal.is_empty(), "{literal:?}");

    // Refutable contexts handle a length mismatch by choosing another path.
    let matched = errs(
        "fun main() {\n  let values = [1]\n  match values {\n    [a, b] => println(a),\n    _ => println(0),\n  }\n}\n",
    );
    assert!(matched.is_empty(), "{matched:?}");
    let conditional = errs(
        "fun main() {\n  let values = [1]\n  if let [a, b] = values {\n    println(a)\n  }\n}\n",
    );
    assert!(conditional.is_empty(), "{conditional:?}");
}

#[test]
fn record_argument_of_the_annotated_type_is_accepted() {
    // A free function with an annotated record parameter takes a value of
    // that record.
    let e = errs(
        "type Vec2 = {\n    x: float64\n    y: float64\n}\nfun length_sq(v: Vec2) -> float64 {\n    return v.x * v.x + v.y * v.y\n}\nfun main() {\n    let v = Vec2 { x: 3.0, y: 4.0 }\n    let r: float64 = length_sq(v)\n}\n",
    );
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn record_argument_without_the_annotated_fields_is_rejected() {
    // A record lacking a field of the annotated parameter's record type
    // (`Other` has no `x`) is not usable as that parameter.
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

// --- unresolved identifiers are name-resolution errors ---

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
    let e =
        errs("fun main() {\n    let p: int32 = println(\"x\")\n    let t: int32 = input()\n}\n");
    assert!(
        e.iter()
            .any(|m| m.contains("cannot use `void` where `int32` is required")),
        "{e:?}"
    );
    // Without the stdlib, `input` falls back to the same `string!` the real
    // definition infers.
    assert!(
        e.iter()
            .any(|m| m.contains("cannot use `Result<string, string>` where `int32` is required")),
        "{e:?}"
    );
}

#[test]
fn type_of_is_not_a_builtin() {
    // `type_of` and `_type_name` are not builtins: a call without a
    // definition is an unknown function.
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
            .any(|m| m.contains("cannot use `Result<string, string>` where `string` is required")),
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
fn string_find_checks_types_and_nested_excess_diagnostics() {
    let e = infer_errs("fun main() {\n    _string_find(1, \"x\", missing_find_argument)\n}\n");
    assert!(
        e.iter()
            .any(|m| m.contains("cannot use `int32` where `string` is required")),
        "{e:?}"
    );
    assert!(
        e.iter()
            .any(|m| m.contains("unknown name `missing_find_argument`")),
        "{e:?}"
    );
}

#[test]
fn zero_argument_runtime_builtins_walk_excess_arguments() {
    let e = infer_errs(
        "fun main() {\n    _flush(missing_flush_argument)\n    _argv(missing_argv_argument)\n}\n",
    );
    // Arity recovery still visits each supplied expression, preserving the
    // diagnostics users can fix independently of the outer call.
    for name in ["missing_flush_argument", "missing_argv_argument"] {
        assert!(
            e.iter()
                .any(|m| m.contains(&format!("unknown name `{name}`"))),
            "{name}: {e:?}"
        );
    }
}

#[test]
fn reserved_error_call_keeps_its_resolved_signature_contract() {
    let e = prelude_infer_errs(
        "fun main() {\n\
                 error()\n\
                 error(\"x\", 1)\n\
                 error(\"x\", Location { file: \"main.cz\", line: 1, col: 1 }, missing_extra)\n\
             }\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("`error` expects 1 to 2 argument(s), got 0")),
        "{e:?}"
    );
    assert!(
        e.iter()
            .any(|m| m.contains("cannot use `int32` where `Location` is required")),
        "{e:?}"
    );
    assert!(
        e.iter().any(|m| m.contains("unknown name `missing_extra`")),
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
fn spawn_requires_a_void_returning_closure() {
    let e = infer_errs("fun main() {\n    spawn(() -> 1)\n}\n");
    assert!(
        e.iter()
            .any(|m| m.contains("expects a closure returning `void`")),
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

// --- declared return types hold on every return path ---

#[test]
fn nested_if_return_violating_declared_type_is_rejected() {
    // A `return` inside an `if` evaluated as a statement-expression must
    // still be checked against the declared return type.
    let e = errs("fun f(n: int32) -> int32 {\n    if n <= 0 { return \"x\" }\n    return n\n}\n");
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

// --- fixed arrays T[n] cannot grow; slices T[] can ---

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

#[test]
fn slice_methods_enforce_exact_arity_and_walk_excess_arguments() {
    let e = infer_errs(
        "fun main() {\n\
                 let xs: int32[] = []\n\
                 xs.push()\n\
                 xs.insert(0)\n\
                 xs.pop(missing_pop_argument)\n\
                 xs.remove()\n\
                 xs.len(missing_len_argument)\n\
             }\n",
    );
    for (method, arity) in [
        ("push", 1),
        ("insert", 2),
        ("pop", 0),
        ("remove", 1),
        ("len", 0),
    ] {
        assert!(
            e.iter()
                .any(|m| m.contains(&format!("method `{method}` takes {arity}"))),
            "{method}: {e:?}"
        );
    }
    for name in ["missing_pop_argument", "missing_len_argument"] {
        assert!(
            e.iter()
                .any(|m| m.contains(&format!("unknown name `{name}`"))),
            "{name}: {e:?}"
        );
    }
}

// --- closure body constraints are verified at call sites ---

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
fn closure_storage_constraint_is_enforced_at_every_call() {
    // The closure parameter is stored into a concrete array, so the body
    // fixes it to the element type before the closure is generalized.
    let array = errs(
        "fun main() {\n  let xs: int32[] = []\n  let put = (x) -> { xs.push(x) }\n  put(1)\n  put(\"bad\")\n}\n",
    );
    assert!(
        array
            .iter()
            .any(|m| m.contains("cannot use `string` where `int32` is required")),
        "{array:?}"
    );

    // A top-level place follows the same rule; globals must not turn a
    // captured closure parameter into a fresh type at each call.
    let global = errs(
        "let sink: int32 = 0\nfun main() {\n  let put = (x) -> { sink = x }\n  put(\"bad\")\n}\n",
    );
    assert!(
        global
            .iter()
            .any(|m| m.contains("cannot use `string` where `int32` is required")),
        "{global:?}"
    );
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
fn closure_method_constraint_ignores_same_named_free_function() {
    let e = infer_errs(
        "fun speak() {}\n\
             fun main() {\n    let f = (x) -> x.speak()\n    f(1)\n}\n",
    );
    // Instance-call dispatch has no UFCS fallback, so an unrelated free
    // function cannot satisfy the receiver's recorded method shape.
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
    // function, where the closure's receiver parameter resolves against the
    // enclosing record type.
    let src = "type Calc = {\n    base: int32\n    apply: (self, int32) -> int32\n}\nfun main() {\n    let c = Calc { base: 10, apply: (receiver, n) -> { return receiver.base + n } }\n}\n";
    let e = errs(src);
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn closure_typed_field_body_return_mismatch_is_rejected() {
    // The closure body is checked against the field's declared return type, so
    // returning an int where `-> string` is required is an error.
    let e = errs(
        "type Obj = {\n    transform: (self, string) -> string\n}\nfun main() {\n    let o = Obj { transform: (receiver, s) -> { return 1 } }\n}\n",
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

// --- empty arrays pin their element type from first use ---

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
    let e = errs("fun main() {\n    let xs = []\n    xs.push(1)\n    let y: int32 = xs[0]\n}\n");
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn empty_array_pinned_to_string_reads_as_string() {
    let e =
        errs("fun main() {\n    let xs = []\n    xs.push(\"x\")\n    let y: string = xs[0]\n}\n");
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

// --- the free `len` builtin has a static int64 contract ---

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

/// `pick`'s inferred return is re-wrapped as `?` because the body returns
/// `null`, over a parameter variable the closure leaves open. Pinning that
/// variable to `string?` must not build `string??` -- and a nullable
/// argument reaching an open parameter pins it rather than demanding a null
/// check, exactly as it does for an unannotated free-function parameter.
#[test]
fn nullable_inferred_return_over_a_nullable_argument_stays_single() {
    let e = errs(
        "fun pick(x) {\n    if 1 == 2 {\n        return null\n    }\n    return x\n}\n\
             fun main() {\n    let a: string? = \"hi\"\n    let f = (s) -> pick(s)\n    \
             let r: string? = f(a)\n}\n",
    );
    assert!(e.is_empty(), "{e:?}");
}

#[test]
fn a_mismatched_branch_literal_is_reported_once() {
    // The branch value is checked against the slot's record; the whole
    // `if` is not checked again, which would restate the same mismatch
    // at the branch block.
    let e = errs(
        "type Named = { name: string, id: int32 }\n\
             fun main() {\n\
             let c = true\n\
             let p: Named = if c { { id: 1, name: \"a\" } } else { { id: 2 } }\n\
             }\n",
    );
    assert_eq!(e.len(), 1, "{e:?}");
    assert!(e[0].contains("missing field(s) `name`"), "{e:?}");
}

/// The plugin dispatch builtins are nameable from source, and the runtime
/// reads each payload slot at the signature's type without re-checking it.
/// The checker therefore has to type the whole call: string leading
/// operands, a literal signature it can read, and a payload matching it.
#[test]
fn plugin_call_builtin_checks_its_operands_against_the_signature() {
    let plugin_call = |args: &str| {
        errs(&format!(
            "fun main() {{\n    let v = _plugin_call_i({args})\n}}\n"
        ))
    };

    // A well-formed direct call still type-checks (the shape the loader's
    // synthesized wrappers emit).
    assert!(
        plugin_call("\"lib.so\", \"add\", \"ii:i\", 1, 2").is_empty(),
        "a correct call must be accepted"
    );

    // A non-string leading operand.
    let e = plugin_call("1, 2, 3");
    assert!(
        e.iter().any(|m| m.contains("where `string` is required")),
        "{e:?}"
    );

    // The signature must be readable at check time.
    let e = errs(
        "fun main() {\n    let s = \"ii:i\"\n    let v = _plugin_call_i(\"l\", \"f\", s, 1, 2)\n}\n",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("signature must be a string literal")),
        "{e:?}"
    );

    let e = plugin_call("\"l\", \"f\", \"zz\", 1");
    assert!(
        e.iter()
            .any(|m| m.contains("malformed plugin call signature")),
        "{e:?}"
    );

    // Payload arity and payload types are both fixed by the signature.
    let e = plugin_call("\"l\", \"f\", \"ii:i\", 1");
    assert!(
        e.iter()
            .any(|m| m.contains("passes 1 argument(s), signature `ii:i` has 2")),
        "{e:?}"
    );
    let e = plugin_call("\"l\", \"f\", \"si:i\", 42, 1");
    assert!(
        e.iter().any(|m| m.contains("where `string` is required")),
        "{e:?}"
    );
}
