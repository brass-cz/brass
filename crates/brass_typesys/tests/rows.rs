//! Row inference over parsed programs: presence (Required vs Guarded), forced
//! types from annotated positions, interprocedural row union through forwarded
//! parameters, and the view-ineligibility rules.

use brass_hir::{IntKind, LoadedModule, Type};
use brass_typesys::{Presence, RowInfo, RowTy, check_row};

fn analyze(src: &str) -> (brass_hir::Program, RowInfo) {
    let ast = brass_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = brass_hir::lower(&modules);
    assert!(errors.is_empty(), "lower errors: {errors:?}");
    let rows = RowInfo::analyze(&program);
    (program, rows)
}

#[test]
fn unguarded_read_is_required_and_return_forces_the_declared_primitive() {
    // `p.x` is read with no guard and returned where `int32` is declared, so
    // the row must demand the field at exactly that type.
    let (_p, rows) = analyze("fun get_x(p) -> int32 {\n  return p.x\n}\n");
    let pr = rows.function_param("get_x", 0).expect("row for p");
    assert!(pr.eligible);
    let f = &pr.row.fields["x"];
    assert_eq!(f.presence, Presence::Required);
    assert_eq!(f.ty, RowTy::Forced(Type::Int(IntKind::I32)));
}

#[test]
fn truthiness_guard_makes_the_field_guarded_with_the_forced_type() {
    // The open-fields idiom: every access of `name` (the test and the guarded
    // return) tolerates absence, and the `-> string` return forces its type.
    let src = "fun get_name(person) -> string {\n\
               \x20 if person.name {\n    return person.name\n  } else {\n    return \"no name\"\n  }\n}\n";
    let (_p, rows) = analyze(src);
    let pr = rows.function_param("get_name", 0).expect("row");
    assert!(pr.eligible);
    let f = &pr.row.fields["name"];
    assert_eq!(f.presence, Presence::Guarded);
    assert_eq!(f.ty, RowTy::Forced(Type::Str));
}

#[test]
fn disjunctive_presence_tests_are_guarded_but_prove_neither_operand() {
    // Both sides of `||` tolerate an absent field. The second function also
    // pins that the true arm does not prove either alternative present.
    let src = "fun any(p) {\n  if p.a || p.b {\n    return\n  }\n}\n\
               fun read_after_any(p) {\n  if p.a || p.b {\n    println(p.a)\n    println(p.b)\n  }\n}\n";
    let (_p, rows) = analyze(src);
    let any = rows.function_param("any", 0).expect("row");
    assert_eq!(any.row.fields["a"].presence, Presence::Guarded);
    assert_eq!(any.row.fields["b"].presence, Presence::Guarded);

    let read = rows.function_param("read_after_any", 0).expect("row");
    assert_eq!(read.row.fields["a"].presence, Presence::Required);
    assert_eq!(read.row.fields["b"].presence, Presence::Required);
}

#[test]
fn forwarding_unions_the_callee_row() {
    // `display` never touches `last_name` itself; forwarding `obj` into
    // `helper` must pull helper's requirement into display's row.
    let src = "fun helper(o) -> string {\n  return o.last_name\n}\n\
               fun display(obj) {\n  println(obj.first_name)\n  println(helper(obj))\n}\n";
    let (_p, rows) = analyze(src);
    let pr = rows.function_param("display", 0).expect("row");
    assert!(pr.eligible);
    assert_eq!(pr.row.fields["last_name"].presence, Presence::Required);
    assert_eq!(
        pr.row.fields["last_name"].ty,
        RowTy::Forced(Type::Str),
        "the callee's declared-return force must propagate"
    );
    // A field read in a rendering position is an unguarded read: the caller
    // must provide it (render-null degradation lives behind explicit guards).
    assert_eq!(pr.row.fields["first_name"].presence, Presence::Required);
}

#[test]
fn escapes_and_method_receiver_use_are_view_ineligible() {
    // Each parameter keeps the full-value path: a returned parameter
    // escapes; a method receiver dispatches on the full type; a closure
    // capture outlives the frame; an annotated callee position is typed.
    let src = "type T = { x: int32 }\n\
               fun T.m(self) -> int32 {\n  return self.x\n}\n\
               fun ret(p) {\n  return p\n}\n\
               fun recv(p) -> int32 {\n  return p.m()\n}\n\
               fun cap(p) {\n  let f = () -> p.x\n  return f()\n}\n\
               fun annot(q: anonymous { x: int32 }) -> int32 {\n  return q.x\n}\n\
               fun fwd(p) -> int32 {\n  return annot(p)\n}\n";
    let (_p, rows) = analyze(src);
    for name in ["ret", "recv", "cap", "fwd"] {
        let pr = rows.function_param(name, 0).expect(name);
        assert!(!pr.eligible, "`{name}`'s parameter must be ineligible");
    }
}

#[test]
fn check_row_reports_missing_and_forced_type_issues_only_for_required_fields() {
    let src = "fun show(p) -> string {\n\
               \x20 let age: int32 = p.age\n\
               \x20 if p.nick {\n    return p.nick\n  }\n  return p.name\n}\n";
    let (_p, rows) = analyze(src);
    let pr = rows.function_param("show", 0).expect("row");
    // Value lacking `name`, with a wrongly-typed `age` and a wrongly-typed
    // guarded `nick`: only the two Required problems are value-site errors --
    // the guarded field degrades to null instead.
    let fields = vec![
        ("age".to_string(), Type::Str),
        ("nick".to_string(), Type::Int(IntKind::I32)),
    ];
    let issues = check_row(&pr.row, &fields);
    assert!(
        issues.iter().any(|m| m == "missing field `name`"),
        "{issues:?}"
    );
    assert!(
        issues
            .iter()
            .any(|m| m == "field `age`: cannot use `string` where `int32` is required"),
        "{issues:?}"
    );
    assert_eq!(issues.len(), 2, "guarded `nick` must not error: {issues:?}");
}

/// A structural source with the given fields, as the checker and the back ends
/// see an anonymous argument.
fn structural(fields: &[(&str, Type)]) -> brass_hir::NominalType {
    let Type::Record(n) = brass_hir::structural_record(
        fields
            .iter()
            .map(|(name, ty)| (name.to_string(), ty.clone()))
            .collect(),
    ) else {
        unreachable!("structural_record builds a record");
    };
    n
}

fn view_field(view: &Type, name: &str) -> Type {
    let Type::Record(n) = view else {
        panic!("a view is a record: {view:?}");
    };
    n.substitution.get(name).cloned().expect("view field")
}

#[test]
fn view_keeps_the_source_field_types_and_drops_untouched_fields() {
    // `show(p.n)` forces `float64` on a required field and `if p.flag` guards
    // a bool: the view must still carry the argument's own `int32` and `bool`,
    // or the body's arithmetic and its truthiness test would change.
    let src = "fun show(x: float64) {\n  println(x)\n}\n\
               fun half(p) {\n  show(p.n)\n  if p.flag {\n    return p.n / 2\n  }\n  return 0\n}\n";
    let (_p, rows) = analyze(src);
    let pr = rows.function_param("half", 0).expect("row");
    assert_eq!(
        pr.row.fields["n"].ty,
        RowTy::Forced(Type::Float(brass_hir::FloatKind::F64))
    );
    let source = structural(&[
        ("n", Type::Int(IntKind::I32)),
        ("flag", Type::Bool),
        ("extra", Type::Str),
    ]);
    let view = brass_typesys::view_type(&pr.row, &source).expect("view");
    assert_eq!(view_field(&view, "n"), Type::Int(IntKind::I32));
    assert_eq!(view_field(&view, "flag"), Type::Bool);
    let Type::Record(n) = &view else {
        unreachable!()
    };
    assert!(n.substitution.get("extra").is_none());
}

#[test]
fn view_reads_an_absent_or_unusable_guarded_field_as_null() {
    // The guarded `n` is forced to int64 by `take64`: an absent field and a
    // string field both read as the always-null `never?` (the body takes its
    // fallback), while a nullable int32 keeps its own type (narrowing serves
    // the forced use after the presence test).
    let src = "fun take64(x: int64) -> int64 {\n  return x\n}\n\
               fun f(p) -> int64 {\n  if p.n {\n    return take64(p.n)\n  }\n  return -1\n}\n";
    let (_p, rows) = analyze(src);
    let pr = rows.function_param("f", 0).expect("row");
    assert_eq!(pr.row.fields["n"].presence, Presence::Guarded);
    let view_of = |fields: &[(&str, Type)]| {
        brass_typesys::view_type(&pr.row, &structural(fields)).expect("view")
    };
    assert_eq!(
        view_field(&view_of(&[("m", Type::Bool)]), "n"),
        Type::null()
    );
    assert_eq!(view_field(&view_of(&[("n", Type::Str)]), "n"), Type::null());
    let nullable = Type::nullable(Type::Int(IntKind::I32));
    assert_eq!(
        view_field(&view_of(&[("n", nullable.clone())]), "n"),
        nullable
    );
}

#[test]
fn a_call_through_a_local_shadowing_a_function_is_not_a_forward() {
    // `helper` the function reads `a`, but each body calls a LOCAL value named
    // `helper`: the call passes the whole parameter to an unknown callee, so
    // the parameter must keep its full value instead of taking the global
    // helper's row.
    let src = "fun helper(x) {\n  return x.a\n}\n\
               fun via_let(p) {\n  let helper = (q) -> q.b\n  return helper(p)\n}\n\
               fun via_param(p, helper) {\n  return helper(p)\n}\n\
               fun via_global(p) {\n  return helper(p)\n}\n";
    let (_p, rows) = analyze(src);
    for name in ["via_let", "via_param"] {
        let pr = rows.function_param(name, 0).expect(name);
        assert!(!pr.eligible, "`{name}`'s parameter must be ineligible");
        assert!(!pr.row.fields.contains_key("a"), "`{name}`: {:?}", pr.row);
    }
    let global = rows.function_param("via_global", 0).expect("row");
    assert!(global.eligible);
    assert_eq!(global.row.fields["a"].presence, Presence::Required);
}
