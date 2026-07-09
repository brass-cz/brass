//! Row inference over parsed programs: presence (Required vs Guarded), forced
//! types from annotated positions, interprocedural row union through forwarded
//! parameters, and the view-ineligibility rules.

use prepoly_hir::{IntKind, LoadedModule, Type};
use prepoly_typesys::{Presence, RowInfo, RowTy, check_row};

fn analyze(src: &str) -> (prepoly_hir::Program, RowInfo) {
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = prepoly_hir::lower(&modules);
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
fn forwarding_unions_the_callee_row() {
    // `display` never touches `last_name` itself; forwarding `obj` into
    // `helper` must pull helper's requirement into display's row (C.2.2).
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
    // Each parameter keeps today's full-value path: a returned parameter
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
