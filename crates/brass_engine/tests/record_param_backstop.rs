//! Monomorphization backstop for record-annotated parameters: an instance is
//! compiled at the argument's own type, so an argument that lacks a field the
//! annotation declares must stop instantiation with an internal error rather
//! than compile a body that reads a field the value does not have. The
//! checker rejects such programs, so this drives lowering and
//! monomorphization directly, without the checker.

use brass_engine::monomorphize;
use brass_hir::LoadedModule;

fn monomorphize_unchecked(source: &str) -> Option<String> {
    let ast = brass_parser::parse(source).expect("parse");
    let modules = [LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = brass_hir::lower(&modules);
    assert!(errors.is_empty(), "lower errors: {errors:?}");
    let mir = brass_mir::lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    mono.main_skip
}

#[test]
fn a_record_argument_missing_a_declared_field_is_an_internal_error() {
    let skip = monomorphize_unchecked(
        "type Big = { a: int32, b: string }\n\
         type Small = { a: int32 }\n\
         fun use_big(x: Big) -> string {\n  return x.b\n}\n\
         fun main() {\n  let s = use_big(Small { a: 1 })\n}\n",
    )
    .expect("main must not monomorphize");
    assert!(
        skip.contains("internal error") && skip.contains("lacks its field `b`"),
        "unexpected reason: {skip}"
    );
}

#[test]
fn a_record_argument_with_every_declared_field_instantiates() {
    let skip = monomorphize_unchecked(
        "type Small = { a: int32 }\n\
         type Big = { a: int32, b: string }\n\
         fun use_small(x: Small) -> int32 {\n  return x.a\n}\n\
         fun main() {\n  let s = use_small(Big { a: 1, b: \"s\" })\n}\n",
    );
    assert!(skip.is_none(), "main was skipped: {skip:?}");
}
