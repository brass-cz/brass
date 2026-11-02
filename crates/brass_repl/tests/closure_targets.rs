//! The interpreter reports the missing closure instance without losing its symbol.

#[test]
fn missing_target_keeps_the_symbol_and_argument_effects() {
    let ast = brass_parser::parse(
        "fun effect() -> int32 { println(\"argument\")\n return 7 }\n\
         fun main() { let f = (x: int32) -> x\n f(effect()) }",
    )
    .unwrap();
    let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    let mir = brass_mir::lower_program(&program);
    let mut mono = brass_engine::monomorphize(&mir, &program).unwrap();
    let index = mono
        .functions
        .iter()
        .position(|f| f.symbol == "main")
        .unwrap();
    let mut body = mono.functions[index].body.clone();
    // An absent identity leaves the creation and call signatures untouched.
    let absent = brass_mir::ClosureId(u32::MAX);
    for block in &mut body.blocks {
        for stmt in &mut block.stmts {
            if let brass_mir::MirStmt::Assign(_, brass_mir::Rvalue::Closure { id, .. }) = stmt {
                *id = absent;
            }
        }
    }
    mono.functions[index].body = &body;
    let symbol = brass_engine::closure_symbol(
        absent,
        &[],
        &[brass_hir::Type::Int(brass_hir::IntKind::I32)],
    );
    let mut output = Vec::new();
    let error = brass_repl::Interp::new(&mono, &program, &mut output)
        .run()
        .unwrap_err();
    assert_eq!(
        error,
        format!("internal error: call of a closure that has no compiled instance (`{symbol}`)")
    );
    assert_eq!(output, b"argument\n");
}
