//! Unit tests of the reflective specializer.

use brass_hir::{LoadedModule, NominalType, Substitution};

use super::*;

fn lower(src: &str) -> Program {
    let ast = brass_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        source: None,
        path: vec!["main".into()],
        ast,
        is_prelude: false,
    }];
    let (program, errors) = brass_hir::lower(&modules);
    assert!(errors.is_empty(), "lower errors: {errors:?}");
    program
}

fn receiver_symbol(program: &Program, name: &str) -> String {
    program
        .types
        .values()
        .find(|info| info.name == name)
        .expect("receiver")
        .symbol
        .clone()
}

fn keyed_need(program: &Program, receiver: &str, key: Type) -> KeyedNeed {
    KeyedNeed {
        recv: receiver_symbol(program, receiver),
        method: "into".into(),
        key,
    }
}

#[test]
fn specialization_spans_reserve_only_the_lanes_the_body_uses() {
    // Two leaf specializations, each a one-arm `infer.from` dispatch (its
    // body plus one arm lane), reserve only the four lanes they use, so both
    // bases stay within three shift units, well inside a 32-bit `usize`.
    let program = lower(
        "type Decoder = { value: int64 }\n\
         fun Decoder.into(self) -> infer! {\n\
           return infer.from(self.value)\n\
         }\n",
    );
    let generated = specialize_all(
        &program,
        &[
            keyed_need(&program, "Decoder", Type::Str),
            keyed_need(&program, "Decoder", Type::Bool),
        ],
    )
    .expect("specialize");
    assert_eq!(generated.len(), 2);
    let shifts: Vec<_> = generated
        .iter()
        .map(|generated| {
            let span = generated.decl.body.span;
            span.lo - span.source_span().lo
        })
        .collect();
    assert_ne!(shifts[0], shifts[1]);
    assert!(
        shifts
            .iter()
            .all(|shift| *shift <= 3 * brass_hir::SPAN_SHIFT_UNIT)
    );
}

#[test]
fn fields_loop_uses_the_concrete_record_field_substitution() {
    // The declaration's open `value` field must specialize recursively at
    // the concrete instance's `string`, not at the shared declaration hole.
    let program = lower(
        "type Target = { value }\n\
         type Decoder = { marker: int32 }\n\
         fun Decoder.into(self) -> infer! {\n\
           let ret: infer\n\
           for field in fields(ret) {\n\
             ret[field] = self.into()!\n\
           }\n\
           return ret\n\
         }\n",
    );
    let target = program
        .types
        .values()
        .find(|info| info.name == "Target")
        .expect("Target");
    let mut substitution = Substitution::empty();
    substitution.insert("value", Type::Str);
    let key = Type::Record(NominalType::with_substitution(
        target.id,
        target.name.clone(),
        substitution,
    ));
    let generated = specialize_all(&program, &[keyed_need(&program, "Decoder", key.clone())])
        .expect("specialize");
    assert!(generated.iter().any(|decl| decl.key == Type::Str));
    let root = generated
        .iter()
        .find(|decl| decl.key == key)
        .expect("root specialization");
    assert_eq!(
        count_method_calls(&root.decl.body, &mangled_name("into", &Type::Str)),
        1
    );
}

/// A record key `Target { a: string, b: string }` of a two-field declaration.
fn two_field_target(program: &Program) -> Type {
    program
        .types
        .values()
        .find(|info| info.name == "Target")
        .expect("Target")
        .type_ref()
}

/// The annotation of the first `let` in `block` or in a block statement
/// nested in it.
fn first_let_annotation(block: &Block) -> Option<TypeExpr> {
    block.stmts.iter().find_map(|stmt| match stmt {
        Stmt::Let { ty, .. } => ty.clone(),
        Stmt::Expr(Expr::Block(inner, _)) => first_let_annotation(inner),
        _ => None,
    })
}

#[test]
fn record_walk_is_found_by_the_iterated_binding_not_its_name() {
    // The walked binding is `out`, not `ret`: the loop over it must still be
    // unrolled into one field specialization call per field.
    let program = lower(
        "type Target = { a: string, b: string }\n\
         type Decoder = { marker: int32 }\n\
         fun Decoder.into(self) -> infer! {\n\
           let out: infer\n\
           for field in fields(out) {\n\
             out[field] = self.into()!\n\
           }\n\
           return out\n\
         }\n",
    );
    let key = two_field_target(&program);
    let generated = specialize_all(&program, &[keyed_need(&program, "Decoder", key.clone())])
        .expect("specialize");
    let root = generated
        .iter()
        .find(|decl| decl.key == key)
        .expect("root specialization");
    assert_eq!(
        count_method_calls(&root.decl.body, &mangled_name("into", &Type::Str)),
        2
    );
    assert_eq!(count_method_calls(&root.decl.body, "into"), 0);
}

#[test]
fn nullable_record_key_walks_the_payload_fields() {
    // At `Target?` the walked binding is the payload `Target` (a present
    // object decodes as the record, which promotes into the nullable result),
    // and the loop unrolls over `Target`'s fields.
    let program = lower(
        "type Target = { a: string, b: string }\n\
         type Decoder = { marker: int32 }\n\
         fun Decoder.into(self) -> infer! {\n\
           let ret: infer\n\
           for field in fields(ret) {\n\
             ret[field] = self.into()!\n\
           }\n\
           return ret\n\
         }\n",
    );
    let payload = two_field_target(&program);
    let key = Type::nullable(payload.clone());
    let generated = specialize_all(&program, &[keyed_need(&program, "Decoder", key.clone())])
        .expect("specialize");
    let root = generated
        .iter()
        .find(|decl| decl.key == key)
        .expect("root specialization");
    let Some(TypeExpr::Named(annotated, _)) = first_let_annotation(&root.decl.body) else {
        panic!("the walked binding keeps an annotation");
    };
    let Type::Record(n) = &payload else {
        unreachable!()
    };
    assert_eq!(annotated, brass_hir::generated_type_name(n.id));
    assert_eq!(
        count_method_calls(&root.decl.body, &mangled_name("into", &Type::Str)),
        2
    );
}

#[test]
fn nullable_key_unwraps_a_fallible_conversion() {
    // `int64.from` is range-checked (`int64!`); at an `int64?` key its Result
    // cannot flow into the `int64?` result, so the conversion is unwrapped
    // with `!` and its value promotes. At `int64` the Result is returned as is.
    let program = lower(
        "type Num = | Real { value: float64 }\n\
         fun Num.into(self) -> infer! {\n\
           match self {\n\
             Num.Real { value } => { return infer.from(value) }\n\
           }\n\
         }\n",
    );
    let propagated = |key: Type| {
        let generated =
            specialize_all(&program, &[keyed_need(&program, "Num", key)]).expect("specialize");
        let mut found = false;
        let mut visit = |e: &Expr| {
            if matches!(e, Expr::ErrorProp(inner, _) if matches!(&**inner, Expr::Call(..))) {
                found = true;
            }
        };
        walk_exprs(&generated[0].decl.body, &mut visit);
        found
    };
    assert!(propagated(Type::nullable(Type::Int(
        brass_hir::IntKind::I64
    ))));
    assert!(!propagated(Type::Int(brass_hir::IntKind::I64)));
}

#[test]
fn conversion_dispatch_gives_each_arm_its_own_spans() {
    // `infer.from(self.value)` names no source type, so it becomes a type-test
    // dispatch with one arm per source the key converts from: at `int64?`, the
    // identity and the nine other numeric types, each a propagated
    // `int64.from`. The checker and the lowering key their sidecars by span,
    // so the arms' tests, conversions and `!`s must not share one.
    let program = lower(
        "type Decoder = { value: int32 }\n\
         fun Decoder.into(self) -> infer! {\n\
           return infer.from(self.value)\n\
         }\n",
    );
    let key = Type::nullable(Type::Int(brass_hir::IntKind::I64));
    let generated =
        specialize_all(&program, &[keyed_need(&program, "Decoder", key)]).expect("specialize");
    let mut tests = 0;
    let mut spans = Vec::new();
    let mut visit = |e: &Expr| match e {
        Expr::TypeTest(..) => {
            tests += 1;
            spans.push(e.span());
        }
        Expr::If(..) | Expr::Call(..) | Expr::ErrorProp(..) => spans.push(e.span()),
        _ => {}
    };
    walk_all_exprs(&generated[0].decl.body, &mut visit);
    assert_eq!(tests, 10);
    let distinct: fxhash::FxHashSet<_> = spans.iter().collect();
    assert_eq!(distinct.len(), spans.len());
}

/// Visit the expressions of `block`'s expression, `return` and `let`
/// statements, descending through the node kinds a conversion dispatch is
/// built from (`!`, unary, field, type test, call, `if`, `match`, block).
fn walk_all_exprs(block: &Block, visit: &mut impl FnMut(&Expr)) {
    fn expr(e: &Expr, visit: &mut impl FnMut(&Expr)) {
        visit(e);
        match e {
            Expr::ErrorProp(inner, _)
            | Expr::Unary(_, inner, _)
            | Expr::Field(inner, _, _)
            | Expr::TypeTest(inner, _, _, _) => expr(inner, visit),
            Expr::Call(callee, args, _) => {
                expr(callee, visit);
                args.iter().for_each(|arg| expr(&arg.expr, visit));
            }
            Expr::If(cond, then, els, _) => {
                expr(cond, visit);
                walk_all_exprs(then, visit);
                if let Some(els) = els {
                    expr(els, visit);
                }
            }
            Expr::Match(scrutinee, arms, _) => {
                expr(scrutinee, visit);
                arms.iter().for_each(|arm| expr(&arm.body, visit));
            }
            Expr::Block(b, _) => walk_all_exprs(b, visit),
            _ => {}
        }
    }
    for stmt in &block.stmts {
        match stmt {
            Stmt::Expr(e) | Stmt::Return(Some(e), _) => expr(e, visit),
            Stmt::Let { value: Some(e), .. } => expr(e, visit),
            _ => {}
        }
    }
}

/// Visit the expressions of `block`'s expression, `return` and `let`
/// statements, descending only through `!`, `match` arms and nested blocks.
fn walk_exprs(block: &Block, visit: &mut impl FnMut(&Expr)) {
    fn expr(e: &Expr, visit: &mut impl FnMut(&Expr)) {
        visit(e);
        match e {
            Expr::ErrorProp(inner, _) => expr(inner, visit),
            Expr::Match(scrutinee, arms, _) => {
                expr(scrutinee, visit);
                arms.iter().for_each(|arm| expr(&arm.body, visit));
            }
            Expr::Block(b, _) => walk_exprs(b, visit),
            _ => {}
        }
    }
    for stmt in &block.stmts {
        match stmt {
            Stmt::Expr(e) | Stmt::Return(Some(e), _) => expr(e, visit),
            Stmt::Let { value: Some(e), .. } => expr(e, visit),
            _ => {}
        }
    }
}

#[test]
fn infer_substitution_reaches_every_composite_type_expression() {
    // The shape includes function, tuple, anonymous, mut/ref, typeof, and
    // refinement nesting so no composite can strand an `infer` annotation.
    let span = brass_hir::Span::new(1, 2);
    let infer = || TypeExpr::Named("infer".into(), span);
    let ty = TypeExpr::Fun(
        vec![
            TypeExpr::Tuple(
                vec![
                    TypeExpr::Array(Box::new(infer()), Some(2), span),
                    TypeExpr::Nullable(Box::new(TypeExpr::Fallible(Box::new(infer()), span)), span),
                ],
                span,
            ),
            TypeExpr::Anonymous(
                vec![(
                    "value".into(),
                    TypeExpr::Mut(Box::new(TypeExpr::Ref(Box::new(infer()), span)), span),
                    span,
                )],
                span,
            ),
            TypeExpr::TypeOf(
                Box::new(Expr::TypeTest(
                    Box::new(Expr::Ident("x".into(), span)),
                    infer(),
                    false,
                    span,
                )),
                span,
            ),
        ],
        Box::new(TypeExpr::Refine(
            Box::new(TypeExpr::Named("Base".into(), span)),
            vec![(
                "slot".into(),
                TypeExpr::Fun(vec![infer()], Box::new(infer()), span),
                span,
            )],
            span,
        )),
        span,
    );
    let program = Program::empty();
    let mut work = Vec::new();
    let mut specializer = Specializer {
        program: &program,
        recv: "Receiver",
        method: "into",
        key: &Type::Str,
        scrutinee: Type::Void,
        work: &mut work,
        walked: fxhash::FxHashSet::default(),
        walk_targets: fxhash::FxHashSet::default(),
        located: false,
        dispatch_stride: 1,
    };
    let substituted = specializer.subst_type(&ty, &HashMap::default());
    assert_eq!(count_infer_types(&substituted), 0);
}

#[test]
fn recursive_call_rewrite_walks_nested_control_flow_and_values() {
    // The recursive call sits inside every node kind a shallow walk would
    // clone wholesale: loops, blocks, conditionals, matches, closures,
    // arrays, and unary ops.
    let span = brass_hir::Span::new(1, 2);
    let call = || {
        Expr::Call(
            Box::new(Expr::Field(
                Box::new(Expr::Ident("x".into(), span)),
                "into".into(),
                span,
            )),
            Vec::new(),
            span,
        )
    };
    let nested = Block {
        stmts: vec![
            Stmt::While {
                cond: call(),
                body: Block {
                    stmts: vec![Stmt::Expr(Expr::If(
                        Box::new(call()),
                        Block {
                            stmts: vec![Stmt::Expr(Expr::Match(
                                Box::new(call()),
                                vec![MatchArm {
                                    pattern: Pattern::Wildcard(span),
                                    body: call(),
                                    span,
                                }],
                                span,
                            ))],
                            span,
                        },
                        Some(Box::new(Expr::Block(
                            Block {
                                stmts: vec![Stmt::Expr(call())],
                                span,
                            },
                            span,
                        ))),
                        span,
                    ))],
                    span,
                },
                span,
            },
            Stmt::For {
                pat: Pattern::Binding("item".into(), None, span),
                iter: Expr::Array(vec![call()], span),
                body: Block {
                    stmts: vec![Stmt::Let {
                        pat: Pattern::Binding("f".into(), None, span),
                        ty: Some(TypeExpr::TypeOf(Box::new(call()), span)),
                        value: Some(Expr::Closure(
                            Vec::new(),
                            Box::new(Expr::Array(
                                vec![Expr::Unary(UnaryOp::Not, Box::new(call()), span)],
                                span,
                            )),
                            span,
                        )),
                        is_const: false,
                        span,
                    }],
                    span,
                },
                span,
            },
        ],
        span,
    };
    let original = count_method_calls(&nested, "into");
    assert!(original >= 8);
    let rewritten = RewriteInto {
        method: "into",
        mangled: "into__string",
    }
    .block(&nested);
    assert_eq!(count_method_calls(&rewritten, "into"), 0);
    assert_eq!(count_method_calls(&rewritten, "into__string"), original);
}

fn count_infer_types(ty: &TypeExpr) -> usize {
    match ty {
        TypeExpr::Named(name, _) => usize::from(name == "infer"),
        TypeExpr::Array(inner, _, _)
        | TypeExpr::Nullable(inner, _)
        | TypeExpr::Fallible(inner, _)
        | TypeExpr::Mut(inner, _)
        | TypeExpr::Ref(inner, _) => count_infer_types(inner),
        TypeExpr::Fun(params, ret, _) => {
            params.iter().map(count_infer_types).sum::<usize>() + count_infer_types(ret)
        }
        TypeExpr::Tuple(items, _) => items.iter().map(count_infer_types).sum(),
        TypeExpr::Anonymous(fields, _) => {
            fields.iter().map(|(_, ty, _)| count_infer_types(ty)).sum()
        }
        TypeExpr::TypeOf(expr, _) => count_infer_expr(expr),
        TypeExpr::Refine(base, fields, _) => {
            count_infer_types(base)
                + fields
                    .iter()
                    .map(|(_, ty, _)| count_infer_types(ty))
                    .sum::<usize>()
        }
        TypeExpr::TypeSlot(_) | TypeExpr::SelfField(..) => 0,
    }
}

fn count_infer_expr(expr: &Expr) -> usize {
    match expr {
        Expr::TypeTest(subject, ty, _, _) => count_infer_expr(subject) + count_infer_types(ty),
        _ => 0,
    }
}

fn count_method_calls(block: &Block, method: &str) -> usize {
    block
        .stmts
        .iter()
        .map(|stmt| match stmt {
            Stmt::Let { ty, value, .. } => {
                ty.as_ref().map_or(0, |ty| count_type_calls(ty, method))
                    + value
                        .as_ref()
                        .map_or(0, |value| count_expr_calls(value, method))
            }
            Stmt::Assign { target, value, .. } => {
                count_expr_calls(target, method) + count_expr_calls(value, method)
            }
            Stmt::Expr(expr) | Stmt::Return(Some(expr), _) => count_expr_calls(expr, method),
            Stmt::While { cond, body, .. } => {
                count_expr_calls(cond, method) + count_method_calls(body, method)
            }
            Stmt::For { iter, body, .. } => {
                count_expr_calls(iter, method) + count_method_calls(body, method)
            }
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => 0,
        })
        .sum()
}

fn count_type_calls(ty: &TypeExpr, method: &str) -> usize {
    match ty {
        TypeExpr::Array(inner, _, _)
        | TypeExpr::Nullable(inner, _)
        | TypeExpr::Fallible(inner, _)
        | TypeExpr::Mut(inner, _)
        | TypeExpr::Ref(inner, _) => count_type_calls(inner, method),
        TypeExpr::Fun(params, ret, _) => {
            params
                .iter()
                .map(|param| count_type_calls(param, method))
                .sum::<usize>()
                + count_type_calls(ret, method)
        }
        TypeExpr::Tuple(items, _) => items
            .iter()
            .map(|item| count_type_calls(item, method))
            .sum(),
        TypeExpr::Anonymous(fields, _) => fields
            .iter()
            .map(|(_, ty, _)| count_type_calls(ty, method))
            .sum(),
        TypeExpr::TypeOf(expr, _) => count_expr_calls(expr, method),
        TypeExpr::Refine(base, fields, _) => {
            count_type_calls(base, method)
                + fields
                    .iter()
                    .map(|(_, ty, _)| count_type_calls(ty, method))
                    .sum::<usize>()
        }
        TypeExpr::Named(..) | TypeExpr::TypeSlot(_) | TypeExpr::SelfField(..) => 0,
    }
}

fn count_expr_calls(expr: &Expr, method: &str) -> usize {
    let own = usize::from(matches!(
        expr,
        Expr::Call(callee, _, _)
            if matches!(&**callee, Expr::Field(_, name, _) if name == method)
    ));
    own + match expr {
        Expr::Unary(_, inner, _) | Expr::ErrorProp(inner, _) | Expr::Field(inner, _, _) => {
            count_expr_calls(inner, method)
        }
        Expr::TypeTest(subject, ty, _, _) => {
            count_expr_calls(subject, method) + count_type_calls(ty, method)
        }
        Expr::Binary(_, left, right, _)
        | Expr::Index(left, right, _)
        | Expr::Range(left, right, _) => {
            count_expr_calls(left, method) + count_expr_calls(right, method)
        }
        Expr::Call(callee, args, _) => {
            count_expr_calls(callee, method)
                + args
                    .iter()
                    .map(|arg| count_expr_calls(&arg.expr, method))
                    .sum::<usize>()
        }
        Expr::Str(segments, _) => segments
            .iter()
            .map(|segment| match segment {
                StrSeg::Lit(_) => 0,
                StrSeg::Expr(expr) => count_expr_calls(expr, method),
            })
            .sum(),
        Expr::Closure(params, body, _) => {
            params
                .iter()
                .map(|param| {
                    param
                        .ty
                        .as_ref()
                        .map_or(0, |ty| count_type_calls(ty, method))
                })
                .sum::<usize>()
                + count_expr_calls(body, method)
        }
        Expr::Array(items, _) => items
            .iter()
            .map(|item| count_expr_calls(item, method))
            .sum(),
        Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => fields
            .iter()
            .map(|(_, value)| count_expr_calls(value, method))
            .sum(),
        Expr::If(cond, then, els, _) => {
            count_expr_calls(cond, method)
                + count_method_calls(then, method)
                + els.as_ref().map_or(0, |els| count_expr_calls(els, method))
        }
        Expr::IfLet(_, scrutinee, then, els, _) => {
            count_expr_calls(scrutinee, method)
                + count_method_calls(then, method)
                + els.as_ref().map_or(0, |els| count_expr_calls(els, method))
        }
        Expr::Match(scrutinee, arms, _) => {
            count_expr_calls(scrutinee, method)
                + arms
                    .iter()
                    .map(|arm| count_expr_calls(&arm.body, method))
                    .sum::<usize>()
        }
        Expr::Block(block, _) => count_method_calls(block, method),
        Expr::Int(..)
        | Expr::Float(..)
        | Expr::Bool(..)
        | Expr::Null(_)
        | Expr::Ident(..)
        | Expr::SelfExpr(_) => 0,
    }
}
