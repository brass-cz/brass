//! Lowering: collect AST modules into the HIR `Program`, assigning runtime
//! type ids (Result is fixed at id 0) and variant tags, and gathering each
//! module's top-level statements for initialization.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use prepoly_lexer::Span;
use prepoly_parser::ast::{Member, TopLevel, TypeBody, TypeDecl};

use crate::hir::*;
use crate::types::{NominalInfo, Type, resolve};

/// A collection error (duplicate name).
#[derive(Clone, Debug)]
pub struct LowerError {
    pub message: String,
    pub span: Span,
}

/// Collect all modules into a `Program`. Errors list duplicate declarations.
pub fn lower(modules: &[LoadedModule]) -> (Program, Vec<LowerError>) {
    let mut types: HashMap<String, TypeInfo> = HashMap::new();
    let mut functions: HashMap<String, FunInfo> = HashMap::new();
    let mut inits = Vec::new();
    let mut module_imports: HashMap<Vec<String>, Vec<String>> = HashMap::new();
    let mut import_origins: HashMap<Vec<String>, HashMap<String, Vec<String>>> = HashMap::new();
    let mut errors = Vec::new();
    let mut next_id: i32 = 1; // 0 is reserved for Result

    types.insert("Result".to_string(), result_type());

    // How many modules define each top-level function/type name. A name defined
    // in a single module keeps its bare symbol (so all existing bare-name lookups
    // and codegen symbols are unchanged); a name defined in several modules is
    // qualified per module so the definitions coexist.
    let fn_name_modules = name_module_counts(modules, |item| match item {
        TopLevel::Fun(f) => Some(&f.name),
        _ => None,
    });
    let type_name_modules = name_module_counts(modules, |item| match item {
        TopLevel::Type(t) => Some(&t.name),
        _ => None,
    });

    for m in modules {
        // Record the names this module imports so per-module visibility can
        // tell an imported cross-module name from an inaccessible one.
        let imported = module_imports.entry(m.path.clone()).or_default();
        for imp in &m.ast.imports {
            imported.extend(imp.names.iter().cloned());
        }
        let origins = import_origins.entry(m.path.clone()).or_default();
        for imp in &m.ast.imports {
            for name in &imp.names {
                origins
                    .entry(name.clone())
                    .or_insert_with(|| imp.path.clone());
            }
        }
        let mut stmts = Vec::new();
        for item in &m.ast.items {
            match item {
                TopLevel::Type(td) => {
                    let symbol = qualified_symbol(&td.name, &m.path, &type_name_modules);
                    // Same symbol => same name twice in one module (a genuine
                    // duplicate, or a clash with the builtin `Result`). A
                    // different module yields a different symbol, so cross-module
                    // same-named types coexist.
                    if types.contains_key(&symbol) {
                        if td.name != "Result" {
                            errors.push(LowerError {
                                message: format!("duplicate type `{}`", td.name),
                                span: td.span,
                            });
                        }
                        continue;
                    }
                    let info = type_info(td, next_id, &m.path, symbol.clone(), &mut errors);
                    next_id += 1;
                    types.insert(symbol, info);
                }
                TopLevel::Fun(f) => {
                    let symbol = qualified_symbol(&f.name, &m.path, &fn_name_modules);
                    // Same symbol => same name defined twice in the same module:
                    // a genuine duplicate. A different module yields a different
                    // symbol, so cross-module same names coexist.
                    if functions.contains_key(&symbol) {
                        errors.push(LowerError {
                            message: format!("duplicate function `{}`", f.name),
                            span: f.span,
                        });
                    } else {
                        functions.insert(
                            symbol.clone(),
                            FunInfo {
                                signature: CallableSignature::from_function(f),
                                decl: Rc::new(f.clone()),
                                module: m.path.clone(),
                                symbol,
                            },
                        );
                    }
                }
                TopLevel::Stmt(s) => stmts.push(s.clone()),
            }
        }
        inits.push(ModuleInit {
            path: m.path.clone(),
            stmts,
        });
    }

    let mut program = Program {
        types,
        functions,
        inits,
        module_imports,
        import_origins,
    };
    resolve_program_annotations(&mut program);

    (program, errors)
}

/// Count, per top-level name (selected by `extract`), how many distinct modules
/// define it. A name defined in a single module stays bare; one defined in
/// several is qualified per module so the definitions coexist.
fn name_module_counts(
    modules: &[LoadedModule],
    extract: impl Fn(&TopLevel) -> Option<&String>,
) -> HashMap<String, usize> {
    let mut per_name: HashMap<String, HashSet<Vec<String>>> = HashMap::new();
    for m in modules {
        for item in &m.ast.items {
            if let Some(name) = extract(item) {
                per_name
                    .entry(name.clone())
                    .or_default()
                    .insert(m.path.clone());
            }
        }
    }
    per_name
        .into_iter()
        .map(|(name, mods)| (name, mods.len()))
        .collect()
}

/// The unique storage/codegen symbol for a top-level name: its bare form when
/// only one module defines that name, or the qualified `Name@a/b` form when
/// several do (see [`crate::hir::qualify`]).
fn qualified_symbol(name: &str, module: &[String], counts: &HashMap<String, usize>) -> String {
    if counts.get(name).copied().unwrap_or(0) > 1 {
        crate::hir::qualify(name, module)
    } else {
        name.to_string()
    }
}

fn type_info(
    td: &TypeDecl,
    id: i32,
    module: &[String],
    symbol: String,
    errors: &mut Vec<LowerError>,
) -> TypeInfo {
    let kind = match &td.body {
        TypeBody::Record(members) => {
            let (fields, methods) = split_members(members, &td.name, errors);
            TypeKind::Record { fields, methods }
        }
        TypeBody::Sum(variants) => {
            let mut seen = HashSet::new();
            TypeKind::Sum {
                variants: variants
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        if !seen.insert(v.name.clone()) {
                            errors.push(LowerError {
                                message: format!("duplicate variant `{}.{}`", td.name, v.name),
                                span: v.span,
                            });
                        }
                        let owner = format!("{}.{}", td.name, v.name);
                        let (fields, methods) = split_members(&v.members, &owner, errors);
                        VariantInfo {
                            name: v.name.clone(),
                            tag: i as i32,
                            fields,
                            methods,
                        }
                    })
                    .collect(),
            }
        }
    };
    TypeInfo {
        name: td.name.clone(),
        id,
        interfaces: td.interfaces.clone(),
        kind,
        module: module.to_vec(),
        span: td.span,
        symbol,
    }
}

fn split_members(
    members: &[Member],
    owner: &str,
    errors: &mut Vec<LowerError>,
) -> (Vec<FieldInfo>, HashMap<String, MethodInfo>) {
    let mut fields = Vec::new();
    let mut methods = HashMap::new();
    let mut field_names = HashSet::new();
    let mut method_names = HashSet::new();
    for m in members {
        match m {
            Member::Field(f) => {
                if !field_names.insert(f.name.clone()) {
                    errors.push(LowerError {
                        message: format!("duplicate field `{owner}.{}`", f.name),
                        span: f.span,
                    });
                    continue;
                }
                fields.push(FieldInfo {
                    name: f.name.clone(),
                    ty: f.ty.clone(),
                    resolved_ty: None,
                });
            }
            Member::Method(mt) => {
                if !method_names.insert(mt.name.clone()) {
                    errors.push(LowerError {
                        message: format!("duplicate method `{owner}.{}`", mt.name),
                        span: mt.span,
                    });
                    continue;
                }
                methods.insert(
                    mt.name.clone(),
                    MethodInfo {
                        signature: CallableSignature::from_method(mt),
                        decl: Rc::new(mt.clone()),
                    },
                );
            }
        }
    }
    (fields, methods)
}

/// Built-in `Result = Ok { value } | Err { error }`.
fn result_type() -> TypeInfo {
    TypeInfo {
        name: "Result".into(),
        id: RESULT_TYPE_ID,
        interfaces: Vec::new(),
        kind: TypeKind::Sum {
            variants: vec![
                VariantInfo {
                    name: "Ok".into(),
                    tag: 0,
                    fields: vec![FieldInfo {
                        name: "value".into(),
                        ty: None,
                        resolved_ty: None,
                    }],
                    methods: HashMap::new(),
                },
                VariantInfo {
                    name: "Err".into(),
                    tag: 1,
                    fields: vec![FieldInfo {
                        name: "error".into(),
                        ty: None,
                        resolved_ty: None,
                    }],
                    methods: HashMap::new(),
                },
            ],
        },
        module: Vec::new(),
        span: Span::new(0, 0),
        symbol: "Result".into(),
    }
}

fn resolve_program_annotations(program: &mut Program) {
    let mut next_unknown = 0;
    // Nominal info keyed by each type's unique symbol (the type-table key).
    let nominal_by_symbol: HashMap<String, NominalInfo> = program
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
    let import_origins = program.import_origins.clone();
    // Resolve a bare type name to its nominal info from a given module: its own
    // bare/unique symbol, this module's qualified definition, or the imported
    // one. Captures only the snapshots above, so it does not borrow
    // `program` and can run while the type/function tables are mutated.
    let resolve_nominal = |module: &[String], name: &str| -> Option<NominalInfo> {
        crate::hir::resolve_qualified(&nominal_by_symbol, &import_origins, module, name).copied()
    };

    for info in program.types.values_mut() {
        let module = info.module.clone();
        let nominal = |name: &str| resolve_nominal(&module, name);
        match &mut info.kind {
            TypeKind::Record { fields, methods } => {
                fields
                    .iter_mut()
                    .for_each(|field| resolve_field_annotation(field, &nominal, &mut next_unknown));
                methods.values_mut().for_each(|method| {
                    let assign_ret_unknown = method.decl.body.is_none();
                    resolve_signature_annotations(
                        &mut method.signature,
                        &nominal,
                        &mut next_unknown,
                        true,
                        assign_ret_unknown,
                    )
                });
            }
            TypeKind::Sum { variants } => {
                for variant in variants {
                    variant.fields.iter_mut().for_each(|field| {
                        resolve_field_annotation(field, &nominal, &mut next_unknown)
                    });
                    variant.methods.values_mut().for_each(|method| {
                        let assign_ret_unknown = method.decl.body.is_none();
                        resolve_signature_annotations(
                            &mut method.signature,
                            &nominal,
                            &mut next_unknown,
                            true,
                            assign_ret_unknown,
                        )
                    });
                }
            }
        }
    }

    program.functions.values_mut().for_each(|fun| {
        let module = fun.module.clone();
        let nominal = |name: &str| resolve_nominal(&module, name);
        resolve_signature_annotations(
            &mut fun.signature,
            &nominal,
            &mut next_unknown,
            false,
            false,
        )
    });

    propagate_interface_field_constraints(program);
    propagate_interface_method_constraints(program);
}

fn resolve_field_annotation(
    field: &mut FieldInfo,
    nominal: &impl Fn(&str) -> Option<NominalInfo>,
    next_unknown: &mut u32,
) {
    field.resolved_ty = match &field.ty {
        Some(ty) => resolve(ty, nominal)
            .ok()
            .map(|t| crate::freshen_infer(t, &mut || fresh_unknown(next_unknown))),
        None => {
            let id = *next_unknown;
            *next_unknown += 1;
            Some(Type::Unknown(id))
        }
    };
}

fn resolve_signature_annotations(
    signature: &mut CallableSignature,
    nominal: &impl Fn(&str) -> Option<NominalInfo>,
    next_unknown: &mut u32,
    assign_param_unknowns: bool,
    assign_ret_unknown: bool,
) {
    for param in &mut signature.params {
        param.resolved_ty = match &param.ty {
            Some(ty) => resolve(ty, nominal)
                .ok()
                .map(|t| crate::freshen_infer(t, &mut || fresh_unknown(next_unknown))),
            None if assign_param_unknowns && param.name != "self" => {
                Some(fresh_unknown(next_unknown))
            }
            None => None,
        };
    }
    signature.ret_ty = match &signature.ret {
        Some(ty) => resolve(ty, nominal)
            .ok()
            .map(|t| crate::freshen_infer(t, &mut || fresh_unknown(next_unknown))),
        None if assign_ret_unknown => Some(fresh_unknown(next_unknown)),
        None => None,
    };
}

fn fresh_unknown(next_unknown: &mut u32) -> Type {
    let id = *next_unknown;
    *next_unknown += 1;
    Type::Unknown(id)
}

fn propagate_interface_field_constraints(program: &mut Program) {
    let interface_fields: HashMap<String, Vec<(String, Type)>> = program
        .types
        .iter()
        .filter_map(|(name, info)| match &info.kind {
            TypeKind::Record { fields, .. } => Some((
                name.clone(),
                fields
                    .iter()
                    .filter_map(|field| {
                        let ty = field.resolved_ty.clone()?;
                        (!ty.is_unknown()).then(|| (field.name.clone(), ty))
                    })
                    .collect(),
            )),
            TypeKind::Sum { .. } => None,
        })
        .collect();

    for info in program.types.values_mut() {
        let constraints = info
            .interfaces
            .iter()
            .filter_map(|name| interface_fields.get(name))
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        if constraints.is_empty() {
            continue;
        }
        match &mut info.kind {
            TypeKind::Record { fields, .. } => {
                apply_field_constraints(fields, &constraints);
            }
            TypeKind::Sum { variants } => {
                variants
                    .iter_mut()
                    .for_each(|variant| apply_field_constraints(&mut variant.fields, &constraints));
            }
        }
    }
}

fn apply_field_constraints(fields: &mut [FieldInfo], constraints: &[(String, Type)]) {
    for (name, ty) in constraints {
        if let Some(field) = fields.iter_mut().find(|field| field.name == *name)
            && field.resolved_ty.as_ref().is_some_and(Type::is_unknown)
        {
            field.resolved_ty = Some(ty.clone());
        }
    }
}

#[derive(Clone)]
struct MethodConstraint {
    name: String,
    params: Vec<(usize, Type)>,
    ret: Option<Type>,
}

fn propagate_interface_method_constraints(program: &mut Program) {
    let interface_methods: HashMap<String, Vec<MethodConstraint>> = program
        .types
        .iter()
        .filter_map(|(name, info)| match &info.kind {
            TypeKind::Record { methods, .. } => Some((
                name.clone(),
                methods
                    .values()
                    .map(|method| method_constraint(&method.signature))
                    .collect(),
            )),
            TypeKind::Sum { .. } => None,
        })
        .collect();

    for info in program.types.values_mut() {
        let constraints = info
            .interfaces
            .iter()
            .filter_map(|name| interface_methods.get(name))
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        if constraints.is_empty() {
            continue;
        }
        match &mut info.kind {
            TypeKind::Record { methods, .. } => apply_method_constraints(methods, &constraints),
            TypeKind::Sum { variants } => variants
                .iter_mut()
                .for_each(|variant| apply_method_constraints(&mut variant.methods, &constraints)),
        }
    }
}

fn method_constraint(signature: &CallableSignature) -> MethodConstraint {
    MethodConstraint {
        name: signature.name.clone(),
        params: signature
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, param)| {
                let ty = param.resolved_ty.clone()?;
                (!ty.is_unknown()).then_some((idx, ty))
            })
            .collect(),
        ret: signature.ret_ty.clone().filter(|ty| !ty.is_unknown()),
    }
}

fn apply_method_constraints(
    methods: &mut HashMap<String, MethodInfo>,
    constraints: &[MethodConstraint],
) {
    for constraint in constraints {
        let Some(method) = methods.get_mut(&constraint.name) else {
            continue;
        };
        for (idx, ty) in &constraint.params {
            if let Some(param) = method.signature.params.get_mut(*idx)
                && param.resolved_ty.as_ref().is_none_or(Type::is_unknown)
            {
                param.resolved_ty = Some(ty.clone());
            }
        }
        if let Some(ret) = &constraint.ret
            && method
                .signature
                .ret_ty
                .as_ref()
                .is_none_or(Type::is_unknown)
        {
            method.signature.ret_ty = Some(ret.clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use prepoly_parser::parse;

    use super::lower;
    use crate::{IntKind, LoadedModule, Type, TypeKind};

    fn lower_messages(src: &str) -> Vec<String> {
        let ast = parse(src).expect("parse");
        let (_, errors) = lower(&[LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        errors.into_iter().map(|e| e.message).collect()
    }

    fn lower_modules_messages(modules: &[(&[&str], &str)]) -> Vec<String> {
        let loaded: Vec<LoadedModule> = modules
            .iter()
            .map(|(path, src)| LoadedModule {
                path: path.iter().map(|s| s.to_string()).collect(),
                ast: parse(src).expect("parse"),
            })
            .collect();
        let (_, errors) = lower(&loaded);
        errors.into_iter().map(|e| e.message).collect()
    }

    #[test]
    fn same_name_in_one_module_is_a_plain_duplicate() {
        let errors = lower_messages(
            "fun helper() -> int32 { return 1 }\nfun helper() -> int32 { return 2 }\n",
        );
        assert!(
            errors.iter().any(|m| m == "duplicate function `helper`"),
            "{errors:?}"
        );
    }

    #[test]
    fn cross_module_same_function_name_coexists() {
        // The same function name defined in two different modules now
        // coexists with distinct module-qualified symbols rather than being a
        // lower-time duplicate. (Ambiguity is an error only when both are
        // imported into one module; see prepoly_resolve.)
        let modules: &[(&[&str], &str)] = &[
            (&["a", "util"], "fun helper() -> int32 { return 1 }\n"),
            (&["b", "util"], "fun helper() -> int32 { return 2 }\n"),
        ];
        let errors = lower_modules_messages(modules);
        assert!(errors.is_empty(), "expected coexistence, got {errors:?}");

        let loaded: Vec<LoadedModule> = modules
            .iter()
            .map(|(path, src)| LoadedModule {
                path: path.iter().map(|s| s.to_string()).collect(),
                ast: parse(src).expect("parse"),
            })
            .collect();
        let (program, _) = lower(&loaded);
        assert!(
            program.functions.contains_key("helper@a/util"),
            "a.util helper symbol"
        );
        assert!(
            program.functions.contains_key("helper@b/util"),
            "b.util helper symbol"
        );
    }

    fn lower_program(modules: &[(&[&str], &str)]) -> crate::Program {
        let loaded: Vec<LoadedModule> = modules
            .iter()
            .map(|(path, src)| LoadedModule {
                path: path.iter().map(|s| s.to_string()).collect(),
                ast: parse(src).expect("parse"),
            })
            .collect();
        let (program, errors) = lower(&loaded);
        assert!(errors.is_empty(), "lower errors: {errors:?}");
        program
    }

    #[test]
    fn qualified_name_symbol_is_name_at_slash_path() {
        let q = crate::QualifiedName::new("helper", &["a".into(), "util".into()]);
        assert_eq!(q.symbol(), "helper@a/util");
        assert_eq!(q.to_string(), "helper@a/util");
    }

    #[test]
    fn resolve_function_follows_imports_to_the_right_module() {
        // `helper` is defined in two modules, so it has module-qualified symbols.
        // From `main`, which imports it from `a.util`, the bare name must resolve
        // to a.util's definition (not b.util's) -- the central resolver drives
        // both the typed `resolve_function` and the `resolve_fn_symbol` shim.
        let program = lower_program(&[
            (&["a", "util"], "fun helper() -> int32 { return 1 }\n"),
            (&["b", "util"], "fun helper() -> int32 { return 2 }\n"),
            (
                &["main"],
                "import a.util.{ helper }\nfun run() -> int32 { return helper() }\n",
            ),
        ]);
        let main = vec!["main".to_string()];
        assert_eq!(
            program.resolve_function(&main, "helper").map(|f| &f.symbol),
            Some(&"helper@a/util".to_string()),
        );
        assert_eq!(
            program.resolve_fn_symbol(&main, "helper").as_deref(),
            Some("helper@a/util"),
        );
    }

    #[test]
    fn resolve_function_finds_the_callers_own_module_definition() {
        let program = lower_program(&[
            (&["a", "util"], "fun helper() -> int32 { return 1 }\n"),
            (&["b", "util"], "fun helper() -> int32 { return 2 }\n"),
        ]);
        let b = vec!["b".to_string(), "util".to_string()];
        assert_eq!(
            program.resolve_function(&b, "helper").map(|f| &f.symbol),
            Some(&"helper@b/util".to_string()),
        );
    }

    #[test]
    fn resolve_type_follows_imports() {
        // Same-named type in two modules -> qualified symbols; the import decides
        // which one a bare annotation in `main` resolves to.
        let program = lower_program(&[
            (&["geo"], "type Vec2 = { x: float64 }\n"),
            (&["phys"], "type Vec2 = { vx: float64 }\n"),
            (&["main"], "import geo.{ Vec2 }\n"),
        ]);
        let main = vec!["main".to_string()];
        assert_eq!(
            program.resolve_type(&main, "Vec2").map(|t| &t.symbol),
            Some(&"Vec2@geo".to_string()),
        );
    }

    #[test]
    fn duplicate_record_field_is_reported() {
        let errors = lower_messages("type Point = {\n    x: int32\n    x: int32\n}\n");
        assert!(
            errors
                .iter()
                .any(|m| m.contains("duplicate field `Point.x`")),
            "{errors:?}"
        );
    }

    #[test]
    fn duplicate_record_method_is_reported() {
        let errors =
            lower_messages("type Counter = {\n    get() { return 1 }\n    get() { return 2 }\n}\n");
        assert!(
            errors
                .iter()
                .any(|m| m.contains("duplicate method `Counter.get`")),
            "{errors:?}"
        );
    }

    #[test]
    fn duplicate_sum_variant_is_reported() {
        let errors = lower_messages("type Color = Red | Red\n");
        assert!(
            errors
                .iter()
                .any(|m| m.contains("duplicate variant `Color.Red`")),
            "{errors:?}"
        );
    }

    #[test]
    fn duplicate_variant_member_is_reported() {
        let errors = lower_messages(
            "type Shape =\n    | Circle {\n        radius: float64\n        radius: float64\n    }\n",
        );
        assert!(
            errors
                .iter()
                .any(|m| m.contains("duplicate field `Shape.Circle.radius`")),
            "{errors:?}"
        );
    }

    #[test]
    fn lowers_signatures_and_annotations_into_hir() {
        let ast = parse(
            "type Wrapper = {\n    inner: Box\n}\ntype Box = {\n    value: int32\n    get(self) -> int32 { return self.value }\n}\nfun id(x: Box) -> int32 { return x.value }\n",
        )
        .expect("parse");
        let (program, errors) = lower(&[LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty(), "{errors:?}");

        let box_id = program.types.get("Box").expect("type lowered").id;
        let fun = program.functions.get("id").expect("function lowered");
        assert_eq!(fun.signature.name, "id");
        assert_eq!(fun.signature.params[0].name, "x");
        assert_eq!(
            fun.signature.params[0].resolved_ty,
            Some(Type::Record(
                program.types.get("Box").unwrap().nominal_ref()
            ))
        );
        assert!(fun.signature.ret.is_some());
        assert_eq!(fun.signature.ret_ty, Some(Type::Int(IntKind::I32)));

        let box_ty = program.types.get("Box").expect("type lowered");
        let TypeKind::Record { methods, .. } = &box_ty.kind else {
            panic!("Box should be a record");
        };
        let method = methods.get("get").expect("method lowered");
        assert_eq!(method.signature.name, "get");
        assert_eq!(method.signature.params[0].name, "self");
        assert!(method.signature.ret.is_some());
        assert_eq!(method.signature.ret_ty, Some(Type::Int(IntKind::I32)));

        let wrapper_ty = program.types.get("Wrapper").expect("type lowered");
        let TypeKind::Record { fields, .. } = &wrapper_ty.kind else {
            panic!("Wrapper should be a record");
        };
        assert_eq!(
            fields[0].resolved_ty,
            Some(Type::Record(box_ty.nominal_ref()))
        );
        assert_eq!(
            fields[0].resolved_ty.as_ref().and_then(|ty| match ty {
                Type::Record(nominal) => Some(nominal.id),
                _ => None,
            }),
            Some(box_id)
        );
    }

    #[test]
    fn assigns_stable_unknowns_to_unannotated_type_fields() {
        let ast = parse(
            "type Box = {\n    value\n    label\n}\ntype Pair =\n    | Both { left, right }\n",
        )
        .expect("parse");
        let (program, errors) = lower(&[LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty(), "{errors:?}");

        let box_ty = program.types.get("Box").expect("record lowered");
        let TypeKind::Record { fields, .. } = &box_ty.kind else {
            panic!("Box should be a record");
        };
        // Each declaration field owns a stable inference variable in HIR.
        assert!(matches!(fields[0].resolved_ty, Some(Type::Unknown(_))));
        assert!(matches!(fields[1].resolved_ty, Some(Type::Unknown(_))));
        assert_ne!(fields[0].resolved_ty, fields[1].resolved_ty);

        let pair_ty = program.types.get("Pair").expect("sum lowered");
        let TypeKind::Sum { variants } = &pair_ty.kind else {
            panic!("Pair should be a sum");
        };
        let both = variants
            .iter()
            .find(|variant| variant.name == "Both")
            .unwrap();
        assert!(matches!(both.fields[0].resolved_ty, Some(Type::Unknown(_))));
        assert!(matches!(both.fields[1].resolved_ty, Some(Type::Unknown(_))));
        assert_ne!(both.fields[0].resolved_ty, both.fields[1].resolved_ty);
    }

    #[test]
    fn propagates_concrete_interface_field_constraints() {
        let ast = parse(
            "type Named = {\n    name: string\n}\ntype User: Named = {\n    name\n}\ntype Pet: Named =\n    | Cat { name }\n    | Dog { name }\n",
        )
        .expect("parse");
        let (program, errors) = lower(&[LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty(), "{errors:?}");

        let user = program.types.get("User").expect("record lowered");
        let TypeKind::Record { fields, .. } = &user.kind else {
            panic!("User should be a record");
        };
        assert_eq!(fields[0].resolved_ty, Some(Type::Str));

        let pet = program.types.get("Pet").expect("sum lowered");
        let TypeKind::Sum { variants } = &pet.kind else {
            panic!("Pet should be a sum");
        };
        // Every variant must receive the interface's concrete field constraint.
        assert!(
            variants
                .iter()
                .all(|variant| variant.fields[0].resolved_ty == Some(Type::Str))
        );
    }

    #[test]
    fn assigns_stable_unknowns_to_unannotated_interface_method_signatures() {
        let ast = parse("type Consumer = {\n    consume(self, value)\n}\n").expect("parse");
        let (program, errors) = lower(&[LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty(), "{errors:?}");

        let consumer = program.types.get("Consumer").expect("record lowered");
        let TypeKind::Record { methods, .. } = &consumer.kind else {
            panic!("Consumer should be a record");
        };
        let method = methods.get("consume").expect("method lowered");
        // `self` is still supplied by the receiver, while interface-only data
        // parameters and returns receive stable unknowns for later substitution.
        assert_eq!(method.signature.params[0].name, "self");
        assert!(method.signature.params[0].resolved_ty.is_none());
        assert!(matches!(
            method.signature.params[1].resolved_ty,
            Some(Type::Unknown(_))
        ));
        assert!(matches!(method.signature.ret_ty, Some(Type::Unknown(_))));
        assert_ne!(
            method.signature.params[1].resolved_ty,
            method.signature.ret_ty
        );
    }

    #[test]
    fn assigns_stable_unknowns_to_unannotated_method_body_params() {
        let ast = parse(
            "type Box = {\n    value\n    set(self, value) {\n        self.value = value\n    }\n    make(value) {\n        return Self { value: value }\n    }\n}\n",
        )
        .expect("parse");
        let (program, errors) = lower(&[LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty(), "{errors:?}");

        let box_ty = program.types.get("Box").expect("record lowered");
        let TypeKind::Record { fields, methods } = &box_ty.kind else {
            panic!("Box should be a record");
        };
        let field_ty = fields[0].resolved_ty.clone();
        let set = methods.get("set").expect("instance method lowered");
        let make = methods.get("make").expect("static method lowered");

        // Method body parameters own stable HIR unknowns; body return types
        // remain inferred from the body unless the source declares `-> T`.
        assert!(matches!(field_ty, Some(Type::Unknown(_))));
        assert!(matches!(
            set.signature.params[1].resolved_ty,
            Some(Type::Unknown(_))
        ));
        assert!(matches!(
            make.signature.params[0].resolved_ty,
            Some(Type::Unknown(_))
        ));
        assert_ne!(field_ty, set.signature.params[1].resolved_ty);
        assert_ne!(
            set.signature.params[1].resolved_ty,
            make.signature.params[0].resolved_ty
        );
        assert!(set.signature.ret_ty.is_none());
        assert!(make.signature.ret_ty.is_none());
    }

    #[test]
    fn propagates_concrete_interface_method_constraints() {
        let ast = parse(
            "type Setter = {\n    set(self, value: string) -> string\n}\ntype User: Setter = {\n    set(self, value) { return value }\n}\n",
        )
        .expect("parse");
        let (program, errors) = lower(&[LoadedModule {
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty(), "{errors:?}");

        let user = program.types.get("User").expect("record lowered");
        let TypeKind::Record { methods, .. } = &user.kind else {
            panic!("User should be a record");
        };
        let method = methods.get("set").expect("method lowered");
        assert_eq!(method.signature.params[1].resolved_ty, Some(Type::Str));
        assert_eq!(method.signature.ret_ty, Some(Type::Str));
    }
}
