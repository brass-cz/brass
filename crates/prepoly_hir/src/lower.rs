//! Lowering: collect AST modules into the HIR `Program`, assigning runtime
//! type ids (Result is fixed at id 0) and variant tags, and gathering each
//! module's top-level statements for initialization.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use prepoly_parser::Span;
use prepoly_parser::ast::{Member, TopLevel, TypeBody, TypeDecl};

use crate::hir::*;
use crate::types::{NominalInfo, Type};

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
    let mut import_renames: HashMap<Vec<String>, HashMap<String, String>> = HashMap::new();
    let mut module_aliases: HashMap<Vec<String>, HashMap<String, Vec<String>>> = HashMap::new();
    let mut errors = Vec::new();
    let mut next_id: i32 = 1; // 0 is reserved for Result
    // `fun T.m(...)` method implementations, resolved to their receiver type
    // after every type is collected (so a method may precede its type's `type`
    // declaration, and the same-module rule can be enforced).
    let mut method_impls: Vec<(Rc<prepoly_parser::ast::FunDecl>, Vec<String>)> = Vec::new();
    // `type Alias = <type expr>` declarations, resolved after all nominal types
    // are collected (an alias may refine a type declared anywhere).
    let mut alias_decls: Vec<(String, Vec<String>, TypeDecl)> = Vec::new();

    // How many modules define each top-level function/type name. A name defined
    // in a single module keeps its bare symbol (so all existing bare-name lookups
    // and codegen symbols are unchanged); a name defined in several modules is
    // qualified per module so the definitions coexist.
    // Only free functions compete for a bare storage symbol. A method
    // implementation `fun T.m(...)` is keyed by its receiver type, not by `m`, so
    // it neither inflates the free-function name count nor clashes with a free
    // function of the same name.
    let fn_name_modules = name_module_counts(modules, |item| match item {
        TopLevel::Fun(f) if f.recv.is_none() => Some(&f.name),
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
            imported.extend(imp.names.iter().map(|n| n.local.clone()));
        }
        let origins = import_origins.entry(m.path.clone()).or_default();
        let renames = import_renames.entry(m.path.clone()).or_default();
        let aliases = module_aliases.entry(m.path.clone()).or_default();
        for imp in &m.ast.imports {
            if let Some(alias) = &imp.alias {
                aliases
                    .entry(alias.clone())
                    .or_insert_with(|| imp.path.clone());
            }
        }
        for imp in &m.ast.imports {
            for name in &imp.names {
                origins
                    .entry(name.local.clone())
                    .or_insert_with(|| imp.path.clone());
                if name.local != name.remote {
                    renames
                        .entry(name.local.clone())
                        .or_insert_with(|| name.remote.clone());
                }
            }
        }
        let mut stmts = Vec::new();
        for item in &m.ast.items {
            match item {
                TopLevel::Type(td) => {
                    // `Result` is the type behind the fallibility sugar (`T!`,
                    // `error(..)`, Ok-wrapping, `!`). The prelude's declaration
                    // (std/prelude/error.pp) is pinned to RESULT_TYPE_ID under
                    // the bare `Result` symbol so every construct that builds a
                    // Result by default finds the same nominal. A user's `type
                    // Result` is an ordinary declaration that shadows it in the
                    // declaring module's scope; it always takes the qualified
                    // symbol so it never competes for the prelude's bare key
                    // (the sugar's fallback), even in a program without the
                    // prelude.
                    if td.name == "Result" && m.is_prelude {
                        if types.contains_key(&td.name) {
                            errors.push(LowerError {
                                message: "duplicate type `Result`".to_string(),
                                span: td.span,
                            });
                            continue;
                        }
                        let info =
                            type_info(td, RESULT_TYPE_ID, &m.path, td.name.clone(), &mut errors);
                        validate_prelude_result(&info, td.span, &mut errors);
                        types.insert(td.name.clone(), info);
                        continue;
                    }
                    let symbol = if td.name == "Result" {
                        crate::hir::qualify(&td.name, &m.path)
                    } else {
                        qualified_symbol(&td.name, &m.path, &type_name_modules)
                    };
                    // Same symbol => same name twice in one module (a genuine
                    // duplicate). A different module yields a different symbol,
                    // so cross-module same-named types coexist.
                    if types.contains_key(&symbol)
                        || alias_decls.iter().any(|(s, _, _)| *s == symbol)
                    {
                        errors.push(LowerError {
                            message: format!("duplicate type `{}`", td.name),
                            span: td.span,
                        });
                        continue;
                    }
                    // An alias (`type X = <type expr>`) is not a nominal of its
                    // own; defer it until every nominal type is known so its
                    // refinement base resolves.
                    if matches!(td.body, TypeBody::Alias(_)) {
                        alias_decls.push((symbol, m.path.clone(), td.clone()));
                        continue;
                    }
                    let info = type_info(td, next_id, &m.path, symbol.clone(), &mut errors);
                    next_id += 1;
                    types.insert(symbol, info);
                }
                TopLevel::Fun(f) if f.recv.is_some() => {
                    // A method implementation: deferred until all types are known.
                    method_impls.push((Rc::new(f.clone()), m.path.clone()));
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

    // Programs assembled without the prelude (unit tests, embedders) still
    // need Result -- every fallibility construct references it. Fall back to
    // the built-in declaration when no prelude module provided one.
    types
        .entry("Result".to_string())
        .or_insert_with(result_type);

    let mut primitive_methods: HashMap<(String, String), String> = HashMap::new();
    inject_method_impls(
        &method_impls,
        &mut types,
        &mut functions,
        &mut primitive_methods,
        &mut errors,
    );

    // Build reverse-alias table: for items stored under their bare name
    // (unique program-wide), record qualify(name, module) -> bare_name so
    // marker-based resolution can reach them.
    let mut symbol_aliases: HashMap<String, String> = HashMap::new();
    for (symbol, info) in &types {
        if symbol == &info.name && !info.module.is_empty() {
            let qualified = crate::hir::qualify(&info.name, &info.module);
            if qualified != *symbol {
                symbol_aliases.insert(qualified, symbol.clone());
            }
        }
    }
    for (symbol, info) in &functions {
        let bare_name = &info.signature.name;
        if symbol == bare_name && !info.module.is_empty() {
            let qualified = crate::hir::qualify(bare_name, &info.module);
            if qualified != *symbol {
                symbol_aliases.insert(qualified, symbol.clone());
            }
        }
    }

    let mut program = Program {
        types,
        functions,
        inits,
        prelude_modules: modules
            .iter()
            .filter(|m| m.is_prelude)
            .map(|m| m.path.clone())
            .collect(),
        module_imports,
        import_origins,
        import_renames,
        module_aliases,
        symbol_aliases,
        primitive_methods,
        type_aliases: HashMap::new(),
        next_infer_var: 0,
    };
    resolve_program_annotations(&mut program, &alias_decls, &mut errors);

    (program, errors)
}

/// Attach each `fun T.m(...)` method implementation to its receiver type.
///
/// A method on a nominal user type is injected into that type's method table, so
/// it is indistinguishable downstream from a method that was written inside the
/// type body -- it dispatches, type-checks, and lowers through the same paths and
/// is available wherever the type is in scope, with no separate import. The
/// implementation must live in the same module that declares the type.
///
/// A method on a primitive or array receiver (`fun string.split`, `fun infer[].map`)
/// is the standard library's privilege only: its body is stored as an ordinary
/// function under a receiver-qualified symbol (so it never clashes with a free
/// function or another class's method of the same name) and recorded in
/// `primitive_methods` for dispatch. The receiver's `self` parameter is annotated
/// with the receiver type so the body type-checks against it.
fn inject_method_impls(
    method_impls: &[(Rc<prepoly_parser::ast::FunDecl>, Vec<String>)],
    types: &mut HashMap<String, TypeInfo>,
    functions: &mut HashMap<String, FunInfo>,
    primitive_methods: &mut HashMap<(String, String), String>,
    errors: &mut Vec<LowerError>,
) {
    use prepoly_parser::ast::{FunDecl, Method, TypeExpr};
    for (f, module) in method_impls {
        let recv = f.recv.as_ref().expect("method impl has a receiver");
        // Classify the receiver: an array `T[]`, a primitive scalar word, or a
        // nominal user type named in this module.
        let (recv_name, is_array) = match recv {
            TypeExpr::Named(n, _) => (n.as_str(), false),
            TypeExpr::Array(inner, None, _) => match inner.as_ref() {
                TypeExpr::Named(n, _) => (n.as_str(), true),
                _ => {
                    errors.push(LowerError {
                        message: "method receiver array element must be a type name".to_string(),
                        span: f.span,
                    });
                    continue;
                }
            },
            _ => {
                errors.push(LowerError {
                    message: "unsupported method receiver type".to_string(),
                    span: f.span,
                });
                continue;
            }
        };

        if let Some(class) = Type::primitive_class_of_name(recv_name, is_array) {
            // Methods on primitive types are reserved to the standard library.
            if module.first().map(String::as_str) != Some("std") {
                errors.push(LowerError {
                    message: format!(
                        "methods on the primitive type `{recv_name}` can only be defined in the standard library"
                    ),
                    span: f.span,
                });
                continue;
            }
            // Annotate the leading `self` with the receiver type so the body
            // type-checks against the concrete primitive/array.
            let mut params = f.params.clone();
            if let Some(first) = params.first_mut()
                && first.name == "self"
                && first.ty.is_none()
            {
                first.ty = Some(recv.clone());
            }
            let symbol = crate::types::prim_method_symbol(class, &f.name);
            let key = (class.to_string(), f.name.clone());
            if primitive_methods.contains_key(&key) {
                errors.push(LowerError {
                    message: format!("duplicate method `{}` on `{recv_name}`", f.name),
                    span: f.span,
                });
                continue;
            }
            let decl = FunDecl {
                name: f.name.clone(),
                recv: f.recv.clone(),
                params,
                ret: f.ret.clone(),
                body: f.body.clone(),
                span: f.span,
                doc: f.doc.clone(),
            };
            functions.insert(
                symbol.clone(),
                FunInfo {
                    signature: CallableSignature::from_function(&decl),
                    decl: Rc::new(decl),
                    module: module.clone(),
                    symbol: symbol.clone(),
                },
            );
            primitive_methods.insert(key, symbol);
            continue;
        }

        // Nominal receiver: find the type of this name declared in this module.
        let target = types
            .iter()
            .find(|(_, info)| info.name == recv_name && &info.module == module)
            .map(|(symbol, _)| symbol.clone());
        let Some(symbol) = target else {
            // The type exists elsewhere (wrong module) or not at all.
            let exists_elsewhere = types.values().any(|info| info.name == recv_name);
            errors.push(LowerError {
                message: if exists_elsewhere {
                    format!(
                        "method `{}` on `{recv_name}` must be defined in the module that declares `{recv_name}`",
                        f.name
                    )
                } else {
                    format!("unknown type `{recv_name}` for method `{}`", f.name)
                },
                span: f.span,
            });
            continue;
        };
        let method = Method {
            name: f.name.clone(),
            params: f.params.clone(),
            ret: f.ret.clone(),
            body: Some(f.body.clone()),
            span: f.span,
            doc: f.doc.clone(),
        };
        let info = types.get_mut(&symbol).expect("symbol just resolved");
        inject_nominal_method(info, method, errors);
    }
}

/// Insert `method` into `info`'s method table(s). A record type takes the method
/// directly; a sum type takes it into every variant (a `recv.m()` call requires
/// every variant to provide `m`, so the body is shared across them). An existing
/// method of the same name with a body is a genuine duplicate; a body-less
/// signature (an interface requirement the type restated) is filled in.
fn inject_nominal_method(
    info: &mut TypeInfo,
    method: prepoly_parser::ast::Method,
    errors: &mut Vec<LowerError>,
) {
    let span = method.span;
    let name = method.name.clone();
    let type_name = info.name.clone();
    let method_info = MethodInfo {
        signature: CallableSignature::from_method(&method),
        decl: Rc::new(method),
    };
    let insert = |methods: &mut HashMap<String, MethodInfo>, errors: &mut Vec<LowerError>| {
        if methods.get(&name).is_some_and(|m| m.decl.body.is_some()) {
            errors.push(LowerError {
                message: format!("duplicate method `{type_name}.{name}`"),
                span,
            });
        } else {
            methods.insert(name.clone(), method_info.clone());
        }
    };
    match &mut info.kind {
        TypeKind::Record { methods, .. } => insert(methods, errors),
        TypeKind::Sum { variants } => {
            for v in variants {
                insert(&mut v.methods, errors);
            }
        }
    }
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
    let mut slots = Vec::new();
    let kind = match &td.body {
        TypeBody::Record(members) => {
            let (fields, methods, slot_names) = split_members(members, &td.name, errors);
            slots = slot_names.into_iter().map(|n| (n, 0u32)).collect();
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
                        let (fields, methods, sslots) = split_members(&v.members, &owner, errors);
                        if !sslots.is_empty() {
                            errors.push(LowerError {
                                message: format!(
                                    "a sum variant `{owner}` cannot declare a `type` slot"
                                ),
                                span: v.span,
                            });
                        }
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
        // Aliases are diverted before `type_info`; this arm is never reached.
        TypeBody::Alias(_) => unreachable!("alias declarations do not build a TypeInfo"),
    };
    TypeInfo {
        name: td.name.clone(),
        id,
        interfaces: td.interfaces.clone(),
        kind,
        module: module.to_vec(),
        span: td.span,
        symbol,
        slots,
        doc: td.doc.clone(),
    }
}

fn split_members(
    members: &[Member],
    owner: &str,
    errors: &mut Vec<LowerError>,
) -> (Vec<FieldInfo>, HashMap<String, MethodInfo>, Vec<String>) {
    let mut fields = Vec::new();
    let mut methods = HashMap::new();
    let mut slots = Vec::new();
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
                // A `slot: type` field is a type parameter, not a value field: it
                // is recorded as a slot (no runtime storage) rather than in
                // `fields`, so it is excluded from layout, construction, and
                // reflection automatically.
                if matches!(f.ty, Some(prepoly_parser::ast::TypeExpr::TypeSlot(_))) {
                    slots.push(f.name.clone());
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
    (fields, methods, slots)
}

/// The prelude's `Result` declaration is load-bearing: every fallibility
/// construct assumes exactly `| Ok { value } | Err { error }` (tags 0/1,
/// generic unannotated payload fields, no slots). Reject any drift in
/// std/prelude/error.pp loudly instead of letting the sugar misbehave.
fn validate_prelude_result(info: &TypeInfo, span: Span, errors: &mut Vec<LowerError>) {
    let shape_ok = match &info.kind {
        TypeKind::Sum { variants } => {
            variants.len() == 2
                && variants[0].name == "Ok"
                && variants[0].fields.len() == 1
                && variants[0].fields[0].name == "value"
                && variants[0].fields[0].ty.is_none()
                && variants[1].name == "Err"
                && variants[1].fields.len() == 1
                && variants[1].fields[0].name == "error"
                && variants[1].fields[0].ty.is_none()
                && info.slots.is_empty()
        }
        TypeKind::Record { .. } => false,
    };
    if !shape_ok {
        errors.push(LowerError {
            message: "the prelude `Result` must be declared as `| Ok { value } | Err { error }`"
                .to_string(),
            span,
        });
    }
}

/// Built-in `Result = Ok { value } | Err { error }`, used when no prelude
/// module declares it (std/prelude/error.pp is the normal source).
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
        slots: Vec::new(),
        doc: None,
    }
}

fn resolve_program_annotations(
    program: &mut Program,
    alias_decls: &[(String, Vec<String>, TypeDecl)],
    errors: &mut Vec<LowerError>,
) {
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
    let import_renames_snap = program.import_renames.clone();
    // Resolve a bare type name to its nominal info from a given module: its own
    // bare/unique symbol, this module's qualified definition, or the imported
    // one. Captures only the snapshots above, so it does not borrow
    // `program` and can run while the type/function tables are mutated.
    let resolve_nominal = |module: &[String], name: &str| -> Option<NominalInfo> {
        crate::hir::resolve_qualified(
            &nominal_by_symbol,
            &import_origins,
            &import_renames_snap,
            module,
            name,
        )
        .copied()
    };

    // Records carry type slots, `Self.field` references, and refinements: resolve
    // their fields (and the `type Alias = ..` declarations) with the slot-aware
    // resolver, which also fills each record's slot variables. It shares
    // `next_unknown` so its variables do not collide with the ones below.
    crate::typedecl::resolve_type_decls(
        program,
        alias_decls,
        &nominal_by_symbol,
        &mut next_unknown,
        errors,
    );

    // Sum variant fields may name a `type Alias = ..` (a concrete refinement
    // like json's `_JsonObject`); resolve such names through the alias table
    // `resolve_type_decls` just filled, so the field's declared type reaches
    // the back ends -- a bare sum crossing a function boundary has no
    // construction substitution to fall back on.
    let alias_types: HashMap<String, Type> = program
        .type_aliases
        .iter()
        .map(|(k, a)| (k.clone(), a.ty.clone()))
        .collect();
    for info in program.types.values_mut() {
        let module = info.module.clone();
        let nominal = |name: &str| resolve_nominal(&module, name);
        let alias = |name: &str| -> Option<Type> {
            crate::hir::resolve_qualified(
                &alias_types,
                &import_origins,
                &import_renames_snap,
                &module,
                name,
            )
            .cloned()
        };
        match &mut info.kind {
            // Record fields are resolved by `resolve_type_decls` above; only the
            // method signatures remain.
            TypeKind::Record { methods, .. } => {
                methods.values_mut().for_each(|method| {
                    let assign_ret_unknown = method.decl.body.is_none();
                    resolve_signature_annotations(
                        &mut method.signature,
                        &nominal,
                        &alias,
                        &mut next_unknown,
                        true,
                        assign_ret_unknown,
                    )
                });
            }
            TypeKind::Sum { variants } => {
                for variant in variants {
                    variant.fields.iter_mut().for_each(|field| {
                        resolve_variant_field_annotation(field, &nominal, &alias, &mut next_unknown)
                    });
                    variant.methods.values_mut().for_each(|method| {
                        let assign_ret_unknown = method.decl.body.is_none();
                        resolve_signature_annotations(
                            &mut method.signature,
                            &nominal,
                            &alias,
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
        let alias = |name: &str| -> Option<Type> {
            crate::hir::resolve_qualified(
                &alias_types,
                &import_origins,
                &import_renames_snap,
                &module,
                name,
            )
            .cloned()
        };
        resolve_signature_annotations(
            &mut fun.signature,
            &nominal,
            &alias,
            &mut next_unknown,
            false,
            false,
        )
    });

    propagate_interface_field_constraints(program);
    propagate_interface_method_constraints(program);
    // Publish the counter so every downstream solver can seed past the ids
    // now embedded in the program's types (see `Program::next_infer_var`).
    program.next_infer_var = next_unknown;
}

/// Resolve a sum variant field's declared type. The annotation may name a
/// `type Alias = ..` (see the alias snapshot at the call site); an
/// unannotated field is a free type parameter.
fn resolve_variant_field_annotation(
    field: &mut FieldInfo,
    nominal: &impl Fn(&str) -> Option<NominalInfo>,
    alias: &impl Fn(&str) -> Option<Type>,
    next_unknown: &mut u32,
) {
    field.resolved_ty = match &field.ty {
        Some(ty) => crate::types::resolve_with_aliases(ty, nominal, alias)
            .ok()
            .map(|t| crate::freshen_infer(t, &mut || fresh_unknown(next_unknown))),
        None => {
            let id = *next_unknown;
            *next_unknown += 1;
            Some(Type::Unknown(id))
        }
    };
}

/// Resolve a callable's declared parameter and return annotations. Aliases are
/// consulted like they are for a sum variant's fields: an annotation naming a
/// `type Alias = Base { .. }` refinement (`_TomlTable`) must resolve to the
/// alias's substituted type. Without that, `resolve` failed as an unknown name
/// and the annotation was dropped -- a parameter so annotated read back as
/// `void` at every use, and a declared `-> Alias!` lost its `!`, so the caller's
/// error propagation had no `Result` to unwrap.
fn resolve_signature_annotations(
    signature: &mut CallableSignature,
    nominal: &impl Fn(&str) -> Option<NominalInfo>,
    alias: &impl Fn(&str) -> Option<Type>,
    next_unknown: &mut u32,
    assign_param_unknowns: bool,
    assign_ret_unknown: bool,
) {
    for param in &mut signature.params {
        param.resolved_ty = match &param.ty {
            Some(ty) => crate::types::resolve_with_aliases(ty, nominal, alias)
                .ok()
                .map(|t| crate::freshen_infer(t, &mut || fresh_unknown(next_unknown))),
            None if assign_param_unknowns && param.name != "self" => {
                Some(fresh_unknown(next_unknown))
            }
            None => None,
        };
    }
    signature.ret_ty = match &signature.ret {
        Some(ty) => crate::types::resolve_with_aliases(ty, nominal, alias)
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
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        errors.into_iter().map(|e| e.message).collect()
    }

    fn lower_modules_messages(modules: &[(&[&str], &str)]) -> Vec<String> {
        let loaded: Vec<LoadedModule> = modules
            .iter()
            .map(|(path, src)| LoadedModule {
                is_prelude: false,
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
                is_prelude: false,
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
                is_prelude: false,
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
    fn type_slots_are_kept_out_of_the_value_fields() {
        // `key`/`value: type` are slots (type parameters), not value fields; a
        // real field expresses its type over them with `Self.slot`.
        let program = lower_program(&[(
            &["main"],
            "type _E = {\n key\n value\n }\n\
             type Box = {\n key: type\n value: type\n \
             arr: _E { key: Self.key, value: Self.value }?[]\n n: int64\n }\n",
        )]);
        let info = program.types.get("Box").expect("Box exists");
        let TypeKind::Record { fields, .. } = &info.kind else {
            panic!("Box is a record");
        };
        let field_names: Vec<&str> = fields.iter().map(|f| f.name.as_str()).collect();
        assert_eq!(field_names, vec!["arr", "n"]);
        let slot_names: Vec<&str> = info.slots.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(slot_names, vec!["key", "value"]);
    }

    #[test]
    fn self_field_cycle_is_rejected() {
        // `a` refers to `b`'s type and `b` back to `a`'s: a circular unification,
        // rejected by the occurs-check.
        let errors = lower_messages("type Loop = {\n a: Self.b\n b: Self.a\n n: int64\n }\n");
        assert!(
            errors.iter().any(|m| m.contains("circular type")),
            "{errors:?}"
        );
    }

    #[test]
    fn refinement_alias_is_a_concrete_instance() {
        // `type IntBox = Box { key: string, value: int64 }` pins Box's slots and
        // resolves to a Box instance whose substitution covers every real field.
        let program = lower_program(&[(
            &["main"],
            "type Box = {\n key: type\n value: type\n n: int64\n }\n\
             type IntBox = Box { key: string, value: int64 }\n",
        )]);
        let alias = program.type_aliases.get("IntBox").expect("IntBox alias");
        let Type::Record(nom) = &alias.ty else {
            panic!("alias resolves to a record instance, got {:?}", alias.ty);
        };
        assert_eq!(nom.name, "Box");
        assert_eq!(nom.substitution.get("n"), Some(&Type::Int(IntKind::I64)));
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
        let errors = lower_messages(
            "type Counter = {\n    n: int32\n}\nfun Counter.get() { return 1 }\nfun Counter.get() { return 2 }\n",
        );
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
            "type Wrapper = {\n    inner: Box\n}\ntype Box = {\n    value: int32\n}\nfun Box.get(self) -> int32 { return self.value }\nfun id(x: Box) -> int32 { return x.value }\n",
        )
        .expect("parse");
        let (program, errors) = lower(&[LoadedModule {
            is_prelude: false,
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
            is_prelude: false,
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
            is_prelude: false,
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
            is_prelude: false,
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
            "type Box = {\n    value\n}\nfun Box.set(self, value) {\n    self.value = value\n}\nfun Box.make(value) {\n    return Self { value: value }\n}\n",
        )
        .expect("parse");
        let (program, errors) = lower(&[LoadedModule {
            is_prelude: false,
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
            "type Setter = {\n    set(self, value: string) -> string\n}\ntype User: Setter = {\n    name: string\n}\nfun User.set(self, value) { return value }\n",
        )
        .expect("parse");
        let (program, errors) = lower(&[LoadedModule {
            is_prelude: false,
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
