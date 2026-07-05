//! Resolution of record type declarations that use type SLOTS, `Self.field`
//! references, and `Base { .. }` refinements.
//!
//! A record may declare type parameters as `slot: type` fields (see
//! [`TypeInfo::slots`]). Each slot is given an inference variable; another
//! field expresses its type over the slots with `Self.slot`
//! (`entries: _Entry { key: Self.key }?[]`). A refinement -- an inline
//! `Base { field: T }` or the right-hand side of a `type Alias = Base { .. }`
//! -- fills those variables, yielding a concrete instance.
//!
//! Inter-field type dependencies are resolved like Hindley-Milner inference:
//! every field and slot is assigned a variable, and `Self.field` resolves to
//! that field's variable. Following the references while a field is still being
//! resolved is exactly an occurs-check -- a field whose type refers back to
//! itself (`a: Self.b`, `b: Self.a`, or `a: Self.a[]`) is a circular
//! unification and is rejected rather than expanded forever.

use std::collections::{HashMap, HashSet};

use prepoly_parser::Span;
use prepoly_parser::ast::{TypeBody, TypeDecl, TypeExpr};

use std::collections::BTreeMap;

use crate::hir::{Program, TypeAlias, TypeKind};
use crate::types::{
    INFER_VAR, NominalInfo, NominalType, Substitution, Type, freshen_infer, is_fully_known,
    resolve, substitute_vars,
};

/// Static metadata about one type, gathered before resolution so a refinement
/// can read its base's fields/slots without a mutable borrow of the type table.
struct TypeMeta {
    id: i32,
    name: String,
    module: Vec<String>,
    is_record: bool,
    /// Slot name -> its inference variable.
    slots: Vec<(String, u32)>,
    /// Real field name -> (declared type expression, its inference variable).
    fields: Vec<(String, Option<TypeExpr>, u32)>,
}

impl TypeMeta {
    fn slot_var(&self, name: &str) -> Option<u32> {
        self.slots.iter().find(|(n, _)| n == name).map(|(_, v)| *v)
    }
    fn field(&self, name: &str) -> Option<(&Option<TypeExpr>, u32)> {
        self.fields
            .iter()
            .find(|(n, _, _)| n == name)
            .map(|(_, te, v)| (te, *v))
    }
}

/// Resolve every record type's field annotations (honoring slots, `Self.field`,
/// and refinements), fill each record's slot variables, and resolve the
/// `type Alias = ..` declarations into [`Program::type_aliases`]. Sum types keep
/// the plain per-field resolution in `lower.rs` -- they carry no slots.
pub(crate) fn resolve_type_decls(
    program: &mut Program,
    aliases: &[(String, Vec<String>, TypeDecl)],
    nominal_by_symbol: &HashMap<String, NominalInfo>,
    next_unknown: &mut u32,
    errors: &mut Vec<crate::lower::LowerError>,
) {
    // Gather metadata and allocate a fresh variable per slot and per record
    // field. Slot variables become the type's parameters; field variables let
    // `Self.field` and the occurs-check refer to a field before it is resolved.
    type FieldDecls = Vec<(String, Option<TypeExpr>)>;
    let mut meta: HashMap<String, TypeMeta> = HashMap::new();
    for (symbol, info) in program.types.iter() {
        let (is_record, slot_names, field_texprs): (bool, Vec<String>, FieldDecls) =
            match &info.kind {
                TypeKind::Record { fields, .. } => (
                    true,
                    info.slots.iter().map(|(n, _)| n.clone()).collect(),
                    fields
                        .iter()
                        .map(|f| (f.name.clone(), f.ty.clone()))
                        .collect(),
                ),
                TypeKind::Sum { .. } => (false, Vec::new(), Vec::new()),
            };
        let slots = slot_names
            .into_iter()
            .map(|n| {
                let v = *next_unknown;
                *next_unknown += 1;
                (n, v)
            })
            .collect();
        let fields = field_texprs
            .into_iter()
            .map(|(n, te)| {
                let v = *next_unknown;
                *next_unknown += 1;
                (n, te, v)
            })
            .collect();
        meta.insert(
            symbol.clone(),
            TypeMeta {
                id: info.id,
                name: info.name.clone(),
                module: info.module.clone(),
                is_record,
                slots,
                fields,
            },
        );
    }

    let mut resolver = Resolver {
        meta: &meta,
        nominal_by_symbol,
        import_origins: &program.import_origins,
        import_renames: &program.import_renames,
        next_unknown,
        resolved: HashMap::new(),
        gray: HashSet::new(),
        errors: Vec::new(),
    };

    // Resolve every record field (memoized inside the resolver).
    let record_syms: Vec<String> = meta
        .iter()
        .filter(|(_, m)| m.is_record)
        .map(|(s, _)| s.clone())
        .collect();
    let mut field_results: HashMap<(String, String), Type> = HashMap::new();
    for sym in &record_syms {
        let field_names: Vec<String> = meta[sym].fields.iter().map(|(n, _, _)| n.clone()).collect();
        for fname in field_names {
            let ty = resolver.resolve_field(sym, &fname);
            field_results.insert((sym.clone(), fname), ty);
        }
    }

    // Resolve each `type Alias = <type expr>` in its own module (no enclosing
    // type, so `Self.field` is not available there).
    let mut alias_results: Vec<(String, Vec<String>, Type, Span)> = Vec::new();
    for (symbol, module, td) in aliases {
        let TypeBody::Alias(te) = &td.body else {
            continue;
        };
        let ty = resolver.resolve_texpr(None, module, te);
        alias_results.push((symbol.clone(), module.clone(), ty, td.span));
    }

    errors.append(&mut resolver.errors);

    // Write the slot variables and resolved field types back into the program.
    for sym in &record_syms {
        let m = &meta[sym];
        let slots = m.slots.clone();
        if let Some(info) = program.types.get_mut(sym) {
            info.slots = slots;
            if let TypeKind::Record { fields, .. } = &mut info.kind {
                for f in fields.iter_mut() {
                    if let Some(t) = field_results.remove(&(sym.clone(), f.name.clone())) {
                        f.resolved_ty = Some(t);
                    }
                }
            }
        }
    }
    for (symbol, module, ty, span) in alias_results {
        program
            .type_aliases
            .insert(symbol, TypeAlias { module, ty, span });
    }
}

struct Resolver<'a> {
    meta: &'a HashMap<String, TypeMeta>,
    nominal_by_symbol: &'a HashMap<String, NominalInfo>,
    import_origins: &'a HashMap<Vec<String>, HashMap<String, Vec<String>>>,
    import_renames: &'a HashMap<Vec<String>, HashMap<String, String>>,
    next_unknown: &'a mut u32,
    /// Memoized resolved field types, keyed by (owner symbol, field name).
    resolved: HashMap<(String, String), Type>,
    /// Fields currently being resolved: revisiting one is a circular type.
    gray: HashSet<(String, String)>,
    errors: Vec<crate::lower::LowerError>,
}

impl Resolver<'_> {
    fn fresh(&mut self) -> u32 {
        let v = *self.next_unknown;
        *self.next_unknown += 1;
        v
    }

    /// The unique symbol a type NAME resolves to from `module` (its own/unique,
    /// this module's qualified, or an imported definition). Mirrors
    /// [`crate::hir::resolve_qualified`] but returns the matched key.
    fn symbol_of(&self, module: &[String], name: &str) -> Option<String> {
        // Rename first, as in `resolve_qualified`: a renamed local must not be
        // captured by an unrelated module's unique definition of that name.
        if let Some(remote) = self.import_renames.get(module).and_then(|m| m.get(name)) {
            let origin = self.import_origins.get(module)?.get(name)?;
            let qo = crate::hir::qualify(remote, origin);
            if self.meta.contains_key(&qo) {
                return Some(qo);
            }
            return self.meta.contains_key(remote).then(|| remote.clone());
        }
        if self.meta.contains_key(name) {
            return Some(name.to_string());
        }
        let q = crate::hir::qualify(name, module);
        if self.meta.contains_key(&q) {
            return Some(q);
        }
        let origin = self.import_origins.get(module)?.get(name)?;
        let qo = crate::hir::qualify(name, origin);
        self.meta.contains_key(&qo).then_some(qo)
    }

    /// Resolve one record field's type, memoized. A field referenced while it is
    /// still resolving forms a cycle (occurs-check failure) and is reported once.
    fn resolve_field(&mut self, sym: &str, field: &str) -> Type {
        let key = (sym.to_string(), field.to_string());
        if let Some(t) = self.resolved.get(&key) {
            return t.clone();
        }
        let Some(m) = self.meta.get(sym) else {
            return Type::Unknown(self.fresh());
        };
        let Some((texpr, var)) = m.field(field).map(|(te, v)| (te.clone(), v)) else {
            return Type::Unknown(self.fresh());
        };
        // An unannotated field is a free type parameter: its variable stands for
        // it (shared with every `Self.field` that names it).
        let Some(texpr) = texpr else {
            let t = Type::Unknown(var);
            self.resolved.insert(key, t.clone());
            return t;
        };
        if !self.gray.insert(key.clone()) {
            self.errors.push(crate::lower::LowerError {
                message: format!(
                    "field `{field}` of `{}` has a circular type (it refers to itself)",
                    m.name
                ),
                span: texpr.span(),
            });
            return Type::Unknown(var);
        }
        let module = m.module.clone();
        let owner = sym.to_string();
        let mut t = self.resolve_texpr(Some(&owner), &module, &texpr);
        // Freshen each `infer` placeholder into its own variable, matching the
        // plain field resolver.
        t = freshen_infer(t, &mut || {
            let v = *self.next_unknown;
            *self.next_unknown += 1;
            Type::Unknown(v)
        });
        self.gray.remove(&key);
        self.resolved.insert(key, t.clone());
        t
    }

    /// Resolve a type expression appearing in `owner`'s declaration (or, for an
    /// alias right-hand side, `owner` is `None`) in `module`, handling
    /// `Self.field`, `Base { .. }` refinements, and ordinary types.
    fn resolve_texpr(&mut self, owner: Option<&str>, module: &[String], te: &TypeExpr) -> Type {
        match te {
            TypeExpr::Array(inner, Some(n), _) => {
                Type::Array(Box::new(self.resolve_texpr(owner, module, inner)), *n)
            }
            TypeExpr::Array(inner, None, _) => {
                Type::Slice(Box::new(self.resolve_texpr(owner, module, inner)))
            }
            TypeExpr::Nullable(inner, _) => {
                Type::Nullable(Box::new(self.resolve_texpr(owner, module, inner)))
            }
            TypeExpr::Fallible(inner, _) => Type::result(
                self.resolve_texpr(owner, module, inner),
                Type::Unknown(INFER_VAR),
            ),
            TypeExpr::Mut(inner, _) => {
                Type::Mut(Box::new(self.resolve_texpr(owner, module, inner)))
            }
            TypeExpr::Ref(inner, _) => {
                Type::Ref(Box::new(self.resolve_texpr(owner, module, inner)))
            }
            TypeExpr::Tuple(elems, _) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| self.resolve_texpr(owner, module, e))
                    .collect(),
            ),
            TypeExpr::Fun(params, ret, _) => Type::Fun(
                params
                    .iter()
                    .map(|p| self.resolve_texpr(owner, module, p))
                    .collect(),
                Box::new(self.resolve_texpr(owner, module, ret)),
            ),
            TypeExpr::Anonymous(fields, _) => {
                let resolved = fields
                    .iter()
                    .map(|(n, ft)| (n.clone(), self.resolve_texpr(owner, module, ft)))
                    .collect();
                crate::types::structural_record(resolved)
            }
            TypeExpr::SelfField(field, span) => self.self_field(owner, field, *span),
            TypeExpr::Refine(base, entries, span) => {
                self.resolve_refine(owner, module, base, entries, *span)
            }
            // A nested `type` slot has no meaning; a `typeof` needs the checker.
            TypeExpr::TypeSlot(span) => {
                self.errors.push(crate::lower::LowerError {
                    message: "`type` may only be a field's whole declared type".into(),
                    span: *span,
                });
                Type::Unknown(self.fresh())
            }
            // `Named`/`typeof` and the leaf forms go through the pure resolver.
            other => {
                let nominal = |name: &str| self.nominal_lookup(module, name);
                resolve(other, nominal).unwrap_or(Type::Unknown(INFER_VAR))
            }
        }
    }

    fn nominal_lookup(&self, module: &[String], name: &str) -> Option<NominalInfo> {
        crate::hir::resolve_qualified(
            self.nominal_by_symbol,
            self.import_origins,
            self.import_renames,
            module,
            name,
        )
        .copied()
    }

    /// `Self.field` inside `owner`'s declaration: the referenced slot's variable,
    /// or the referenced field's resolved type (with cycle detection).
    fn self_field(&mut self, owner: Option<&str>, field: &str, span: Span) -> Type {
        let Some(sym) = owner.map(str::to_string) else {
            self.errors.push(crate::lower::LowerError {
                message: format!("`Self.{field}` is only valid inside a type declaration"),
                span,
            });
            return Type::Unknown(self.fresh());
        };
        if let Some(v) = self.meta[&sym].slot_var(field) {
            return Type::Unknown(v);
        }
        if self.meta[&sym].field(field).is_some() {
            return self.resolve_field(&sym, field);
        }
        self.errors.push(crate::lower::LowerError {
            message: format!(
                "`Self.{field}` names no field or slot of `{}`",
                self.meta[&sym].name
            ),
            span,
        });
        Type::Unknown(self.fresh())
    }

    /// Resolve `Base { field: T, .. }`: pin the named slots/fields of `Base` and
    /// build a fully concrete instance whose substitution covers every real
    /// field. An omitted slot is left open (`infer`).
    fn resolve_refine(
        &mut self,
        owner: Option<&str>,
        module: &[String],
        base: &TypeExpr,
        entries: &[(String, TypeExpr)],
        span: Span,
    ) -> Type {
        let TypeExpr::Named(bname, _) = base else {
            self.errors.push(crate::lower::LowerError {
                message: "a refinement base must be a named record type".into(),
                span,
            });
            return Type::Unknown(self.fresh());
        };
        let Some(bsym) = self.symbol_of(module, bname) else {
            self.errors.push(crate::lower::LowerError {
                message: format!("unknown type `{bname}` in refinement"),
                span,
            });
            return Type::Unknown(self.fresh());
        };
        if !self.meta[&bsym].is_record {
            self.errors.push(crate::lower::LowerError {
                message: format!("`{bname}` is not a record type and cannot be refined"),
                span,
            });
            return Type::Unknown(self.fresh());
        }
        // Pin map: slot variable / field name -> the type it is fixed to.
        let mut slot_pins: HashMap<u32, Type> = HashMap::new();
        let mut field_pins: HashMap<String, Type> = HashMap::new();
        for (fname, fte) in entries {
            let t = self.resolve_texpr(owner, module, fte);
            let slot = self.meta[&bsym].slot_var(fname);
            let is_field = self.meta[&bsym].field(fname).is_some();
            if let Some(v) = slot {
                slot_pins.insert(v, t);
            } else if is_field {
                // Refining a real field: its base type must match. A slot has no
                // declared type, so pinning it is always fine; a field whose
                // declared type is already concrete may only be pinned to the same
                // type (an inferred field is simply fixed by the pin).
                let declared = self.resolve_field(&bsym, fname);
                if is_fully_known(&declared) && is_fully_known(&t) && declared != t {
                    self.errors.push(crate::lower::LowerError {
                        message: format!(
                            "refining field `{fname}` of `{}`: its type is `{}`, not `{}`",
                            self.meta[&bsym].name,
                            declared.display(),
                            t.display()
                        ),
                        span: fte.span(),
                    });
                }
                field_pins.insert(fname.clone(), t);
            } else {
                self.errors.push(crate::lower::LowerError {
                    message: format!(
                        "`{}` has no field or slot `{fname}` to refine",
                        self.meta[&bsym].name
                    ),
                    span: fte.span(),
                });
            }
        }
        // Every declared slot variable maps to its pin, or to `infer` when
        // omitted (an open slot the use site fills).
        let slot_map: BTreeMap<u32, Type> = self.meta[&bsym]
            .slots
            .iter()
            .map(|(_, v)| {
                (
                    *v,
                    slot_pins
                        .get(v)
                        .cloned()
                        .unwrap_or(Type::Unknown(INFER_VAR)),
                )
            })
            .collect();

        let base_fields: Vec<String> = self.meta[&bsym]
            .fields
            .iter()
            .map(|(n, _, _)| n.clone())
            .collect();
        let mut subst = Substitution::empty();
        for fname in base_fields {
            let ty = if let Some(t) = field_pins.get(&fname) {
                t.clone()
            } else {
                let declared = self.resolve_field(&bsym, &fname);
                substitute_vars(&declared, &slot_map)
            };
            subst.insert(fname, ty);
        }
        let (id, name) = (self.meta[&bsym].id, self.meta[&bsym].name.clone());
        Type::Record(NominalType::with_substitution(id, name, subst))
    }
}
