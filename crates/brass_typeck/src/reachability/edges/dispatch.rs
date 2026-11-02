//! Dispatch and producer facts share the reachability worklist's inhabited set.

use super::{Edges, Expr, Reason, Type};
use brass_hir::rendering::{RenderForm, render_method};
use brass_hir::{FloatKind, IntKind, TypeKind};
use fxhash::FxHashSet as HashSet;

impl Edges<'_, '_> {
    /// Retain an exact owner or the admissible virtual family for this frame.
    pub(super) fn method(&mut self, owner: Option<i32>, name: &str, reason: Reason) {
        if owner.is_none() {
            self.inhabited_dependent |= !self.open;
            self.cause(if self.open {
                "open root frame: same-name family"
            } else {
                "unresolved receiver: inhabited same-name family"
            });
        }
        for key in self.method_targets(owner, name) {
            self.edge(key, reason);
        }
    }

    /// Enumerate the same virtual family for selection and shared-effect proofs.
    pub(super) fn method_targets(&self, owner: Option<i32>, name: &str) -> Vec<usize> {
        self.index.observe_method(name);
        if let Some(owner) = owner {
            return self
                .index
                .methods
                .get(&(owner, name))
                .cloned()
                .unwrap_or_default();
        }
        let mut targets: Vec<_> = self
            .index
            .families
            .get(name)
            .into_iter()
            .flatten()
            .filter(|(owner, _)| self.open || self.inhabited.nominal.contains(owner))
            .map(|(_, id)| *id)
            .collect();
        targets.extend(
            self.index
                .primitive_families
                .get(name)
                .into_iter()
                .flatten()
                .filter(|(class, _)| self.open || self.inhabited.primitive.contains(class))
                .map(|(_, id)| *id),
        );
        targets.sort_unstable();
        targets
    }

    fn value_bound(&self, name: &str) -> bool {
        self.locals.contains(name)
            || self
                .index
                .globals
                .get(self.module)
                .is_some_and(|names| names.contains(name))
    }

    /// A union of local names spans nested scopes. Keep a syntactically possible
    /// static target too, since a later/out-of-scope binding cannot hide it.
    pub(super) fn possible_static(&mut self, expr: &Expr, name: &str) {
        if let Expr::Ident(qualifier, _) = expr
            && self.locals.contains(qualifier)
            && let Some(owner) = self.names.nominal(qualifier)
        {
            self.cause("local scope union: possible static qualifier");
            if matches!(name, "new" | "default" | "from") {
                self.inhabited.ty(self.index.program, &owner.type_ref());
            }
            self.method(Some(owner.id), name, Reason::ExplicitUse);
        }
    }

    /// Recognize only unshadowed nominal qualifiers and literal constructors.
    pub(super) fn receiver(&self, expr: &Expr) -> Option<i32> {
        match expr {
            Expr::SelfExpr(_) => self.owner.map(|t| t.id),
            // A declared structural receiver can be supplied by another
            // nominal. Only a constructor/static qualifier fixes its owner;
            // value parameters retain the same-name dispatch family.
            Expr::Ident(name, _) if self.value_bound(name) => None,
            Expr::Ident(name, _) | Expr::TypeLit(name, _, _) | Expr::VariantLit(name, _, _, _) => {
                if name == "Self" {
                    self.owner.map(|t| t.id)
                } else {
                    self.names.nominal(name).map(|t| t.id)
                }
            }
            _ => None,
        }
    }

    /// Resolve a primitive static qualifier through the HIR naming authority.
    pub(super) fn qualifier_class(&self, expr: &Expr) -> Option<&'static str> {
        let Expr::Ident(name, _) = expr else {
            return None;
        };
        if self.value_bound(name) || self.names.ty(name).is_some() {
            return None;
        }
        self.names
            .alias(name)
            .and_then(|alias| alias.ty.primitive_class())
            .or_else(|| Type::primitive_class_of_name(name, false))
    }

    /// Recognize syntax whose primitive dispatch class cannot vary by context.
    pub(super) fn known_class(&self, expr: &Expr) -> Option<&'static str> {
        match expr {
            Expr::Str(..) => Some("string"),
            Expr::Bool(..) => Some("bool"),
            Expr::Call(callee, _, _) => match callee.as_ref() {
                Expr::Field(base, name, _) if name == "from" => self.qualifier_class(base),
                Expr::Ident(name, _) => self
                    .names
                    .function(name)
                    .and_then(|f| f.signature.ret_ty.as_ref())
                    .and_then(Type::primitive_class),
                _ => None,
            },
            // Unsuffixed numeric literals adapt to context, so retain all
            // compatible primitive families instead of guessing an instance.
            _ => self.qualifier_class(expr),
        }
    }

    /// Retain the top-level renderer and effective debug at every nested position.
    pub(super) fn rendering(&mut self, value: Option<&Expr>) {
        self.rendering_form(value, RenderForm::Display);
    }

    /// Explicit debug never retains a display method just for rendering.
    pub(super) fn rendering_form(&mut self, value: Option<&Expr>, form: RenderForm) {
        if let Some(class) = value.and_then(|v| self.known_class(v))
            && class != "array"
        {
            return;
        }
        if let Some(id) = value.and_then(|v| self.receiver(v))
            && let Some(info) = self.index.program.type_by_id(id)
        {
            self.render_type(&info.type_ref(), form, &mut HashSet::default());
            return;
        }
        if let Some(Expr::Array(values, _)) = value {
            for value in values {
                self.rendering_form(Some(value), RenderForm::Debug);
            }
            return;
        }
        if matches!(value, Some(Expr::Null(_))) {
            return;
        }
        self.cause(if self.open {
            "open root frame: rendering families"
        } else {
            "rendering without instance: inhabited rendering families"
        });
        if form == RenderForm::Display {
            self.method(None, "display", Reason::ImplicitUse);
        }
        self.method(None, "debug", Reason::ImplicitUse);
    }

    fn render_type(&mut self, ty: &Type, form: RenderForm, seen: &mut HashSet<i32>) {
        match ty {
            Type::Record(n) | Type::Sum(n) if seen.insert(n.id) => {
                if let Some(name) = render_method(self.index.program, ty, form) {
                    self.method(Some(n.id), name, Reason::ImplicitUse);
                } else if let Some(info) = self.index.program.type_by_id(n.id) {
                    let groups = match &info.kind {
                        TypeKind::Record { fields, .. } => vec![(None, fields)],
                        TypeKind::Sum { variants } => variants
                            .iter()
                            .map(|v| (Some(v.name.as_str()), &v.fields))
                            .collect(),
                    };
                    for (variant, fields) in groups {
                        for field in fields {
                            let key = variant.map_or_else(
                                || field.name.clone(),
                                |v| format!("{v}.{}", field.name),
                            );
                            if let Some(ty) = n.substitution.get(&key).cloned().or_else(|| {
                                super::super::layout::field(self.index.program, info, field)
                            }) {
                                self.render_type(&ty, RenderForm::Debug, seen);
                            } else {
                                self.method(None, "debug", Reason::ImplicitUse);
                            }
                        }
                    }
                }
                seen.remove(&n.id);
            }
            Type::Array(t, _) | Type::Slice(t) => self.render_type(t, RenderForm::Debug, seen),
            Type::Nullable(t) | Type::ConstOf(t) | Type::Ref(t) | Type::Mut(t) => {
                self.render_type(t, form, seen)
            }
            Type::Tuple(ts) => {
                for t in ts {
                    self.render_type(t, RenderForm::Debug, seen);
                }
            }
            Type::Unknown(_) | Type::SelfType => {
                if form == RenderForm::Display {
                    self.method(None, "display", Reason::ImplicitUse);
                }
                self.method(None, "debug", Reason::ImplicitUse);
            }
            _ => {}
        }
    }

    /// Retain inhabited layouts, or the catalog for an unconstrained root input.
    pub(super) fn reflection(&mut self, value: Option<&Expr>) {
        if let Some(id) = value.and_then(|v| self.receiver(v)) {
            self.nominal(id, Reason::ImplicitUse);
            return;
        }
        if value.and_then(|v| self.known_class(v)).is_some() {
            return;
        }
        if self.open {
            self.cause("open root frame: full reflection catalog");
            for key in 0..self.index.entries.len() {
                self.edge(key, Reason::ImplicitUse);
            }
            return;
        }
        self.inhabited_dependent = true;
        self.cause("reflection without instance: inhabited field layouts");
        // fields() exposes data fields, not the owner's method declarations.
        // Callback literals/values are visited at their producer; declared
        // callback return types are propagated by Inhabited::ty.
        let ids: Vec<_> = self.inhabited.nominal.iter().copied().collect();
        for id in ids {
            self.nominal(id, Reason::ImplicitUse);
        }
    }

    /// Collect value producers without interpreting guards or executing inference.
    pub(super) fn produce(&mut self, expr: &Expr) {
        let p = self.index.program;
        match expr {
            Expr::Ident(name, _) => {
                for info in self.names.variants(name).iter() {
                    self.inhabited.ty(p, &info.type_ref());
                }
            }
            Expr::Str(..) => {
                self.inhabited.ty(p, &Type::Str);
            }
            Expr::Bool(..) => {
                self.inhabited.ty(p, &Type::Bool);
            }
            Expr::Int(..) => {
                for kind in [
                    IntKind::I8,
                    IntKind::I16,
                    IntKind::I32,
                    IntKind::I64,
                    IntKind::U8,
                    IntKind::U16,
                    IntKind::U32,
                    IntKind::U64,
                ] {
                    self.inhabited.ty(p, &Type::Int(kind));
                }
            }
            Expr::Float(..) => {
                self.inhabited.ty(p, &Type::Float(FloatKind::F32));
                self.inhabited.ty(p, &Type::Float(FloatKind::F64));
            }
            Expr::Null(..) => {
                self.inhabited.wrappers.insert("nullable");
            }
            Expr::Array(..) => {
                self.inhabited.primitive.insert("array");
            }
            Expr::Closure(..) => {
                self.inhabited.wrappers.insert("function");
            }
            Expr::TypeLit(name, _, _) | Expr::VariantLit(name, _, _, _) => {
                self.inhabited.named(self.index, self.module, name);
                if name.is_empty() {
                    self.inhabited.wrappers.insert("anonymous");
                }
            }
            Expr::Field(base, member, _) => {
                // A payload-free variant is a value expression too.
                if let Some(id) = self.receiver(base)
                    && let Some(info) = p.type_by_id(id)
                    && matches!(&info.kind, TypeKind::Sum { variants } if variants.iter().any(|v| &v.name == member))
                {
                    self.inhabited.ty(p, &info.type_ref());
                }
            }
            Expr::Call(callee, _, _) => {
                if let Expr::Ident(name, _) = callee.as_ref()
                    && let Some(ty) = brass_hir::builtin_returns::builtin_return(name, || {
                        self.names.function("input").is_some()
                    })
                {
                    self.inhabited.ty(p, &ty);
                }
                if let Expr::Field(base, member, _) = callee.as_ref() {
                    // Static factories may return Self without an explicit
                    // nominal annotation. Structural from/default are builtins.
                    if let Some(id) = self.receiver(base)
                        && let Some(info) = p.type_by_id(id)
                        && matches!(member.as_str(), "new" | "default" | "from")
                    {
                        self.inhabited.ty(p, &info.type_ref());
                    }
                    if let Some(class) = self.qualifier_class(base) {
                        self.inhabited.primitive.insert(class);
                    }
                }
            }
            _ => {}
        }
    }
}

impl Edges<'_, '_> {
    /// Resolve source callees whose identity is fixed by syntax. Structural or
    /// shadowed calls have no absence proof even when a virtual family is empty.
    pub(super) fn exact_call_targets(&self, callee: &Expr) -> Vec<usize> {
        match callee {
            Expr::Ident(name, _) if !self.value_bound(name) => self
                .names
                .function(name)
                .and_then(|f| self.index.functions.get(f.symbol.as_str()))
                .cloned()
                .into_iter()
                .collect(),
            Expr::Field(base, name, _) => {
                self.index.observe_method(name);
                if let Some(owner) = self.receiver(base) {
                    return self
                        .index
                        .methods
                        .get(&(owner, name.as_str()))
                        .cloned()
                        .unwrap_or_default();
                }
                self.known_class(base)
                    .and_then(|class| {
                        self.index
                            .program
                            .primitive_methods
                            .get(&(class.into(), name.clone()))
                    })
                    .and_then(|symbol| self.index.functions.get(symbol.as_str()))
                    .cloned()
                    .into_iter()
                    .collect()
            }
            _ => Vec::new(),
        }
    }
}
