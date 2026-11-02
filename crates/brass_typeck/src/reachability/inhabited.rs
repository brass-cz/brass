//! Producer facts for rapid type analysis, independent of solver variables.

use brass_hir::{Program, Type, TypeKind};
use brass_parser::ast::TypeExpr;
use std::collections::BTreeSet;

/// Monotone runtime type families; structural wrappers retain their contents.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Inhabited {
    pub(super) nominal: BTreeSet<i32>,
    pub(super) primitive: BTreeSet<&'static str>,
    pub(super) wrappers: BTreeSet<&'static str>,
}

impl Inhabited {
    /// Monotone fact count; growth does not require cloning the sets.
    pub(super) fn len(&self) -> usize {
        self.nominal.len() + self.primitive.len() + self.wrappers.len()
    }

    /// Include a produced value and every possible declared field/element value.
    /// Nominal recursion terminates after each declaration's fields are visited;
    /// substitutions are visited on every occurrence, including recursive maps.
    pub(super) fn ty(&mut self, program: &Program, ty: &Type) {
        if let Some(class) = ty.primitive_class() {
            self.primitive.insert(class);
        }
        match ty {
            Type::Record(n) | Type::Sum(n) => {
                for (_, ty) in n.substitution.iter() {
                    self.ty(program, ty);
                }
                if self.nominal.insert(n.id)
                    && let Some(info) = program.type_by_id(n.id)
                {
                    let groups = match &info.kind {
                        TypeKind::Record { fields, .. } => vec![fields],
                        TypeKind::Sum { variants } => variants.iter().map(|v| &v.fields).collect(),
                    };
                    for fields in groups {
                        for field in fields {
                            if let Some(ty) = super::layout::field(program, info, field) {
                                self.ty(program, &ty);
                            }
                        }
                    }
                }
            }
            Type::Array(t, _) | Type::Slice(t) => self.ty(program, t),
            Type::Nullable(t) => {
                self.wrappers.insert("nullable");
                self.ty(program, t);
            }
            Type::ConstOf(t) | Type::Ref(t) | Type::Mut(t) => self.ty(program, t),
            Type::Tuple(ts) => {
                self.wrappers.insert("tuple");
                for t in ts {
                    self.ty(program, t);
                }
            }
            Type::Fun(_, ret) => {
                self.wrappers.insert("function");
                self.ty(program, ret);
            }
            _ => {}
        }
    }

    /// Resolve declaration types without treating a mere imported name as a value.
    pub(super) fn named(&mut self, index: &super::ItemIndex<'_>, module: &[String], name: &str) {
        let program = index.program;
        let names = &index.names[module];
        if let Some(alias) = names.alias(name) {
            self.ty(program, &alias.ty);
        } else if let Some(info) = names.ty(name) {
            self.ty(program, &info.type_ref());
        } else if let Some(class) = Type::primitive_class_of_name(name, false) {
            self.primitive.insert(class);
        }
        for info in names.variants(name).iter() {
            self.ty(program, &info.type_ref());
        }
    }

    /// A declared result, default binding or conversion destination can produce
    /// these types, including nested keyed targets and anonymous field shapes.
    pub(super) fn annotation(
        &mut self,
        index: &super::ItemIndex<'_>,
        module: &[String],
        ty: &TypeExpr,
    ) {
        match ty {
            TypeExpr::Named(name, _) => self.named(index, module, name),
            TypeExpr::Array(t, _, _) => {
                self.primitive.insert("array");
                self.annotation(index, module, t);
            }
            TypeExpr::Nullable(t, _) => {
                self.wrappers.insert("nullable");
                self.annotation(index, module, t);
            }
            TypeExpr::Fallible(t, _) => {
                self.named(index, module, brass_hir::RESULT_TYPE_NAME);
                self.annotation(index, module, t);
            }
            TypeExpr::Mut(t, _) | TypeExpr::Ref(t, _) => self.annotation(index, module, t),
            TypeExpr::Tuple(ts, _) => {
                self.wrappers.insert("tuple");
                for t in ts {
                    self.annotation(index, module, t);
                }
            }
            TypeExpr::Fun(_, ret, _) => {
                self.wrappers.insert("function");
                self.annotation(index, module, ret);
            }
            TypeExpr::Refine(base, fields, _) => {
                self.annotation(index, module, base);
                for (_, t, _) in fields {
                    self.annotation(index, module, t);
                }
            }
            TypeExpr::Anonymous(fields, _) => {
                self.wrappers.insert("anonymous");
                for (_, t, _) in fields {
                    self.annotation(index, module, t);
                }
            }
            TypeExpr::TypeOf(..) | TypeExpr::SelfField(..) | TypeExpr::TypeSlot(_) => {}
        }
    }
}
