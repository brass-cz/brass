//! Stable declaration catalog. Names are resolved by HIR, never by this index.

pub(super) mod snapshot;

use brass_hir::{
    FunInfo, ItemId, ItemKind, MethodBodyId, MethodInfo, ModuleId, ModuleInit, ModuleSource,
    Program, TypeAlias, TypeInfo, TypeKind,
};
use brass_parser::Span;
use fxhash::FxHashMap as HashMap;

/// A body in its exact checking context; variant copies remain distinct.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BodyId {
    /// A free or primitive-receiver function.
    Function(ItemId),
    /// An ordinary or reflective method declaration, with its owner and variant.
    Method(MethodBodyId),
    /// One loaded module's initialization sequence, including an empty sequence.
    Initializer(ItemId),
}

/// A catalog entry can require a layout without requiring every method body.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ItemKey {
    /// An executable or checkable body.
    Body(BodyId),
    /// A nominal declaration or alias.
    Type(ItemId),
}

/// Borrowed HIR data for one catalog entry; no cloned bodies or type inference.
pub(super) enum Declaration<'a> {
    Function(&'a FunInfo),
    Method(&'a TypeInfo, &'a MethodInfo),
    Type(&'a TypeInfo),
    Alias(&'a TypeAlias),
    Initializer(&'a ModuleInit),
}

/// Source extent and provenance accompany every stable catalog identity.
pub(super) struct Entry<'a> {
    pub(super) key: ItemKey,
    pub(super) module: &'a [String],
    pub(super) source: Option<&'a ModuleSource>,
    pub(super) declaration: Declaration<'a>,
    pub(super) label: String,
}

/// Combined declaration catalog, built for selection and optional observation.
/// It contains unused declarations too, preserving negative member facts.
pub struct ItemIndex<'a> {
    pub(super) effect_time: std::cell::Cell<std::time::Duration>,
    pub(super) certificate_time: std::cell::Cell<std::time::Duration>,
    pub(super) names: HashMap<&'a [String], super::names::Names<'a>>,
    pub(super) program: &'a Program,
    pub(super) entries: Vec<Entry<'a>>,
    pub(super) lookup: HashMap<ItemKey, usize>,
    pub(super) functions: HashMap<&'a str, usize>,
    pub(super) types: HashMap<i32, usize>,
    pub(super) methods: HashMap<(i32, &'a str), Vec<usize>>,
    pub(super) families: HashMap<&'a str, Vec<(i32, usize)>>,
    pub(super) primitive_families: HashMap<&'a str, Vec<(&'a str, usize)>>,
    pub(super) primitives: HashMap<(&'a str, &'a str), usize>,
    pub(super) shared_variables: std::cell::OnceCell<fxhash::FxHashSet<u32>>,
    pub(super) effects: super::effects::Cache,
    pub(super) method_reads: std::cell::RefCell<fxhash::FxHashSet<u64>>,
    pub(super) globals: HashMap<Vec<String>, std::collections::BTreeSet<String>>,
    pub(super) aliases: HashMap<Span, usize>,
}

impl<'a> ItemIndex<'a> {
    /// Inventory a completed HIR catalog without checking any body. Synthetic
    /// test graphs use module namespace plus span when no loader identity exists.
    pub fn new(program: &'a Program) -> Self {
        let started = super::cost::start();
        let mut this = Self {
            certificate_time: Default::default(),
            effect_time: Default::default(),
            program,
            names: Default::default(),
            entries: Vec::new(),
            lookup: HashMap::default(),
            functions: HashMap::default(),
            types: HashMap::default(),
            methods: HashMap::default(),
            families: HashMap::default(),
            primitive_families: HashMap::default(),
            primitives: HashMap::default(),
            shared_variables: Default::default(),
            aliases: HashMap::default(),
            effects: Default::default(),
            method_reads: Default::default(),
            globals: Default::default(),
        };
        let mut functions: Vec<_> = program.functions.values().collect();
        functions.sort_by_key(|f| (f.decl.span.lo, &f.symbol));
        for f in functions {
            let key = ItemKey::Body(BodyId::Function(this.id(
                &f.module,
                f.decl.span,
                ItemKind::Function,
            )));
            this.functions.insert(f.symbol.as_str(), this.entries.len());
            this.push(
                key,
                &f.module,
                f.decl.span,
                Declaration::Function(f),
                f.symbol.clone(),
            );
        }
        let mut types: Vec<_> = program.types.values().collect();
        types.sort_by_key(|t| (t.span.lo, &t.symbol));
        for t in types {
            let id = this.id(&t.module, t.span, ItemKind::Type);
            let key = ItemKey::Type(id.clone());
            this.types.insert(t.id, this.entries.len());
            this.push(
                key,
                &t.module,
                t.span,
                Declaration::Type(t),
                t.symbol.clone(),
            );
            let groups = match &t.kind {
                TypeKind::Record { methods, .. } => vec![(None, methods)],
                TypeKind::Sum { variants } => {
                    variants.iter().map(|v| (Some(v.tag), &v.methods)).collect()
                }
            };
            for (variant, methods) in groups {
                let mut methods: Vec<_> = methods.values().collect();
                methods.sort_by_key(|m| (m.decl.span.lo, &m.signature.name));
                for m in methods {
                    let mid =
                        program
                            .method_body_id(t, m, variant)
                            .unwrap_or_else(|| MethodBodyId {
                                owner: id.clone(),
                                module: id.module.clone(),
                                offset: m.decl.span.lo,
                                variant,
                                name: m.signature.name.clone(),
                            });
                    let key = ItemKey::Body(BodyId::Method(mid));
                    this.methods
                        .entry((t.id, m.signature.name.as_str()))
                        .or_default()
                        .push(this.entries.len());
                    this.families
                        .entry(m.signature.name.as_str())
                        .or_default()
                        .push((t.id, this.entries.len()));
                    this.push(
                        key,
                        &t.module,
                        m.decl.span,
                        Declaration::Method(t, m),
                        format!("{}.{}:{variant:?}", t.symbol, m.signature.name),
                    );
                }
            }
        }
        let mut aliases: Vec<_> = program.type_aliases.iter().collect();
        aliases.sort_by_key(|(name, a)| (a.span.lo, *name));
        for (name, a) in aliases {
            let key = ItemKey::Type(this.id(&a.module, a.span, ItemKind::Type));
            this.aliases.insert(a.span, this.entries.len());
            this.push(key, &a.module, a.span, Declaration::Alias(a), name.clone());
        }
        for init in &program.inits {
            let span = Span::new(
                init.source.as_ref().map_or(0, |s| s.base),
                init.source.as_ref().map_or(0, |s| s.base),
            );
            let key = ItemKey::Body(BodyId::Initializer(this.id(
                &init.path,
                span,
                ItemKind::Initializer,
            )));
            this.push(
                key,
                &init.path,
                span,
                Declaration::Initializer(init),
                format!("init:{}", init.path.join("/")),
            );
        }
        for ((class, name), symbol) in &program.primitive_methods {
            if let Some(&id) = this.functions.get(symbol.as_str()) {
                this.primitives.insert((class.as_str(), name.as_str()), id);
                this.primitive_families
                    .entry(name.as_str())
                    .or_default()
                    .push((class.as_str(), id));
            }
        }
        for family in this.primitive_families.values_mut() {
            family.sort_unstable_by_key(|(_, id)| *id);
        }
        for entry in &this.entries {
            this.names
                .entry(entry.module)
                .or_insert_with(|| super::names::Names::new(program, entry.module));
        }
        super::cost::finish("catalog", started);
        let started = super::cost::start();
        this.effects = super::effects::Cache::new(this.entries.len());
        for init in &program.inits {
            for statement in &init.stmts {
                if let brass_parser::ast::Stmt::Let { pat, .. } = statement {
                    this.globals
                        .entry(init.path.clone())
                        .or_default()
                        .extend(pat.bound_names().into_iter().map(str::to_owned));
                }
            }
        }
        super::cost::finish("effects", started);
        this
    }

    /// Track positive and negative method-family reads. Hash collisions only
    /// cause extra invalidation; equal names always invalidate the same read.
    pub(super) fn observe_method(&self, name: &str) {
        self.method_reads.borrow_mut().insert(fxhash::hash64(name));
    }

    /// Number of bodies and layouts, including variant checking contexts.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether this catalog has no declarations or initializers.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Stable identities paired with display labels, in deterministic order.
    pub fn items(&self) -> impl Iterator<Item = (&ItemKey, &str)> {
        self.entries.iter().map(|e| (&e.key, e.label.as_str()))
    }

    /// Explain retained method producers separately from runtime-use edges.
    pub fn shared_obligations(
        &self,
    ) -> impl Iterator<Item = (&ItemKey, &str, super::SharedObligation)> {
        self.entries.iter().filter_map(|entry| {
            let Declaration::Method(owner, method) = &entry.declaration else {
                return None;
            };
            super::shared_obligation(self, owner, method)
                .map(|reason| (&entry.key, entry.label.as_str(), reason))
        })
    }

    /// Transitive conservative footprints in catalog order, for shadow diagnostics.
    pub fn effect_summaries(
        &self,
    ) -> impl Iterator<Item = (&ItemKey, &str, &super::EffectSummary)> {
        self.entries
            .iter()
            .enumerate()
            .filter(|(_, entry)| matches!(entry.key, ItemKey::Body(_)))
            .map(|(id, entry)| {
                (
                    &entry.key,
                    entry.label.as_str(),
                    super::effects::summary(self, id, false),
                )
            })
    }

    /// External footprints for closed sum roots, with no record co owner.
    pub fn rootless_effect_summaries(
        &self,
    ) -> impl Iterator<Item = (&ItemKey, &str, &super::EffectSummary)> {
        self.entries
            .iter()
            .enumerate()
            .filter(|(_, entry)| matches!(entry.key, ItemKey::Body(_)))
            .map(|(id, entry)| {
                (
                    &entry.key,
                    entry.label.as_str(),
                    super::effects::summary(self, id, true),
                )
            })
    }

    /// Rebind body-only AST rewrites to an unchanged declaration catalog. Names,
    /// source IDs and numeric type IDs must be stable. Certificates are discarded
    /// because inserted calls can alter effects; no catalog is reconstructed.
    pub fn refresh_bodies(&mut self, program: &'a Program) {
        for entry in &mut self.entries {
            entry.declaration = match entry.declaration {
                Declaration::Function(old) => {
                    let new = &program.functions[&old.symbol];
                    debug_assert_eq!(old.decl.span, new.decl.span);
                    Declaration::Function(new)
                }
                Declaration::Method(old_owner, old) => {
                    let owner = &program.types[&old_owner.symbol];
                    assert_eq!(
                        owner.id, old_owner.id,
                        "body rewrite changed nominal identity"
                    );
                    let ItemKey::Body(BodyId::Method(id)) = &entry.key else {
                        unreachable!()
                    };
                    let methods = match (&owner.kind, id.variant) {
                        (TypeKind::Record { methods, .. }, None) => methods,
                        (TypeKind::Sum { variants }, Some(tag)) => {
                            &variants
                                .iter()
                                .find(|v| v.tag == tag)
                                .expect("stable variant")
                                .methods
                        }
                        _ => unreachable!("body rewrite changed owner layout"),
                    };
                    Declaration::Method(owner, &methods[&old.signature.name])
                }
                Declaration::Type(old) => {
                    let new = &program.types[&old.symbol];
                    assert_eq!(new.id, old.id, "body rewrite changed nominal identity");
                    Declaration::Type(new)
                }
                Declaration::Alias(old) => Declaration::Alias(
                    program
                        .type_aliases
                        .values()
                        .find(|alias| alias.span == old.span && alias.module == old.module)
                        .expect("stable alias"),
                ),
                Declaration::Initializer(old) => {
                    let pos = self
                        .program
                        .inits
                        .iter()
                        .position(|init| std::ptr::eq(init, old))
                        .expect("catalog initializer");
                    let new = &program.inits[pos];
                    debug_assert_eq!(new.path, old.path);
                    Declaration::Initializer(new)
                }
            };
        }
        self.program = program;
        for (module, names) in &mut self.names {
            *names = super::names::Names::new(program, module);
        }
        self.effects = super::effects::Cache::new(self.entries.len());
        self.method_reads.get_mut().clear();
    }

    fn id(&self, module: &[String], span: Span, kind: ItemKind) -> ItemId {
        item_id(self.program, module, span, kind)
    }

    fn push(
        &mut self,
        key: ItemKey,
        module: &'a [String],
        span: Span,
        declaration: Declaration<'a>,
        label: String,
    ) {
        assert!(
            self.lookup
                .insert(key.clone(), self.entries.len())
                .is_none(),
            "duplicate source identity: {label}"
        );
        self.entries.push(Entry {
            key,
            module,
            source: self.program.module_source(module, span),
            declaration,
            label,
        });
    }
}

/// Stable identity for real and synthetic catalogs, shared by selection and coverage.
pub(super) fn item_id(program: &Program, module: &[String], span: Span, kind: ItemKind) -> ItemId {
    program
        .item_id(module, span, kind)
        .unwrap_or_else(|| ItemId {
            module: ModuleId::new(format!("<{}>", module.join("/")), module),
            offset: span.lo,
            kind,
        })
}
