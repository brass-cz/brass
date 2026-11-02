//! Portable catalog handles preserve indices across append-only HIR mutation.
//! Bodies are rebound by their existing storage symbol, never copied or resolved
//! from source names. Only fresh generated methods allocate new catalog slots.

use super::{BodyId, Declaration, Entry, ItemIndex, ItemKey};
use brass_hir::{GeneratedDecl, Program, TypeKind};
use fxhash::FxHashMap as HashMap;

#[derive(Clone)]
enum Locator {
    Function(String),
    Method(String, String, Option<i32>),
    Type(String),
    Alias(String),
    Initializer(usize),
}

#[derive(Clone)]
struct Slot {
    key: ItemKey,
    label: String,
    locator: Locator,
}

/// Owned catalog metadata; it has no AST borrows and can cross the lazy boundary.
pub(in crate::reachability) struct Snapshot {
    slots: Vec<Slot>,
    lookup: HashMap<ItemKey, usize>,
    functions: HashMap<String, usize>,
    types: HashMap<i32, usize>,
    methods: HashMap<(i32, String), Vec<usize>>,
    families: HashMap<String, Vec<(i32, usize)>>,
    primitive_families: HashMap<String, Vec<(String, usize)>>,
    primitives: HashMap<(String, String), usize>,
    aliases: HashMap<brass_parser::Span, usize>,
    globals: HashMap<Vec<String>, std::collections::BTreeSet<String>>,
    shared_variables: Option<fxhash::FxHashSet<u32>>,
    method_reads: fxhash::FxHashSet<u64>,
    effects: crate::reachability::effects::FrozenCache,
}

impl ItemIndex<'_> {
    /// Save catalog metadata once with the settled reachability state. No body is cloned.
    pub(in crate::reachability) fn snapshot(&self) -> Snapshot {
        Snapshot {
            slots: self
                .entries
                .iter()
                .map(|e| Slot {
                    key: e.key.clone(),
                    label: e.label.clone(),
                    locator: match &e.declaration {
                        Declaration::Function(f) => Locator::Function(f.symbol.clone()),
                        Declaration::Type(t) => Locator::Type(t.symbol.clone()),
                        Declaration::Method(t, m) => {
                            let ItemKey::Body(BodyId::Method(id)) = &e.key else {
                                unreachable!()
                            };
                            Locator::Method(t.symbol.clone(), m.signature.name.clone(), id.variant)
                        }
                        Declaration::Alias(a) => Locator::Alias(
                            self.program
                                .type_aliases
                                .iter()
                                .find(|(_, v)| std::ptr::eq(*v, *a))
                                .expect("catalog alias")
                                .0
                                .clone(),
                        ),
                        Declaration::Initializer(i) => Locator::Initializer(
                            self.program
                                .inits
                                .iter()
                                .position(|v| std::ptr::eq(v, *i))
                                .expect("catalog initializer"),
                        ),
                    },
                })
                .collect(),
            lookup: self.lookup.clone(),
            functions: self
                .functions
                .iter()
                .map(|(k, v)| ((*k).into(), *v))
                .collect(),
            types: self.types.clone(),
            methods: self
                .methods
                .iter()
                .map(|((t, n), v)| ((*t, (*n).into()), v.clone()))
                .collect(),
            families: self
                .families
                .iter()
                .map(|(k, v)| ((*k).into(), v.clone()))
                .collect(),
            primitive_families: self
                .primitive_families
                .iter()
                .map(|(k, v)| {
                    (
                        (*k).into(),
                        v.iter().map(|(c, i)| ((*c).into(), *i)).collect(),
                    )
                })
                .collect(),
            primitives: self
                .primitives
                .iter()
                .map(|((c, n), v)| (((*c).into(), (*n).into()), *v))
                .collect(),
            aliases: self.aliases.clone(),
            globals: self.globals.clone(),
            shared_variables: self.shared_variables.get().cloned(),
            method_reads: self.method_reads.borrow().clone(),
            effects: self.effects.freeze(),
        }
    }
}

impl Snapshot {
    /// Whether appended names can change an earlier positive or negative lookup.
    pub(in crate::reachability) fn changes_reads(&self, generated: &[GeneratedDecl]) -> bool {
        generated
            .iter()
            .any(|g| self.method_reads.contains(&fxhash::hash64(&g.decl.name)))
    }

    /// Rebind existing handles without sorting, source-ID construction, or a closure.
    pub(in crate::reachability) fn bind<'a>(
        &'a self,
        program: &'a Program,
        changed: bool,
    ) -> ItemIndex<'a> {
        let started = crate::reachability::cost::start();
        let entries: Vec<_> = self
            .slots
            .iter()
            .map(|slot| {
                let (module, span, declaration) = match &slot.locator {
                    Locator::Function(symbol) => {
                        let f = &program.functions[symbol];
                        (&f.module, f.decl.span, Declaration::Function(f))
                    }
                    Locator::Type(symbol) => {
                        let t = &program.types[symbol];
                        (&t.module, t.span, Declaration::Type(t))
                    }
                    Locator::Method(symbol, name, variant) => {
                        let t = &program.types[symbol];
                        let methods = match (&t.kind, variant) {
                            (TypeKind::Record { methods, .. }, None) => methods,
                            (TypeKind::Sum { variants }, Some(tag)) => {
                                &variants
                                    .iter()
                                    .find(|v| v.tag == *tag)
                                    .expect("stable variant")
                                    .methods
                            }
                            _ => unreachable!("append changed layout"),
                        };
                        let m = &methods[name];
                        (&t.module, m.decl.span, Declaration::Method(t, m))
                    }
                    Locator::Alias(symbol) => {
                        let a = &program.type_aliases[symbol];
                        (&a.module, a.span, Declaration::Alias(a))
                    }
                    Locator::Initializer(pos) => {
                        let i = &program.inits[*pos];
                        let base = i.source.as_ref().map_or(0, |s| s.base);
                        (
                            &i.path,
                            brass_parser::Span::new(base, base),
                            Declaration::Initializer(i),
                        )
                    }
                };
                Entry {
                    key: slot.key.clone(),
                    label: slot.label.clone(),
                    module,
                    source: program.module_source(module, span),
                    declaration,
                }
            })
            .collect();
        let mut names = HashMap::default();
        for e in &entries {
            names
                .entry(e.module)
                .or_insert_with(|| crate::reachability::names::Names::new(program, e.module));
        }
        let index = ItemIndex {
            effect_time: Default::default(),
            certificate_time: Default::default(),
            program,
            entries,
            names,
            lookup: self.lookup.clone(),
            functions: self
                .functions
                .iter()
                .map(|(k, v)| (k.as_str(), *v))
                .collect(),
            types: self.types.clone(),
            methods: self
                .methods
                .iter()
                .map(|((t, n), v)| ((*t, n.as_str()), v.clone()))
                .collect(),
            families: self
                .families
                .iter()
                .map(|(k, v)| (k.as_str(), v.clone()))
                .collect(),
            primitive_families: self
                .primitive_families
                .iter()
                .map(|(k, v)| {
                    (
                        k.as_str(),
                        v.iter().map(|(c, i)| (c.as_str(), *i)).collect(),
                    )
                })
                .collect(),
            primitives: self
                .primitives
                .iter()
                .map(|((c, n), v)| ((c.as_str(), n.as_str()), *v))
                .collect(),
            aliases: self.aliases.clone(),
            effects: if changed {
                crate::reachability::effects::Cache::new(self.slots.len())
            } else {
                self.effects.thaw()
            },
            method_reads: std::cell::RefCell::new(self.method_reads.clone()),
            globals: self.globals.clone(),
            shared_variables: self
                .shared_variables
                .clone()
                .map_or_else(Default::default, std::cell::OnceCell::from),
        };
        crate::reachability::cost::finish("catalog-rebind", started);
        index
    }
}

impl<'a> ItemIndex<'a> {
    /// Append specialized methods without replacing an existing identity. New
    /// names invalidate negative dispatch/effect facts but keep storage indices.
    pub(in crate::reachability) fn append_generated(&mut self, generated: &[GeneratedDecl]) {
        let started = crate::reachability::cost::start();
        for g in generated {
            let t = self
                .program
                .types
                .values()
                .find(|t| t.name == g.receiver && t.module == g.module)
                .expect("generated owner");
            let groups = match &t.kind {
                TypeKind::Record { methods, .. } => vec![(None, methods)],
                TypeKind::Sum { variants } => {
                    variants.iter().map(|v| (Some(v.tag), &v.methods)).collect()
                }
            };
            for (variant, methods) in groups {
                let m = &methods[&g.decl.name];
                let mid = self
                    .program
                    .method_body_id(t, m, variant)
                    .unwrap_or_else(|| {
                        let owner = super::item_id(
                            self.program,
                            &t.module,
                            t.span,
                            brass_hir::ItemKind::Type,
                        );
                        brass_hir::MethodBodyId {
                            module: owner.module.clone(),
                            owner,
                            offset: m.decl.span.lo,
                            variant,
                            name: m.signature.name.clone(),
                        }
                    });
                let key = ItemKey::Body(BodyId::Method(mid));
                assert!(
                    !self.lookup.contains_key(&key),
                    "generated body already indexed"
                );
                let id = self.entries.len();
                self.methods
                    .entry((t.id, m.signature.name.as_str()))
                    .or_default()
                    .push(id);
                self.families
                    .entry(m.signature.name.as_str())
                    .or_default()
                    .push((t.id, id));
                self.push(
                    key,
                    &t.module,
                    m.decl.span,
                    Declaration::Method(t, m),
                    format!("{}.{}:{variant:?}", t.symbol, m.signature.name),
                );
            }
        }
        self.effects.extend(self.entries.len());
        crate::reachability::cost::finish("catalog-append", started);
    }
}
