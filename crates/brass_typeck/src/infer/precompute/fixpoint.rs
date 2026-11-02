//! The return-table fixpoint of the precompute pass: every function's and
//! method's light-pass return, re-inferred until no entry changes, with the
//! table reads that decide which entries a change makes stale.

use super::*;

impl<'a> Checker<'a> {
    fn requested_return(&self, entry: &ReturnEntry) -> bool {
        self.preparation.as_ref().is_none_or(|view| {
            entry
                .body(view)
                .is_some_and(|id| view.selection.body_roots.contains(id))
        })
    }

    fn extend_return_preparation(&mut self, entry: &ReturnEntry) {
        let Some(view) = &mut self.preparation else {
            return;
        };
        let view = Rc::make_mut(view);
        let body = entry.body(view).expect("catalog return identity").clone();
        debug_assert!(!view.selection.body_roots.contains(&body));
        tracing::debug!(target: "brass::item_preparation", ?body, "item: return dependency growth");
        let index = self
            .selection_index
            .get_or_insert_with(|| Rc::new(crate::reachability::ItemIndex::new(self.program)));
        view.set_selection(
            crate::reachability::Reachability::extend(
                index,
                &view.selection,
                crate::reachability::ItemKey::Body(body),
            )
            .into(),
        );
    }

    /// Infer every function and method return the light pass can derive, as
    /// one fixpoint over both tables. A selected context starts with its requested
    /// entries; observed return reads extend the same reachability closure before
    /// settlement. Absence during a round is provisional, never completed coverage.
    ///
    /// An entry depends on the entries of the callables its body calls -- a
    /// function's value may flow OUT of a method call (`http`'s `fetch` returns
    /// `client.fetch(path)`), a method may propagate another type's method
    /// (`Tcp.close` propagating `File.close`), and a chain of `f(n)! + 1` calls
    /// carries its callee's `Result` shape up one level per call. Every round
    /// re-infers, against the previous round's tables, each entry that read
    /// an entry the round before changed (see `precompute_return_entries`),
    /// so the result depends neither on the callables' names nor on the depth
    /// of a chain: a chain of any length settles within as many rounds as it
    /// has links.
    ///
    /// A FULLY-KNOWN function annotation is the declaration itself; it is
    /// entered once. A `T!` annotation is not fully known -- it names only the
    /// OK payload -- so its Err side is completed here like an inferred return.
    pub(in crate::infer) fn precompute_returns(&mut self) {
        let mut functions: Vec<String> = self.program.functions.keys().cloned().collect();
        functions.sort();
        let mut methods: Vec<(String, String, String, Vec<String>)> = self
            .program
            .types
            .values()
            .flat_map(|info| match &info.kind {
                TypeKind::Record { methods, .. } => methods
                    .keys()
                    .map(|m| {
                        (
                            info.symbol.clone(),
                            info.symbol.clone(),
                            m.clone(),
                            info.module.clone(),
                        )
                    })
                    .collect::<Vec<_>>(),
                TypeKind::Sum { variants } => variants
                    .iter()
                    .flat_map(|variant| {
                        variant.methods.keys().map(|m| {
                            (
                                format!("{}.{}", info.symbol, variant.name),
                                info.symbol.clone(),
                                m.clone(),
                                info.module.clone(),
                            )
                        })
                    })
                    .collect(),
            })
            .collect();
        methods.sort();
        let entries: Vec<ReturnEntry> = functions
            .into_iter()
            .map(ReturnEntry::Function)
            .chain(
                methods
                    .into_iter()
                    .map(
                        |(qualifier, self_type, method, module)| ReturnEntry::Method {
                            qualifier,
                            self_type,
                            method,
                            module,
                        },
                    ),
            )
            .collect();
        // Each round can propagate one more dependency edge. The extra round
        // observes stability after every entry has received its dependencies.
        self.precompute_return_entries(&entries, entries.len().saturating_add(1));
    }

    /// Settle `entries` within `limit` rounds. Round 0 infers requested entries; each
    /// later round re-infers only the entries whose inference READ an entry the
    /// previous round changed (the light pass records its table reads, see
    /// `Checker::light_reads`), which is what makes the fixpoint cheap: almost
    /// every entry settles in the first round.
    fn precompute_return_entries(&mut self, entries: &[ReturnEntry], limit: usize) {
        let mut readers: HashMap<ReturnKey, Vec<usize>> = HashMap::default();
        // Source coverage is immutable for this fixpoint. Project it once onto
        // entry indices rather than hashing source identities on every round.
        let covered: Option<Vec<bool>> = self.item_seed.as_ref().map(|view| {
            entries
                .iter()
                .map(|entry| {
                    entry
                        .body(view)
                        .is_some_and(|id| view.coverage.returns.contains(id))
                })
                .collect()
        });
        let mut active: Option<Vec<bool>> = self.preparation.as_ref().map(|_| {
            entries
                .iter()
                .map(|entry| self.requested_return(entry))
                .collect()
        });
        let mut dirty: Vec<usize> = (0..entries.len())
            .filter(|i| active.as_ref().is_none_or(|a| a[*i]))
            .collect();
        let lookup: HashMap<_, _> = if self.preparation.is_some() {
            entries
                .iter()
                .enumerate()
                .map(|(i, e)| (e.key(), i))
                .collect()
        } else {
            HashMap::default()
        };
        let mut abandoned: HashSet<usize> = HashSet::default();
        // Each entry's shape as of the round that last stored it. The stored
        // entry itself may since have been pinned by a reader's light pass (a
        // caller that pushes into the array a callee returns), so it is the
        // inference's own answer, not the table's current state, that decides
        // whether the entry changed.
        let mut shapes: Vec<Option<Type>> = vec![None; entries.len()];
        for round in 0..limit {
            let mut changing: Vec<usize> = Vec::new();
            let mut cursor = 0;
            while let Some(&index) = dirty.get(cursor) {
                cursor += 1;
                let previous = self.light_reads.replace(Some(HashSet::default()));
                let changed = self.precompute_return_entry(
                    &entries[index],
                    round,
                    &mut shapes[index],
                    covered.as_ref().is_some_and(|covered| covered[index]),
                );
                let reads = self.light_reads.replace(previous).unwrap_or_default();
                for key in reads {
                    if let Some(active) = &mut active
                        && let Some(&dependency) = lookup.get(&key)
                        && !active[dependency]
                    {
                        // A missing selected fact is not an Unknown answer. Close
                        // the actual dependency before allowing this fixpoint out.
                        self.extend_return_preparation(&entries[dependency]);
                        for (i, entry) in entries.iter().enumerate() {
                            if !active[i] && self.requested_return(entry) {
                                active[i] = true;
                                // Activation belongs to this round: delaying it
                                // would consume a propagation round without making
                                // the new entry available to any reader.
                                dirty.push(i);
                            }
                        }
                    }
                    let list = readers.entry(key).or_default();
                    if !list.contains(&index) {
                        list.push(index);
                    }
                }
                if changed && self.abandon_unbounded_return(&entries[index]) {
                    abandoned.insert(index);
                } else if changed {
                    changing.push(index);
                }
            }
            if changing.is_empty() {
                if let Some(view) = &mut self.preparation {
                    let view = Rc::make_mut(view);
                    for (i, _) in active
                        .as_ref()
                        .expect("selected preparation")
                        .iter()
                        .enumerate()
                        .filter(|(_, active)| **active)
                    {
                        if let Some(id) = entries[i].body(view) {
                            let id = id.clone();
                            view.coverage_mut().returns.insert(id);
                        }
                    }
                }
                return;
            }
            if round + 1 == limit {
                let changing: Vec<&ReturnEntry> = changing.iter().map(|&i| &entries[i]).collect();
                self.report_unconverged_returns(&changing);
                return;
            }
            let mut next: Vec<usize> = changing
                .iter()
                .flat_map(|&i| {
                    readers
                        .get(&entries[i].key())
                        .into_iter()
                        .flatten()
                        .copied()
                })
                .filter(|i| !abandoned.contains(i))
                .collect();
            next.sort_unstable();
            next.dedup();
            dirty = next;
        }
    }

    /// Stop inferring an entry whose type keeps nesting deeper: a recursive
    /// call that wraps its own result (`return [g(n - 1)]`) describes an
    /// infinite type, which no number of rounds settles. The callable is
    /// reported, its entry is left an open variable, and the fixpoint no longer
    /// re-infers it. Whether the entry was abandoned.
    fn abandon_unbounded_return(&mut self, entry: &ReturnEntry) -> bool {
        let (current, name, span) = match entry {
            ReturnEntry::Function(symbol) => {
                let info = &self.program.functions[symbol];
                (
                    self.function_returns.get(symbol),
                    info.signature.name.clone(),
                    info.decl.name_span,
                )
            }
            ReturnEntry::Method {
                qualifier, method, ..
            } => (
                self.method_returns
                    .get(&(qualifier.clone(), method.clone())),
                method.clone(),
                self.method_name_span(qualifier, method),
            ),
        };
        let Some(current) = current else {
            return false;
        };
        if type_depth(&self.resolve(current)) <= MAX_INFERRED_RETURN_DEPTH {
            return false;
        }
        self.errors.push(TypeError {
            message: format!(
                "cannot infer the return type of `{name}`: its recursive calls nest the \
                 result inside itself without end; annotate the return type of `{name}`"
            ),
            span,
        });
        let open = self.fresh_unknown();
        match entry {
            ReturnEntry::Function(symbol) => {
                self.function_returns.insert(symbol.clone(), open);
            }
            ReturnEntry::Method {
                qualifier, method, ..
            } => {
                self.method_returns
                    .insert((qualifier.clone(), method.clone()), open);
            }
        }
        true
    }

    /// `function_returns[symbol]`, recorded as a read of the precompute entry
    /// in progress (see `light_reads`) -- also when it is still absent, since
    /// its later arrival is a change the reader depends on.
    pub(in crate::infer) fn read_function_return(&self, symbol: &str) -> Option<Type> {
        if let Some(reads) = self.light_reads.borrow_mut().as_mut() {
            reads.insert(ReturnKey::Function(symbol.to_string()));
        }
        self.function_returns.get(symbol).cloned()
    }

    /// `method_returns[key]`, recorded like [`Self::read_function_return`].
    pub(in crate::infer) fn read_method_return(&self, key: &(String, String)) -> Option<Type> {
        if let Some(reads) = self.light_reads.borrow_mut().as_mut() {
            reads.insert(ReturnKey::Method(key.0.clone(), key.1.clone()));
        }
        self.method_returns.get(key).cloned()
    }

    /// Re-infer one table entry; whether its shape differs from `shape`, the
    /// one it was last stored with (up to the renumbering of its open
    /// variables). A changed entry is stored, and `shape` updated.
    fn precompute_return_entry(
        &mut self,
        entry: &ReturnEntry,
        round: usize,
        shape: &mut Option<Type>,
        covered: bool,
    ) -> bool {
        match entry {
            ReturnEntry::Function(name) => {
                let Some(info) = self.program.functions.get(name) else {
                    return false;
                };
                // A seeded context function's return is already in the table.
                if covered || self.seeded_module(&info.module) {
                    return false;
                }
                if round == 0 && self.item_seed.is_some() {
                    debug_assert!(
                        !covered && !self.function_returns.contains_key(name),
                        "uncovered function has a seeded return: {name}"
                    );
                    tracing::debug!(target: "brass::item_preparation", name, context = self.item_seed.as_ref().is_some_and(|v| v.functions.get(name).is_some_and(|id| v.catalog.contains(id))), "item: return fallback");
                }
                let fully_known = info
                    .signature
                    .ret_ty
                    .as_ref()
                    .is_some_and(brass_hir::is_fully_known);
                if fully_known && round > 0 && shape.is_some() {
                    return false;
                }
                let ty = self.function_return_entry(info);
                let current = self.canonical_return_shape(&ty);
                let changed = shape.as_ref() != Some(&current);
                if changed {
                    self.function_returns.insert(name.clone(), ty);
                    *shape = Some(current);
                }
                changed
            }
            ReturnEntry::Method {
                qualifier,
                self_type,
                method,
                module,
            } => {
                // A seeded context type's returns are already in the table.
                if self.seeded_module(module) {
                    return false;
                }
                let key = (qualifier.clone(), method.clone());
                if covered {
                    return false;
                }
                if round == 0 && self.item_seed.is_some() {
                    debug_assert!(
                        !covered && !self.method_returns.contains_key(&key),
                        "uncovered method has a seeded return: {key:?}"
                    );
                    tracing::debug!(target: "brass::item_preparation", qualifier, method, context = self.item_seed.as_ref().is_some_and(|v| v.methods.get(&key).is_some_and(|id| v.catalog.contains(id))), "item: return fallback");
                }
                // As in `function_return_entry`: the light pass resolves names
                // against the current module, which here is the TYPE's.
                let saved = std::mem::replace(&mut self.current_module, module.clone());
                let (ty, has_props) = self.infer_method_return(qualifier, self_type, method);
                self.current_module = saved;
                if has_props {
                    self.method_return_props.insert(key.clone());
                }
                let current = self.canonical_return_shape(&ty);
                let changed = shape.as_ref() != Some(&current);
                if changed {
                    self.method_returns.insert(key, ty);
                    *shape = Some(current);
                }
                changed
            }
        }
    }

    /// The name span of the method a `method_returns` key names. Keys carry
    /// storage identities, independent of the caller's source scope.
    fn method_name_span(&self, qualifier: &str, method: &str) -> Span {
        let (symbol, variant) = qualifier
            .split_once('.')
            .map_or((qualifier, None), |(s, v)| (s, Some(v)));
        match &self.program.types[symbol].kind {
            TypeKind::Record { methods, .. } => methods[method].decl.name_span,
            TypeKind::Sum { variants } => {
                variants
                    .iter()
                    .find(|v| Some(v.name.as_str()) == variant)
                    .expect("method entry's variant")
                    .methods[method]
                    .decl
                    .name_span
            }
        }
    }

    /// The defensive internal error for a return table that did not settle
    /// within its round budget, reported at each changing callable's name.
    fn report_unconverged_returns(&mut self, changing: &[&ReturnEntry]) {
        let names = changing
            .iter()
            .map(|entry| match entry {
                ReturnEntry::Function(name) => name.clone(),
                ReturnEntry::Method {
                    qualifier, method, ..
                } => format!("{qualifier}.{method}"),
            })
            .collect::<Vec<_>>()
            .join(", ");
        for entry in changing {
            let span = match entry {
                ReturnEntry::Function(name) => self.program.functions[name].decl.name_span,
                ReturnEntry::Method {
                    qualifier, method, ..
                } => self.method_name_span(qualifier, method),
            };
            self.errors.push(TypeError {
                message: format!(
                    "internal compiler error: return inference did not converge; changing \
                     entries: {names}"
                ),
                span,
            });
        }
    }
}

/// How deeply an inferred return type may nest before the precompute fixpoint
/// treats it as the unbounded growth of a self-wrapping recursion. Declared
/// types nest far less; this only has to be out of their reach.
const MAX_INFERRED_RETURN_DEPTH: usize = 64;

/// How deeply `ty`'s type constructors nest.
fn type_depth(ty: &Type) -> usize {
    match ty {
        Type::Record(n) | Type::Sum(n) => {
            1 + n
                .substitution
                .iter()
                .map(|(_, t)| type_depth(t))
                .max()
                .unwrap_or(0)
        }
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Nullable(inner)
        | Type::ConstOf(inner)
        | Type::Mut(inner)
        | Type::Ref(inner) => 1 + type_depth(inner),
        Type::Tuple(elems) => 1 + elems.iter().map(type_depth).max().unwrap_or(0),
        Type::Fun(params, ret) => {
            1 + params
                .iter()
                .chain(std::iter::once(ret.as_ref()))
                .map(type_depth)
                .max()
                .unwrap_or(0)
        }
        _ => 0,
    }
}

/// One entry of the return tables the precompute fixpoint settles: a free
/// function by its symbol, or a method by its qualifier (the record's storage
/// symbol, or `Sum.Variant`), receiver type, name and defining module.
enum ReturnEntry {
    Function(String),
    Method {
        qualifier: String,
        self_type: String,
        method: String,
        module: Vec<String>,
    },
}

impl ReturnEntry {
    fn body<'v>(
        &self,
        view: &'v crate::reachability::AnalysisView,
    ) -> Option<&'v crate::reachability::BodyId> {
        match self {
            Self::Function(symbol) => view.functions.get(symbol),
            Self::Method {
                qualifier, method, ..
            } => view.methods.get(&(qualifier.clone(), method.clone())),
        }
    }

    fn key(&self) -> ReturnKey {
        match self {
            ReturnEntry::Function(symbol) => ReturnKey::Function(symbol.clone()),
            ReturnEntry::Method {
                qualifier, method, ..
            } => ReturnKey::Method(qualifier.clone(), method.clone()),
        }
    }
}

/// A return-table key: `function_returns`' symbol, or `method_returns`'
/// (qualifier, method name).
#[derive(Clone, PartialEq, Eq, Hash)]
pub(in crate::infer) enum ReturnKey {
    Function(String),
    Method(String, String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn method_return_budget_reports_changing_symbols_at_method_names() {
        // Exhausting an intentionally short budget pins the otherwise defensive
        // ICE, including the changing identity and the exact method-name span.
        let source = "type Item = { value: int32 }\nfun Item.get(self) { return self.value }\ntype Choice = | One { value: int32 }\nfun Choice.get(self) { return self.value }";
        let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["main".into()],
            ast: brass_parser::parse(source).unwrap(),
        }]);
        assert!(errors.is_empty());
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        checker.precompute_return_entries(
            &[
                ReturnEntry::Method {
                    qualifier: "Item".into(),
                    self_type: "Item".into(),
                    method: "get".into(),
                    module: vec!["main".into()],
                },
                ReturnEntry::Method {
                    qualifier: "Choice.One".into(),
                    self_type: "Choice".into(),
                    method: "get".into(),
                    module: vec!["main".into()],
                },
            ],
            1,
        );
        assert_eq!(checker.errors.len(), 2);
        assert_eq!(
            checker.errors[0].message,
            "internal compiler error: return inference did not converge; changing entries: Item.get, Choice.One.get"
        );
        let start = source.find("get").unwrap();
        assert_eq!(checker.errors[0].span, Span::new(start, start + 3));
        assert_eq!(checker.errors[1].message, checker.errors[0].message);
        let start = source.rfind("get").unwrap();
        assert_eq!(checker.errors[1].span, Span::new(start, start + 3));
    }
}
