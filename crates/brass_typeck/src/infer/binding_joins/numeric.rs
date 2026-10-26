//! Literal provenance and the least numeric storage solution of a body.

use super::super::*;

/// Copy-on-write lexical origins, absent on the ordinary checking path.
#[derive(Clone, Default)]
pub(in crate::infer) struct Origins(Option<Rc<HashMap<String, usize>>>);

impl Origins {
    /// The origin of a numeric binding in this lexical frame.
    pub(in crate::infer) fn get(&self, name: &str) -> Option<&usize> {
        self.0.as_ref()?.get(name)
    }

    /// Whether a lexical binding carries a numeric origin.
    pub(in crate::infer) fn contains_key(&self, name: &str) -> bool {
        self.get(name).is_some()
    }

    /// Associate a lexical name with its root in the current negotiation.
    pub(in crate::infer) fn insert(&mut self, name: String, origin: usize) {
        Rc::make_mut(self.0.get_or_insert_with(Default::default)).insert(name, origin);
    }

    /// Shadowing a binding ends its previous origin edge in this frame.
    pub(in crate::infer) fn remove(&mut self, name: &str) {
        if self.contains_key(name) {
            Rc::make_mut(self.0.as_mut().unwrap()).remove(name);
        }
    }
}

/// A literal floor or a lexical root whose demands remain negotiable.
#[derive(Clone, Debug, PartialEq)]
pub(in crate::infer) enum Source {
    Root(usize),
    Value(Type),
    Arithmetic(Type, Vec<usize>),
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct Site {
    calls: Vec<Span>,
    span: Span,
}

#[derive(Clone)]
struct Root {
    site: Site,
    floor: Type,
    ty: Type,
    global: bool,
    parents: Vec<usize>,
}

#[derive(Clone)]
struct NumericOwner {
    parent: Option<usize>,
    calls: Vec<Span>,
    body: Span,
    entries: std::collections::BTreeMap<Vec<(usize, usize)>, Type>,
    storage: bool,
}

#[derive(Clone)]
enum ReturnOrigin {
    Fixed,
    Argument(usize),
    Value(Type),
    Arithmetic(Type, Vec<usize>),
}

#[derive(Clone)]
struct PureReplay {
    origin: ReturnOrigin,
    layouts: Vec<(Vec<Span>, Span, brass_hir::NumericLayout)>,
    arguments: Vec<(Site, Type)>,
}

/// Instance-local literal provenance; ordinary types stay concrete and unchanged.
#[derive(Clone, Default)]
pub(in crate::infer) struct NumericState {
    /// An enclosing negotiation owns nested calls until its final body walk ends.
    pub(in crate::infer) active: bool,
    /// A private walk is collecting origins and stores rather than publishing them.
    pub(in crate::infer) probing: bool,
    /// The settled walk changes a binding or argument from ordinary inference.
    pub(in crate::infer) changed: bool,
    bindings: HashMap<Site, Type>,
    argument_types: HashMap<Site, Type>,
    /// Lexical call path distinguishing repeated source bodies during negotiation.
    pub(in crate::infer) calls: Vec<Span>,
    candidates: HashMap<Site, Type>,
    pure_returns: HashMap<ElaborationMemoKey, PureReplay>,
    layouts: HashMap<(Vec<Span>, Span), brass_hir::NumericLayout>,
    owners: Vec<NumericOwner>,
    owner_stack: Vec<usize>,
    roots: Vec<Root>,
    expressions: HashMap<Site, Source>,
    /// Origins supplied to the parameter frame of each lexical call.
    pub(in crate::infer) arguments: HashMap<Vec<Span>, Vec<Option<Source>>>,
    /// Live return origins for each active callable, innermost last.
    pub(in crate::infer) returns: Vec<Vec<Option<Source>>>,
    /// The named call result passed back to its caller after checking a body.
    pub(in crate::infer) result: Option<Source>,
    /// The closure result retained across the application solver snapshot.
    pub(in crate::infer) closure_result: Option<Source>,
    observed: HashMap<Site, Vec<brass_typesys::JoinOperand>>,
    /// Top-level stores may settle global origins in this negotiation.
    pub(in crate::infer) module_scope: bool,
    /// Settled module binding types exported before callable bodies are checked.
    pub(in crate::infer) globals: HashMap<(Vec<String>, String), Type>,
}

impl Checker<'_> {
    /// Whether an independent body needs an origin negotiation at its own root.
    pub(in crate::infer) fn numeric_body_needs_settlement(
        &self,
        body: &Block,
        scopes: &ScopeStack,
    ) -> bool {
        !self.numeric_body_is_settled()
            && self.numeric_unsettled_body_needs_settlement(body, scopes)
    }

    /// Structural root decision after the ordinary-instance certificate declined.
    pub(in crate::infer) fn numeric_unsettled_body_needs_settlement(
        &self,
        body: &Block,
        scopes: &ScopeStack,
    ) -> bool {
        if let Some(index) = self.numeric_eligibility.get() {
            return !index.body(body.span);
        }
        if eligibility::Eligibility::local(&body.stmts, true, |callee, inputs| match callee {
            Expr::Ident(name, _) => {
                self.numeric_local_call(name, self.lookup(scopes, name).is_some(), inputs)
            }
            Expr::Field(base, name, _) => {
                let receiver = match &**base {
                    Expr::Ident(name, _) => self.lookup(scopes, name),
                    Expr::SelfExpr(_) => self.lookup(scopes, "self"),
                    _ => None,
                };
                let methods = if let Some(receiver) = receiver {
                    let receiver = self.resolve(&receiver);
                    if !brass_hir::is_fully_known(&receiver) {
                        return None;
                    }
                    self.methods_for_type(&receiver, name)?
                } else {
                    let qualifier = match &**base {
                        Expr::Ident(name, _) => name.as_str(),
                        Expr::SelfExpr(_) => "Self",
                        _ => return None,
                    };
                    vec![self.method_for_qualifier(qualifier, name)?]
                };
                Some((
                    methods.iter().all(|method| {
                        method
                            .signature
                            .params
                            .iter()
                            .all(|param| param.name == "self" || param.ty.is_some())
                            || method
                                .method
                                .body
                                .as_ref()
                                .is_some_and(|body| eligibility::Eligibility::leaf(&body.stmts))
                    }),
                    false,
                ))
            }
            _ => None,
        }) {
            return false;
        }
        !self.numeric_eligibility().body(body.span)
    }

    /// An intrinsic-only body certifies its entire subtree without a program graph.
    pub(in crate::infer) fn numeric_body_is_locally_closed(
        &self,
        body: &Block,
        scopes: &ScopeStack,
    ) -> bool {
        eligibility::Eligibility::local(&body.stmts, false, |callee, _| {
            let Expr::Ident(name, _) = callee else {
                return None;
            };
            self.numeric_intrinsic(name, self.lookup(scopes, name).is_some())
                .then_some((true, true))
        })
    }

    /// The same local-first decision for top-level statements.
    pub(in crate::infer) fn numeric_init_needs_settlement(&self, init: &ModuleInit) -> bool {
        if let Some(index) = self.numeric_eligibility.get() {
            return !index.init(&init.path);
        }
        if eligibility::Eligibility::local(&init.stmts, true, |callee, inputs| {
            let Expr::Ident(name, _) = callee else {
                return None;
            };
            self.numeric_local_call(
                name,
                self.global_defs
                    .values()
                    .any(|defs| defs.contains_key(name)),
                inputs,
            )
        }) {
            return false;
        }
        !self.numeric_eligibility().init(&init.path)
    }

    fn numeric_globals_need_settlement(&self, init: &ModuleInit) -> bool {
        if eligibility::Eligibility::local(&init.stmts, false, |callee, _| {
            let Expr::Ident(name, _) = callee else {
                return None;
            };
            self.numeric_intrinsic(
                name,
                self.global_defs
                    .values()
                    .any(|defs| defs.contains_key(name)),
            )
            .then_some((true, true))
        }) {
            return false;
        }
        !self.numeric_eligibility().transitive_init(&init.path)
    }

    fn numeric_local_call(&self, name: &str, bound: bool, inputs: bool) -> Option<(bool, bool)> {
        if self.numeric_intrinsic(name, bound) {
            return Some((true, true));
        }
        if bound {
            return None;
        }
        self.lookup_function(name).map(|info| {
            (
                inputs
                    && (info.signature.params.iter().all(|param| param.ty.is_some())
                        || eligibility::Eligibility::leaf(&info.decl.body.stmts)),
                info.signature.ret_ty.is_some(),
            )
        })
    }

    fn numeric_intrinsic(&self, name: &str, bound: bool) -> bool {
        matches!(name, "typeof" | "fields")
            || (!matches!(name, "spawn" | "with" | "_with_all")
                && self.calls_prelude_function(name, bound)
                && self.builtin_function_type_light(name).is_some())
    }

    /// Structural eligibility shared by all roots in this checker.
    pub(in crate::infer) fn numeric_eligibility(&self) -> &eligibility::Eligibility {
        self.numeric_eligibility.get_or_init(|| {
            eligibility::Eligibility::new(self.program, |name| {
                self.builtin_function_type_light(name).is_some()
            })
        })
    }

    /// A storage-free call graph cannot need a standalone numeric retry.
    /// Build the immutable graph only when ordinary seed/memo proofs are absent.
    pub(in crate::infer) fn numeric_body_has_no_storage(&self, body: Span) -> bool {
        self.numeric_pure_spans
            .get_or_init(|| {
                let pure = pure::bodies(self.program);
                self.program
                    .functions
                    .values()
                    .filter(|info| pure.contains(&info.symbol))
                    .map(|info| info.decl.body.span)
                    .collect()
            })
            .contains(&body)
    }

    /// A checked ordinary instance certifies zero growth at its unchanged inputs.
    pub(in crate::infer) fn numeric_body_is_settled(&self) -> bool {
        if !self.numeric_seed_ordinary {
            return false;
        }
        let Some(tag) = self.current_instance() else {
            return false;
        };
        let brass_hir::InstanceCallable::Function(symbol) = &tag.callable else {
            return self.numeric_fixed_method(&tag);
        };
        let Some(info) = self.program.functions.get(symbol) else {
            return false;
        };
        // Annotated parameters keep their declaration types at every demand.
        // The context seed already checked that same body and environment.
        if self.seeded_module(&info.module)
            && info.signature.params.iter().all(|param| {
                param
                    .resolved_ty
                    .as_ref()
                    .is_some_and(brass_hir::is_fully_known)
            })
        {
            return true;
        }
        // A clean ordinary elaboration certifies this effective argument tuple.
        // This proof is disabled after any numeric retry, whose entries may
        // describe a body that required negotiation to satisfy its demands.
        let checked = |args: &[Type]| {
            self.elaboration_memo_key("fn", symbol, None, args, &[])
                .is_some_and(|context| self.elaboration_memo.contains_key(&context.key))
        };
        if checked(&tag.args) {
            return true;
        }
        // Runtime demands can spell an argument before its annotated widening.
        // The body still sees the annotation, so its ordinary check at those
        // effective inputs is the same zero-growth proof.
        let effective: Vec<_> = info
            .signature
            .params
            .iter()
            .zip(&tag.args)
            .map(|(param, arg)| {
                param
                    .resolved_ty
                    .as_ref()
                    .filter(|ty| brass_hir::is_fully_known(ty))
                    .unwrap_or(arg)
                    .clone()
            })
            .collect();
        effective != tag.args && checked(&effective)
    }

    // A monomorphic declaring type and annotated arguments reproduce the
    // context seed's method environment, including its fixed Self fields.
    fn numeric_fixed_method(&self, tag: &instances::InstanceTag) -> bool {
        let brass_hir::InstanceCallable::Method { owner, method } = &tag.callable else {
            return false;
        };
        let Some(info) = self.program.types.get(owner) else {
            return false;
        };
        if !self.seeded_module(&info.module)
            || !self
                .global_defs
                .values()
                .flat_map(|defs| defs.values())
                .all(brass_hir::is_fully_known)
            || !info.slots.is_empty()
            || self
                .schemes
                .get(owner)
                .is_some_and(|scheme| !scheme.params.is_empty())
        {
            return false;
        }
        let fields_known = |fields: &[brass_hir::FieldInfo]| {
            fields.iter().all(|field| {
                field
                    .resolved_ty
                    .as_ref()
                    .is_some_and(brass_hir::is_fully_known)
            })
        };
        let checked = |method: &brass_hir::MethodInfo| {
            method.signature.params.iter().all(|param| {
                if param.name == "self" {
                    tag.args
                        .first()
                        .is_some_and(|ty| self.resolve(ty) == info.type_ref())
                } else {
                    param
                        .resolved_ty
                        .as_ref()
                        .is_some_and(brass_hir::is_fully_known)
                }
            })
        };
        match &info.kind {
            brass_hir::TypeKind::Record { fields, methods } => {
                fields_known(fields) && methods.get(method).is_some_and(checked)
            }
            brass_hir::TypeKind::Sum { variants } => {
                !variants.is_empty()
                    && variants.iter().all(|variant| {
                        fields_known(&variant.fields)
                            && variant.methods.get(method).is_some_and(checked)
                    })
            }
        }
    }

    /// Begin a body independently of calls evaluated in its argument list.
    pub(in crate::infer) fn enter_numeric_body(&mut self, body: Span) {
        if self.numeric.probing {
            let id = self.numeric.owners.len();
            self.numeric.owners.push(NumericOwner {
                parent: self.numeric.owner_stack.last().copied(),
                calls: self.numeric.calls.clone(),
                body,
                entries: Default::default(),
                storage: false,
            });
            self.numeric.owner_stack.push(id);
        }
    }

    /// Complete a concrete storage contract and include its nested effects in its caller.
    pub(in crate::infer) fn leave_numeric_body(&mut self, exports_origin: bool) {
        if !self.numeric.probing {
            return;
        }
        let Some(id) = self.numeric.owner_stack.pop() else {
            return;
        };
        let owner = &self.numeric.owners[id];
        if !owner.storage || !exports_origin {
            return;
        }
        let layout: brass_hir::NumericLayout = owner
            .entries
            .iter()
            .map(|(site, ty)| (site.clone(), ty.clone()))
            .collect::<Vec<_>>()
            .into();
        self.numeric
            .layouts
            .insert((owner.calls.clone(), owner.body), layout.clone());
        if let Some(parent) = owner.parent {
            let mut prefix: Vec<_> = owner
                .calls
                .iter()
                .skip(self.numeric.owners[parent].calls.len())
                .map(|span| (span.lo, span.hi))
                .collect();
            prefix.push((owner.body.lo, owner.body.hi));
            self.numeric.owners[parent].storage = true;
            for (path, ty) in layout.iter() {
                let mut path_here = prefix.clone();
                path_here.extend(path);
                self.numeric.owners[parent]
                    .entries
                    .insert(path_here, ty.clone());
            }
        }
    }

    /// The completed storage contract for this call's body, independent of literal spelling.
    pub(in crate::infer) fn numeric_layout_for(
        &self,
        body: Span,
    ) -> Option<brass_hir::NumericLayout> {
        self.numeric
            .layouts
            .get(&(self.numeric.calls.clone(), body))
            .filter(|layout| !layout.is_empty())
            .cloned()
    }

    /// Recursive calls reuse the active completed body at the same effective inputs.
    pub(in crate::infer) fn numeric_callable_layout(
        &self,
        callable: &brass_hir::InstanceCallable,
        args: &[Type],
        body: Span,
    ) -> Option<brass_hir::NumericLayout> {
        if !self.numeric.probing {
            let args: Vec<_> = args.iter().map(|ty| self.resolve(ty)).collect();
            if let Some(tag) = self.instance_stack.iter().rev().find(|tag| {
                &tag.callable == callable
                    && tag
                        .args
                        .iter()
                        .map(|ty| self.resolve(ty))
                        .eq(args.iter().cloned())
            }) {
                return tag.numeric_layout.clone();
            }
        }
        self.numeric_layout_for(body)
    }

    fn numeric_storage_kind(&self, argument: bool) -> brass_hir::TypedExprKind {
        use brass_hir::TypedExprKind::*;
        match (self.current_instance().is_some(), argument) {
            (true, false) => InstanceNumericBinding,
            (true, true) => InstanceNumericArgument,
            (false, false) => NumericBinding,
            (false, true) => NumericArgument,
        }
    }

    // A dedicated generic body can approximate an open operand at a literal's
    // default. Such observations must not pin calls the checker has not yet
    // elaborated at their concrete inputs.
    fn numeric_instance_is_concrete(&self) -> bool {
        self.current_instance().is_some_and(|tag| {
            tag.args
                .iter()
                .all(|ty| brass_hir::is_fully_known(&self.resolve(ty)))
        })
    }

    /// Record concrete storage even for a closed binding, so equal effective bodies share a key.
    pub(in crate::infer) fn note_numeric_binding_layout(&mut self, pat: &Pattern, ty: &Type) {
        if !self.numeric_enabled || self.discarded_walks > 0 {
            return;
        }
        let Pattern::Binding(_, None, span) = pat else {
            return;
        };
        if !self.numeric.probing {
            if self.numeric_instance_is_concrete()
                && matches!(self.resolve(ty), Type::Int(_) | Type::Float(_))
            {
                self.record_typed(
                    self.numeric_storage_kind(false),
                    *span,
                    ty.clone(),
                    Constness::Unknown,
                );
            }
            return;
        }
        self.note_numeric_layout_slot(*span, ty);
    }

    fn note_numeric_layout_slot(&mut self, span: Span, ty: &Type) {
        if !self.numeric.probing || self.discarded_walks > 0 {
            return;
        }
        let ty = self.resolve(ty);
        if !matches!(ty, Type::Int(_) | Type::Float(_)) {
            return;
        }
        if let Some(id) = self.numeric.owner_stack.last().copied() {
            let owner = &mut self.numeric.owners[id];
            let mut path: Vec<_> = self
                .numeric
                .calls
                .iter()
                .skip(owner.calls.len())
                .map(|span| (span.lo, span.hi))
                .collect();
            path.push((span.lo, span.hi));
            owner.entries.insert(path, ty);
        }
    }

    /// Whether the immutable call graph permits parameter-relative provenance replay.
    pub(in crate::infer) fn numeric_pure_body(&self, symbol: &str) -> bool {
        self.numeric_pure_bodies.contains(symbol)
            || (self.numeric_closed_bodies.contains(symbol)
                && self
                    .numeric
                    .arguments
                    .get(&self.numeric.calls)
                    .is_none_or(|args| args.iter().all(Option::is_none)))
    }

    /// Separate provisional memo entries by argument provenance and its default floor.
    pub(in crate::infer) fn numeric_memo_flavor(&self, context: &mut ElaborationMemoContext) {
        context.key.callable.push_str(":numeric-probe");
        let mut classes = HashMap::default();
        let aliases: Vec<_> = self
            .numeric
            .arguments
            .get(&self.numeric.calls)
            .into_iter()
            .flatten()
            .map(|origin| match origin {
                Some(Source::Root(id)) => {
                    let next = classes.len();
                    Some(*classes.entry(*id).or_insert(next))
                }
                _ => None,
            })
            .collect();
        context
            .key
            .callable
            .push_str(&format!(":origins={aliases:?}"));
        context.key.scheme_inputs = self
            .numeric
            .arguments
            .get(&self.numeric.calls)
            .map(|args| {
                args.iter()
                    .map(|source| source.as_ref().map(|source| self.numeric_floor(source)))
                    .collect()
            })
            .unwrap_or_default();
    }

    /// Restore a pure body's return origin without replaying private root identifiers.
    pub(in crate::infer) fn replay_numeric_origin(
        &mut self,
        context: &ElaborationMemoContext,
        body: Span,
    ) {
        let Some(replay) = self.numeric.pure_returns.get(&context.key).cloned() else {
            return;
        };
        self.numeric.changed |= !replay.layouts.is_empty() || !replay.arguments.is_empty();
        for (suffix, body, layout) in &replay.layouts {
            let mut calls = self.numeric.calls.clone();
            calls.extend(suffix);
            self.numeric.layouts.insert((calls, *body), layout.clone());
        }
        for (relative, ty) in &replay.arguments {
            let mut site = relative.clone();
            site.calls = self
                .numeric
                .calls
                .iter()
                .chain(&relative.calls)
                .copied()
                .collect();
            self.numeric.argument_types.insert(site, ty.clone());
        }
        let layout = self.numeric_layout_for(body).unwrap_or_default();
        self.enter_numeric_body(body);
        if let Some(owner) = self.numeric.owner_stack.last().copied() {
            self.numeric.owners[owner].storage = !layout.is_empty();
            self.numeric.owners[owner]
                .entries
                .extend(layout.iter().cloned());
        }
        self.leave_numeric_body(true);
        self.numeric.result = (|| match &replay.origin {
            ReturnOrigin::Fixed => None,
            ReturnOrigin::Value(ty) => Some(Source::Value(ty.clone())),
            ReturnOrigin::Argument(index) => self
                .numeric
                .arguments
                .get(&self.numeric.calls)
                .and_then(|args| args.get(*index))
                .cloned()
                .flatten(),
            ReturnOrigin::Arithmetic(floor, indices) => {
                let args = self
                    .numeric
                    .arguments
                    .get(&self.numeric.calls)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                let parents: Option<Vec<_>> = indices
                    .iter()
                    .map(|index| match args.get(*index)? {
                        Some(Source::Root(id)) => Some(*id),
                        _ => None,
                    })
                    .collect();
                Some(Source::Arithmetic(floor.clone(), parents?))
            }
        })();
    }

    /// Retain only return origins expressed entirely in the memo's explicit inputs.
    pub(in crate::infer) fn save_numeric_origin(
        &mut self,
        context: &ElaborationMemoContext,
    ) -> bool {
        let origin = match &self.numeric.result {
            None => ReturnOrigin::Fixed,
            Some(Source::Value(ty)) => ReturnOrigin::Value(ty.clone()),
            Some(Source::Arithmetic(floor, parents)) => {
                let args = self.numeric.arguments.get(&self.numeric.calls);
                let indices: Option<Vec<_>> = parents
                    .iter()
                    .map(|parent| {
                        args?
                            .iter()
                            .position(|arg| arg.as_ref() == Some(&Source::Root(*parent)))
                    })
                    .collect();
                let Some(indices) = indices else { return false };
                ReturnOrigin::Arithmetic(floor.clone(), indices)
            }
            Some(root @ Source::Root(_)) => {
                let Some(index) = self
                    .numeric
                    .arguments
                    .get(&self.numeric.calls)
                    .and_then(|args| args.iter().position(|arg| arg.as_ref() == Some(root)))
                else {
                    return false;
                };
                ReturnOrigin::Argument(index)
            }
        };
        let prefix = &self.numeric.calls;
        let layouts = self
            .numeric
            .layouts
            .iter()
            .filter(|((calls, _), _)| calls.starts_with(prefix))
            .map(|((calls, body), layout)| (calls[prefix.len()..].to_vec(), *body, layout.clone()))
            .collect();
        let arguments = self
            .numeric
            .argument_types
            .iter()
            .filter(|(site, _)| site.calls.starts_with(prefix))
            .map(|(site, ty)| {
                (
                    Site {
                        calls: site.calls[prefix.len()..].to_vec(),
                        span: site.span,
                    },
                    ty.clone(),
                )
            })
            .collect();
        self.numeric.pure_returns.insert(
            context.key.clone(),
            PureReplay {
                origin,
                layouts,
                arguments,
            },
        );
        true
    }

    fn numeric_site(&self, span: Span) -> Site {
        Site {
            calls: self.numeric.calls.clone(),
            span,
        }
    }

    fn numeric_floor(&self, source: &Source) -> Type {
        match source {
            Source::Root(id) => self.numeric.roots[*id].floor.clone(),
            Source::Value(ty) | Source::Arithmetic(ty, _) => ty.clone(),
        }
    }

    fn numeric_parents(source: &Source) -> Vec<usize> {
        match source {
            Source::Root(id) => vec![*id],
            Source::Value(_) => Vec::new(),
            Source::Arithmetic(_, parents) => parents.clone(),
        }
    }

    /// Retrieve the origin recorded for this expression in its current call path.
    pub(in crate::infer) fn numeric_source(&self, expr: &Expr) -> Option<Source> {
        self.numeric
            .expressions
            .get(&self.numeric_site(expr.span()))
            .cloned()
    }

    /// Keep provenance through literal arithmetic and lexical copies, never field reads.
    pub(in crate::infer) fn note_numeric_expression(&mut self, expr: &Expr, scopes: &ScopeStack) {
        if !self.numeric.probing || self.discarded_walks > 0 {
            return;
        }
        let source = if let Some(literal) = brass_typesys::NumericLiteral::of_expr(expr) {
            literal
                .fits(&literal.default_type())
                .then(|| Source::Value(literal.default_type()))
        } else {
            match expr {
                Expr::Ident(name, _) => scopes
                    .iter()
                    .rev()
                    .find(|frame| frame.contains_key(name))
                    .and_then(|frame| frame.numeric.get(name))
                    .copied()
                    .map(Source::Root),
                Expr::Unary(UnaryOp::Neg | UnaryOp::BitNot, inner, _) => {
                    self.numeric_source(inner).map(|source| {
                        Source::Arithmetic(
                            self.numeric_floor(&source),
                            Self::numeric_parents(&source),
                        )
                    })
                }
                Expr::Binary(op, left, right, _) => self
                    .numeric_source(left)
                    .zip(self.numeric_source(right))
                    .and_then(|(a, b)| {
                        let mut parents = Self::numeric_parents(&a);
                        parents.extend(Self::numeric_parents(&b));
                        parents.sort_unstable();
                        parents.dedup();
                        let (a, b) = (self.numeric_floor(&a), self.numeric_floor(&b));
                        brass_typesys::numeric_binary(
                            *op,
                            brass_typesys::NumericOperand::new(
                                &a,
                                brass_typesys::NumericLiteral::of_expr(left),
                            ),
                            brass_typesys::NumericOperand::new(
                                &b,
                                brass_typesys::NumericLiteral::of_expr(right),
                            ),
                        )
                        .ok()
                        .map(|typing| typing.result)
                        .filter(|ty| matches!(ty, Type::Int(_) | Type::Float(_)))
                        .map(|ty| Source::Arithmetic(ty, parents))
                    }),
                Expr::Call(..) => self.numeric_source(expr),
                Expr::Block(block, _) => block.stmts.last().and_then(|stmt| match stmt {
                    Stmt::Expr(expr) => self.numeric_source(expr),
                    _ => None,
                }),
                _ => None,
            }
        };
        let site = self.numeric_site(expr.span());
        if let Some(source) = source {
            self.numeric.expressions.insert(site, source);
        } else {
            self.numeric.expressions.remove(&site);
        }
    }

    /// Retain a call's return origin in its caller's lexical context.
    pub(in crate::infer) fn note_numeric_call(&mut self, span: Span) {
        let site = self.numeric_site(span);
        if let Some(source) = self.numeric.result.take() {
            self.numeric.expressions.insert(site, source);
        } else {
            self.numeric.expressions.remove(&site);
        }
    }

    fn numeric_root(&mut self, site: Span, source: Source, actual: &Type) -> usize {
        if let Source::Root(id) = source {
            return id;
        }
        let floor = self.numeric_floor(&source);
        let parents = Self::numeric_parents(&source);
        let site = self.numeric_site(site);
        let ty = self.numeric.candidates.get(&site).unwrap_or(&floor).clone();
        let id = self.numeric.roots.len();
        self.numeric.roots.push(Root {
            site: site.clone(),
            floor: floor.clone(),
            ty,
            global: false,
            parents,
        });
        let actual = self.resolve(actual);
        self.numeric.observed.entry(site).or_default().extend([
            brass_typesys::JoinOperand::value(floor),
            brass_typesys::JoinOperand::value(actual),
        ]);
        id
    }

    /// Bind a numeric origin beside its settled type, preserving ordinary scope lookup.
    pub(in crate::infer) fn numeric_binding_type(
        &mut self,
        pat: &Pattern,
        expr: &Expr,
        actual: &Type,
        scopes: &mut ScopeStack,
    ) -> Type {
        if !self.numeric.active || self.discarded_walks > 0 {
            return actual.clone();
        }
        let Pattern::Binding(name, None, span) = pat else {
            return actual.clone();
        };
        if !self.numeric.probing {
            let Some(ty) = self
                .numeric
                .bindings
                .get(&self.numeric_site(*span))
                .cloned()
            else {
                return actual.clone();
            };
            self.expect_expr_assignable(actual, &ty, expr);
            scopes.last_mut().unwrap().insert(name.clone(), ty.clone());
            self.record_typed(
                self.numeric_storage_kind(false),
                *span,
                ty.clone(),
                Constness::Unknown,
            );
            return ty;
        }
        let Some(source) = self.numeric_source(expr) else {
            return actual.clone();
        };
        if !matches!(self.resolve(actual), Type::Int(_) | Type::Float(_)) {
            return actual.clone();
        }
        let id = self.numeric_root(*span, source, actual);
        if self.numeric.module_scope && scopes.len() == 1 && self.return_contexts.is_empty() {
            self.numeric.roots[id].global = true;
        }
        let ty = self.numeric.roots[id].ty.clone();
        if ty != self.resolve(actual) {
            self.numeric.changed = true;
            if let Some(owner) = self.numeric.owner_stack.last().copied() {
                self.numeric.owners[owner].storage = true;
            }
        }
        self.numeric
            .bindings
            .insert(self.numeric_site(*span), ty.clone());
        self.expect_expr_assignable(actual, &ty, expr);
        scopes.last_mut().unwrap().insert(name.clone(), ty.clone());
        scopes.last_mut().unwrap().numeric.insert(name.clone(), id);
        self.record_typed(
            self.numeric_storage_kind(false),
            *span,
            ty.clone(),
            Constness::Unknown,
        );
        ty
    }

    /// Collect only live stores to the lexical binding whose origin is still open.
    pub(in crate::infer) fn numeric_store(
        &mut self,
        target: &Expr,
        value: &Type,
        literal: Option<&Expr>,
        scopes: &ScopeStack,
    ) {
        if !self.numeric.probing || self.discarded_walks > 0 {
            return;
        }
        let Expr::Ident(name, _) = target else { return };
        let Some((frame, id)) = scopes
            .iter()
            .enumerate()
            .rev()
            .find(|(_, frame)| frame.contains_key(name))
            .and_then(|(index, frame)| frame.numeric.get(name).copied().map(|id| (index, id)))
        else {
            return;
        };
        let root = &self.numeric.roots[id];
        if root.global && frame == 0 && !self.return_contexts.is_empty() {
            return;
        }
        let site = root.site.clone();
        let ty = self.resolve(value);
        if matches!(ty, Type::Int(_) | Type::Float(_)) {
            self.numeric
                .observed
                .entry(site)
                .or_default()
                .push(brass_typesys::JoinOperand {
                    ty,
                    literal: literal.and_then(brass_typesys::NumericLiteral::of_expr),
                });
        }
    }

    /// Literal-origin arguments negotiate before the callee's instance is committed.
    pub(in crate::infer) fn numeric_argument(
        &mut self,
        expr: &Expr,
        ty: &Type,
    ) -> (Type, Option<Source>) {
        let result = self.numeric_argument_inner(expr, ty);
        if self.numeric.probing && result.0 != *ty {
            self.numeric.changed = true;
            if let Some(owner) = self.numeric.owner_stack.last().copied() {
                self.numeric.owners[owner].storage = true;
            }
        }
        self.note_numeric_layout_slot(expr.span(), &result.0);
        if !self.numeric.probing
            && self.discarded_walks == 0
            && self.numeric_instance_is_concrete()
            && matches!(self.resolve(&result.0), Type::Int(_) | Type::Float(_))
        {
            self.record_typed(
                self.numeric_storage_kind(true),
                expr.span(),
                result.0.clone(),
                Constness::Unknown,
            );
        }
        result
    }

    fn numeric_argument_inner(&mut self, expr: &Expr, ty: &Type) -> (Type, Option<Source>) {
        if self.discarded_walks > 0 {
            return (ty.clone(), None);
        }
        if !self.numeric.probing {
            let effective = self
                .numeric
                .argument_types
                .get(&self.numeric_site(expr.span()))
                .unwrap_or(ty)
                .clone();
            if effective != *ty {
                self.expect_expr_assignable(ty, &effective, expr);
                self.record_typed(
                    self.numeric_storage_kind(true),
                    expr.span(),
                    effective.clone(),
                    Constness::Unknown,
                );
            }
            return (effective, None);
        }
        let Some(source) = self.numeric_source(expr) else {
            return (ty.clone(), None);
        };
        if !matches!(self.resolve(ty), Type::Int(_) | Type::Float(_)) {
            return (ty.clone(), None);
        }
        let id = self.numeric_root(expr.span(), source, ty);
        let effective = self.numeric.roots[id].ty.clone();
        if effective != *ty {
            self.numeric
                .argument_types
                .insert(self.numeric_site(expr.span()), effective.clone());
        }
        self.expect_expr_assignable(ty, &effective, expr);
        self.record_typed(
            self.numeric_storage_kind(true),
            expr.span(),
            effective.clone(),
            Constness::Unknown,
        );
        (effective, Some(Source::Root(id)))
    }

    /// Resolve only provisional observations; diagnostics and channels stay private.
    pub(in crate::infer) fn settle_numeric_body(
        &mut self,
        body: &Block,
        scopes: &ScopeStack,
        ret: Option<&Type>,
    ) -> NumericState {
        // With no storage or effects anywhere in this call graph, a standalone
        // body has no demand that can grow a floor. Call-site negotiations still
        // walk it under their caller's active provenance state.
        if self.numeric_body_has_no_storage(body.span) {
            return NumericState {
                active: true,
                ..Default::default()
            };
        }
        self.settle_numeric(false, |probe| {
            probe.check_block_root(body, &mut scopes.clone(), ret);
        })
    }

    /// Settle only top-level writes before publishing any module storage layout.
    pub(in crate::infer) fn settle_numeric_init(&mut self, init: &ModuleInit) -> NumericState {
        if init.stmts.is_empty() {
            return NumericState {
                active: true,
                module_scope: true,
                ..Default::default()
            };
        }
        self.settle_numeric(true, |probe| driver::check_init_body(probe, init))
    }

    /// Supply settled module types to method checking and context construction.
    pub(in crate::infer) fn settle_numeric_globals(&mut self) {
        let enabled = self.numeric_enabled;
        if !enabled && !self.lazy_profile {
            return;
        }
        self.numeric_enabled = true;
        for init in &self.program.inits {
            if !enabled && (!self.global_defs.get(&init.path).is_some_and(|defs| defs.values().any(|ty| matches!(self.resolve(ty), Type::Int(_) | Type::Float(_))))
                || init.stmts.iter().all(|stmt| matches!(stmt, Stmt::Let { value: Some(expr), .. } if value_literal(expr).is_some()))) {
                continue;
            }
            if self.seeded_module(&init.path) {
                continue;
            }
            if !enabled {
                let module = std::mem::replace(&mut self.current_module, init.path.clone());
                let needed = self.numeric_globals_need_settlement(init);
                self.current_module = module;
                if !needed {
                    continue;
                }
            }
            let settled = self.settle_numeric_init(init);
            for ((module, name), ty) in settled.globals {
                if let Some(globals) = self.global_defs.get_mut(&module) {
                    if globals.get(&name) != Some(&ty) {
                        self.numeric_seed_ordinary = false;
                    }
                    globals.insert(name, ty);
                }
            }
        }
        self.global_scopes.clear();
        self.numeric_enabled = enabled;
    }

    // Negotiation reads semantic state, not the accumulated publication log.
    // Its own typed observations suffice for private coverage checks; the
    // committed walk retains and extends the complete cross-instance history.
    fn fork_numeric_probe(&mut self) -> Self {
        let typed = std::mem::take(&mut self.typed);
        let seen = std::mem::take(&mut self.typed_seen);
        let instances = std::mem::take(&mut self.instance_typed);
        let instance_seen = std::mem::take(&mut self.instance_typed_seen);
        let numeric = std::mem::take(&mut self.numeric_observations);
        let numeric_seen = std::mem::take(&mut self.numeric_observed);
        let keyed = std::mem::take(&mut self.keyed_observations);
        let changes = std::mem::take(&mut self.channel_changes);
        let mut probe = self.clone();
        probe.completion.active = false;
        self.channel_changes = changes;
        self.keyed_observations = keyed;
        self.numeric_observed = numeric_seen;
        self.numeric_observations = numeric;
        self.instance_typed_seen = instance_seen;
        self.instance_typed = instances;
        self.typed_seen = seen;
        self.typed = typed;
        probe
    }

    fn settle_numeric(&mut self, module_scope: bool, check: impl Fn(&mut Self)) -> NumericState {
        let mut candidates = HashMap::default();
        loop {
            let mut probe = self.fork_numeric_probe();
            probe.numeric = NumericState {
                active: true,
                probing: true,
                module_scope,
                candidates: candidates.clone(),
                ..Default::default()
            };
            probe.speculation_depth += 1;
            check(&mut probe);
            // Derived roots are allocated after their operand roots. Reverse
            // allocation order carries a result's demand through every copy
            // and literal-only operator without rewalking source expressions.
            for root in probe.numeric.roots.iter().rev() {
                let Some(operands) = probe.numeric.observed.get(&root.site) else {
                    continue;
                };
                let Ok(Some(ty)) = brass_typesys::join_values(self.program, operands) else {
                    continue;
                };
                for parent in &root.parents {
                    let site = probe.numeric.roots[*parent].site.clone();
                    probe
                        .numeric
                        .observed
                        .entry(site)
                        .or_default()
                        .push(brass_typesys::JoinOperand::value(ty.clone()));
                }
            }
            let mut changed = false;
            let mut observations: Vec<_> = probe.numeric.observed.iter().collect();
            observations.sort_by(|(a, _), (b, _)| {
                a.calls
                    .iter()
                    .map(|s| (s.lo, s.hi))
                    .cmp(b.calls.iter().map(|s| (s.lo, s.hi)))
                    .then((a.span.lo, a.span.hi).cmp(&(b.span.lo, b.span.hi)))
            });
            for (site, operands) in observations {
                let Ok(Some(next)) = brass_typesys::join_values(self.program, operands) else {
                    continue;
                };
                let floor = &operands[0].ty;
                let previous = candidates.get(site).unwrap_or(floor);
                if *previous == next {
                    candidates.insert(site.clone(), next);
                    continue;
                }
                let union = brass_typesys::join_values(
                    self.program,
                    &[
                        brass_typesys::JoinOperand::value(previous.clone()),
                        brass_typesys::JoinOperand::value(next.clone()),
                    ],
                )
                .ok()
                .flatten();
                if union.as_ref() != Some(&next) {
                    self.errors.push(TypeError {
                        span: site.span,
                        message:
                            "numeric inference has no self-consistent type; annotate the binding"
                                .into(),
                    });
                    return NumericState {
                        active: true,
                        changed: true,
                        candidates,
                        ..Default::default()
                    };
                }
                candidates.insert(site.clone(), next);
                changed = true;
            }
            if !changed {
                self.numeric_seed_ordinary &= !probe.numeric.changed;
                return NumericState {
                    active: true,
                    changed: probe.numeric.changed,
                    module_scope,
                    candidates,
                    globals: probe.numeric.globals,
                    bindings: probe.numeric.bindings,
                    argument_types: probe.numeric.argument_types,
                    layouts: probe.numeric.layouts,
                    ..Default::default()
                };
            }
        }
    }
}

#[cfg(test)]
mod tests;

/// Storage-free call graph eligibility for provenance memoization.
pub(in crate::infer) mod pure;

/// Structural zero-growth proofs for independent body roots.
pub(in crate::infer) mod eligibility;
