//! Syntactic dependencies use HIR resolution. Open dispatch retains a family;
//! it does not guess types or depend on the timing of background checking.

use super::certificate::shared_obligation;
use super::index::{Declaration, ItemIndex};
use super::inhabited::Inhabited;

mod dispatch;
mod effects;
use crate::walk::{self, ExprVisitor};
use brass_hir::{CallableSignature, Reason, Type, TypeInfo, TypeKind};
use brass_parser::ast::{Block, Expr, Pattern, Stmt, StrSeg, TypeExpr};
use fxhash::FxHashSet as HashSet;

/// Edges of one selected declaration and explanations for conservative widening.
#[derive(Clone)]
pub(super) struct Dependencies {
    pub(super) edges: Vec<(usize, Reason)>,
    pub(super) causes: Vec<&'static str>,
    pub(super) open: bool,
    pub(super) inhabited_dependent: bool,
    pub(super) effects: super::effects::EffectSummary,
    pub(super) calls: Vec<usize>,
    pub(super) rootless: super::effects::EffectSummary,
    pub(super) rootless_calls: Vec<usize>,
}

/// Traverse a body with the same name/dispatch authority for selection and effects.
pub(super) fn dependencies(
    index: &ItemIndex<'_>,
    key: usize,
    inhabited: &mut Inhabited,
    root: bool,
    open: bool,
    summaries: bool,
    globals_only: bool,
) -> Dependencies {
    let entry = &index.entries[key];
    let mut visitor = Edges {
        index,
        names: &index.names[entry.module],
        inhabited,
        root,
        open,
        inhabited_dependent: false,
        module: entry.module,
        owner: None,
        locals: HashSet::default(),
        edges: Vec::new(),
        edge_bits: vec![0; index.entries.len()],
        causes: Vec::new(),
        effects: super::effects::EffectSummary::default(),
        rootless: super::effects::EffectSummary::default(),
        rootless_calls: Vec::new(),
        calls: Vec::new(),
        callees: HashSet::default(),
        summaries,
        globals_only,
        entry_boundary: matches!(&entry.declaration, Declaration::Initializer(_))
            || matches!(&entry.declaration, Declaration::Function(f) if index.program.entry_function() == Some(f.symbol.as_str())),
    };
    match &entry.declaration {
        Declaration::Function(f) => {
            if summaries
                && !globals_only
                && f.signature
                    .ret_ty
                    .as_ref()
                    .is_none_or(|ty| !super::certificate::closed_layout(index.program, ty))
            {
                visitor
                    .effects
                    .shared_cells
                    .insert(format!("{}:open function return", f.symbol));
            }
            visitor.signature(&f.signature);
            visitor.block(&f.decl.body);
        }
        Declaration::Method(t, m) => {
            visitor.owner = Some(t);
            if summaries && !globals_only {
                if let Some(reason) = super::certificate::signature_obligation(index.program, t, m)
                {
                    visitor
                        .effects
                        .shared_cells
                        .insert(format!("{}.{}:{reason:?}", t.symbol, m.signature.name));
                }
                if m.decl.body.is_none() {
                    visitor.effects.unknown_calls.insert(format!(
                        "{}.{}:unavailable body",
                        t.symbol, m.signature.name
                    ));
                }
            }
            if !globals_only && m.signature.params.first().is_some_and(|p| p.name == "self") {
                visitor.inhabited.ty(index.program, &t.type_ref());
                if root && !super::certificate::closed_layout(index.program, &t.type_ref()) {
                    visitor.open = true;
                }
            }
            visitor.nominal(t.id, Reason::ExplicitUse);
            if !summaries && brass_hir::keyed_return(m.decl.ret.as_ref()) {
                // Specialization inserts a call-position parameter and error
                // branches even when the template does not spell either one.
                if let Some(location) = index.program.prelude_type("Location") {
                    visitor.inhabited.ty(index.program, &location.type_ref());
                    visitor.nominal(location.id, Reason::Generated);
                }
                if let Some(error) = visitor.names.function("error") {
                    visitor.edge(index.functions[error.symbol.as_str()], Reason::Generated);
                }
            }
            visitor.signature(&m.signature);
            if let Some(body) = &m.decl.body {
                visitor.block(body);
            }
            // A body can constrain an open parameter through assignment,
            // arithmetic or a typed helper. Local effects are not an absence
            // proof when the checking frame itself contains shared cells.
            if summaries
                && !globals_only
                && m.signature
                    .params
                    .iter()
                    .filter(|p| p.name != "self")
                    .any(|p| {
                        p.resolved_ty
                            .as_ref()
                            .is_none_or(|ty| !super::certificate::closed_layout(index.program, ty))
                    })
            {
                visitor.effects.shared_cells.insert(format!(
                    "{}.{}:open method input",
                    t.symbol, m.signature.name
                ));
            }
        }
        Declaration::Type(t) if !summaries => {
            for parent in &t.interfaces {
                // HIR has already resolved interface names to storage symbols;
                // resolving that symbol again as a source alias can lose it.
                if let Some(info) = index.program.types.get(parent) {
                    visitor.nominal(info.id, Reason::ExplicitUse);
                } else {
                    visitor.name(parent);
                }
            }
            let groups = match &t.kind {
                TypeKind::Record { fields, methods } => vec![(fields, methods)],
                TypeKind::Sum { variants } => {
                    variants.iter().map(|v| (&v.fields, &v.methods)).collect()
                }
            };
            for (fields, methods) in groups {
                for field in fields {
                    if let Some(ty) = &field.resolved_ty {
                        visitor.ty(ty);
                    }
                    if let Some(annotation) = &field.ty {
                        visitor.annotation(annotation);
                    }
                }
                for method in methods.values() {
                    // An abstract member is a structural requirement; a value
                    // can supply it through another nominal's method body.
                    if method.decl.body.is_none() {
                        visitor.method(None, &method.signature.name, Reason::ImplicitUse);
                        continue;
                    }
                    if brass_hir::keyed_return(method.decl.ret.as_ref()) {
                        continue;
                    }
                    if let Some(obligation) = shared_obligation(index, t, method) {
                        let cause = match obligation {
                            super::SharedObligation::OpenLayout => "open shared layout",
                            super::SharedObligation::OpenSignature => "open shared signature",
                            super::SharedObligation::UnclassifiedEffects => {
                                "unclassified shared effects"
                            }
                        };
                        visitor.cause(cause);
                        visitor.method(Some(t.id), &method.signature.name, Reason::SharedInference);
                    }
                }
            }
        }
        Declaration::Type(_) => {}
        Declaration::Alias(alias) => visitor.ty(&alias.ty),
        Declaration::Initializer(init) => {
            for statement in &init.stmts {
                visitor.statement(statement);
            }
            if !summaries {
                // Initializers own shared global cells. Even a read in an
                // uncalled body can constrain an open cell through its use.
                // Without a closed-cell proof, keep every contributor to this
                // module's globals, including transitive and imported uses.
                for &candidate in super::effects::global_contributors(index, &init.path) {
                    visitor.edge(candidate, Reason::SharedInference);
                }
            }
        }
    }
    Dependencies {
        edges: visitor.edges,
        causes: visitor.causes,
        open: visitor.open,
        inhabited_dependent: visitor.inhabited_dependent,
        effects: visitor.effects,
        calls: visitor.calls,
        rootless: visitor.rootless,
        rootless_calls: visitor.rootless_calls,
    }
}

struct Edges<'a, 'p> {
    inhabited: &'a mut Inhabited,
    root: bool,
    open: bool,
    inhabited_dependent: bool,
    index: &'a ItemIndex<'p>,
    names: &'a super::names::Names<'p>,
    module: &'a [String],
    owner: Option<&'a TypeInfo>,
    /// Entry propagation aborts through the prelude renderer instead of returning.
    entry_boundary: bool,
    locals: HashSet<String>,
    edges: Vec<(usize, Reason)>,
    edge_bits: Vec<u8>,
    causes: Vec<&'static str>,
    effects: super::effects::EffectSummary,
    rootless: super::effects::EffectSummary,
    rootless_calls: Vec<usize>,
    calls: Vec<usize>,
    callees: HashSet<brass_parser::Span>,
    summaries: bool,
    globals_only: bool,
}

impl Edges<'_, '_> {
    fn edge(&mut self, key: usize, reason: Reason) {
        let bit = 1 << reason as u8;
        if self.edge_bits[key] & bit == 0 {
            self.edge_bits[key] |= bit;
            self.edges.push((key, reason));
        }
    }

    fn cause(&mut self, cause: &'static str) {
        if !self.causes.contains(&cause) {
            self.causes.push(cause);
        }
    }

    fn nominal(&mut self, id: i32, reason: Reason) {
        if let Some(key) = self.index.types.get(&id) {
            self.edge(*key, reason);
        }
    }

    fn name(&mut self, name: &str) {
        if self.globals_only {
            return;
        }
        if let Some(f) = self.names.function(name) {
            self.edge(self.index.functions[f.symbol.as_str()], Reason::ExplicitUse);
        }
        if let Some(alias) = self.names.alias(name) {
            self.edge(self.index.aliases[&alias.span], Reason::ExplicitUse);
        }
        if let Some(t) = self.names.nominal(name) {
            self.nominal(t.id, Reason::ExplicitUse);
        }
        if name == "Self"
            && let Some(t) = self.owner
        {
            self.nominal(t.id, Reason::ExplicitUse);
        }
    }

    fn ty(&mut self, ty: &Type) {
        if self.globals_only {
            return;
        }
        match ty {
            Type::Record(n) | Type::Sum(n) => {
                self.nominal(n.id, Reason::ExplicitUse);
                for (name, ty) in n.substitution.iter() {
                    self.ty(ty);
                    if matches!(ty, Type::Fun(..)) {
                        self.method(None, name, Reason::ImplicitUse);
                    }
                }
            }
            Type::Array(t, _)
            | Type::Slice(t)
            | Type::Nullable(t)
            | Type::ConstOf(t)
            | Type::Mut(t)
            | Type::Ref(t) => self.ty(t),
            Type::Tuple(ts) => ts.iter().for_each(|t| self.ty(t)),
            Type::Fun(ps, ret) => {
                ps.iter().for_each(|t| self.ty(t));
                self.ty(ret);
            }
            _ => {}
        }
    }

    fn produce_annotation(&mut self, ty: &TypeExpr) {
        if !self.globals_only {
            self.inhabited.annotation(self.index, self.module, ty);
        }
    }

    fn annotation(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Named(name, _) => self.name(name),
            TypeExpr::Array(t, _, _)
            | TypeExpr::Nullable(t, _)
            | TypeExpr::Mut(t, _)
            | TypeExpr::Ref(t, _) => self.annotation(t),
            TypeExpr::Fallible(t, _) => {
                self.name(brass_hir::RESULT_TYPE_NAME);
                self.annotation(t);
            }
            TypeExpr::Fun(ps, ret, _) => {
                for p in ps {
                    self.annotation(p);
                }
                self.annotation(ret);
            }
            TypeExpr::Tuple(ts, _) => {
                for t in ts {
                    self.annotation(t);
                }
            }
            TypeExpr::Anonymous(fields, _) => {
                for (name, ty, _) in fields {
                    self.annotation(ty);
                    if matches!(ty, TypeExpr::Fun(..)) {
                        self.method(None, name, Reason::ImplicitUse);
                    }
                }
            }
            TypeExpr::Refine(base, fields, _) => {
                self.annotation(base);
                for (_, t, _) in fields {
                    self.annotation(t);
                }
            }
            TypeExpr::TypeOf(e, _) => walk::walk_expr(e, self),
            TypeExpr::SelfField(_, _) => {
                if let Some(t) = self.owner {
                    self.nominal(t.id, Reason::ExplicitUse);
                }
            }
            TypeExpr::TypeSlot(_) => {}
        }
    }

    fn signature(&mut self, signature: &CallableSignature) {
        for param in &signature.params {
            self.locals.insert(param.name.clone());
            if let Some(t) = &param.resolved_ty {
                if self.summaries
                    && !self.globals_only
                    && param.name != "self"
                    && super::certificate::borrows_layout(self.index, t)
                {
                    self.rootless.shared_cells.insert(format!(
                        "{}:{}:borrowed parameter layout",
                        self.module.join("/"),
                        signature.name
                    ));
                }
                if !self.globals_only {
                    self.inhabited.ty(self.index.program, t);
                }
                self.ty(t);
            }
            if let Some(t) = &param.ty {
                self.produce_annotation(t);
                self.annotation(t);
            }
            if self.root && (param.name != "self" || self.owner.is_none()) {
                let declared = param.resolved_ty.clone().or_else(|| {
                    param.ty.as_ref().and_then(|ty| {
                        super::layout::annotation(self.index.program, self.module, ty)
                    })
                });
                if declared
                    .as_ref()
                    .is_none_or(|ty| !super::certificate::closed_layout(self.index.program, ty))
                {
                    self.open = true;
                }
            }
        }
        if let Some(t) = &signature.ret_ty {
            if self.summaries
                && !self.globals_only
                && super::certificate::borrows_layout(self.index, t)
            {
                self.rootless.shared_cells.insert(format!(
                    "{}:{}:borrowed return layout",
                    self.module.join("/"),
                    signature.name
                ));
            }
            if !self.globals_only {
                self.inhabited.ty(self.index.program, t);
            }
            if matches!(t, Type::SelfType)
                && let Some(owner) = self.owner
            {
                self.inhabited.ty(self.index.program, &owner.type_ref());
            }
            self.ty(t);
        }
        if let Some(t) = &signature.ret {
            self.produce_annotation(t);
            self.annotation(t);
        }
    }

    fn pattern(&mut self, pattern: &Pattern) {
        // Pattern bindings can shadow a nominal qualifier in loops and match
        // arms as well as lets. Retaining the union of names only widens later
        // dispatch. A possible static qualifier is also retained when the
        // union includes a later or out-of-scope binding with the same name.
        self.locals
            .extend(pattern.bound_names().into_iter().map(str::to_owned));
        match pattern {
            Pattern::Binding(name, qualifier, _) | Pattern::Record(name, qualifier, _, _) => {
                if let Some(qualifier) = qualifier {
                    // A qualified variant names exactly one sum. Its suffix
                    // must not make unrelated sums with that variant used.
                    self.name(&qualifier.ty);
                } else {
                    self.name(name);
                    for t in (!self.globals_only)
                        .then(|| self.names.variants(name))
                        .iter()
                        .flat_map(|v| v.iter())
                    {
                        self.nominal(t.id, Reason::ExplicitUse);
                    }
                }
                if let Pattern::Record(_, _, fields, _) = pattern {
                    for field in fields {
                        if let Some(p) = &field.pat {
                            self.pattern(p);
                        }
                    }
                }
            }
            Pattern::Array(ps, _) => {
                for p in ps {
                    self.pattern(p);
                }
            }
            Pattern::Literal(e, _) => walk::walk_expr(e, self),
            Pattern::Wildcard(_) => {}
        }
    }

    fn block(&mut self, block: &Block) {
        for statement in &block.stmts {
            self.statement(statement);
        }
    }

    fn block_annotations(&mut self, block: &Block) {
        for statement in &block.stmts {
            self.statement_effects(statement);
            match statement {
                Stmt::Let { pat, ty, .. } => {
                    self.pattern(pat);
                    if let Some(ty) = ty {
                        self.annotation(ty);
                        self.produce_annotation(ty);
                    }
                    for name in pat.bound_names() {
                        self.locals.insert(name.into());
                    }
                }
                Stmt::While { body, .. } => self.block_annotations(body),
                Stmt::For { pat, body, .. } => {
                    self.pattern(pat);
                    self.block_annotations(body);
                }
                _ => {}
            }
        }
    }

    fn statement(&mut self, statement: &Stmt) {
        self.statement_effects(statement);
        match statement {
            Stmt::Let { pat, ty, value, .. } => {
                self.pattern(pat);
                if let Some(t) = ty {
                    if self.summaries
                        && !self.globals_only
                        && super::layout::annotation(self.index.program, self.module, t)
                            .is_some_and(|ty| super::certificate::borrows_layout(self.index, &ty))
                    {
                        self.rootless.shared_cells.insert(format!(
                            "{}:{}:borrowed local layout",
                            self.module.join("/"),
                            statement.span().lo
                        ));
                    }
                    self.annotation(t);
                    self.produce_annotation(t);
                }
                if let Some(v) = value {
                    walk::walk_expr(v, self);
                }
                // Bindings may be reassigned or shadowed. No inferred receiver
                // type is persisted here; an unknown receiver widens instead.
                for name in pat.bound_names() {
                    self.locals.insert(name.into());
                }
            }
            Stmt::Assign { target, value, .. } => {
                walk::walk_expr(target, self);
                walk::walk_expr(value, self);
            }
            Stmt::Expr(e) | Stmt::Return(Some(e), _) => walk::walk_expr(e, self),
            Stmt::While { cond, body, .. } => {
                walk::walk_expr(cond, self);
                self.block(body);
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                self.pattern(pat);
                walk::walk_expr(iter, self);
                self.block(body);
            }
            Stmt::Return(None, _) | Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }
}

impl ExprVisitor for Edges<'_, '_> {
    fn visit(&mut self, expr: &Expr) {
        self.expression_effects(expr);
        if !self.globals_only {
            self.produce(expr);
        }
        match expr {
            Expr::Ident(name, _) if !self.globals_only => self.name(name),
            Expr::TypeLit(name, _, _) | Expr::VariantLit(name, _, _, _) if !self.globals_only => {
                self.name(name)
            }
            Expr::Field(receiver, name, _) if !self.globals_only => {
                // Primitive qualifiers use the same dispatch-class authority as
                // HIR lowering. Builtin static conversions have no source body.
                let class = self.known_class(receiver);
                if let Some(class) = class {
                    if let Some(&id) = self.index.primitives.get(&(class, name.as_ref())) {
                        self.edge(id, Reason::ExplicitUse);
                    }
                } else {
                    self.possible_static(receiver, name);
                    self.method(self.receiver(receiver), name, Reason::ExplicitUse);
                }
                if name == "debug" {
                    self.rendering_form(Some(receiver), brass_hir::rendering::RenderForm::Debug);
                }
                if name == "from"
                    && matches!(receiver.as_ref(), Expr::Ident(name, _) if name == "infer")
                {
                    self.cause("reflective conversion without key: inhabited from family");
                    self.method(None, name, Reason::Generated);
                }
            }
            Expr::Call(callee, args, _) if !self.globals_only => {
                for target in self.exact_call_targets(callee) {
                    self.edge(target, Reason::ExplicitUse);
                }
                if matches!(callee.as_ref(), Expr::Ident(name, _) if matches!(name.as_str(), "print" | "println" | "to_string"))
                {
                    self.rendering(args.first().map(|a| &a.expr));
                }
                if matches!(callee.as_ref(), Expr::Field(base, name, _) if name == "from" && self.qualifier_class(base) == Some("string"))
                {
                    self.rendering(args.first().map(|a| &a.expr));
                }
                // Nullable context builds an error on its missing-value arm.
                // An unresolved receiver can take this builtin lowering even
                // when no source call names the prelude constructor.
                if matches!(callee.as_ref(), Expr::Field(base, name, _) if name == "context" && self.receiver(base).is_none())
                    && let Some(error) = self.names.function("error")
                {
                    self.edge(
                        self.index.functions[error.symbol.as_str()],
                        Reason::ImplicitUse,
                    );
                }
                if matches!(callee.as_ref(), Expr::Ident(name, _) if name == "fields") {
                    self.reflection(args.first().map(|a| &a.expr));
                }
            }
            Expr::Str(parts, _)
                if !self.globals_only && parts.iter().any(|p| matches!(p, StrSeg::Expr(_))) =>
            {
                for part in parts {
                    if let StrSeg::Expr(value) = part {
                        self.rendering(Some(value));
                    }
                }
            }
            Expr::Closure(params, _, _) => {
                for p in params {
                    if self.root || self.open {
                        let declared = p.ty.as_ref().and_then(|ty| {
                            super::layout::annotation(self.index.program, self.module, ty)
                        });
                        if let Some(ty) = &declared {
                            self.inhabited.ty(self.index.program, ty);
                        }
                        if declared.as_ref().is_none_or(|ty| {
                            !super::certificate::closed_layout(self.index.program, ty)
                        }) {
                            self.open = true;
                        }
                    }
                    if let Some(t) = &p.ty {
                        self.annotation(t);
                    }
                    self.locals.insert(p.name.clone());
                }
            }
            Expr::ErrorProp(..) if self.entry_boundary && !self.globals_only => {
                if let Some(render) = self.names.function("_render_unhandled") {
                    self.edge(
                        self.index.functions[render.symbol.as_str()],
                        Reason::ImplicitUse,
                    );
                }
            }
            Expr::TypeTest(_, ty, _, _) => self.annotation(ty),
            Expr::IfLet(pattern, _, body, _, _) => {
                self.pattern(pattern);
                self.block_annotations(body);
            }
            Expr::Match(_, arms, _) => {
                for arm in arms {
                    self.pattern(&arm.pattern);
                }
            }
            Expr::Block(block, _) | Expr::If(_, block, _, _) => self.block_annotations(block),
            // Operators and assignment have primitive/structural implementations,
            // not user overloads. Their operands already expose every source use.
            Expr::Ident(..)
            | Expr::TypeLit(..)
            | Expr::VariantLit(..)
            | Expr::Field(..)
            | Expr::Call(..)
            | Expr::Unary(..)
            | Expr::Binary(..)
            | Expr::Index(..)
            | Expr::ErrorProp(..)
            | Expr::Array(..)
            | Expr::Range(..)
            | Expr::Int(..)
            | Expr::Float(..)
            | Expr::Bool(..)
            | Expr::Null(..)
            | Expr::SelfExpr(..)
            | Expr::Str(..) => {}
        }
    }
}
