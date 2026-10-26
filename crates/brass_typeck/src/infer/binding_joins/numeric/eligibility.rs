//! Conservative structural proof that no numeric origin can grow in a call graph.

use super::*;

/// Roots whose local stores and transitive calls cannot widen a literal floor.
#[derive(Default)]
pub(in crate::infer) struct Eligibility {
    bodies: HashSet<Span>,
    transitive: HashSet<Span>,
    inits: HashSet<Vec<String>>,
    transitive_inits: HashSet<Vec<String>>,
}

struct Body<'a> {
    span: Option<Span>,
    module: Option<&'a Vec<String>>,
    name: Option<&'a str>,
    params: &'a [brass_parser::ast::Param],
    annotated_return: bool,
    stmts: &'a [Stmt],
}

#[derive(Default)]
struct Scan<'a> {
    origins: HashSet<&'a str>,
    locals: HashSet<&'a str>,
    opaque: Vec<&'a str>,
    declarations: Vec<(&'a str, &'a Expr)>,
    stores: Vec<(&'a str, &'a Expr)>,
    fields: HashSet<&'a str>,
    calls: Vec<(&'a Expr, &'a [brass_parser::ast::Arg])>,
}

impl Eligibility {
    /// A leaf with no binding stores cannot add a wider value to an incoming origin.
    pub(in crate::infer) fn leaf(stmts: &[Stmt]) -> bool {
        let mut scan = Scan::default();
        scan.statements(stmts);
        scan.stores.is_empty() && scan.calls.is_empty()
    }

    /// Local stores and closed calls can prove zero growth without a program graph.
    /// A known callee supplies whether incoming origins are closed and its return is annotated.
    /// The callback's flag requests the input proof only for origin-carrying arguments.
    /// Independent calls are allowed only when callees settle their own roots.
    pub(in crate::infer) fn local(
        stmts: &[Stmt],
        independent_calls: bool,
        callable: impl Fn(&Expr, bool) -> Option<(bool, bool)>,
    ) -> bool {
        let mut scan = Scan::default();
        scan.statements(stmts);
        let mut closed = HashSet::default();
        for (callee, _) in &scan.calls {
            if primitive_call(callee, &scan.locals) {
                continue;
            }
            let Expr::Ident(name, _) = callee else {
                if !independent_calls {
                    return false;
                }
                continue;
            };
            if scan.locals.contains(name.as_str()) {
                if !independent_calls {
                    return false;
                }
                continue;
            }
            let Some((_, closed_return)) = callable(callee, false) else {
                if !independent_calls {
                    return false;
                }
                continue;
            };
            if closed_return {
                closed.insert(name.as_str());
            }
        }
        loop {
            let before = scan.origins.len();
            for (name, value) in &scan.declarations {
                if scan.origin(value, &closed) {
                    scan.origins.insert(name);
                }
            }
            if before == scan.origins.len() {
                break;
            }
        }
        let integers = std::cell::OnceCell::new();
        scan.stores
            .iter()
            .all(|(name, value)| scan.store_is_closed(name, value, &integers))
            && scan.calls.iter().all(|(callee, args)| {
                if primitive_call(callee, &scan.locals) {
                    return true;
                }
                if args.iter().all(|arg| !scan.origin(&arg.expr, &closed)) {
                    return true;
                }
                let shadowed = match callee {
                    Expr::Ident(name, _) => scan.locals.contains(name.as_str()),
                    Expr::Field(base, _, _) => match &**base {
                        Expr::Ident(name, _) => scan.locals.contains(name.as_str()),
                        Expr::SelfExpr(_) => scan.locals.contains("self"),
                        _ => true,
                    },
                    _ => true,
                };
                !shadowed && callable(callee, true).is_some_and(|(closed, _)| closed)
            })
    }

    /// Build once per checker; ambiguous names retain every possible callee.
    pub(in crate::infer) fn new(program: &Program, builtin: impl Fn(&str) -> bool) -> Self {
        let mut bodies = Vec::new();
        for f in program.functions.values() {
            bodies.push(Body {
                span: Some(f.decl.body.span),
                module: None,
                name: Some(&f.signature.name),
                params: &f.decl.params,
                annotated_return: f.signature.ret_ty.is_some(),
                stmts: &f.decl.body.stmts,
            });
        }
        for ty in program.types.values() {
            let methods: Vec<_> = match &ty.kind {
                brass_hir::TypeKind::Record { methods, .. } => methods.values().collect(),
                brass_hir::TypeKind::Sum { variants } => {
                    variants.iter().flat_map(|v| v.methods.values()).collect()
                }
            };
            for m in methods {
                if let Some(body) = &m.decl.body {
                    bodies.push(Body {
                        span: Some(body.span),
                        module: None,
                        name: Some(&m.signature.name),
                        params: &m.decl.params,
                        annotated_return: m.signature.ret_ty.is_some(),
                        stmts: &body.stmts,
                    });
                }
            }
        }
        for init in &program.inits {
            bodies.push(Body {
                span: None,
                module: Some(&init.path),
                name: None,
                params: &[],
                annotated_return: false,
                stmts: &init.stmts,
            });
        }
        let scans: Vec<_> = bodies
            .iter()
            .map(|body| {
                let mut scan = Scan::default();
                scan.parameters(body.params);
                scan.origins.clear();
                scan.statements(body.stmts);
                scan
            })
            .collect();
        let globals: HashSet<_> = scans
            .iter()
            .zip(&bodies)
            .filter(|(_, body)| body.module.is_some())
            .flat_map(|(scan, _)| scan.locals.iter().copied())
            .collect();
        let written: HashSet<_> = scans
            .iter()
            .flat_map(|scan| scan.fields.iter().copied())
            .collect();
        let mut fields = HashSet::default();
        for ty in program.types.values() {
            match &ty.kind {
                brass_hir::TypeKind::Record { fields: fs, .. } => {
                    fields.extend(fs.iter().map(|f| f.name.as_str()))
                }
                brass_hir::TypeKind::Sum { variants } => fields.extend(
                    variants
                        .iter()
                        .flat_map(|v| v.fields.iter().map(|f| f.name.as_str())),
                ),
            }
        }
        let mut names: HashMap<&str, Vec<usize>> = HashMap::default();
        for (id, body) in bodies.iter().enumerate() {
            if let Some(name) = body.name {
                names.entry(name).or_default().push(id);
            }
        }
        let mut closed_calls: HashSet<_> = names
            .iter()
            .filter(|(_, ids)| ids.iter().all(|id| bodies[*id].annotated_return))
            .map(|(name, _)| *name)
            .collect();
        for scan in &scans {
            for (callee, _) in &scan.calls {
                if let Expr::Ident(name, _) = callee
                    && !names.contains_key(name.as_str())
                    && (builtin(name) || matches!(name.as_str(), "typeof" | "fields"))
                {
                    closed_calls.insert(name.as_str());
                }
            }
        }
        closed_calls.retain(|name| {
            !globals.contains(name) && !fields.contains(name) && !written.contains(*name)
        });
        let mut ordinary = vec![true; bodies.len() * 3];
        let mut reverse = vec![Vec::new(); bodies.len() * 3];
        let mut pending = Vec::new();
        // Root checks have no incoming origins. Calls carrying origins use
        // the second context; the third also includes independent callee
        // storage, for global pre-settlement and private ordinary replay.
        for (body_id, (body, mut scan)) in bodies.iter().zip(scans).enumerate() {
            scan.locals.extend(globals.iter().copied());
            let integers = std::cell::OnceCell::new();
            for context in 0..3 {
                let id = body_id * 3 + context;
                if context == 1 {
                    scan.origins.extend(
                        body.params
                            .iter()
                            .filter(|param| param.ty.is_none())
                            .map(|param| param.name.as_str()),
                    );
                }
                // Adding incoming origins only grows the same name worklist;
                // the transitive context reads its completed result unchanged.
                if context != 2 {
                    loop {
                        let before = scan.origins.len();
                        for (name, value) in &scan.declarations {
                            if scan.origin(value, &closed_calls) {
                                scan.origins.insert(name);
                            }
                        }
                        if before == scan.origins.len() {
                            break;
                        }
                    }
                }
                let mut safe = scan
                    .stores
                    .iter()
                    .all(|(name, value)| scan.store_is_closed(name, value, &integers));
                for (callee, args) in &scan.calls {
                    if primitive_call(callee, &scan.locals) {
                        continue;
                    }
                    let (name, dynamic) = match callee {
                        Expr::Ident(name, _) => (
                            name.as_str(),
                            scan.locals.contains(name.as_str()) || globals.contains(name.as_str()),
                        ),
                        Expr::Field(_, name, _) => (
                            name.as_str(),
                            fields.contains(name.as_str()) || written.contains(name.as_str()),
                        ),
                        _ => {
                            safe = false;
                            continue;
                        }
                    };
                    if dynamic {
                        safe = false;
                    }
                    if let Some(candidates) = names.get(name) {
                        if context == 2 {
                            for &callee in candidates {
                                reverse[callee * 3 + 2].push(id);
                            }
                        } else if args.iter().any(|arg| scan.origin(&arg.expr, &closed_calls)) {
                            for &callee in candidates {
                                if bodies[callee]
                                    .params
                                    .iter()
                                    .any(|param| param.ty.is_none() && param.name != "self")
                                {
                                    reverse[callee * 3 + 1].push(id);
                                }
                            }
                        }
                    } else {
                        // Intrinsics have no source body or numeric storage. A
                        // callable field or lexical binding still declines above.
                        let intrinsic = match callee {
                            Expr::Ident(..) => {
                                matches!(
                                    name,
                                    "print" | "println" | "len" | "typeof" | "fields" | "assert"
                                ) || (builtin(name)
                                    && !matches!(name, "spawn" | "with" | "_with_all"))
                            }
                            Expr::Field(..) => matches!(
                                name,
                                "push"
                                    | "pop"
                                    | "insert"
                                    | "remove"
                                    | "len"
                                    | "from"
                                    | "parse"
                                    | "default"
                                    | "debug"
                            ),
                            _ => false,
                        };
                        safe &= intrinsic;
                    }
                }
                if !safe {
                    ordinary[id] = false;
                    pending.push(id);
                }
            }
        }
        while let Some(id) = pending.pop() {
            for &caller in &reverse[id] {
                if ordinary[caller] {
                    ordinary[caller] = false;
                    pending.push(caller);
                }
            }
        }
        let mut result = Self::default();
        for (id, body) in bodies.into_iter().enumerate() {
            if ordinary[id * 3 + 2]
                && let Some(span) = body.span
            {
                result.transitive.insert(span);
            }
            if ordinary[id * 3 + 2]
                && let Some(module) = body.module
            {
                result.transitive_inits.insert(module.clone());
            }
            if !ordinary[id * 3] {
                continue;
            }
            if let Some(span) = body.span {
                result.bodies.insert(span);
            }
            if let Some(module) = body.module {
                result.inits.insert(module.clone());
            }
        }
        result
    }

    /// No reachable store can grow a floor in this body.
    pub(in crate::infer) fn body(&self, span: Span) -> bool {
        self.bodies.contains(&span)
    }

    /// The entire reachable graph is zero-growth, including incoming origins.
    pub(in crate::infer) fn transitive(&self, span: Span) -> bool {
        self.transitive.contains(&span)
    }

    /// Top-level settlement also accounts for independent callee origins.
    pub(in crate::infer) fn transitive_init(&self, module: &[String]) -> bool {
        self.transitive_inits.contains(module)
    }

    /// No reachable store can grow a floor in this module initializer.
    pub(in crate::infer) fn init(&self, module: &[String]) -> bool {
        self.inits.contains(module)
    }
}

impl<'a> Scan<'a> {
    // A connected group of int32-floor locals stays at that floor when all
    // initializers and stores use only the group and int32-fitting integers.
    // Opaque/shadowing declarations remove the whole spelling from the proof.
    fn integer_locals(&self) -> HashSet<&'a str> {
        let empty = HashSet::default();
        let mut integers: HashSet<_> = self
            .declarations
            .iter()
            .filter(|(name, value)| !self.opaque.contains(name) && integer_expr(value, &empty))
            .map(|(name, _)| *name)
            .collect();
        loop {
            let mut rejected = Vec::new();
            for (name, value) in self.declarations.iter().chain(&self.stores) {
                if integers.contains(name) && !integer_expr(value, &integers) {
                    rejected.push(*name);
                }
            }
            if rejected.is_empty() {
                return integers;
            }
            for name in rejected {
                integers.remove(name);
            }
        }
    }

    fn store_is_closed(
        &self,
        name: &str,
        value: &Expr,
        integers: &std::cell::OnceCell<HashSet<&'a str>>,
    ) -> bool {
        !self.origins.contains(name) || self_literal(value, name) || {
            let integers = integers.get_or_init(|| self.integer_locals());
            integers.contains(name) && integer_expr(value, integers)
        }
    }

    fn pattern(&mut self, pat: &'a Pattern) {
        match pat {
            Pattern::Binding(name, _, _) => {
                self.locals.insert(name);
                self.opaque.push(name);
            }
            Pattern::Array(parts, _) => {
                for part in parts {
                    self.pattern(part);
                }
            }
            Pattern::Record(_, _, fields, _) => {
                for field in fields {
                    if let Some(pat) = &field.pat {
                        self.pattern(pat);
                    } else {
                        self.locals.insert(&field.name);
                        self.opaque.push(&field.name);
                    }
                }
            }
            _ => {}
        }
    }

    fn parameters(&mut self, params: &'a [brass_parser::ast::Param]) {
        for param in params {
            self.locals.insert(&param.name);
            self.opaque.push(&param.name);
            if param.ty.is_none() {
                self.origins.insert(&param.name);
            }
        }
    }

    fn statements(&mut self, stmts: &'a [Stmt]) {
        for stmt in stmts {
            match stmt {
                Stmt::Let { pat, ty, value, .. } => {
                    if !matches!(pat, Pattern::Binding(_, None, _) if ty.is_none() && value.is_some())
                    {
                        self.pattern(pat);
                    }
                    if let Pattern::Binding(name, None, _) = pat {
                        self.locals.insert(name);
                        if ty.is_none()
                            && let Some(value) = value
                        {
                            self.declarations.push((name, value));
                        }
                    }
                    if let Some(value) = value {
                        self.expression(value);
                    }
                }
                Stmt::Assign { target, value, .. } => {
                    if let Expr::Ident(name, _) = target {
                        self.stores.push((name, value));
                    }
                    self.expression(target);
                    self.expression(value);
                }
                Stmt::While { cond, body, .. } => {
                    self.expression(cond);
                    self.statements(&body.stmts);
                }
                Stmt::For {
                    pat, iter, body, ..
                } => {
                    self.pattern(pat);
                    self.expression(iter);
                    self.statements(&body.stmts);
                }
                Stmt::Expr(expr) | Stmt::Return(Some(expr), _) => self.expression(expr),
                _ => {}
            }
        }
    }

    fn expression(&mut self, expr: &'a Expr) {
        match expr {
            Expr::Call(callee, args, _) => {
                self.calls.push((callee, args));
                self.expression(callee);
                for arg in args {
                    self.expression(&arg.expr);
                }
            }
            Expr::Closure(params, body, _) => {
                self.parameters(params);
                self.expression(body);
            }
            Expr::Unary(_, e, _)
            | Expr::Field(e, _, _)
            | Expr::ErrorProp(e, _)
            | Expr::TypeTest(e, _, _, _) => self.expression(e),
            Expr::Binary(_, a, b, _) | Expr::Index(a, b, _) | Expr::Range(a, b, _) => {
                self.expression(a);
                self.expression(b);
            }
            Expr::IfLet(pat, cond, body, tail, _) => {
                self.pattern(pat);
                self.expression(cond);
                self.statements(&body.stmts);
                if let Some(tail) = tail {
                    self.expression(tail);
                }
            }
            Expr::If(cond, body, tail, _) => {
                self.expression(cond);
                self.statements(&body.stmts);
                if let Some(tail) = tail {
                    self.expression(tail);
                }
            }
            Expr::Block(body, _) => self.statements(&body.stmts),
            Expr::Match(value, arms, _) => {
                self.expression(value);
                for arm in arms {
                    self.pattern(&arm.pattern);
                    self.expression(&arm.body);
                }
            }
            Expr::Array(values, _) => {
                for value in values {
                    self.expression(value);
                }
            }
            Expr::TypeLit(_, fields, _) | Expr::VariantLit(_, _, fields, _) => {
                for (name, value) in fields {
                    self.fields.insert(name);
                    self.expression(value);
                }
            }
            Expr::Str(parts, _) => {
                for part in parts {
                    if let brass_parser::ast::StrSeg::Expr(expr) = part {
                        self.expression(expr);
                    }
                }
            }
            _ => {}
        }
    }

    fn origin(&self, expr: &Expr, closed_calls: &HashSet<&str>) -> bool {
        match expr {
            Expr::Int(..) | Expr::Float(..) => true,
            Expr::Call(callee, _, _) => {
                if primitive_call(callee, &self.locals) {
                    return false;
                }
                match &**callee {
                    Expr::Ident(name, _) if !self.locals.contains(name.as_str()) => {
                        !closed_calls.contains(name.as_str())
                    }
                    Expr::Field(_, name, _) => !closed_calls.contains(name.as_str()),
                    _ => true,
                }
            }
            Expr::Ident(name, _) => self.origins.contains(name.as_str()),
            Expr::Unary(_, value, _) => self.origin(value, closed_calls),
            Expr::Binary(_, a, b, _) => {
                self.origin(a, closed_calls) && self.origin(b, closed_calls)
            }
            Expr::Block(body, _) => {
                matches!(body.stmts.last(), Some(Stmt::Expr(value)) if self.origin(value, closed_calls))
            }
            _ => false,
        }
    }
}

// Arithmetic containing only the stored root and int32-fitting integers cannot
// exceed that root's default floor. Other names and float literals decline proof.
fn self_literal(expr: &Expr, name: &str) -> bool {
    if let Some(value) = expr.int_literal_value() {
        return i32::try_from(value).is_ok();
    }
    match expr {
        Expr::Ident(value, _) => value == name,
        Expr::Unary(_, value, _) => self_literal(value, name),
        Expr::Binary(_, a, b, _) => self_literal(a, name) && self_literal(b, name),
        _ => false,
    }
}

fn integer_expr(expr: &Expr, names: &HashSet<&str>) -> bool {
    if let Some(value) = expr.int_literal_value() {
        return i32::try_from(value).is_ok();
    }
    match expr {
        Expr::Ident(name, _) => names.contains(name.as_str()),
        Expr::Unary(_, value, _) => integer_expr(value, names),
        Expr::Binary(_, a, b, _) => integer_expr(a, names) && integer_expr(b, names),
        _ => false,
    }
}

// Primitive conversions have a declared result and never elaborate a source body.
fn primitive_call(callee: &Expr, locals: &HashSet<&str>) -> bool {
    matches!(callee, Expr::Field(base, method, _) if matches!(&**base,
        Expr::Ident(name, _) if !locals.contains(name.as_str())
            && builtins::primitive_static_return(name, method).is_some()))
}
