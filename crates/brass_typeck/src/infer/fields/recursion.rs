//! Recursion guards for call graphs that require compile-time field expansion.

use super::*;

// Bound distinct reflected expansions independently of the general body budget.
const MAX_FIELDS_RECURSION_DEPTH: usize = 8;
const INCOMPLETE_FIELDS: &str = "cannot determine this `fields(..)` loop's field list within the elaboration limit; simplify the recursive call chain";

/// A conservative call graph: each body maps to a reachable `fields` expression.
/// Names retain all matching functions and methods, including references passed
/// as values. An indirect call can reach any reflected body.
#[derive(Default)]
pub(in crate::infer) struct Reflection {
    loops: HashMap<Span, Span>,
}

impl Reflection {
    /// Index named references and indirect calls once for the checked program.
    pub(in crate::infer) fn new(program: &Program, builtin: impl Fn(&str) -> bool) -> Self {
        let mut bodies = Vec::new();
        for f in program.functions.values() {
            bodies.push((f.signature.name.as_str(), &f.decl.body, &f.decl.params));
        }
        for ty in program.types.values() {
            let methods: Vec<_> = match &ty.kind {
                TypeKind::Record { methods, .. } => methods.values().collect(),
                TypeKind::Sum { variants } => {
                    variants.iter().flat_map(|v| v.methods.values()).collect()
                }
            };
            for method in methods {
                if let Some(body) = &method.decl.body {
                    bodies.push((method.signature.name.as_str(), body, &method.decl.params));
                }
            }
        }
        let mut scans = Vec::new();
        let mut names: HashMap<&str, Vec<usize>> = HashMap::default();
        for (i, (name, body, params)) in bodies.iter().enumerate() {
            names.entry(name).or_default().push(i);
            let mut scan = Scan::default();
            scan.locals.extend(params.iter().map(|p| p.name.clone()));
            scan.block(body);
            scans.push(scan);
        }
        for scan in &mut scans {
            scan.indirect |= scan.calls.iter().any(|name| {
                scan.locals.contains(name) || (!names.contains_key(name.as_str()) && !builtin(name))
            });
        }
        let mut reachable: Vec<_> = scans.iter().map(|s| s.field_loop).collect();
        let Some(any_loop) = reachable.iter().flatten().copied().min_by_key(|s| s.lo) else {
            return Self::default();
        };
        loop {
            let mut changed = false;
            for (i, scan) in scans.iter().enumerate() {
                if reachable[i].is_some() {
                    continue;
                }
                let target = if scan.indirect {
                    Some(any_loop)
                } else {
                    scan.names
                        .iter()
                        .filter_map(|name| names.get(name.as_str()))
                        .flatten()
                        .filter_map(|j| reachable[*j])
                        .min_by_key(|s| s.lo)
                };
                if target.is_some() {
                    reachable[i] = target;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        Self {
            loops: bodies
                .iter()
                .zip(reachable)
                .filter_map(|((_, body, _), site)| site.map(|site| (body.span, site)))
                .collect(),
        }
    }
}

#[derive(Default)]
struct Scan {
    names: HashSet<String>,
    field_loop: Option<Span>,
    indirect: bool,
    calls: HashSet<String>,
    locals: HashSet<String>,
}

impl Scan {
    fn block(&mut self, body: &Block) {
        for stmt in &body.stmts {
            if let Stmt::Let { pat, .. } = stmt {
                self.locals
                    .extend(pat.bound_names().into_iter().map(str::to_owned));
            }
            match stmt {
                Stmt::For {
                    pat, iter, body, ..
                } => {
                    self.locals
                        .extend(pat.bound_names().into_iter().map(str::to_owned));
                    self.expr(iter);
                    self.block(body);
                }
                Stmt::While { cond, body, .. } => {
                    self.expr(cond);
                    self.block(body);
                }
                Stmt::Let {
                    value: Some(value), ..
                }
                | Stmt::Return(Some(value), _)
                | Stmt::Expr(value) => self.expr(value),
                Stmt::Assign { target, value, .. } => {
                    self.expr(target);
                    self.expr(value);
                }
                _ => {}
            }
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Block(body, _) => {
                self.block(body);
                return;
            }
            Expr::If(cond, body, tail, _) => {
                self.expr(cond);
                self.block(body);
                if let Some(tail) = tail {
                    self.expr(tail);
                }
                return;
            }
            Expr::IfLet(pat, value, body, tail, _) => {
                self.locals
                    .extend(pat.bound_names().into_iter().map(str::to_owned));
                self.expr(value);
                self.block(body);
                if let Some(tail) = tail {
                    self.expr(tail);
                }
                return;
            }
            Expr::Match(value, arms, _) => {
                self.expr(value);
                for arm in arms {
                    self.locals
                        .extend(arm.pattern.bound_names().into_iter().map(str::to_owned));
                    self.expr(&arm.body);
                }
                return;
            }
            Expr::Closure(params, body, _) => {
                self.locals.extend(params.iter().map(|p| p.name.clone()));
                self.expr(body);
                return;
            }
            Expr::Ident(name, _) | Expr::Field(_, name, _) => {
                self.names.insert(name.clone());
            }
            Expr::Call(callee, _, span) => match &**callee {
                Expr::Ident(name, _) if name == "fields" => {
                    self.field_loop = Some(*span);
                }
                Expr::Ident(name, _) => {
                    self.calls.insert(name.clone());
                }
                Expr::Field(..) => {
                    self.indirect = true;
                }
                _ => self.indirect = true,
            },
            _ => {}
        }
        brass_hir::captures::walk_subexprs(expr, &mut |child| self.expr(child));
    }
}

impl Checker<'_> {
    /// Expand only fully known, distinct reflected instances. Open frames use
    /// the symbol guard; concrete expansion is bounded and reports an incomplete
    /// field list at the loop instead of accepting an unchecked instance.
    /// `None` stops this elaboration after the limit diagnostic is recorded.
    pub(in crate::infer) fn fields_recursion_key(
        &mut self,
        key: String,
        callable: &brass_hir::InstanceCallable,
        body: Span,
        args: &[Type],
    ) -> Option<String> {
        if !self.instantiating.contains(&key) || self.reflection_loop(body).is_none() {
            return Some(key);
        }
        let canonical = |arg: &Type| brass_hir::instance_key_type(self.program, &self.resolve(arg));
        let args: Vec<_> = args.iter().map(canonical).collect();
        if !args.iter().all(brass_hir::is_fully_known) {
            return Some(key);
        }
        let prefix = format!("{key}:fields=");
        // Dedicated declaration passes contribute an instance frame but no
        // elaboration key. They precede all call-site frames, so pairing from
        // the top excludes them while retaining each active call's guard.
        let frames = self
            .instance_stack
            .iter()
            .rev()
            .filter(|tag| tag.callable == *callable);
        let keys = self
            .elaboration_stack
            .iter()
            .rev()
            .filter(|active| **active == key || active.starts_with(&prefix));
        for (frame, active) in frames.zip(keys) {
            let previous: Vec<_> = frame.args.iter().map(canonical).collect();
            if !previous.iter().all(brass_hir::is_fully_known) {
                return Some(key);
            }
            if previous == args {
                return Some(active.clone());
            }
        }
        if self
            .elaboration_stack
            .iter()
            .filter(|active| active.contains(":fields="))
            .count()
            >= MAX_FIELDS_RECURSION_DEPTH
        {
            self.depth_capped += 1;
            self.report_incomplete_fields(body);
            return None;
        }
        Some(format!("{prefix}{args:?}"))
    }

    fn reflection_loop(&self, body: Span) -> Option<Span> {
        self.fields_reflection
            .get_or_init(|| {
                Reflection::new(self.program, |name| {
                    self.builtin_function_type_light(name).is_some()
                })
            })
            .loops
            .get(&brass_hir::unshift_span(body))
            .copied()
    }

    /// Identify field-list limit diagnostics that must retain their loop location.
    pub(in crate::infer) fn is_incomplete_fields(error: &TypeError) -> bool {
        error.message.starts_with(INCOMPLETE_FIELDS)
    }

    /// A capped reflected walk cannot provide a safe expansion for its instance.
    pub(in crate::infer) fn report_incomplete_fields(&mut self, body: Span) {
        if let Some(span) = self.reflection_loop(body) {
            self.errors.push(TypeError {
                message: INCOMPLETE_FIELDS.to_owned(),
                span,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn program(source: &str) -> Program {
        let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["main".into()],
            ast: brass_parser::parse(source).unwrap(),
        }]);
        assert!(errors.is_empty(), "{errors:?}");
        program
    }

    #[test]
    fn capped_reflection_reports_the_reachable_loop() {
        let p = program(
            "fun walk(v) -> int32 { for f in fields(v) { }\n return 0 }\n fun forward(v) -> int32 { return walk(v) }",
        );
        let mut c = Checker::new(&p, Rc::new(brass_typesys::RowInfo::analyze(&p)));
        // Exhaust the existing depth bound without building a large fixture.
        for i in 0..64 {
            c.instantiating.insert(format!("occupied:{i}"));
        }
        let f = &p.functions["forward"];
        c.instantiate_function_call(
            "forward",
            &f.module,
            &f.signature.params,
            &f.decl.body,
            f.signature.ret_ty.clone(),
            Type::Int(IntKind::I32),
            &[Type::Bool],
            f.decl.body.span,
        );
        assert_eq!(c.errors.len(), 1, "{:?}", c.errors);
        let loop_site = c
            .reflection_loop(p.functions["walk"].decl.body.span)
            .unwrap();
        assert_eq!(c.errors[0].span, loop_site);
        assert!(
            c.errors[0]
                .message
                .contains("this `fields(..)` loop's field list")
        );
        assert!(c.fields_loops.is_empty());
    }

    #[test]
    fn open_recursive_arguments_and_frames_reuse_the_symbol_guard() {
        let p = program("fun walk(v) -> int32 { for f in fields(v) { }\n return 0 }");
        let mut c = Checker::new(&p, Rc::new(brass_typesys::RowInfo::analyze(&p)));
        let callable = brass_hir::InstanceCallable::Function("walk".into());
        let body = p.functions["walk"].decl.body.span;
        let base = "fn:walk".to_owned();
        c.instantiating.insert(base.clone());
        c.elaboration_stack.push(base.clone());
        c.enter_instance(callable.clone(), &[Type::Bool]);
        let open = Type::Nullable(Box::new(Type::Unknown(brass_hir::INFER_VAR)));
        assert_eq!(
            c.fields_recursion_key(base.clone(), &callable, body, std::slice::from_ref(&open))
                .unwrap(),
            base
        );
        c.leave_instance();
        c.enter_instance(callable.clone(), &[open]);
        assert_eq!(
            c.fields_recursion_key(base.clone(), &callable, body, &[Type::Str])
                .unwrap(),
            base
        );
        assert!(c.errors.is_empty());
    }

    #[test]
    fn concrete_expansion_is_bounded_before_the_general_budget() {
        let p = program("fun walk(v) -> int32 { for f in fields(v) { }\n return 0 }");
        let mut c = Checker::new(&p, Rc::new(brass_typesys::RowInfo::analyze(&p)));
        let callable = brass_hir::InstanceCallable::Function("walk".into());
        let body = p.functions["walk"].decl.body.span;
        let base = "fn:walk".to_owned();
        c.instantiating.insert(base.clone());
        c.elaboration_stack.push(base.clone());
        c.enter_instance(callable.clone(), &[Type::Bool]);
        let mut arg = Type::Bool;
        for _ in 0..MAX_FIELDS_RECURSION_DEPTH {
            arg = Type::Slice(Box::new(arg));
            let key = c
                .fields_recursion_key(base.clone(), &callable, body, std::slice::from_ref(&arg))
                .unwrap();
            assert_ne!(key, base);
            c.instantiating.insert(key.clone());
            c.elaboration_stack.push(key);
            c.enter_instance(callable.clone(), std::slice::from_ref(&arg));
        }
        // A matching back-edge remains valid even when distinct expansion is full.
        assert_eq!(
            c.fields_recursion_key(base.clone(), &callable, body, &[Type::Bool])
                .unwrap(),
            base
        );
        arg = Type::Slice(Box::new(arg));
        assert_eq!(
            c.fields_recursion_key(base.clone(), &callable, body, &[arg]),
            None
        );
        assert_eq!(c.errors.len(), 1);
        assert_eq!(c.errors[0].span, c.reflection_loop(body).unwrap());
        assert_eq!(c.depth_capped, 1);
        assert_eq!(c.elaborations, 0);
    }

    #[test]
    fn recursive_guards_retain_the_matching_instance() {
        let p = program("fun walk(v) -> int32 { for f in fields(v) { }\n return 0 }");
        let mut c = Checker::new(&p, Rc::new(brass_typesys::RowInfo::analyze(&p)));
        let callable = brass_hir::InstanceCallable::Function("walk".into());
        let body = p.functions["walk"].decl.body.span;
        let base = "fn:walk".to_owned();
        c.instantiating.insert(base.clone());
        c.elaboration_stack.push(base.clone());
        c.enter_instance(callable.clone(), &[Type::Bool]);
        assert_eq!(
            c.fields_recursion_key(base.clone(), &callable, body, &[Type::Bool])
                .unwrap(),
            base
        );
        assert_eq!(
            c.fields_recursion_key(
                base.clone(),
                &callable,
                body,
                &[Type::ConstOf(Box::new(Type::Bool))]
            )
            .unwrap(),
            base
        );
        let child = c
            .fields_recursion_key(base.clone(), &callable, body, &[Type::Str])
            .unwrap();
        assert_ne!(child, base);
        c.instantiating.insert(child.clone());
        c.elaboration_stack.push(child.clone());
        c.enter_instance(callable.clone(), &[Type::Str]);
        // A back-edge chooses its own frame, whether immediate or mutual.
        assert_eq!(
            c.fields_recursion_key(base.clone(), &callable, body, &[Type::Str])
                .unwrap(),
            child
        );
        assert_eq!(
            c.fields_recursion_key(base.clone(), &callable, body, &[Type::Bool])
                .unwrap(),
            base
        );
    }
}
