//! A tree-walking interpreter over monomorphized MIR.
//!
//! The interpreter is the REPL's execution back end. It does not implement
//! `prepoly_engine::Codegen` -- that trait is a *compiler* seam (it walks each MIR
//! block once to emit code, so it cannot itself iterate a loop). Instead the
//! interpreter consumes the same [`MonoProgram`] the typed LLVM back end consumes
//! and walks the control-flow graph directly: it follows `Goto`/`CondBranch`
//! terminators at run time, so loops and recursion execute naturally.
//!
//! The dispatch mirrors `prepoly_engine::codegen` arm for arm -- call routing
//! (free / method / static / builtin / indirect), the implicit `Ok`-wrapping of a
//! fallible callable's bare return, growable-array methods, typed I/O -- but each
//! leaf evaluates a [`Value`] rather than emitting an instruction. Because the
//! program is already monomorphized, every operand's concrete type is known and is
//! consulted for width/sign-correct integer arithmetic and for rendering.

use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Write;
use std::rc::Rc;

use prepoly_engine::{
    MonoFunction, MonoProgram, binary_operand_type, closure_symbol, instance_symbol, is_comparison,
    method_symbol, numeric_conv_ret, operand_type_of, prim_method_instance, static_symbol,
};
use prepoly_hir::{FloatKind, IntKind, Program, RESULT_TYPE_ID, Type};
use prepoly_mir::{Callee, Literal, MirStmt, Operand, Place, Projection, Rvalue, Terminator};
use prepoly_parser::ast::{BinOp, UnaryOp};

use crate::format::{float_str, format_value};
use crate::value::{ClosureObj, MAX_VALUE_DEPTH, Value, VariantObj};

/// Guard against unbounded native recursion: a runaway recursive Prepoly program
/// would otherwise overflow the host stack and abort the process. Deep enough for
/// ordinary recursion (factorial, tree walks) while keeping a clear error.
const MAX_DEPTH: usize = 8000;

/// One activation record: the storage for a body's locals (parameters, captures,
/// and temporaries), indexed by `LocalId`.
struct Frame {
    locals: Vec<Value>,
}

/// The interpreter over one monomorphized program.
pub struct Interp<'p, 'm> {
    program: &'p MonoProgram<'m>,
    hir: &'p Program,
    out: &'p mut dyn Write,
    /// Module-level globals, written by init bodies and read via `Rvalue::Global`.
    globals: HashMap<String, Value>,
    depth: usize,
}

impl<'p, 'm> Interp<'p, 'm> {
    pub fn new(program: &'p MonoProgram<'m>, hir: &'p Program, out: &'p mut dyn Write) -> Self {
        Interp {
            program,
            hir,
            out,
            globals: HashMap::new(),
            depth: 0,
        }
    }

    /// Run the program: every module initializer in order, then `main`.
    pub fn run(&mut self) -> Result<(), String> {
        let program = self.program;
        for sym in &program.init_symbols {
            if let Some(f) = program.lookup(sym) {
                self.run_instance(f, Vec::new(), &[])?;
            }
        }
        if let Some(main) = program.lookup("main") {
            self.run_instance(main, Vec::new(), &[])?;
        }
        Ok(())
    }

    /// Execute one callable instance with the given argument and capture values,
    /// returning its result. Parameters and captures are bound into a fresh frame,
    /// then the CFG is walked from the entry block.
    fn run_instance(
        &mut self,
        f: &MonoFunction,
        args: Vec<Value>,
        captures: &[Value],
    ) -> Result<Value, String> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            self.depth -= 1;
            return Err("call stack depth exceeded (unbounded recursion?)".into());
        }
        let mut frame = Frame {
            locals: vec![Value::Void; f.local_types.len()],
        };
        for (i, p) in f.body.params.iter().enumerate() {
            frame.locals[p.index()] = args.get(i).cloned().unwrap_or(Value::Void);
        }
        for (cap, val) in f.captures.iter().zip(captures.iter()) {
            frame.locals[cap.index()] = val.clone();
        }
        let result = self.exec_cfg(f, &mut frame);
        self.depth -= 1;
        result
    }

    /// Walk the control-flow graph, following terminators until a `Return`.
    fn exec_cfg(&mut self, f: &MonoFunction, frame: &mut Frame) -> Result<Value, String> {
        let mut block = f.body.entry;
        loop {
            let bb = f.body.block(block);
            for s in &bb.stmts {
                self.exec_stmt(f, frame, s)?;
            }
            match &bb.term {
                Terminator::Return(op) => return self.eval_return(f, frame, op),
                Terminator::Goto(b) => block = *b,
                Terminator::CondBranch { cond, then, els } => {
                    // Mirror the typed back end's fold (including the structural
                    // graceful degradation: a then-branch that cannot type for this
                    // value makes the condition statically false), then fall back to
                    // a runtime truthiness test.
                    block = match prepoly_engine::cond_static_truthiness(
                        f.body,
                        &f.local_types,
                        &f.ret,
                        cond,
                        *then,
                    ) {
                        Some(true) => *then,
                        Some(false) => *els,
                        None => {
                            let cty = operand_type_of(cond, &f.local_types);
                            let v = self.eval_operand(f, frame, cond, &cty)?;
                            if truthy(&v, &cty) { *then } else { *els }
                        }
                    };
                }
                Terminator::Unreachable => {
                    return Err("reached unreachable code (an unmatched `match`)".into());
                }
            }
        }
    }

    /// Evaluate a body's return value, applying the fallible `Ok`-wrapping the
    /// typed back end applies: a fallible callable that returns a bare (non-Result)
    /// value yields `Result.Ok { value: v }`.
    fn eval_return(
        &mut self,
        f: &MonoFunction,
        frame: &mut Frame,
        op: &Operand,
    ) -> Result<Value, String> {
        if matches!(f.ret, Type::Void) {
            return Ok(Value::Void);
        }
        let op_ty = operand_type_of(op, &f.local_types);
        // A fallible callable implicitly Ok-wraps a bare return value. Exempt:
        // a `null` returned when the ret is `Result<..>?` -- the failure arm
        // of a nullable `expr!` returns null itself, not `Ok(null)`. (With a
        // plain `Result` ret, a null IS an Ok payload.)
        let null_passthrough =
            op_ty.is_null() && matches!(&f.ret, Type::Nullable(inner) if inner.is_result_type());
        if f.fallible && !is_result_ty(&op_ty) && !null_passthrough {
            let ok_ty = result_ok_type(&f.ret);
            let v = self.eval_operand(f, frame, op, &ok_ty)?;
            Ok(make_variant("Ok", &[("value", v)]))
        } else {
            let v = self.eval_operand(f, frame, op, &f.ret)?;
            Ok(v)
        }
    }

    fn exec_stmt(
        &mut self,
        f: &MonoFunction,
        frame: &mut Frame,
        s: &MirStmt,
    ) -> Result<(), String> {
        match s {
            MirStmt::Assign(local, rv) => {
                let dest = f.local_type(*local).clone();
                let v = self.eval_rvalue(f, frame, rv, &dest)?;
                frame.locals[local.index()] = v;
                Ok(())
            }
            MirStmt::Eval(rv) => {
                self.eval_rvalue(f, frame, rv, &Type::Void)?;
                Ok(())
            }
            MirStmt::Store(place, op) => self.exec_store(f, frame, place, op),
            MirStmt::SetGlobal(name, op) => {
                let gty = self
                    .program
                    .global_type(name)
                    .cloned()
                    .unwrap_or(Type::Void);
                let v = self.eval_operand(f, frame, op, &gty)?;
                self.globals.insert(name.clone(), v);
                Ok(())
            }
        }
    }

    /// `obj.field = v` / `arr[i] = v`: mutate the heap object the base local holds.
    fn exec_store(
        &mut self,
        f: &MonoFunction,
        frame: &mut Frame,
        place: &Place,
        op: &Operand,
    ) -> Result<(), String> {
        match place.proj.as_slice() {
            [Projection::Field(field)] => {
                let base_ty = f.local_type(place.local).clone();
                let fty = record_field_type(&base_ty, field);
                let v = self.eval_operand(f, frame, op, &fty)?;
                let base = frame.locals[place.local.index()].clone();
                let key = field_key(field).to_string();
                match base {
                    Value::Record(map) => {
                        map.borrow_mut().insert(key, v);
                    }
                    Value::Variant(var) => {
                        var.fields.borrow_mut().insert(key, v);
                    }
                    _ => {}
                }
                Ok(())
            }
            [Projection::Index(idx)] => {
                let arr_ty = f.local_type(place.local).clone();
                let elem_ty = element_type(&arr_ty);
                let v = self.eval_operand(f, frame, op, &elem_ty)?;
                let it = operand_type_of(idx, &f.local_types);
                let i = self.eval_operand(f, frame, idx, &it)?.as_int();
                let base = frame.locals[place.local.index()].clone();
                if let Value::Array(arr) = base {
                    let mut b = arr.borrow_mut();
                    let i = i as usize;
                    if i >= b.len() {
                        return Err("array index out of bounds (store)".into());
                    }
                    b[i] = v;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn eval_rvalue(
        &mut self,
        f: &MonoFunction,
        frame: &mut Frame,
        rv: &Rvalue,
        dest_ty: &Type,
    ) -> Result<Value, String> {
        match rv {
            Rvalue::Use(op) => self.eval_operand(f, frame, op, dest_ty),
            Rvalue::Bin(op, a, b) => {
                let operand_ty = if is_comparison(*op) {
                    binary_operand_type(a, b, &f.local_types)
                } else {
                    dest_ty.clone()
                };
                let va = self.eval_operand(f, frame, a, &operand_ty)?;
                let vb = self.eval_operand(f, frame, b, &operand_ty)?;
                eval_bin(*op, &va, &vb, &operand_ty)
            }
            Rvalue::Un(UnaryOp::Not, a) => {
                let aty = operand_type_of(a, &f.local_types);
                let va = self.eval_operand(f, frame, a, &aty)?;
                Ok(eval_unary(UnaryOp::Not, &va, &aty))
            }
            Rvalue::Un(op, a) => {
                let va = self.eval_operand(f, frame, a, dest_ty)?;
                Ok(eval_unary(*op, &va, dest_ty))
            }
            Rvalue::Call(callee, args) => self.eval_call(f, frame, callee, args, dest_ty),
            Rvalue::Record { fields, .. } => {
                let mut map = HashMap::with_capacity(fields.len());
                for (name, op) in fields {
                    let fty = record_field_type(dest_ty, name);
                    let v = self.eval_operand(f, frame, op, &fty)?;
                    map.insert(name.clone(), v);
                }
                Ok(Value::Record(Rc::new(RefCell::new(map))))
            }
            // `T.from(v)`: the same per-instance decision as the JIT. `dest_ty` is
            // `T?`; using the source's static (per-instance) type, if it has every
            // field `T` declares with a matching type, build the record by copying
            // those fields (shared, like the JIT's retain), else yield null.
            Rvalue::RecordFrom { source, .. } => {
                let target = match dest_ty {
                    Type::Nullable(inner) => inner.as_ref().clone(),
                    other => other.clone(),
                };
                let src_ty = operand_type_of(source, &f.local_types);
                if !record_from_succeeds(&src_ty, &target) {
                    return Ok(Value::Null);
                }
                let src = self.eval_operand(f, frame, source, &src_ty)?;
                let Value::Record(src_map) = src else {
                    return Ok(Value::Null);
                };
                let mut map = HashMap::new();
                for name in record_field_names(&target) {
                    if let Some(v) = src_map.borrow().get(&name) {
                        map.insert(name, v.clone());
                    }
                }
                Ok(Value::Record(Rc::new(RefCell::new(map))))
            }
            // The view of a callee parameter's row: a filtered clone of the
            // source record holding exactly the view type's fields, with a
            // guarded field the source lacks (or carries at a non-flowing
            // type) materialized as null. The per-field decision is the shared
            // engine plan over the static types, so the interpreter and the
            // typed back end degrade identically. A non-structural destination
            // is mono's defensive identity pass-through.
            Rvalue::RecordView { source, .. } => {
                let src_ty = operand_type_of(source, &f.local_types);
                if !matches!(dest_ty, Type::Record(n) if n.id == prepoly_hir::STRUCTURAL_RECORD_ID)
                {
                    return self.eval_operand(f, frame, source, dest_ty);
                }
                let src = self.eval_operand(f, frame, source, &src_ty)?;
                let src_map = match &src {
                    Value::Record(map) => Some(map.clone()),
                    _ => None,
                };
                let mut map = HashMap::new();
                for (name, fty, plan) in prepoly_engine::view_field_plans(dest_ty, &src_ty) {
                    let v = match (&plan, &src_map) {
                        (prepoly_engine::ViewFieldPlan::Copy, Some(m)) => {
                            let ft = record_field_type(&src_ty, &name);
                            let v = m.borrow().get(&name).cloned().unwrap_or(Value::Null);
                            // Value nullability is implicit (a value or Null),
                            // so only the numeric widening of `coerce` applies.
                            coerce(v, &ft, &fty)
                        }
                        _ => Value::Null,
                    };
                    map.insert(name, v);
                }
                Ok(Value::Record(Rc::new(RefCell::new(map))))
            }
            Rvalue::Variant {
                variant, fields, ..
            } => {
                let mut map = HashMap::with_capacity(fields.len());
                for (name, op) in fields {
                    let fty = operand_type_of(op, &f.local_types);
                    let v = self.eval_operand(f, frame, op, &fty)?;
                    map.insert(field_key(name).to_string(), v);
                }
                Ok(Value::Variant(Rc::new(VariantObj {
                    variant: variant.clone(),
                    fields: RefCell::new(map),
                })))
            }
            Rvalue::Closure { id, captures } => {
                let param_types = match dest_ty {
                    Type::Fun(p, _) => p.clone(),
                    _ => Vec::new(),
                };
                let mut capture_types = Vec::with_capacity(captures.len());
                let mut cap_vals = Vec::with_capacity(captures.len());
                for op in captures {
                    let cty = operand_type_of(op, &f.local_types);
                    let v = self.eval_operand(f, frame, op, &cty)?;
                    capture_types.push(cty);
                    cap_vals.push(v);
                }
                Ok(Value::Closure(Rc::new(ClosureObj {
                    id: *id,
                    capture_types,
                    captures: cap_vals,
                    param_types,
                })))
            }
            Rvalue::Array(es) => {
                // A heterogeneous bracket literal is a tuple: each element is
                // built at its own positional type (an int64 element must not be
                // materialized at a uniform int32). A homogeneous one shares the
                // single element type.
                let mut vals = Vec::with_capacity(es.len());
                if let Type::Tuple(elem_types) = dest_ty {
                    for (op, ety) in es.iter().zip(elem_types) {
                        vals.push(self.eval_operand(f, frame, op, ety)?);
                    }
                } else {
                    let elem_ty = element_type(dest_ty);
                    for op in es {
                        vals.push(self.eval_operand(f, frame, op, &elem_ty)?);
                    }
                }
                Ok(Value::Array(Rc::new(RefCell::new(vals))))
            }
            Rvalue::Load(place) => self.eval_load(f, frame, place),
            Rvalue::Global(name) => Ok(self.globals.get(name).cloned().unwrap_or(Value::Void)),
        }
    }

    fn eval_load(
        &mut self,
        f: &MonoFunction,
        frame: &mut Frame,
        place: &Place,
    ) -> Result<Value, String> {
        match place.proj.as_slice() {
            [Projection::Field(field)] => {
                let base = frame.locals[place.local.index()].clone();
                Ok(load_field(&base, field))
            }
            [Projection::Index(idx)] => {
                let base = frame.locals[place.local.index()].clone();
                let it = operand_type_of(idx, &f.local_types);
                let i = self.eval_operand(f, frame, idx, &it)?.as_int();
                match base {
                    Value::Array(a) => a
                        .borrow()
                        .get(i as usize)
                        .cloned()
                        .ok_or_else(|| "array index out of bounds (load)".to_string()),
                    _ => Ok(Value::Void),
                }
            }
            _ => Ok(Value::Void),
        }
    }

    fn eval_operand(
        &mut self,
        f: &MonoFunction,
        frame: &mut Frame,
        op: &Operand,
        expected_ty: &Type,
    ) -> Result<Value, String> {
        match op {
            Operand::Local(id) => {
                let v = frame.locals[id.index()].clone();
                let from = f.local_type(*id);
                Ok(coerce(v, from, expected_ty))
            }
            Operand::Const(lit) => Ok(eval_const(lit, expected_ty)),
        }
    }

    /// Resolve and perform a call, routing exactly as `codegen_call` does.
    fn eval_call(
        &mut self,
        f: &MonoFunction,
        frame: &mut Frame,
        callee: &Callee,
        args: &[Operand],
        dest_ty: &Type,
    ) -> Result<Value, String> {
        let arg_types: Vec<Type> = args
            .iter()
            .map(|a| operand_type_of(a, &f.local_types))
            .collect();
        let target: String = match callee {
            // Growable-array methods are runtime operations on the slice, not user
            // methods.
            Callee::Method(name)
                if name == "push"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                let elem = element_type(&arg_types[0]);
                let arr = self.eval_operand(f, frame, &args[0], &arg_types[0])?;
                let v = self.eval_operand(f, frame, &args[1], &elem)?;
                if let Value::Array(a) = arr {
                    a.borrow_mut().push(v);
                }
                return Ok(Value::Void);
            }
            Callee::Method(name)
                if name == "insert"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                let elem = element_type(&arg_types[0]);
                let arr = self.eval_operand(f, frame, &args[0], &arg_types[0])?;
                let idx = self
                    .eval_operand(f, frame, &args[1], &arg_types[1])?
                    .as_int();
                let v = self.eval_operand(f, frame, &args[2], &elem)?;
                if let Value::Array(a) = arr {
                    let mut b = a.borrow_mut();
                    let i = (idx as usize).min(b.len());
                    b.insert(i, v);
                }
                return Ok(Value::Void);
            }
            Callee::Method(name)
                if name == "remove"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                let arr = self.eval_operand(f, frame, &args[0], &arg_types[0])?;
                let idx = self
                    .eval_operand(f, frame, &args[1], &arg_types[1])?
                    .as_int();
                if let Value::Array(a) = arr {
                    let mut b = a.borrow_mut();
                    if (idx as usize) < b.len() {
                        return Ok(b.remove(idx as usize));
                    }
                    return Err("array remove index out of bounds".into());
                }
                return Ok(Value::Void);
            }
            Callee::Method(name)
                if name == "pop"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                let arr = self.eval_operand(f, frame, &args[0], &arg_types[0])?;
                if let Value::Array(a) = arr {
                    return Ok(a.borrow_mut().pop().unwrap_or(Value::Null));
                }
                return Ok(Value::Null);
            }
            Callee::Method(name)
                if name == "len"
                    && matches!(
                        arg_types.first().map(unwrap_nullable),
                        Some(Type::Slice(_) | Type::Array(..) | Type::Str)
                    ) =>
            {
                let v = self.eval_operand(f, frame, &args[0], &arg_types[0])?;
                return Ok(length_of(&v));
            }
            // File I/O methods are runtime primitives the REPL does not implement.
            Callee::Method(name)
                if matches!(name.as_str(), "read" | "write" | "close" | "size" | "seek")
                    && matches!(arg_types.first(), Some(Type::Record(r)) if r.is_name("File")) =>
            {
                return Err("file I/O is not supported by the REPL runtime".into());
            }
            Callee::Method(name) => {
                let msym = method_symbol(name, &arg_types);
                if self.program.lookup(&msym).is_some() {
                    msym
                } else if let Some(psym) = prim_method_instance(self.program, name, &arg_types) {
                    psym
                } else {
                    instance_symbol(name, &arg_types)
                }
            }
            Callee::Static { ty, method } if numeric_conv_ret(ty, method).is_some() => {
                return self.eval_conv(f, frame, ty, method, args);
            }
            Callee::Static { ty, .. } if ty == "File" => {
                return Err("file standard streams are not supported by the REPL runtime".into());
            }
            // The destination type keys a return-polymorphic, no-argument
            // constructor (a witness-free `new()`) to the instance the
            // monomorphizer created for this result type.
            Callee::Static { ty, method } => static_symbol(ty, method, &arg_types, Some(dest_ty)),
            Callee::Free(base) if base == "print" || base == "println" => {
                return self.eval_io(f, frame, base, args);
            }
            Callee::Free(base) => instance_symbol(base, &arg_types),
            Callee::Builtin(name) => return self.eval_builtin(f, frame, name, args),
            Callee::Indirect(callee_op) => return self.eval_indirect(f, frame, callee_op, args),
        };
        let program = self.program;
        let Some(inst) = program.lookup(&target) else {
            return Err(format!("call to unresolved instance `{target}`"));
        };
        let params = inst.type_args.clone();
        let mut vals = Vec::with_capacity(args.len());
        for (a, pty) in args.iter().zip(params.iter()) {
            vals.push(self.eval_operand(f, frame, a, pty)?);
        }
        self.run_instance(inst, vals, &[])
    }

    /// An indirect (closure) call: resolve the closure's monomorphized instance
    /// from its capture/parameter types, then run it with the captured environment.
    fn eval_indirect(
        &mut self,
        f: &MonoFunction,
        frame: &mut Frame,
        callee_op: &Operand,
        args: &[Operand],
    ) -> Result<Value, String> {
        let callee_ty = operand_type_of(callee_op, &f.local_types);
        let cv = self.eval_operand(f, frame, callee_op, &callee_ty)?;
        let Value::Closure(clo) = cv else {
            return Err("indirect call of a non-closure value".into());
        };
        let params: Vec<Type> = match &callee_ty {
            Type::Fun(p, _) => p.clone(),
            _ => Vec::new(),
        };
        let mut vals = Vec::with_capacity(args.len());
        for (i, a) in args.iter().enumerate() {
            let pty = params.get(i).cloned().unwrap_or(Type::Void);
            vals.push(self.eval_operand(f, frame, a, &pty)?);
        }
        let sym = closure_symbol(clo.id, &clo.capture_types, &clo.param_types);
        let program = self.program;
        let Some(inst) = program.lookup(&sym) else {
            return Err(format!("call to unresolved closure instance `{sym}`"));
        };
        let captures = clo.captures.clone();
        self.run_instance(inst, vals, &captures)
    }

    /// MIR-internal builtins and runtime primitives, mirroring `codegen_builtin`.
    fn eval_builtin(
        &mut self,
        f: &MonoFunction,
        frame: &mut Frame,
        name: &str,
        args: &[Operand],
    ) -> Result<Value, String> {
        match name {
            "value_matches" => {
                let sty = operand_type_of(&args[0], &f.local_types);
                let subj = self.eval_operand(f, frame, &args[0], &sty)?;
                let variant = str_const(&args[1]).unwrap_or_default();
                Ok(Value::Bool(matches_variant(&subj, variant)))
            }
            // `__deep_copy(x)`: a fresh, independent copy of `x` (value-passing of a
            // non-reference heap argument). Aggregates get new mutable storage so the
            // callee's mutations do not reach the caller; immutable/shared values are
            // returned as-is (the Rc share is sound -- they are never mutated).
            "__deep_copy" => {
                let ty = operand_type_of(&args[0], &f.local_types);
                let v = self.eval_operand(f, frame, &args[0], &ty)?;
                deep_copy_value(&v)
            }
            // `__present(x)`: the `if let x = e` presence test -- false only for a
            // null subject. Non-nullable subjects fold statically in
            // `cond_static_truthiness` and never reach here.
            "__present" => {
                let ty = operand_type_of(&args[0], &f.local_types);
                let v = self.eval_operand(f, frame, &args[0], &ty)?;
                Ok(Value::Bool(!v.is_null()))
            }
            // `__nonnull(x)`: narrow a nullable to its inner value. A non-null
            // nullable is represented transparently (the value itself), so this is
            // the identity -- the if-let then-arm has already proven non-null.
            "__nonnull" => {
                let ty = operand_type_of(&args[0], &f.local_types);
                self.eval_operand(f, frame, &args[0], &ty)
            }
            "result_is_ok" => {
                let sty = operand_type_of(&args[0], &f.local_types);
                let subj = self.eval_operand(f, frame, &args[0], &sty)?;
                Ok(Value::Bool(matches_variant(&subj, "Ok")))
            }
            "panic" => {
                let msg = str_const(&args[0]).unwrap_or_default();
                Err(msg.to_string())
            }
            "_panic" => {
                let mty = operand_type_of(&args[0], &f.local_types);
                let m = self.eval_operand(f, frame, &args[0], &mty)?;
                Err(m.as_str().to_string())
            }
            "len" | "array_len" => {
                let ty = operand_type_of(&args[0], &f.local_types);
                let v = self.eval_operand(f, frame, &args[0], &ty)?;
                Ok(length_of(&v))
            }
            "to_string" => {
                let ty = operand_type_of(&args[0], &f.local_types);
                let v = self.eval_operand(f, frame, &args[0], &ty)?;
                let hir = self.hir;
                Ok(Value::str(format_value(hir, &v, &ty)?))
            }
            "print" | "println" => self.eval_io(f, frame, name, args),
            "spawn" | "sync" | "with" | "_with_all" => Err(
                "concurrency (`spawn`/`sync`/`with`) is not supported by the REPL runtime".into(),
            ),
            // Ownership promotions inserted by the spawn auto-acquire pass. The
            // interpreter is single-threaded, so freezing/cowning a value is a
            // no-op; a program that actually spawns still errors at `spawn` above.
            "_cown" | "_freeze" => Ok(Value::Void),
            "__rt_dispatch" => {
                Err("runtime type dispatch is not supported by the REPL runtime".into())
            }
            "open" => Err("file I/O is not supported by the REPL runtime".into()),
            "_float_sqrt" | "_float_floor" | "_float_ceil" | "_float_pow" => {
                let mut vals = Vec::with_capacity(args.len());
                for a in args {
                    vals.push(
                        self.eval_operand(f, frame, a, &Type::Float(FloatKind::F64))?
                            .as_float(),
                    );
                }
                let r = match name {
                    "_float_sqrt" => vals[0].sqrt(),
                    "_float_floor" => vals[0].floor(),
                    "_float_ceil" => vals[0].ceil(),
                    _ => vals[0].powf(vals[1]),
                };
                Ok(Value::Float(r))
            }
            "_string_concat" => {
                let a = self.eval_operand(f, frame, &args[0], &Type::Str)?;
                let b = self.eval_operand(f, frame, &args[1], &Type::Str)?;
                Ok(Value::str(format!("{}{}", a.as_str(), b.as_str())))
            }
            "_string_cmp" => {
                let a = self.eval_operand(f, frame, &args[0], &Type::Str)?;
                let b = self.eval_operand(f, frame, &args[1], &Type::Str)?;
                let c = a.as_str().as_bytes().cmp(b.as_str().as_bytes());
                Ok(Value::Int(match c {
                    std::cmp::Ordering::Less => -1,
                    std::cmp::Ordering::Equal => 0,
                    std::cmp::Ordering::Greater => 1,
                }))
            }
            "_string_slice" => {
                let s = self.eval_operand(f, frame, &args[0], &Type::Str)?;
                let i64t = Type::Int(IntKind::I64);
                let start = self.eval_operand(f, frame, &args[1], &i64t)?.as_int();
                let end = self.eval_operand(f, frame, &args[2], &i64t)?.as_int();
                Ok(Value::str(string_slice(s.as_str(), start, end)))
            }
            "_string_bytes" => {
                let s = self.eval_operand(f, frame, &args[0], &Type::Str)?;
                let bytes: Vec<Value> = s
                    .as_str()
                    .as_bytes()
                    .iter()
                    .map(|b| Value::Int(*b as i64))
                    .collect();
                Ok(Value::Array(Rc::new(RefCell::new(bytes))))
            }
            "_string_find" => {
                let s = self.eval_operand(f, frame, &args[0], &Type::Str)?;
                let sub = self.eval_operand(f, frame, &args[1], &Type::Str)?;
                match s.as_str().find(sub.as_str()) {
                    Some(i) => Ok(Value::Int(i as i64)),
                    None => Ok(Value::Null),
                }
            }
            "_string_char_at" => {
                let s = self.eval_operand(f, frame, &args[0], &Type::Str)?;
                let i = self
                    .eval_operand(f, frame, &args[1], &Type::Int(IntKind::I64))?
                    .as_int();
                Ok(char_at(s.as_str(), i))
            }
            "_string_from_bytes" => {
                let aty = operand_type_of(&args[0], &f.local_types);
                let a = self.eval_operand(f, frame, &args[0], &aty)?;
                let bytes: Vec<u8> = match &a {
                    Value::Array(items) => {
                        items.borrow().iter().map(|v| v.as_int() as u8).collect()
                    }
                    _ => Vec::new(),
                };
                match String::from_utf8(bytes) {
                    Ok(s) => Ok(result_ok(Value::str(s))),
                    Err(_) => Ok(result_err("invalid UTF-8 byte sequence")),
                }
            }
            "_int_to_string" | "_float_to_string" => {
                let aty = operand_type_of(&args[0], &f.local_types);
                let v = self.eval_operand(f, frame, &args[0], &aty)?;
                let hir = self.hir;
                Ok(Value::str(format_value(hir, &v, &aty)?))
            }
            "_int_parse" | "_float_parse" => {
                let s = self.eval_operand(f, frame, &args[0], &Type::Str)?;
                let target = if name == "_int_parse" {
                    Type::Int(IntKind::I64)
                } else {
                    Type::Float(FloatKind::F64)
                };
                Ok(convert(&target, "parse", &Type::Str, &s))
            }
            "_int_to_float" => {
                let x = self.eval_operand(f, frame, &args[0], &Type::Int(IntKind::I64))?;
                Ok(convert(
                    &Type::Float(FloatKind::F64),
                    "from",
                    &Type::Int(IntKind::I64),
                    &x,
                ))
            }
            "_float_to_int" => {
                let x = self.eval_operand(f, frame, &args[0], &Type::Float(FloatKind::F64))?;
                Ok(convert(
                    &Type::Int(IntKind::I64),
                    "from",
                    &Type::Float(FloatKind::F64),
                    &x,
                ))
            }
            "_int_widen" | "_int_narrow" => {
                let i64t = Type::Int(IntKind::I64);
                let x = self.eval_operand(f, frame, &args[0], &i64t)?.as_int();
                let _from = self.eval_operand(f, frame, &args[1], &i64t)?.as_int();
                let to = self.eval_operand(f, frame, &args[2], &i64t)?.as_int();
                let signed = self
                    .eval_operand(f, frame, &args[3], &Type::Bool)?
                    .as_bool();
                if name == "_int_widen" {
                    // Widening preserves the value; it is already correctly extended.
                    Ok(Value::Int(x))
                } else {
                    Ok(int_in_range(x as i128, int_kind_from_bits(to, signed)))
                }
            }
            other => Err(format!(
                "builtin `{other}` is not supported by the REPL runtime"
            )),
        }
    }

    /// A numeric/string conversion `Type.method(arg)`.
    fn eval_conv(
        &mut self,
        f: &MonoFunction,
        frame: &mut Frame,
        ty: &str,
        method: &str,
        args: &[Operand],
    ) -> Result<Value, String> {
        let arg_ty = operand_type_of(&args[0], &f.local_types);
        let v = self.eval_operand(f, frame, &args[0], &arg_ty)?;
        if ty == "string" {
            let hir = self.hir;
            return Ok(Value::str(format_value(hir, &v, &arg_ty)?));
        }
        let target = if let Some(k) = IntKind::from_name(ty) {
            Type::Int(k)
        } else if let Some(k) = float_kind(ty) {
            Type::Float(k)
        } else {
            return Err(format!("unknown conversion target `{ty}`"));
        };
        Ok(convert(&target, method, &arg_ty, &v))
    }

    /// `print`/`println`: render a non-string argument through `to_string`, write
    /// it to the output sink, with a trailing newline for `println`.
    fn eval_io(
        &mut self,
        f: &MonoFunction,
        frame: &mut Frame,
        name: &str,
        args: &[Operand],
    ) -> Result<Value, String> {
        let newline = name == "println";
        let s = match args.first() {
            None => String::new(),
            Some(op) => {
                let ty = operand_type_of(op, &f.local_types);
                let v = self.eval_operand(f, frame, op, &ty)?;
                if matches!(ty, Type::Str) {
                    v.as_str().to_string()
                } else {
                    let hir = self.hir;
                    format_value(hir, &v, &ty)?
                }
            }
        };
        if newline {
            let _ = writeln!(self.out, "{s}");
        } else {
            let _ = write!(self.out, "{s}");
        }
        Ok(Value::Void)
    }
}

// ===== leaf value operations (no `self`) =====

/// Whether a non-bool condition is truthy: a present nullable is truthy, an absent
/// one is not; a bool is itself.
fn truthy(v: &Value, ty: &Type) -> bool {
    // Truthiness is derived from the condition's type: a bool is its own value,
    // a nullable tests non-null, and any other (non-nullable) type is true.
    match ty {
        Type::Bool => v.as_bool(),
        Type::Nullable(_) => !v.is_null(),
        _ => true,
    }
}

/// Whether a value is the named sum variant. A record (single-shape) always
/// matches; a non-aggregate never does.
/// A fresh, independent deep copy of `v`. Aggregates (array, record, sum) are
/// rebuilt with new mutable cells and recursively-copied children, so the copy
/// shares no mutable storage with the original. Scalars and immutable/shared
/// handles (string, closure) are returned as-is -- they are never mutated, so the
/// `Rc` share is sound. Errs past [`MAX_VALUE_DEPTH`]: a self-referential record
/// type can build a reference cycle, which has no finite copy.
fn deep_copy_value(v: &Value) -> Result<Value, String> {
    deep_copy_value_at(v, 0)
}

fn deep_copy_value_at(v: &Value, depth: usize) -> Result<Value, String> {
    if depth > MAX_VALUE_DEPTH {
        return Err("value depth exceeded while copying (cyclic value?)".into());
    }
    Ok(match v {
        Value::Array(a) => Value::Array(Rc::new(RefCell::new(
            a.borrow()
                .iter()
                .map(|e| deep_copy_value_at(e, depth + 1))
                .collect::<Result<_, _>>()?,
        ))),
        Value::Record(r) => Value::Record(Rc::new(RefCell::new(
            r.borrow()
                .iter()
                .map(|(k, val)| Ok((k.clone(), deep_copy_value_at(val, depth + 1)?)))
                .collect::<Result<_, String>>()?,
        ))),
        Value::Variant(var) => Value::Variant(Rc::new(VariantObj {
            variant: var.variant.clone(),
            fields: RefCell::new(
                var.fields
                    .borrow()
                    .iter()
                    .map(|(k, val)| Ok((k.clone(), deep_copy_value_at(val, depth + 1)?)))
                    .collect::<Result<_, String>>()?,
            ),
        })),
        other => other.clone(),
    })
}

fn matches_variant(v: &Value, variant: &str) -> bool {
    match v {
        Value::Variant(var) => var.variant == variant,
        Value::Record(_) => true,
        _ => false,
    }
}

/// The element count of an array, or the byte length of a string.
fn length_of(v: &Value) -> Value {
    match v {
        Value::Array(a) => Value::Int(a.borrow().len() as i64),
        Value::Str(s) => Value::Int(s.len() as i64),
        _ => Value::Int(0),
    }
}

/// Read a field of a record or sum value (a variant-qualified field name reads its
/// last segment).
fn load_field(base: &Value, field: &str) -> Value {
    let key = field_key(field);
    match base {
        // A field the record does not have reads as null (an absent structural
        // field; the type checker typed the access nullable).
        Value::Record(m) => m.borrow().get(key).cloned().unwrap_or(Value::Null),
        Value::Variant(v) => v.fields.borrow().get(key).cloned().unwrap_or(Value::Void),
        _ => Value::Null,
    }
}

/// A binary operator over two values typed `ty`. Integer arithmetic wraps and is
/// re-normalized to the operand width/sign; comparisons respect signedness.
fn eval_bin(op: BinOp, a: &Value, b: &Value, ty: &Type) -> Result<Value, String> {
    // Equality against the null literal (or between nullables) is an identity test.
    if matches!(op, BinOp::Eq | BinOp::Ne) && (a.is_null() || b.is_null()) {
        let eq = a.is_null() && b.is_null();
        return Ok(Value::Bool(if matches!(op, BinOp::Eq) { eq } else { !eq }));
    }
    match ty {
        Type::Int(k) => int_bin(op, a.as_int(), b.as_int(), *k),
        Type::Float(fk) => Ok(float_bin(op, a.as_float(), b.as_float(), *fk)),
        Type::Bool => Ok(bool_bin(op, a.as_bool(), b.as_bool())),
        Type::Str => Ok(str_bin(op, a.as_str(), b.as_str())),
        // A nullable operand narrows to its element type for arithmetic/ordering.
        Type::Nullable(inner) => eval_bin(op, a, b, inner),
        _ => Err(format!(
            "unsupported binary operand type `{}`",
            ty.display()
        )),
    }
}

fn int_bin(op: BinOp, a: i64, b: i64, k: IntKind) -> Result<Value, String> {
    let signed = int_signed(k);
    let res = match op {
        BinOp::Add => a.wrapping_add(b),
        BinOp::Sub => a.wrapping_sub(b),
        BinOp::Mul => a.wrapping_mul(b),
        BinOp::Div => {
            if b == 0 {
                return Err("integer division by zero".into());
            }
            if signed {
                a.wrapping_div(b)
            } else {
                ((a as u64).wrapping_div(b as u64)) as i64
            }
        }
        BinOp::Rem => {
            if b == 0 {
                return Err("integer remainder by zero".into());
            }
            if signed {
                a.wrapping_rem(b)
            } else {
                ((a as u64).wrapping_rem(b as u64)) as i64
            }
        }
        BinOp::BitAnd => a & b,
        BinOp::BitOr => a | b,
        BinOp::BitXor => a ^ b,
        BinOp::Shl => a.wrapping_shl(b as u32),
        BinOp::Shr => {
            if signed {
                a.wrapping_shr(b as u32)
            } else {
                ((a as u64).wrapping_shr(b as u32)) as i64
            }
        }
        BinOp::Eq => return Ok(Value::Bool(a == b)),
        BinOp::Ne => return Ok(Value::Bool(a != b)),
        BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
            let ord = if signed {
                a.cmp(&b)
            } else {
                (a as u64).cmp(&(b as u64))
            };
            return Ok(Value::Bool(ordering_matches(op, ord)));
        }
        BinOp::And | BinOp::Or => {
            return Err("logical `&&`/`||` should have been lowered to control flow".into());
        }
    };
    Ok(Value::Int(norm_int(res, k)))
}

fn float_bin(op: BinOp, a: f64, b: f64, fk: FloatKind) -> Value {
    let res = match op {
        BinOp::Add => a + b,
        BinOp::Sub => a - b,
        BinOp::Mul => a * b,
        BinOp::Div => a / b,
        BinOp::Eq => return Value::Bool(a == b),
        BinOp::Ne => return Value::Bool(a != b),
        BinOp::Lt => return Value::Bool(a < b),
        BinOp::Gt => return Value::Bool(a > b),
        BinOp::Le => return Value::Bool(a <= b),
        BinOp::Ge => return Value::Bool(a >= b),
        _ => a,
    };
    Value::Float(round_f32_if(fk, res))
}

fn bool_bin(op: BinOp, a: bool, b: bool) -> Value {
    match op {
        BinOp::Ne => Value::Bool(a != b),
        _ => Value::Bool(a == b),
    }
}

fn str_bin(op: BinOp, a: &str, b: &str) -> Value {
    match op {
        BinOp::Add => Value::str(format!("{a}{b}")),
        BinOp::Ne => Value::Bool(a != b),
        _ => Value::Bool(a == b),
    }
}

fn ordering_matches(op: BinOp, ord: std::cmp::Ordering) -> bool {
    use std::cmp::Ordering::*;
    match op {
        BinOp::Lt => ord == Less,
        BinOp::Gt => ord == Greater,
        BinOp::Le => ord != Greater,
        BinOp::Ge => ord != Less,
        _ => false,
    }
}

fn eval_unary(op: UnaryOp, v: &Value, ty: &Type) -> Value {
    match op {
        UnaryOp::Neg => match v {
            Value::Int(x) => Value::Int(norm_int(x.wrapping_neg(), int_kind(ty))),
            Value::Float(x) => Value::Float(round_f32_if(float_kind_of(ty), -x)),
            _ => v.clone(),
        },
        UnaryOp::BitNot => match v {
            Value::Int(x) => Value::Int(norm_int(!x, int_kind(ty))),
            _ => v.clone(),
        },
        UnaryOp::Not => match ty {
            Type::Nullable(_) => Value::Bool(v.is_null()),
            _ => Value::Bool(!v.as_bool()),
        },
    }
}

/// Coerce a value to the expected type: only integer width changes and float
/// narrowing are observable; everything else is the identity (a present nullable
/// is already its inner value).
fn coerce(v: Value, from: &Type, to: &Type) -> Value {
    match (&v, to) {
        (Value::Int(x), Type::Int(k)) if !matches!(from, Type::Int(kf) if kf == k) => {
            Value::Int(norm_int(*x, *k))
        }
        // An integer implicitly converts to a float (e.g. `int * float`).
        (Value::Int(x), Type::Float(fk)) => {
            let f = *x as f64;
            Value::Float(if matches!(fk, FloatKind::F32) {
                (f as f32) as f64
            } else {
                f
            })
        }
        (Value::Float(x), Type::Float(FloatKind::F32)) => Value::Float((*x as f32) as f64),
        _ => v,
    }
}

/// Materialize a constant operand at its expected type (a literal flowing into a
/// nullable position is built at the element type, the nullable cell implicit).
fn eval_const(lit: &Literal, expected_ty: &Type) -> Value {
    if let Type::Nullable(inner) = expected_ty
        && !matches!(lit, Literal::Null)
    {
        return eval_const(lit, inner);
    }
    match lit {
        Literal::Int(v) => match expected_ty {
            Type::Int(k) => Value::Int(norm_int(*v, *k)),
            _ => Value::Int(norm_int(*v, IntKind::I32)),
        },
        Literal::Float(v) => match expected_ty {
            Type::Float(FloatKind::F32) => Value::Float((*v as f32) as f64),
            _ => Value::Float(*v),
        },
        Literal::Bool(b) => Value::Bool(*b),
        Literal::Str(s) => Value::str(s.clone()),
        Literal::Void => Value::Void,
        Literal::Null => Value::Null,
    }
}

/// A numeric/string conversion `target.method(arg)`: `string.from` renders;
/// integer/float `from`/`parse` range-check into a typed `Result` (except the
/// infallible `float.from`).
fn convert(target: &Type, method: &str, arg_ty: &Type, v: &Value) -> Value {
    match target {
        Type::Int(k) => match method {
            "from" => match arg_ty {
                Type::Float(_) => float_to_int(v.as_float(), *k),
                _ => int_in_range(v.as_int() as i128, *k),
            },
            // The runtime parses as a wide integer first, so an in-range overflow
            // is reported as out-of-range, not as a parse failure (matching `text`
            // untrimmed in the message).
            "parse" => match v.as_str().trim().parse::<i128>() {
                Ok(n) => int_in_range(n, *k),
                Err(_) => result_err(&format!("cannot parse `{}` as integer", v.as_str())),
            },
            _ => result_err("unsupported integer conversion"),
        },
        Type::Float(k) => match method {
            // `float.from(int)` is infallible; it yields the float value directly.
            "from" => Value::Float(round_f32_if(*k, v.as_float())),
            "parse" => match v.as_str().trim().parse::<f64>() {
                Ok(x) => result_ok(Value::Float(round_f32_if(*k, x))),
                Err(_) => result_err(&format!("cannot parse `{}` as float", v.as_str())),
            },
            _ => result_err("unsupported float conversion"),
        },
        _ => result_err("unsupported conversion target"),
    }
}

/// Truncate a float toward zero and range-check it into integer kind `k`. The
/// out-of-range / non-finite messages match the runtime (`prepoly_runtime`) so the
/// REPL's `Result.Err` text is identical to the JIT's.
fn float_to_int(fx: f64, k: IntKind) -> Value {
    if !fx.is_finite() {
        return result_err(&format!(
            "cannot convert non-finite float `{}` to {}",
            float_str(fx),
            k.name()
        ));
    }
    let truncated = fx.trunc();
    let (min, max) = int_range(int_bits(k), int_signed(k));
    if truncated < min as f64 || truncated > max as f64 {
        return result_err(&format!(
            "float value {} is out of range for {} ({min}..={max})",
            float_str(fx),
            k.name()
        ));
    }
    result_ok(Value::Int(norm_int(truncated as i64, k)))
}

/// `Result.Ok { value }` when `x` fits integer kind `k`, else `Result.Err`, with
/// the runtime's exact out-of-range message.
fn int_in_range(x: i128, k: IntKind) -> Value {
    let (min, max) = int_range(int_bits(k), int_signed(k));
    if x < min || x > max {
        result_err(&format!(
            "integer value {x} is out of range for {} ({min}..={max})",
            k.name()
        ))
    } else {
        result_ok(Value::Int(norm_int(x as i64, k)))
    }
}

fn int_range(bits: u32, signed: bool) -> (i128, i128) {
    if signed {
        let max = (1i128 << (bits - 1)) - 1;
        (-(1i128 << (bits - 1)), max)
    } else {
        (0, (1i128 << bits) - 1)
    }
}

fn result_ok(value: Value) -> Value {
    make_variant("Ok", &[("value", value)])
}

fn result_err(msg: &str) -> Value {
    make_variant("Err", &[("error", Value::str(msg))])
}

fn make_variant(variant: &str, fields: &[(&str, Value)]) -> Value {
    let mut m = HashMap::with_capacity(fields.len());
    for (k, v) in fields {
        m.insert((*k).to_string(), v.clone());
    }
    Value::Variant(Rc::new(VariantObj {
        variant: variant.to_string(),
        fields: RefCell::new(m),
    }))
}

/// The byte substring `[start, end)`, clamped to the string's bounds and snapped
/// to a valid UTF-8 boundary so the slice is always valid.
fn string_slice(s: &str, start: i64, end: i64) -> String {
    let len = s.len() as i64;
    let lo = start.clamp(0, len) as usize;
    let hi = end.clamp(start.max(0), len) as usize;
    let bytes = s.as_bytes();
    let lo = snap_boundary(bytes, lo);
    let hi = snap_boundary(bytes, hi);
    String::from_utf8_lossy(&bytes[lo..hi]).into_owned()
}

/// The UTF-8 character starting at byte offset `i`, as a one-character string, or
/// `null` when `i` is out of range or not a character boundary.
fn char_at(s: &str, i: i64) -> Value {
    // A mid-character index must return null, not slice `s[i..]` (which would
    // panic and abort the interpreter). Matches the runtime's `char_at_byte`, so
    // both back ends agree on out-of-range and non-boundary indices.
    if i < 0 || i as usize >= s.len() || !s.is_char_boundary(i as usize) {
        return Value::Null;
    }
    match s[i as usize..].chars().next() {
        Some(c) => Value::str(c.to_string()),
        None => Value::Null,
    }
}

/// Move `i` back to the nearest UTF-8 character boundary at or before it.
fn snap_boundary(bytes: &[u8], mut i: usize) -> usize {
    while i > 0 && i < bytes.len() && (bytes[i] & 0xC0) == 0x80 {
        i -= 1;
    }
    i
}

// ===== small type helpers =====

fn int_bits(k: IntKind) -> u32 {
    match k {
        IntKind::I8 | IntKind::U8 => 8,
        IntKind::I16 | IntKind::U16 => 16,
        IntKind::I32 | IntKind::U32 => 32,
        IntKind::I64 | IntKind::U64 => 64,
    }
}

fn int_signed(k: IntKind) -> bool {
    matches!(k, IntKind::I8 | IntKind::I16 | IntKind::I32 | IntKind::I64)
}

/// The integer kind for a `(bit width, signedness)` pair, as the `_int_narrow`
/// primitive carries them at runtime. A width other than 8/16/32
/// is the 64-bit kind.
fn int_kind_from_bits(bits: i64, signed: bool) -> IntKind {
    match (bits, signed) {
        (8, true) => IntKind::I8,
        (16, true) => IntKind::I16,
        (32, true) => IntKind::I32,
        (8, false) => IntKind::U8,
        (16, false) => IntKind::U16,
        (32, false) => IntKind::U32,
        (_, false) => IntKind::U64,
        (_, true) => IntKind::I64,
    }
}

/// Truncate `v` to the kind's width and re-extend per its signedness, so the
/// `i64`-carried value stays in canonical form.
fn norm_int(v: i64, k: IntKind) -> i64 {
    let bits = int_bits(k);
    if bits >= 64 {
        return v;
    }
    if int_signed(k) {
        let shift = 64 - bits;
        (v << shift) >> shift
    } else {
        let mask = (1i64 << bits) - 1;
        v & mask
    }
}

fn round_f32_if(fk: FloatKind, x: f64) -> f64 {
    match fk {
        FloatKind::F32 => (x as f32) as f64,
        FloatKind::F64 => x,
    }
}

fn float_kind(s: &str) -> Option<FloatKind> {
    match s {
        "float32" => Some(FloatKind::F32),
        "float64" => Some(FloatKind::F64),
        _ => None,
    }
}

/// The integer kind of a type, defaulting to `int32` for a non-integer (the
/// operand type of `Neg`/`BitNot` is always an integer in valid programs).
fn int_kind(ty: &Type) -> IntKind {
    match ty {
        Type::Int(k) => *k,
        _ => IntKind::I32,
    }
}

fn float_kind_of(ty: &Type) -> FloatKind {
    match ty {
        Type::Float(k) => *k,
        _ => FloatKind::F64,
    }
}

/// Strip one level of nullable: the inner type of a `T?`, else `ty` unchanged.
/// A guard (`if a`) proves a nullable non-null without retyping the MIR local,
/// so a narrowed aggregate still carries the declared nullable; this unwraps it
/// for the dispatch and element/field typing (the interpreter's runtime value of
/// a present nullable is already the inner value, so no value conversion needed).
fn unwrap_nullable(ty: &Type) -> &Type {
    match ty {
        Type::Nullable(inner) => inner,
        other => other,
    }
}

fn element_type(ty: &Type) -> Type {
    match unwrap_nullable(ty) {
        Type::Slice(e) | Type::Array(e, _) => (**e).clone(),
        _ => Type::Void,
    }
}

fn record_field_type(record_ty: &Type, name: &str) -> Type {
    match unwrap_nullable(record_ty) {
        Type::Record(n) => n.substitution.get(name).cloned().unwrap_or(Type::Void),
        _ => Type::Void,
    }
}

/// The field names of a record type, in its substitution's (sorted) order.
fn record_field_names(record_ty: &Type) -> Vec<String> {
    match record_ty {
        Type::Record(n) => n
            .substitution
            .iter()
            .map(|(name, _)| name.to_string())
            .collect(),
        _ => Vec::new(),
    }
}

/// See through reference/mutability/const wrappers to the underlying type.
fn strip_wrappers(ty: &Type) -> &Type {
    match ty {
        Type::Ref(inner) | Type::Mut(inner) | Type::ConstOf(inner) => strip_wrappers(inner),
        other => other,
    }
}

/// Whether `T.from(source)` succeeds for a per-instance `src_ty` and target record
/// `target`: the source must be a record carrying every field `target` declares,
/// each with a matching type. Mirrors the JIT's check so both back ends take the
/// same branch.
fn record_from_succeeds(src_ty: &Type, target: &Type) -> bool {
    let (Type::Record(s), Type::Record(t)) = (strip_wrappers(src_ty), target) else {
        return false;
    };
    t.substitution
        .iter()
        .all(|(name, tty)| s.substitution.get(name).is_some_and(|sty| sty == tty))
}

fn is_result_ty(ty: &Type) -> bool {
    matches!(ty, Type::Sum(n) if n.id == RESULT_TYPE_ID)
}

fn result_ok_type(ret: &Type) -> Type {
    // A `Result<..>?` ret (a body that also propagates a null) Ok-wraps at
    // its inner Result's payload.
    let ret = match ret {
        Type::Nullable(inner) if inner.is_result_type() => inner,
        other => other,
    };
    match ret {
        Type::Sum(n) => n
            .result_payloads()
            .map(|(ok, _)| ok.clone())
            .unwrap_or(Type::Void),
        _ => Type::Void,
    }
}

fn str_const(op: &Operand) -> Option<&str> {
    match op {
        Operand::Const(Literal::Str(s)) => Some(s),
        _ => None,
    }
}

/// The last segment of a possibly variant-qualified field name (`Cons.head` ->
/// `head`; a plain `head` is unchanged).
fn field_key(field: &str) -> &str {
    field.rsplit('.').next().unwrap_or(field)
}
