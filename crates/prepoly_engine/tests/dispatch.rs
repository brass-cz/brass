//! The typed codegen dispatch is exercised end to end with an in-memory backend
//! (no LLVM): a program is parsed, lowered to MIR, monomorphized, and "compiled"
//! by a backend that renders each typed leaf operation to text. This proves the
//! engine monomorphizes and walks the instances, resolving concrete types and
//! calling the leaves, independent of any target.

use prepoly_engine::{Codegen, Engine, MonoFunction, MonoProgram, monomorphize};
use prepoly_hir::{LoadedModule, Type};
use prepoly_mir::{BlockId, LocalId, lower_program};
use prepoly_parser::ast::{BinOp, UnaryOp};

/// A backend whose `Value` is an SSA id and whose every operation appends a line
/// to a transcript. It implements only the leaf methods; all dispatch is the
/// trait's default.
#[derive(Default)]
struct TextBackend {
    out: String,
    next: usize,
}

impl TextBackend {
    fn val(&mut self, s: String) -> usize {
        let id = self.next;
        self.next += 1;
        self.out.push_str(&format!("  v{id} = {s}\n"));
        id
    }
    fn line(&mut self, s: String) {
        self.out.push_str(&format!("  {s}\n"));
    }
}

impl Codegen for TextBackend {
    type Value = usize;

    fn begin_program(&mut self, p: &MonoProgram) {
        self.out
            .push_str(&format!("; program ({} instances)\n", p.functions.len()));
    }
    fn finalize(&mut self) -> Result<(), String> {
        Ok(())
    }
    fn execute(&mut self) -> Result<(), String> {
        Ok(())
    }

    fn begin_body(&mut self, func: &MonoFunction) {
        let params: Vec<String> = func.type_args.iter().map(|t| t.display()).collect();
        self.out.push_str(&format!(
            "fn {}({}) -> {}\n",
            func.symbol,
            params.join(", "),
            func.ret.display()
        ));
    }
    fn end_body(&mut self) {}
    fn begin_block(&mut self, id: BlockId) {
        self.out.push_str(&format!(" {id}:\n"));
    }

    fn load_local(&mut self, id: LocalId) -> usize {
        self.val(format!("load {id}"))
    }
    fn store_local(&mut self, id: LocalId, v: usize) {
        self.line(format!("{id} = v{v}"));
    }

    fn const_int(&mut self, v: i64, ty: &Type) -> usize {
        self.val(format!("{}:{}", v, ty.display()))
    }
    fn const_float(&mut self, v: f64, ty: &Type) -> usize {
        self.val(format!("{}:{}", v, ty.display()))
    }
    fn const_bool(&mut self, v: bool) -> usize {
        self.val(format!("{v}:bool"))
    }
    fn const_str(&mut self, s: &str) -> usize {
        self.val(format!("{s:?}:string"))
    }
    fn coerce(&mut self, v: usize, from: &Type, to: &Type) -> usize {
        if from == to {
            v
        } else {
            self.val(format!("coerce v{v} {}->{}", from.display(), to.display()))
        }
    }
    fn const_null(&mut self) -> usize {
        self.val("null".into())
    }
    fn truthy(&mut self, v: usize, ty: &Type) -> usize {
        self.val(format!("truthy v{v}:{}", ty.display()))
    }
    fn unit(&mut self) -> usize {
        self.val("unit".into())
    }

    fn string_len(&mut self, s: usize) -> usize {
        self.val(format!("len v{s}"))
    }
    fn to_string(&mut self, v: usize, ty: &Type) -> usize {
        self.val(format!("to_string v{v}:{}", ty.display()))
    }
    fn string_slice(&mut self, s: usize, start: usize, end: usize) -> usize {
        self.val(format!("slice v{s}[v{start}..v{end}]"))
    }
    fn string_to_bytes(&mut self, s: usize) -> usize {
        self.val(format!("bytes v{s}"))
    }
    fn string_find(&mut self, s: usize, sub: usize) -> usize {
        self.val(format!("find v{s} v{sub}"))
    }
    fn string_concat(&mut self, a: usize, b: usize) -> usize {
        self.val(format!("concat v{a} v{b}"))
    }
    fn string_cmp(&mut self, a: usize, b: usize) -> usize {
        self.val(format!("strcmp v{a} v{b}"))
    }
    fn string_char_at(&mut self, s: usize, i: usize) -> usize {
        self.val(format!("char_at v{s} v{i}"))
    }
    fn string_from_bytes(&mut self, bytes: usize) -> usize {
        self.val(format!("from_bytes v{bytes}"))
    }
    fn insert(&mut self, arr: usize, _elem_ty: &Type, idx: usize, v: usize) {
        self.line(format!("insert v{arr}[v{idx}] = v{v}"));
    }
    fn remove(&mut self, arr: usize, _elem_ty: &Type, idx: usize) -> usize {
        self.val(format!("remove v{arr}[v{idx}]"))
    }
    fn pop(&mut self, arr: usize, _elem_ty: &Type) -> usize {
        self.val(format!("pop v{arr}"))
    }
    fn deep_copy(&mut self, value: usize, _ty: &Type) -> usize {
        self.val(format!("deep_copy v{value}"))
    }
    fn int_widen(&mut self, x: usize, from: usize, to: usize, signed: usize) -> usize {
        self.val(format!("int_widen v{x} v{from} v{to} v{signed}"))
    }
    fn int_narrow(&mut self, x: usize, from: usize, to: usize, signed: usize) -> usize {
        self.val(format!("int_narrow v{x} v{from} v{to} v{signed}"))
    }
    fn file_open(&mut self, path: usize, mode: usize) -> usize {
        self.val(format!("file_open v{path} v{mode}"))
    }
    fn file_std(&mut self, which: u8) -> usize {
        self.val(format!("file_std {which}"))
    }
    fn file_from_fd(&mut self, fd: usize) -> usize {
        self.val(format!("file_from_fd v{fd}"))
    }
    fn file_read(&mut self, file: usize, n: usize) -> usize {
        self.val(format!("file_read v{file} v{n}"))
    }
    fn file_write(&mut self, file: usize, bytes: usize) -> usize {
        self.val(format!("file_write v{file} v{bytes}"))
    }
    fn file_size(&mut self, file: usize) -> usize {
        self.val(format!("file_size v{file}"))
    }
    fn file_seek(&mut self, file: usize, pos: usize) -> usize {
        self.val(format!("file_seek v{file} v{pos}"))
    }
    fn file_close(&mut self, file: usize) -> usize {
        self.val(format!("file_close v{file}"))
    }
    fn net_call(&mut self, rt_name: &'static str, args: &[usize]) -> usize {
        let args = args
            .iter()
            .map(|a| format!("v{a}"))
            .collect::<Vec<_>>()
            .join(" ");
        self.val(format!("{rt_name} {args}"))
    }
    fn plugin_call(
        &mut self,
        rt_name: &'static str,
        strings: [usize; 3],
        args: &[(usize, Type)],
        _ret: &Type,
    ) -> usize {
        let strings = strings.map(|s| format!("v{s}")).join(" ");
        let args = args
            .iter()
            .map(|(a, _)| format!("v{a}"))
            .collect::<Vec<_>>()
            .join(" ");
        self.val(format!("{rt_name} {strings} [{args}]"))
    }
    fn convert(&mut self, target: &Type, method: &str, _arg_ty: &Type, arg: usize) -> usize {
        self.val(format!("{}.{method}(v{arg})", target.display()))
    }

    fn bin_op(&mut self, op: BinOp, a: usize, b: usize, operand_ty: &Type) -> usize {
        self.val(format!("{op:?}:{} v{a} v{b}", operand_ty.display()))
    }
    fn un_op(&mut self, op: UnaryOp, a: usize, operand_ty: &Type) -> usize {
        self.val(format!("{op:?}:{} v{a}", operand_ty.display()))
    }

    fn call(&mut self, symbol: &str, args: &[usize], ret: &Type) -> usize {
        self.val(format!("call {symbol} {args:?} -> {}", ret.display()))
    }

    fn deferred_dispatch(&mut self, consumer: &str, type_name: &str, value: usize) -> usize {
        self.val(format!("dispatch {consumer} type={type_name} v{value}"))
    }

    fn make_record(&mut self, record_ty: &Type, fields: &[(&str, usize)]) -> usize {
        let fs: Vec<String> = fields.iter().map(|(n, v)| format!("{n}=v{v}")).collect();
        self.val(format!(
            "record {} {{ {} }}",
            record_ty.display(),
            fs.join(", ")
        ))
    }
    fn load_field(&mut self, base: usize, _base_ty: &Type, field: &str) -> usize {
        self.val(format!("field v{base}.{field}"))
    }
    fn store_field(&mut self, base: usize, _base_ty: &Type, field: &str, v: usize) {
        self.line(format!("v{base}.{field} = v{v}"));
    }
    fn make_variant(&mut self, sum_ty: &Type, variant: &str, fields: &[(&str, usize)]) -> usize {
        let fs: Vec<String> = fields.iter().map(|(n, v)| format!("{n}=v{v}")).collect();
        self.val(format!(
            "variant {}.{variant} {{ {} }}",
            sum_ty.display(),
            fs.join(", ")
        ))
    }
    fn pattern_matches(&mut self, subj: usize, _subj_ty: &Type, variant: &str) -> usize {
        self.val(format!("matches v{subj} {variant}"))
    }
    fn emit_panic(&mut self, msg: &str) {
        self.line(format!("panic {msg:?}"));
    }
    fn runtime_panic(&mut self, msg: usize) {
        self.line(format!("panic v{msg}"));
    }
    fn emit_print(&mut self, s: usize, newline: bool) {
        self.line(format!("print v{s} nl={newline}"));
    }
    fn float_builtin(&mut self, name: &str, args: &[usize]) -> usize {
        self.val(format!("{name} {args:?}"))
    }
    fn store_global(&mut self, name: &str, _ty: &Type, v: usize) {
        self.line(format!("global {name} = v{v}"));
    }
    fn load_global(&mut self, name: &str, ty: &Type) -> usize {
        self.val(format!("global {name}:{}", ty.display()))
    }
    fn make_array(&mut self, elem_ty: &Type, elems: &[usize]) -> usize {
        self.val(format!("array<{}> {elems:?}", elem_ty.display()))
    }
    fn make_tuple(&mut self, elem_types: &[Type], elems: &[usize]) -> usize {
        let tys: Vec<String> = elem_types.iter().map(|t| t.display()).collect();
        self.val(format!("tuple<{}> {elems:?}", tys.join(", ")))
    }
    fn tuple_field(&mut self, tup: usize, _elem_types: &[Type], index: usize) -> usize {
        self.val(format!("v{tup}.{index}"))
    }
    fn load_index(&mut self, arr: usize, _arr_ty: &Type, idx: usize) -> usize {
        self.val(format!("v{arr}[v{idx}]"))
    }
    fn store_index(&mut self, arr: usize, _arr_ty: &Type, idx: usize, v: usize) {
        self.line(format!("v{arr}[v{idx}] = v{v}"));
    }
    fn array_len(&mut self, arr: usize) -> usize {
        self.val(format!("array_len v{arr}"))
    }
    fn push(&mut self, arr: usize, elem_ty: &Type, v: usize) {
        self.line(format!("push v{arr} <- v{v}:{}", elem_ty.display()));
    }
    fn make_closure(
        &mut self,
        fun_ty: &Type,
        id: prepoly_mir::ClosureId,
        captures: &[(Type, usize)],
    ) -> usize {
        let cs: Vec<String> = captures.iter().map(|(_, v)| format!("v{v}")).collect();
        self.val(format!(
            "closure#{}:{} [{}]",
            id.index(),
            fun_ty.display(),
            cs.join(", ")
        ))
    }
    fn call_indirect(&mut self, callee: usize, _callee_ty: &Type, args: &[usize]) -> usize {
        self.val(format!("call_indirect v{callee} {args:?}"))
    }

    fn spawn(&mut self, closure: usize) {
        self.line(format!("spawn v{closure}"));
    }
    fn freeze(&mut self, value: usize) {
        self.line(format!("freeze v{value}"));
    }
    fn make_cown(&mut self, value: usize) {
        self.line(format!("cown v{value}"));
    }
    fn thread_join_all(&mut self) {
        self.line("sync".into());
    }
    fn retain(&mut self, value: usize) {
        self.line(format!("retain v{value}"));
    }
    fn release(&mut self, value: usize) {
        self.line(format!("release v{value}"));
    }
    fn release_obj(&mut self, value: usize, ty: &Type) {
        self.line(format!("drop {} v{value}", ty.display()));
    }
    fn release_closure(&mut self, value: usize) {
        self.line(format!("drop_closure v{value}"));
    }
    fn cown_lock(&mut self, obj: usize) {
        self.line(format!("lock v{obj}"));
    }
    fn cown_unlock(&mut self, obj: usize) {
        self.line(format!("unlock v{obj}"));
    }
    fn cown_lock_all(&mut self, arr: usize) {
        self.line(format!("lock_all v{arr}"));
    }
    fn cown_unlock_all(&mut self, arr: usize) {
        self.line(format!("unlock_all v{arr}"));
    }
    fn cown_lock_many(&mut self, objs: &[usize]) {
        self.line(format!("lock_many {objs:?}"));
    }
    fn cown_unlock_many(&mut self, objs: &[usize]) {
        self.line(format!("unlock_many {objs:?}"));
    }
    fn region_open(&mut self, bridge: usize) -> usize {
        self.val(format!("region_open v{bridge}"))
    }
    fn region_close(&mut self, region_id: usize) {
        self.line(format!("region_close v{region_id}"));
    }
    fn region_write(&mut self, container: usize, value: usize) {
        self.line(format!("region_write v{container} v{value}"));
    }
    fn region_store(&mut self, container: usize, old: usize, value: usize, managed_cells: bool) {
        self.line(format!(
            "region_store v{container} v{old} v{value} cells={managed_cells}"
        ));
    }

    fn emit_return(&mut self, v: Option<usize>) {
        match v {
            Some(v) => self.line(format!("return v{v}")),
            None => self.line("return".into()),
        }
    }
    fn emit_goto(&mut self, target: BlockId) {
        self.line(format!("goto {target}"));
    }
    fn emit_cond_branch(&mut self, cond: usize, then: BlockId, els: BlockId) {
        self.line(format!("br v{cond} -> {then} {els}"));
    }
    fn emit_unreachable(&mut self) {
        self.line("unreachable".into());
    }
}

/// Lower a single-module program through HIR + MIR, monomorphize, and render it
/// with the text backend via the engine.
fn render(src: &str) -> String {
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }];
    let (program, _errors) = prepoly_hir::lower(&modules);
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    let mut backend = TextBackend::default();
    Engine::compile(&mut backend, &mono).expect("compile");
    backend.out
}

#[test]
fn dispatch_monomorphizes_and_types_a_recursive_program() {
    // `answer` (a zero-arg root) calls `fact(5)`, which instantiates `fact` for
    // int32; the recursion resolves to the same instance.
    let out = render(
        "fun fact(n) {\n  if n < 2 {\n    return 1\n  }\n  return n * fact(n - 1)\n}\n\
         fun answer() {\n  return fact(5) + 10\n}\n",
    );
    // The int32 instance of `fact` is named and typed (the instance symbol is
    // derived, not hard-coded, so the mangling scheme stays free to change).
    let fact_i32 = prepoly_engine::instance_symbol("fact", &[Type::Int(prepoly_hir::IntKind::I32)]);
    assert!(
        out.contains(&format!("fn {fact_i32}(int32) -> int32")),
        "{out}"
    );
    // `answer` is a zero-arg instance returning int32.
    assert!(out.contains("fn answer() -> int32"), "{out}");
    // Operations carry their concrete operand type.
    assert!(out.contains("Lt:int32"), "{out}");
    assert!(out.contains("Mul:int32"), "{out}");
    // The call targets the int32 instance.
    assert!(out.contains(&format!("call {fact_i32}")), "{out}");
    // Constants are typed at their contextual type, not boxed.
    assert!(out.contains("5:int32") || out.contains("10:int32"), "{out}");
}

#[test]
fn dispatch_specializes_one_function_for_two_types() {
    // `id` is used at both int32 and float64, producing two distinct instances.
    let out = render(
        "fun id(x) {\n  return x\n}\n\
         fun use_int() {\n  return id(1)\n}\n\
         fun use_flt() {\n  return id(2.0)\n}\n",
    );
    let id_i32 = prepoly_engine::instance_symbol("id", &[Type::Int(prepoly_hir::IntKind::I32)]);
    let id_f64 = prepoly_engine::instance_symbol("id", &[Type::Float(prepoly_hir::FloatKind::F64)]);
    assert!(
        out.contains(&format!("fn {id_i32}(int32) -> int32")),
        "{out}"
    );
    assert!(
        out.contains(&format!("fn {id_f64}(float64) -> float64")),
        "{out}"
    );
    assert!(out.contains(&format!("call {id_i32}")), "{out}");
    assert!(out.contains(&format!("call {id_f64}")), "{out}");
}

#[test]
fn unannotated_value_or_null_return_infers_nullable() {
    // A function that returns a value on one path and `null` on another must infer
    // a nullable return type by JOINING both returns, not freeze to whichever return
    // block the fixpoint types first. Freezing to the bare value type made the
    // `null` path fail the "returns a null value where `int32` is required" backstop;
    // freezing to the null path's `never?` made a found value read back as `never`.
    let out = render(
        "fun first(xs: int32[]) {\n  for x in xs {\n    return x\n  }\n  return null\n}\n\
         fun use_it() {\n  return first([1, 2, 3])\n}\n",
    );
    assert!(
        out.contains("-> int32?"),
        "return must join to int32?: {out}"
    );
}

#[test]
fn monomorphize_skips_unsupported_roots() {
    // Monomorphization is best effort: a root outside the typed subset (here a
    // function using the unsupported `input` builtin) is skipped, not fatal, so
    // the rest of the program still types. The skipped root is simply absent.
    let src = "fun does_io() {\n  let s = input()\n  return s\n}\n\
               fun pure() {\n  return 6 * 7\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }];
    let (program, _errors) = prepoly_hir::lower(&modules);
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("best-effort monomorphize");
    assert!(
        mono.lookup("does_io").is_none(),
        "I/O root should be skipped"
    );
    assert!(mono.lookup("pure").is_some(), "pure root should be typed");
}

#[test]
fn failed_frame_rolls_back_mutually_recursive_callee() {
    // Mutual recursion stores the callee (typed against the caller's
    // provisional annotated return) before the caller. When the caller's frame
    // then fails -- here on the unsupported `input` builtin after the recursive
    // call -- the stored callee must be rolled back too: it holds a call to a
    // symbol that will never materialize, and codegen would have no target.
    let src = "fun ping(n: int64) -> int64 {\n  if n == 0 {\n    return pong(n - 1)\n  }\n  let s = input()\n  return 0\n}\n\
               fun pong(n: int64) -> int64 {\n  if n == 0 {\n    return 0\n  }\n  return ping(n - 1)\n}\n\
               fun run_ping() {\n  return ping(3)\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }];
    let (program, _errors) = prepoly_hir::lower(&modules);
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("best-effort monomorphize");
    assert!(
        mono.lookup("ping$$int64").is_none(),
        "failing caller must not be stored"
    );
    assert!(
        mono.lookup("pong$$int64").is_none(),
        "callee typed against the failed frame must be rolled back"
    );
}

#[test]
fn monomorphize_types_module_globals() {
    // A top-level `let` types as a global from its initializer, and a function
    // reading it monomorphizes against that type.
    let src = "let counter = 7\nfun get() {\n  return counter\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }];
    let (program, _errors) = prepoly_hir::lower(&modules);
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    // Globals are keyed per defining module (`name@module`), so two modules'
    // same-named top-level `let`s never share a slot.
    assert_eq!(
        mono.global_type(&prepoly_hir::qualify("counter", &["main".into()]))
            .map(|t| t.display()),
        Some("int32".to_string())
    );
    assert!(mono.lookup("get").is_some());
}

#[test]
fn main_module_top_level_failure_is_surfaced_not_dropped() {
    // A `main` module init that falls outside the typed subset (here mutual
    // recursion without return annotations, which has no sound provisional
    // type to assume) is the program's entry point, so monomorphization fails
    // loudly rather than silently dropping it -- which had let a type-checked
    // program run to a clean exit with no output. (A `main` function in the
    // same shape is already rejected by both back ends.)
    let src = "fun a(n: int32) {\n  if n <= 0 { return 0 }\n  return b(n - 1)\n}\n\
               fun b(n: int32) {\n  if n <= 0 { return 0 }\n  return a(n - 1)\n}\n\
               println(a(5))\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }];
    let (program, _errors) = prepoly_hir::lower(&modules);
    let mir = lower_program(&program);
    let err = monomorphize(&mir, &program)
        .map(|_| ())
        .expect_err("main-init failure must surface");
    assert!(
        err.contains("top-level code") && err.contains("mutual recursion"),
        "error should name the top-level cause, got: {err}"
    );
}

#[test]
fn narrowed_nullable_array_ops_type_and_keep_the_init() {
    // An `if a` guard does not retype the MIR local, so `a` stays `int32[]?` while
    // used as `int32[]` inside the guard. Each op below once made `type_and_store`
    // fail, and because init bodies monomorphize best-effort, the whole init was
    // silently dropped -- a type-checked program produced no output. The init must
    // survive (a non-empty `init_symbols`) and the typed program must compile.
    for (label, body) in [
        ("len", "let n = a.len()"),
        ("for", "for e in a {\n      println(e)\n    }"),
        ("index", "println(a[0])"),
        ("index_store", "a[0] = 9"),
        ("push", "a.push(9)"),
        ("pop", "let last = a.pop()"),
    ] {
        let src = format!("fun f(a: int32[]?) {{\n  if a {{\n    {body}\n  }}\n}}\nf([1, 2, 3])\n");
        let ast = prepoly_parser::parse(&src).expect("parse");
        let modules = [LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }];
        let (program, _errors) = prepoly_hir::lower(&modules);
        let mir = lower_program(&program);
        let mono = monomorphize(&mir, &program).expect("monomorphize");
        assert!(
            !mono.init_symbols.is_empty(),
            "init dropped for narrowed nullable `{label}`"
        );
        // The instance still carries the declared nullable parameter; the back end
        // strips it at each use. The instance is any specialization of `f` (its
        // symbol extends the base name; the exact mangle is the engine's business).
        let f = mono
            .functions
            .iter()
            .find(|f| f.symbol.starts_with("f") && f.symbol != "f")
            .unwrap_or_else(|| panic!("no `f` instance for `{label}`"));
        assert!(
            matches!(f.local_types.first(), Some(prepoly_hir::Type::Nullable(_))),
            "param should stay nullable for `{label}`, got {:?}",
            f.local_types.first().map(|t| t.display())
        );
    }
}
