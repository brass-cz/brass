//! End-to-end: a Prepoly program is parsed, lowered to HIR then MIR,
//! monomorphized into concrete-typed instances, and compiled + run by
//! `prepoly_engine::Engine` driving the `LlvmCodegen` backend over the *typed*
//! `Codegen` trait. This path emits fully unboxed code -- no `Value` boxing, no
//! `pp_*` runtime calls -- so a result returned through `extern "C" fn() -> iN`
//! is correct only if the function really has an unboxed `iN` ABI.
//!
//! Tests serialize through a lock (the JIT/LLVM globals are process-wide).

use std::sync::Mutex;

use inkwell::context::Context;
use prepoly_engine::{Engine, monomorphize};
use prepoly_hir::{LoadedModule, lower};
use prepoly_jit_llvm::LlvmCodegen;
use prepoly_mir::lower_program;

static JIT_LOCK: Mutex<()> = Mutex::new(());

const SRC: &str = "\
fun fact(n) {
    if n < 2 {
        return 1
    }
    return n * fact(n - 1)
}

fun sum_to(n) {
    let s = 0
    let i = 1
    while i <= n {
        s = s + i
        i = i + 1
    }
    return s
}

fun logic(a, b) {
    if a && b {
        return 1
    }
    return 0
}

fun fdouble(x) {
    return x + x
}

fun answer() {
    return fact(5) + 10
}

fun total() {
    return sum_to(10)
}

fun both() {
    return logic(true, true)
}

fun one_false() {
    return logic(true, false)
}

fun fdrun() {
    return fdouble(2.5)
}
";

#[test]
fn engine_jits_unboxed_typed_instances() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    let ast = prepoly_parser::parse(SRC).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    // The recursive `fact` is specialized for int32 with an unboxed signature.
    let fact_i32 = prepoly_engine::instance_symbol(
        "fact",
        &[prepoly_hir::Type::Int(prepoly_hir::IntKind::I32)],
    );
    let sig = backend
        .instance_fn_type_string(&fact_i32)
        .expect("fact instance");
    assert!(
        sig.contains("i32 (i32)"),
        "{fact_i32} should be unboxed: {sig}"
    );

    // Recursion + arithmetic: fact(5) + 10 = 130.
    assert_eq!(backend.run_entry_i32("answer"), Some(130));
    // A `while` loop: 1 + 2 + ... + 10 = 55.
    assert_eq!(backend.run_entry_i32("total"), Some(55));
    // Short-circuit `&&` lowered to control flow.
    assert_eq!(backend.run_entry_i32("both"), Some(1));
    assert_eq!(backend.run_entry_i32("one_false"), Some(0));
    // Unboxed float arithmetic.
    assert_eq!(backend.run_entry_f64("fdrun"), Some(5.0));
}

#[test]
fn one_function_specializes_for_two_types() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    let src = "\
fun id(x) {
    return x
}

fun use_int() {
    return id(7)
}

fun use_flt() {
    return id(1.5)
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    // Two distinct instances of `id` with distinct unboxed signatures.
    let int_sig = backend
        .instance_fn_type_string(&prepoly_engine::instance_symbol(
            "id",
            &[prepoly_hir::Type::Int(prepoly_hir::IntKind::I32)],
        ))
        .expect("id int32");
    let flt_sig = backend
        .instance_fn_type_string(&prepoly_engine::instance_symbol(
            "id",
            &[prepoly_hir::Type::Float(prepoly_hir::FloatKind::F64)],
        ))
        .expect("id float64");
    assert!(int_sig.contains("i32 (i32)"), "{int_sig}");
    assert!(flt_sig.contains("double (double)"), "{flt_sig}");

    assert_eq!(backend.run_entry_i32("use_int"), Some(7));
    assert_eq!(backend.run_entry_f64("use_flt"), Some(1.5));
}

#[test]
fn typed_records_construct_and_read_fields_unboxed() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // A record laid out as a typed heap object (no boxed Value fields); the
    // field reads sum to 7. A second instance with float fields monomorphizes
    // `Point` to a distinct layout.
    let src = "\
type Point = {
    x
    y
}

fun demo() {
    let p = Point { x: 3, y: 4 }
    return p.x + p.y
}

fun fdemo() {
    let p = Point { x: 1.5, y: 2.0 }
    return p.x + p.y
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("demo"), Some(7));
    assert_eq!(backend.run_entry_f64("fdemo"), Some(3.5));
}

#[test]
fn typed_records_with_methods_and_constructors() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // Constructors (static methods returning Self), instance methods reading
    // fields, methods returning records, and a self-mutating method -- all
    // monomorphized to unboxed typed code.
    let src = "\
type Vec2 = {
    x
    y
}

fun Vec2.new(x, y) {
    return Self { x: x, y: y }
}
fun Vec2.sum(self) {
    return self.x + self.y
}
fun Vec2.scaled(self, k) {
    return Self { x: self.x * k, y: self.y * k }
}
fun Vec2.bump(self) {
    self.x = self.x + 1
}

fun demo() {
    let v = Vec2.new(3, 4)
    return v.sum()
}

fun demo_scaled() {
    let v = Vec2.new(3, 4)
    let w = v.scaled(2)
    return w.sum()
}

fun demo_mutate() {
    let v = Vec2.new(3, 4)
    v.bump()
    return v.x
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("demo"), Some(7));
    assert_eq!(backend.run_entry_i32("demo_scaled"), Some(14));
    assert_eq!(backend.run_entry_i32("demo_mutate"), Some(4));
}

#[test]
fn typed_sum_types_construct_match_and_read() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // A sum type laid out as { header | tag | payload-union }; `match` becomes a
    // tag comparison and the bound fields are read from the payload -- all
    // unboxed.
    let src = "\
type Shape =
    | Circle { r: int32 }
    | Rect { w: int32, h: int32 }

fun area(s: Shape) -> int32 {
    return match s {
        Circle { r } => r * r * 3,
        Rect { w, h } => w * h,
    }
}

fun circle_area() {
    return area(Shape.Circle { r: 5 })
}

fun rect_area() {
    return area(Shape.Rect { w: 3, h: 4 })
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    // Circle r=5 -> 5*5*3 = 75; Rect 3x4 -> 12.
    assert_eq!(backend.run_entry_i32("circle_area"), Some(75));
    assert_eq!(backend.run_entry_i32("rect_area"), Some(12));
}

#[test]
fn sum_variant_with_nominal_and_untyped_fields() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // A sum variant may carry a nested record (`Wrap { p: Point, .. }`): the field
    // is a heap pointer laid out independently, constructed, matched, and read
    // through (`p.x`). A separate variant has an *unannotated* field (`Empty
    // { value }`); since it is never constructed or accessed here, its type stays
    // unknown without blocking the typed lowering of the whole sum.
    let src = "\
type Point = {
    x: int32
    y: int32
}

type Node =
    | Empty { value }
    | Wrap { p: Point, tag: int32 }

fun nested_field() {
    const n = Node.Wrap { p: Point { x: 7, y: 9 }, tag: 1 }
    return match n {
        Wrap { p, tag } => p.x + p.y + tag,
        _ => 0,
    }
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    // p.x(7) + p.y(9) + tag(1) = 17, read through the nested record field.
    assert_eq!(backend.run_entry_i32("nested_field"), Some(17));
}

#[test]
fn variant_pattern_binds_field_of_matched_variant() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // Several variants declare a field of the same name (`value`) with different
    // types. A `Text { value }` pattern must bind the matched variant's field
    // (`string`), not the first variant declaring `value` (`Number`'s `int32`):
    // `len(value)` is only well-typed -- and reads the right bytes -- if `value`
    // resolves to the `Text` variant's `string`.
    let src = "\
type J =
    | Number { value: int32 }
    | Text { value: string }

fun text_len() {
    const t = J.Text { value: \"hi\" }
    return match t {
        Text { value } => len(value),
        _ => 0,
    }
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    // len("hi") = 2 -- proves `value` was bound as the `Text` variant's string.
    assert_eq!(backend.run_entry_i64("text_len"), Some(2));
}

#[test]
fn typed_strings_concat_interpolate_and_compare() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // Strings as typed heap handles (no boxed Value): literals, `+` concat,
    // interpolation (to_string), `==`, and `len`.
    let src = "\
fun greet() {
    let s = \"hello\" + \" world\"
    return len(s)
}

fun interp() {
    let n = 42
    let s = \"n={n}\"
    return len(s)
}

fun eq_len() {
    let a = \"abc\"
    let b = \"abc\"
    if a == b {
        return 1
    }
    return 0
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i64("greet"), Some(11)); // "hello world"
    assert_eq!(backend.run_entry_i64("interp"), Some(4)); // "n=42"
    assert_eq!(backend.run_entry_i32("eq_len"), Some(1));
}

#[test]
fn typed_arrays_literal_index_and_length() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // Fixed arrays laid out inline as typed elements (no boxed Value): literal
    // construction, indexed read/write, and length.
    let src = "\
fun sum_ends() {
    let a = [10, 20, 30]
    return a[0] + a[2]
}

fun count() {
    let a = [1, 2, 3, 4]
    return len(a)
}

fun mutate() {
    let a = [5, 6]
    a[1] = 9
    return a[1]
}

fun sum_loop() {
    let a = [1, 2, 3, 4]
    let total = 0
    for x in a {
        total = total + x
    }
    return total
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("sum_ends"), Some(40)); // 10 + 30
    assert_eq!(backend.run_entry_i64("count"), Some(4));
    assert_eq!(backend.run_entry_i32("mutate"), Some(9));
    // A `for` loop iterates the array (int32 counter coerced against int64 len).
    assert_eq!(backend.run_entry_i32("sum_loop"), Some(10)); // 1+2+3+4
}

#[test]
fn typed_growable_arrays_push() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // Growable arrays: an empty `[]` literal (element type inferred from `push`)
    // is filled past its initial capacity and iterated -- all unboxed. This is
    // what the stdlib collection functions (map/filter/fold) are built on.
    let src = "\
fun build() -> int32[] {
    let r = []
    r.push(10)
    r.push(20)
    r.push(30)
    r.push(40)
    r.push(50)
    return r
}

fun sum_built() {
    let r = build()
    let total = 0
    for x in r {
        total = total + x
    }
    return total
}

fun count_built() {
    return len(build())
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("sum_built"), Some(150)); // 10+20+30+40+50
    assert_eq!(backend.run_entry_i64("count_built"), Some(5));
}

#[test]
fn typed_growable_arrays_pop() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // `arr.pop()` removes and returns the last element as a nullable (`_array_pop`): a value when present, null when the array is empty.
    let src = "\
fun pop_last() -> int32 {
    let r = []
    r.push(10)
    r.push(20)
    r.push(30)
    let x = r.pop()
    if x { return x }
    return 0
}

fun len_after_pop() -> int64 {
    let r = []
    r.push(1)
    r.push(2)
    r.pop()
    return len(r)
}

fun pop_empty_is_null() -> int32 {
    let r = []
    r.push(7)
    r.pop()
    let again = r.pop()
    if again { return 1 }
    return 0
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("pop_last"), Some(30));
    assert_eq!(backend.run_entry_i64("len_after_pop"), Some(1));
    assert_eq!(backend.run_entry_i32("pop_empty_is_null"), Some(0));
}

#[test]
fn named_numeric_string_primitives_are_callable() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // The named conversion/string primitives are directly
    // callable, not only reachable through `Type.from`/`parse` and `+`.
    // The infallible primitives return scalars/strings directly, so they exercise
    // the `extern fn -> iN`/`-> f64` ABI. The fallible parses/truncations are
    // covered end to end by the running examples and the typeck suite (`!` makes a
    // function fallible, which would change the return ABI here).
    let src = "\
fun widened() -> float64 {
    return _int_to_float(7, 64)
}

fun cmp_lt() -> int32 {
    return _string_cmp(\"a\", \"b\")
}

fun cmp_gt() -> int32 {
    return _string_cmp(\"b\", \"a\")
}

fun cmp_eq() -> int32 {
    return _string_cmp(\"x\", \"x\")
}

fun concat_len() -> int64 {
    return len(_string_concat(\"foo\", \"bar\"))
}

fun rendered_len() -> int64 {
    return len(_int_to_string(12345))
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_f64("widened"), Some(7.0));
    assert_eq!(backend.run_entry_i32("cmp_lt"), Some(-1));
    assert_eq!(backend.run_entry_i32("cmp_gt"), Some(1));
    assert_eq!(backend.run_entry_i32("cmp_eq"), Some(0));
    assert_eq!(backend.run_entry_i64("concat_len"), Some(6));
    assert_eq!(backend.run_entry_i64("rendered_len"), Some(5));
}

#[test]
fn typed_closures_capture_and_call() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // Direct-call closures: the closure value is a typed environment object
    // (captured values + function pointer), called through that pointer -- no
    // boxed Value. The closure's parameter types come from its call site.
    let src = "\
fun apply() {
    let n = 10
    let g = (x) -> x + n
    return g(5)
}

fun adder() {
    let base = 100
    let add = (a, b) -> a + b + base
    return add(2, 3)
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("apply"), Some(15)); // 5 + 10
    assert_eq!(backend.run_entry_i32("adder"), Some(105)); // 2 + 3 + 100
}

#[test]
fn typed_higher_order_closures() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // A closure passed to a higher-order function and called there: the closure's
    // parameter types are inferred from the callee's use of the parameter (probe),
    // so it is monomorphized and called through its function pointer -- unboxed.
    let src = "\
fun apply_twice(f, x) {
    return f(f(x))
}

fun run_double(g) {
    return g(10)
}

fun via_apply() {
    let inc = (n: int32) -> n + 1
    return apply_twice(inc, 10)
}

fun via_run() {
    return run_double((x: int32) -> x * 2)
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("via_run"), Some(20)); // 10 * 2
    assert_eq!(backend.run_entry_i32("via_apply"), Some(12)); // inc(inc(10))
}

#[test]
fn typed_print_program_runs_on_typed_path() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // A `main` that does typed computation and `println` (string literal +
    // interpolated scalar) monomorphizes -- so the driver runs it on the typed
    // unboxed path -- and executes without falling back to the Value path.
    let src = "\
fun double(n: int32) -> int32 {
    return n * 2
}

fun main() {
    println(\"typed io works\")
    let x = double(21)
    println(\"answer = {x}\")
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    // `main` is in the typed subset (print is typed I/O), so it is compiled.
    assert!(mono.lookup("main").is_some(), "main should monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    // Runs main (writing to stdout) entirely unboxed.
    Engine::run(&mut backend, &mono).expect("engine run");
}

#[test]
fn typed_nullable_wrap_check_and_narrow() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // Nullable `T?` as a heap cell (null = null pointer, no boxed Value): a value
    // is wrapped on return, `null` is the null pointer, `if x` is a non-null test,
    // and narrowing reads the value back out.
    let src = "\
fun first_even(nums: int32[]) -> int32? {
    for n in nums {
        if n % 2 == 0 {
            return n
        }
    }
    return null
}

fun has_even() {
    let r = first_even([1, 3, 4])
    if r {
        return 1
    }
    return 0
}

fun no_even() {
    let r = first_even([1, 3, 5])
    if r {
        return 1
    }
    return 0
}

fun unwrap_or_zero() -> int32 {
    let r = first_even([1, 3, 6])
    if r {
        return r
    }
    return 0
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("has_even"), Some(1)); // 4 present
    assert_eq!(backend.run_entry_i32("no_even"), Some(0)); // null
    assert_eq!(backend.run_entry_i32("unwrap_or_zero"), Some(6)); // narrowed 6
}

#[test]
fn typed_result_ok_err_and_match() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // The built-in generic `Result<T, E>` as a tagged sum (no boxed Value): a
    // fallible function implicitly wraps a bare return as Ok, `error(...)` builds
    // Err, and `match` reads the payloads. Payload types (int32, string) are
    // inferred and laid out via the nominal substitution.
    let src = "\
fun checked(x: int32) {
    if x < 0 {
        return error(\"neg\")
    }
    return x
}

fun ok_val() {
    let r = match checked(5) {
        Ok { value } => value,
        Err { error } => 0 - 1,
    }
    return r
}

fun err_val() {
    let r = match checked(0 - 3) {
        Ok { value } => value,
        Err { error } => 0 - 1,
    }
    return r
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("ok_val"), Some(5)); // Ok(5)
    assert_eq!(backend.run_entry_i32("err_val"), Some(-1)); // Err -> -1
}

#[test]
fn typed_error_propagation_operator() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // The `!` error-propagation operator (result_is_ok + Ok-payload load + Err
    // propagation), all unboxed: `outer` calls `inner(x)!` and either continues
    // with the unwrapped value or returns the propagated Err.
    let src = "\
fun inner(x: int32) {
    if x < 0 {
        return error(\"neg\")
    }
    return x
}

fun outer(x: int32) {
    let y = inner(x)!
    return y + 1
}

fun ok_case() {
    let r = outer(5)
    let v = match r {
        Ok { value } => value,
        Err { error } => 0 - 99,
    }
    return v
}

fun err_case() {
    let r = outer(0 - 7)
    let v = match r {
        Ok { value } => value,
        Err { error } => 0 - 99,
    }
    return v
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("ok_case"), Some(6)); // inner(5)=5, +1
    assert_eq!(backend.run_entry_i32("err_case"), Some(-99)); // Err propagated
}

#[test]
fn typed_numeric_conversions() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // `Type.from` / `Type.parse` as typed conversions returning a typed Result
    // (no boxed Value): range checks and parsing match the runtime exactly.
    let src = "\
fun from_ok() {
    let r = int32.from(1000)
    let v = match r { Ok { value } => value, Err { error } => 0 - 1 }
    return v
}

fun parse_ok() {
    let r = int32.parse(\"123\")
    let v = match r { Ok { value } => value, Err { error } => 0 - 1 }
    return v
}

fun parse_err() {
    let r = int32.parse(\"abc\")
    let v = match r { Ok { value } => value, Err { error } => 0 - 1 }
    return v
}

fun byte_overflow() {
    let r = uint8.from(300)
    let v = match r { Ok { value } => 1, Err { error } => 0 }
    return v
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("from_ok"), Some(1000));
    assert_eq!(backend.run_entry_i32("parse_ok"), Some(123));
    assert_eq!(backend.run_entry_i32("parse_err"), Some(-1)); // parse failure
    assert_eq!(backend.run_entry_i32("byte_overflow"), Some(0)); // 300 > 255
}

#[test]
fn typed_concurrency_spawn_and_with() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // Two real threads concurrently increment a shared counter, each acquiring it
    // with `with` (the cown lock). `main` spawns them; Engine::run joins spawned
    // threads in its epilogue, so when `result` reads the global counter every
    // increment has landed -- and the lock makes it data-race-free, so the total
    // is exact (no lost updates).
    let src = "\
type Counter = {
    n: int32
}

fun Counter.add(self, k: int32) {
    self.n += k
}

let total = Counter { n: 0 }

fun bump(c: ref(mut(Counter))) {
    let i = 0
    while i < 500 {
        with(c, (h) -> {
            h.add(1)
        })
        i = i + 1
    }
}

fun main() {
    spawn(() -> {
        bump(total)
    })
    spawn(() -> {
        bump(total)
    })
}

fun result() -> int32 {
    return total.n
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    // Runs the init (total = 0) and `main` (spawns both threads), then joins them.
    Engine::run(&mut backend, &mono).expect("engine run");

    // 2 threads x 500 locked increments, no lost updates.
    assert_eq!(backend.run_entry_i32("result"), Some(1000));
}

#[test]
fn typed_globals_initialized_and_read() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    // Module-level globals are typed LLVM globals (no boxed Value): the init body
    // runs (via Engine::run) before reads, and functions load the typed global.
    let src = "\
let base = 7
let scale = 3

fun shown() {
    return base
}

fun scaled() {
    return base * scale
}
";
    let ast = prepoly_parser::parse(src).expect("parse");
    let modules = [LoadedModule {
        path: vec!["main".into()],
        ast,
    }];
    let (program, errors) = lower(&modules);
    assert!(errors.is_empty(), "HIR lowering errors: {errors:?}");

    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    // Engine::run executes the init body, initializing the globals.
    Engine::run(&mut backend, &mono).expect("engine run");

    assert_eq!(backend.run_entry_i32("shown"), Some(7));
    assert_eq!(backend.run_entry_i32("scaled"), Some(21)); // 7 * 3
}

/// R6 value-observability: `sync()` joins spawned threads so their effects are
/// observable. Three threads each increment a shared counter under `with` (so the
/// increments are race-free), then `sync()` joins them; reading the counter after
/// `sync()` deterministically sees all three.
#[test]
fn sync_makes_spawned_results_observable() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "type Counter = {\n  n: int32\n}\n\
               fun Counter.bump(self) {\n    self.n += 1\n  }\n\
               fun counted() -> int32 {\n\
               \x20 let c = Counter { n: 0 }\n\
               \x20 spawn(() -> { with(c, (c) -> { c.bump() }) })\n\
               \x20 spawn(() -> { with(c, (c) -> { c.bump() }) })\n\
               \x20 spawn(() -> { with(c, (c) -> { c.bump() }) })\n\
               \x20 sync()\n\
               \x20 return c.n\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    // After `sync()`, all three increments are observed.
    assert_eq!(backend.run_entry_i32("counted"), Some(3));
}

/// R6 reference counting: straight-line string temporaries are reclaimed at
/// return -- the live-block count returns to its pre-call baseline (no leak), and
/// it never goes below (no double free). Validates retain-on-alias + release of
/// dead managed locals at return.
#[test]
fn rc_reclaims_string_temporaries() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "fun work() -> int32 {\n\
               \x20 let a = string.from(1)\n\
               \x20 let b = string.from(2)\n\
               \x20 let c = a\n\
               \x20 return 7\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    let before = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(backend.run_entry_i32("work"), Some(7));
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "string temporaries reclaimed (no leak, no double free): {before} -> {after}"
    );
}

/// R6 reference counting with reassignment: a loop that rebinds a string each
/// iteration reclaims the previous value (release-on-reassign), so live blocks
/// return to baseline rather than growing with the iteration count.
#[test]
fn rc_reclaims_loop_string_temporaries() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "fun churn() -> int32 {\n\
               \x20 let i = 0\n\
               \x20 while i < 50 {\n\
               \x20   let s = string.from(i)\n\
               \x20   i = i + 1\n\
               \x20 }\n\
               \x20 return i\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    let before = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(backend.run_entry_i32("churn"), Some(50));
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "loop string temporaries reclaimed: {before} -> {after}"
    );
}

/// Regression (R6 RC): string interpolation calls `to_string`, which for a string
/// argument is the identity -- its result aliases the argument, so binding it must
/// retain or releasing both the source and the bound copy double-frees (which
/// previously crashed example 02). This asserts soundness: the program runs and the
/// live-block count never drops below baseline (no double free). A small bounded
/// residue remains -- interpolation builds a couple of inline transient string
/// literals not bound to a local, which the current local-scoped reclamation does
/// not reach (sound: they leak, never use-after-free).
#[test]
fn rc_balances_string_interpolation() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "fun name() -> string {\n  return \"green\"\n}\n\
               fun greet() -> int32 {\n\
               \x20 let msg = \"color = {name()}\"\n\
               \x20 return len(msg)\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    let before = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(backend.run_entry_i32("greet"), Some(13)); // "color = green"
    let after = prepoly_runtime::mem::pp_live_blocks();
    // No double free: the count never drops below baseline (the bug it guards
    // manifested as a double free / crash). A small bounded residue (inline
    // transient literals) is reclaimed only once container/transient RC lands.
    assert!(
        after >= before && after - before <= 2,
        "interpolation runs soundly, bounded residue: {before} -> {after}"
    );
}

/// R6 RC: a scalar-field record built and dropped within a function is reclaimed
/// at return (its block is freed), so the live-block count returns to baseline.
#[test]
fn rc_reclaims_record_temporaries() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "type P = {\n  x: int32\n  y: int32\n}\n\
               fun build() -> int32 {\n\
               \x20 let a = P { x: 1, y: 2 }\n\
               \x20 let b = P { x: 3, y: 4 }\n\
               \x20 return a.x + b.y\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    let before = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(backend.run_entry_i32("build"), Some(5)); // 1 + 4
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "record temporaries reclaimed: {before} -> {after}"
    );
}

/// R6 RC recursive destructor: a record owning a string field is reclaimed with
/// its field -- freeing the record releases the string, so live blocks return to
/// baseline (no leak of the field, no double free).
#[test]
fn rc_recursive_destructor_releases_record_fields() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "type Person = {\n  name: string\n  age: int32\n}\n\
               fun build() -> int32 {\n\
               \x20 let p = Person { name: string.from(42), age: 7 }\n\
               \x20 return p.age\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    let before = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(backend.run_entry_i32("build"), Some(7));
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "record + string field reclaimed: {before} -> {after}"
    );
}

/// R6 RC for arrays + sums: a scalar-element array and a sum value built and
/// dropped within a function reclaim to baseline (the array frees its element
/// buffer and header; the sum frees its block).
#[test]
fn rc_reclaims_array_and_sum() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "type Tag =\n  | A { v: int32 }\n  | B\n\
               fun use_arr() -> int32 {\n\
               \x20 let xs = [1, 2, 3, 4, 5]\n\
               \x20 return xs[0]\n\
               }\n\
               fun use_sum() -> int32 {\n\
               \x20 let t = Tag.A { v: 9 }\n\
               \x20 return match t {\n    A { v } => v,\n    B => 0,\n  }\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    let before = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(backend.run_entry_i32("use_arr"), Some(1));
    assert_eq!(backend.run_entry_i32("use_sum"), Some(9));
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(after, before, "array + sum reclaimed: {before} -> {after}");
}

/// R6 RC overwrite: storing into a managed record field, array element,
/// nullable field, or global releases the value being overwritten -- the slot
/// owned it and it is no longer reachable through the slot. Before the
/// release-on-overwrite each loop iteration leaked the previous value (and a
/// nullable slot leaked its cell too), so live blocks grew with the iteration
/// count; now they return to baseline.
#[test]
fn rc_releases_overwritten_field_element_and_global() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "type Box = {\n  value: string\n}\n\
               type Cell = {\n  s: string?\n}\n\
               let g = string.from(0)\n\
               fun churn() -> int32 {\n\
               \x20 let b = Box { value: string.from(1) }\n\
               \x20 let c = Cell { s: null }\n\
               \x20 let xs = [string.from(2)]\n\
               \x20 let i = 0\n\
               \x20 while i < 20 {\n\
               \x20   b.value = string.from(i)\n\
               \x20   c.s = string.from(i)\n\
               \x20   xs[0] = string.from(i)\n\
               \x20   g = string.from(i)\n\
               \x20   i = i + 1\n\
               \x20 }\n\
               \x20 return i\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    // The global holds one string at baseline and one (different) string after,
    // so a balanced run returns exactly to baseline; every overwritten value
    // leaking would leave ~80 extra blocks.
    let before = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(backend.run_entry_i32("churn"), Some(20));
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "overwritten field/element/cell/global values reclaimed: {before} -> {after}"
    );
}

/// R6 RC recursive array content: an array of strings reclaims its elements (the
/// element loop in the destructor releases each), so live blocks return to baseline.
#[test]
fn rc_recursive_array_releases_string_elements() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "fun build() -> int32 {\n\
               \x20 let xs = [string.from(1), string.from(2), string.from(3)]\n\
               \x20 return len(xs)\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    let before = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(backend.run_entry_i32("build"), Some(3));
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "array string elements reclaimed: {before} -> {after}"
    );
}

/// R6 RC recursive sum content: a sum variant owning a string field reclaims it
/// (the tag-dispatched destructor releases the active variant's heap fields), so
/// live blocks return to baseline.
#[test]
fn rc_recursive_sum_releases_variant_fields() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "type Box =\n  | S { name: string }\n  | E\n\
               fun build() -> int32 {\n\
               \x20 let b = Box.S { name: string.from(7) }\n\
               \x20 return match b {\n    S { name } => len(name),\n    E => 0,\n  }\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    let before = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(backend.run_entry_i32("build"), Some(1)); // len("7")
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "sum variant string field reclaimed: {before} -> {after}"
    );
}

/// R6 RC for closures: a spawned closure is moved to its thread, which releases it
/// when it finishes; after `sync()` joins the threads the closure blocks are
/// reclaimed, so live blocks return to baseline (no leak of the closure, no double
/// free across spawner/thread).
#[test]
fn rc_reclaims_spawned_closures() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "fun work() -> int32 {\n\
               \x20 spawn(() -> {\n  })\n\
               \x20 spawn(() -> {\n  })\n\
               \x20 sync()\n\
               \x20 return 1\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    let before = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(backend.run_entry_i32("work"), Some(1));
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "spawned closures reclaimed after sync: {before} -> {after}"
    );
}

/// R6 RC: a spawned closure that captures a heap value (a string) releases the
/// capture via its stored destructor when the thread finishes, so after `sync()`
/// the live-block count returns to baseline (the capture is reclaimed, not leaked).
#[test]
fn rc_spawned_closure_releases_heap_capture() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "fun work() -> int32 {\n\
               \x20 let s = string.from(7)\n\
               \x20 spawn(() -> {\n    let _ = len(s)\n  })\n\
               \x20 sync()\n\
               \x20 return 1\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");

    let before = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(backend.run_entry_i32("work"), Some(1));
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "spawned closure capture reclaimed: {before} -> {after}"
    );
}

/// Array rendering: `to_string` of an array renders `[e0, e1, ...]` (string
/// interpolation of an array), for scalar and nested element types.
#[test]
fn array_renders_as_bracketed_list() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "fun show() -> int32 {\n\
               \x20 let xs = [1, 2, 3]\n\
               \x20 let s = \"{xs}\"\n\
               \x20 return len(s)\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");
    // "[1, 2, 3]" is 9 bytes.
    assert_eq!(backend.run_entry_i32("show"), Some(9));
}

/// A trailing nullable parameter is optional at call sites and keeps
/// its declared (nullable) type whether omitted or passed a value -- including a
/// value type like `int32?`, where `if b` is a null test (so a present `0` takes the
/// `if` branch) and `b` unwraps to `int32` in arithmetic. `pick(10)` omits `b`
/// (null -> 10); `pick(10, 5)` passes it (15); the result is 25.
#[test]
fn trailing_nullable_param_is_optional() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "fun pick(a: int32, b: int32?) -> int32 {\n\
               \x20 if b { return a + b }\n\
               \x20 return a\n\
               }\n\
               fun check() -> int32 {\n\
               \x20 return pick(10) + pick(10, 5)\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");
    assert_eq!(backend.run_entry_i32("check"), Some(25));
}

/// A captured-and-mutated local that is also used in its defining frame after
/// capture is a shared heap cell (RcCell): the closure's mutations
/// are seen through the shared capture, not made on a per-closure copy. `g` adds to
/// `x` twice; `f` returns the shared `x` = 2 (by-value capture would give 0).
#[test]
fn captured_mutated_local_is_a_shared_cell() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "fun f() -> int32 {\n\
               \x20 let x = 0\n\
               \x20 let g = (d: int32) -> {\n\
               \x20   x += d\n\
               \x20   return x\n\
               \x20 }\n\
               \x20 let a = g(1)\n\
               \x20 let b = g(1)\n\
               \x20 return x\n\
               }\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    Engine::run(&mut backend, &mono).expect("engine run");
    assert_eq!(backend.run_entry_i32("f"), Some(2));
}

/// The cycle collector reclaims a reference cycle that plain reference counting
/// cannot. A self-referential record (`a.next = a`, where `next` is a
/// nullable cell whose retained value points back at the node) keeps its own count
/// above zero, so it leaks under counting alone; the collector run at program end
/// frees both the node and its cell, returning the live-block count to its pre-run
/// baseline. Exercises the whole chain: self-referential record monomorphization,
/// null-initialized field declared-typing, nullable-cell reference counting, and the
/// trial-deletion collector.
#[test]
fn cycle_collector_reclaims_record_cycle() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "type Node = { next: Node? }\n\
               fun main() {\n\
               \x20 let a = Node { next: null }\n\
               \x20 a.next = a\n\
               }\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    let before = prepoly_runtime::mem::pp_live_blocks();
    Engine::run(&mut backend, &mono).expect("engine run");
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "the record cycle is reclaimed at program end"
    );
}

/// A multi-node cycle (`a.next = b; b.next = a`) is reclaimed too: the collector
/// walks the whole strongly-connected component, not just self-loops.
#[test]
fn cycle_collector_reclaims_two_node_cycle() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "type Node = { next: Node? }\n\
               fun main() {\n\
               \x20 let a = Node { next: null }\n\
               \x20 let b = Node { next: null }\n\
               \x20 a.next = b\n\
               \x20 b.next = a\n\
               }\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    let before = prepoly_runtime::mem::pp_live_blocks();
    Engine::run(&mut backend, &mono).expect("engine run");
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "the two-node cycle is reclaimed at program end"
    );
}

/// Reclaiming a cycle also reclaims the non-cycle objects it owns: a node in the
/// cycle holds a `string`, which is referenced only through the garbage cycle. The
/// trial-deletion traversal reaches it (its trial-decremented count hits zero), so it
/// is freed along with the cycle -- no leaked string.
#[test]
fn cycle_collector_reclaims_data_owned_by_cycle() {
    let _guard = JIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let src = "type Node = { next: Node?, name: string }\n\
               fun main() {\n\
               \x20 let a = Node { next: null, name: \"hello\" }\n\
               \x20 a.next = a\n\
               }\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errors) = lower(&[LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "lower: {errors:?}");
    let mir = lower_program(&program);
    let mono = monomorphize(&mir, &program).expect("monomorphize");
    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    let before = prepoly_runtime::mem::pp_live_blocks();
    Engine::run(&mut backend, &mono).expect("engine run");
    let after = prepoly_runtime::mem::pp_live_blocks();
    assert_eq!(
        after, before,
        "the cycle and the string it owns are both reclaimed"
    );
}
