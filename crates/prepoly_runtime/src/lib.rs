//! Prepoly runtime: the C-ABI primitives that the typed (unboxed) JIT back end
//! links against. The back end emits monomorphized LLVM that operates on
//! concrete typed values, so the runtime only provides the heap object model
//! (a bump allocator over `Header`-prefixed objects in `crate::mem`), the typed
//! string/array/conversion entry points, and the panic path. There is no boxed
//! value representation and no garbage collector: heap is bump-allocated and the
//! process exits on a runtime error.

pub mod alloc;
pub mod builtins;
pub mod conc;
pub mod gc;
pub mod io;
pub mod mem;
pub mod net;
pub mod region;
pub mod rt;

/// Every C-ABI runtime primitive paired with its address, so the JIT can map
/// the module's external declarations to these implementations directly
/// (robust against symbol stripping). This is exactly the set the typed code
/// generator calls (see `prepoly_jit_llvm::codegen`).
pub fn symbols() -> Vec<(&'static str, usize)> {
    macro_rules! s {
        ($($f:path),* $(,)?) => { vec![ $( (stringify_last(stringify!($f)), $f as *const () as usize) ),* ] };
    }
    s![
        alloc::pp_typed_alloc,
        alloc::pp_retain,
        alloc::pp_release,
        alloc::pp_freeze,
        mem::pp_obj_free,
        alloc::pp_arr_new,
        alloc::pp_arr_copy,
        alloc::pp_arr_deep_copy,
        alloc::pp_arr_push,
        alloc::pp_arr_insert,
        alloc::pp_arr_remove,
        alloc::pp_arr_pop,
        alloc::pp_str_const,
        alloc::pp_str_len,
        alloc::pp_str_concat,
        alloc::pp_str_eq,
        alloc::pp_str_cmp,
        alloc::pp_str_slice,
        alloc::pp_str_to_bytes,
        alloc::pp_str_find,
        alloc::pp_str_indent,
        alloc::pp_int_to_str,
        alloc::pp_float_to_str,
        alloc::pp_bool_to_str,
        alloc::pp_print_str,
        alloc::pp_println_str,
        builtins::pp_str_char_at,
        builtins::pp_str_from_bytes,
        builtins::pp_conv_int_from,
        builtins::pp_conv_int_parse,
        builtins::pp_conv_float_from,
        builtins::pp_conv_float_parse,
        builtins::pp_int_widen,
        builtins::pp_int_narrow,
        builtins::pp_panic,
        builtins::pp_panic_obj,
        conc::pp_spawn,
        conc::pp_join_all,
        conc::pp_lock,
        conc::pp_unlock,
        conc::pp_lock_all,
        conc::pp_unlock_all,
        conc::pp_lock_span,
        conc::pp_unlock_span,
        conc::pp_make_cown,
        region::pp_region_open,
        region::pp_region_open_nested,
        region::pp_region_write,
        region::pp_region_store,
        region::pp_add_reference,
        region::pp_remove_reference,
        region::pp_write_barrier,
        region::pp_region_unborrow,
        region::pp_region_close,
        io::pp_file_open,
        io::pp_file_stdin,
        io::pp_file_stdout,
        io::pp_file_stderr,
        io::pp_file_read,
        io::pp_file_write,
        io::pp_file_size,
        io::pp_file_seek,
        io::pp_file_close,
        net::pp_tcp_connect,
        net::pp_tcp_listen,
        net::pp_tcp_accept,
        net::pp_udp_bind,
        net::pp_udp_send_to,
        net::pp_udp_recv_from,
        net::pp_socket_addr,
        net::pp_socket_set_timeout,
        gc::pp_gc_register,
        gc::pp_gc_collect,
        gc::pp_freeze_deep,
        gc::pp_gc_set_gen0_threshold,
        gc::pp_gc_gen0_runs,
    ]
}

/// Strip a `module::path::name` down to the final `name` segment.
fn stringify_last(path: &'static str) -> &'static str {
    match path.rsplit("::").next() {
        Some(n) => n,
        None => path,
    }
}

/// A process-wide lock serializing tests that read or mutate global heap state --
/// the allocator's `LIVE_BLOCKS` count, the cycle collector's registry, and its
/// generational schedule. These are process globals, so without serialization the
/// default multi-threaded test runner lets one test's allocations perturb another's
/// exact live-block assertions (and the spawn tests leave their closures live on
/// purpose). Every test that allocates or inspects those counters holds this guard
/// for its duration, so they run one at a time.
#[cfg(test)]
pub(crate) fn serial_heap_test() -> std::sync::MutexGuard<'static, ()> {
    static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    LOCK.lock().unwrap_or_else(|e| e.into_inner())
}
