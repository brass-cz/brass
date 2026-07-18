//! A small owning wrapper over LLVM ORC's C API.
//!
//! LLVM's C API does not expose `LLLazyJIT`, but it does expose the lower-level
//! pieces it is built from: custom materialization units, lazy reexports, and
//! indirect stubs. This module combines those pieces so Brass can generate one
//! function module only when its call-through stub is entered for the first
//! time. All raw ownership transfer is kept in this module; callers deal in
//! owning [`OrcModule`] values and ordinary Rust callbacks.

use fxhash::FxHashMap as HashMap;
use std::cell::Cell;
use std::ffi::{CStr, CString, c_void};
use std::mem::ManuallyDrop;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::ptr;

use inkwell::module::Module;
use inkwell::targets::{InitializationConfig, Target};
use llvm_sys::core::{LLVMDisposeMessage, LLVMDisposeModule, LLVMSetDataLayout};
use llvm_sys::error::{LLVMDisposeErrorMessage, LLVMErrorRef, LLVMGetErrorMessage};
use llvm_sys::orc2::lljit::{
    LLVMOrcCreateLLJIT, LLVMOrcCreateLLJITBuilder, LLVMOrcDisposeLLJIT,
    LLVMOrcLLJITBuilderSetJITTargetMachineBuilder, LLVMOrcLLJITGetDataLayoutStr,
    LLVMOrcLLJITGetExecutionSession, LLVMOrcLLJITGetIRTransformLayer, LLVMOrcLLJITGetMainJITDylib,
    LLVMOrcLLJITGetTripleString, LLVMOrcLLJITLookup, LLVMOrcLLJITMangleAndIntern, LLVMOrcLLJITRef,
};
use llvm_sys::orc2::{
    LLVMJITEvaluatedSymbol, LLVMJITSymbolFlags, LLVMJITSymbolGenericFlags, LLVMOrcAbsoluteSymbols,
    LLVMOrcCSymbolAliasMapEntry, LLVMOrcCSymbolAliasMapPair, LLVMOrcCSymbolFlagsMapPair,
    LLVMOrcCSymbolMapPair, LLVMOrcCreateCustomMaterializationUnit,
    LLVMOrcCreateLocalIndirectStubsManager, LLVMOrcCreateLocalLazyCallThroughManager,
    LLVMOrcCreateNewThreadSafeContextFromLLVMContext, LLVMOrcCreateNewThreadSafeModule,
    LLVMOrcDisposeIndirectStubsManager, LLVMOrcDisposeLazyCallThroughManager,
    LLVMOrcDisposeMaterializationResponsibility, LLVMOrcDisposeMaterializationUnit,
    LLVMOrcDisposeSymbols, LLVMOrcDisposeThreadSafeContext, LLVMOrcDisposeThreadSafeModule,
    LLVMOrcExecutionSessionSetErrorReporter, LLVMOrcIRTransformLayerEmit,
    LLVMOrcIRTransformLayerSetTransform, LLVMOrcIndirectStubsManagerRef, LLVMOrcJITDylibDefine,
    LLVMOrcJITDylibRef, LLVMOrcJITTargetMachineBuilderCreateFromTargetMachine,
    LLVMOrcLazyCallThroughManagerRef, LLVMOrcLazyReexports,
    LLVMOrcMaterializationResponsibilityFailMaterialization,
    LLVMOrcMaterializationResponsibilityGetRequestedSymbols,
    LLVMOrcMaterializationResponsibilityRef, LLVMOrcMaterializationUnitRef,
    LLVMOrcSymbolStringPoolEntryStr, LLVMOrcThreadSafeContextRef,
    LLVMOrcThreadSafeModuleWithModuleDo,
};
use llvm_sys::target_machine::{
    LLVMCodeGenOptLevel, LLVMCodeModel, LLVMCreateTargetMachine, LLVMGetDefaultTargetTriple,
    LLVMGetHostCPUFeatures, LLVMGetHostCPUName, LLVMGetTargetFromTriple, LLVMRelocMode,
};
use llvm_sys::transforms::pass_builder::{
    LLVMCreatePassBuilderOptions, LLVMDisposePassBuilderOptions, LLVMRunPasses,
};

type Materializer<'a> = dyn FnMut(&LazyFunction) -> Result<OrcModule, String> + 'a;

/// Owns an LLVM context until it is transferred to ORC. This wrapper makes
/// context ownership explicit across fallible JIT construction: ordinary Rust
/// drops it before a transfer, while the ORC session drops it afterwards.
pub(crate) struct OrcContext {
    context: ManuallyDrop<inkwell::context::Context>,
    transferred: Cell<bool>,
}

impl OrcContext {
    pub(crate) fn new() -> Self {
        Self {
            context: ManuallyDrop::new(inkwell::context::Context::create()),
            transferred: Cell::new(false),
        }
    }

    pub(crate) fn context(&self) -> &inkwell::context::Context {
        &self.context
    }

    fn transfer(&self) -> Result<llvm_sys::prelude::LLVMContextRef, String> {
        if self.transferred.replace(true) {
            Err("LLVM context was transferred to ORC twice".to_string())
        } else {
            Ok(self.context.raw())
        }
    }
}

impl Drop for OrcContext {
    fn drop(&mut self) {
        if !self.transferred.get() {
            // SAFETY: no ORC session accepted the context, so this wrapper
            // remains its sole owner.
            unsafe { ManuallyDrop::drop(&mut self.context) };
        }
    }
}

/// A public callable symbol and the hidden implementation symbol backing its
/// lazy call-through stub.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LazyFunction {
    pub(crate) symbol: String,
    pub(crate) implementation: String,
}

pub(crate) fn lazy_implementation_symbol(symbol: &str) -> String {
    format!("__pp_lazy_body_{symbol}")
}

/// An LLVM module whose raw allocation is owned by Rust until it is transferred
/// to ORC. Consuming an Inkwell module is the only public construction path, so
/// the module cannot be dropped by both wrappers.
pub(crate) struct OrcModule {
    raw: Option<llvm_sys::prelude::LLVMModuleRef>,
}

impl OrcModule {
    pub(crate) fn from_inkwell(module: Module<'_>) -> Self {
        let module = std::mem::ManuallyDrop::new(module);
        let raw = module.as_mut_ptr();
        // ORC will eventually own this allocation. Prevent Inkwell's `Drop`
        // from disposing it while it is represented by `OrcModule`.
        Self { raw: Some(raw) }
    }

    fn take_raw(&mut self) -> llvm_sys::prelude::LLVMModuleRef {
        self.raw.take().expect("ORC module transferred twice")
    }
}

impl Drop for OrcModule {
    fn drop(&mut self) {
        if let Some(raw) = self.raw.take() {
            // SAFETY: `raw` is owned by this value until `take_raw` transfers it.
            unsafe { LLVMDisposeModule(raw) };
        }
    }
}

struct MaterializerState {
    jit: LLVMOrcLLJITRef,
    context: LLVMOrcThreadSafeContextRef,
    data_layout: CString,
    requests: HashMap<String, LazyFunction>,
    callback: *mut (),
    errors: Vec<String>,
}

/// Session errors mirrored for [`materialization_failed`], which is entered
/// from a patched stub and has no session context. Draining on the ordinary
/// report path keeps the mirror scoped to undelivered errors; concurrent
/// sessions (tests) may interleave here, which only affects the wording of a
/// process-ending diagnostic.
static FATAL_ERRORS: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());

/// Jumped to by a lazy call-through stub whose implementation failed to
/// materialize. The caller's frame expected to enter the requested function,
/// so the program cannot continue: report what the session recorded and exit.
extern "C" fn materialization_failed() -> ! {
    let mut message = String::from("lazy compilation failed");
    if let Ok(mut mirror) = FATAL_ERRORS.lock() {
        for error in mirror.drain(..) {
            message.push('\n');
            message.push_str(&error);
        }
    }
    eprintln!("error: {message}");
    std::process::exit(1);
}

impl MaterializerState {
    fn push_error(&mut self, error: impl Into<String>) {
        let error = error.into();
        if let Ok(mut mirror) = FATAL_ERRORS.lock() {
            mirror.push(error.clone());
        }
        self.errors.push(error);
    }

    fn transfer_to_thread_safe_module(
        &mut self,
        mut module: OrcModule,
    ) -> llvm_sys::orc2::LLVMOrcThreadSafeModuleRef {
        let raw = module.take_raw();
        // SAFETY: `raw` and `context` are live LLVM objects owned by this state.
        // `LLVMOrcCreateNewThreadSafeModule` takes ownership of the module and a
        // shared reference to the thread-safe context.
        unsafe {
            LLVMSetDataLayout(raw, self.data_layout.as_ptr());
            LLVMOrcCreateNewThreadSafeModule(raw, self.context)
        }
    }

    fn materialize(&mut self, responsibility: LLVMOrcMaterializationResponsibilityRef) {
        let mut count = 0;
        // SAFETY: `responsibility` is supplied by ORC for this callback. The
        // returned array remains valid until disposed below.
        let symbols = unsafe {
            LLVMOrcMaterializationResponsibilityGetRequestedSymbols(responsibility, &mut count)
        };
        let result = if count == 0 || symbols.is_null() {
            Err("lazy materialization received no symbols".to_string())
        } else {
            // A grouped unit claims several implementations but one emitted
            // module defines them all, so any requested member identifies the
            // group; resolve through the first.
            // SAFETY: the array has at least one element and its string-pool
            // entry is retained for the duration of this callback.
            let name = unsafe {
                let entry = *symbols;
                CStr::from_ptr(LLVMOrcSymbolStringPoolEntryStr(entry))
                    .to_string_lossy()
                    .into_owned()
            };
            let request = self
                .requests
                .get(&name)
                .cloned()
                .ok_or_else(|| format!("unregistered lazy implementation `{name}`"));
            request.and_then(|request| {
                if self.callback.is_null() {
                    return Err(format!(
                        "lazy implementation `{}` was called without a materializer",
                        request.symbol
                    ));
                }
                // SAFETY: `with_materializer` installs a pointer to a live
                // callback for the duration of JIT execution and restores the
                // previous slot before returning.
                let callback = unsafe { &mut *(self.callback as *mut &mut Materializer<'static>) };
                tracing::trace!(
                    target: "brass::perf",
                    symbol = %request.symbol,
                    "back/orc-materialize"
                );
                callback(&request)
            })
        };
        // SAFETY: ownership of the requested-symbol array belongs to this
        // callback and must be released exactly once.
        unsafe { LLVMOrcDisposeSymbols(symbols) };

        match result {
            Ok(module) => {
                let module = self.transfer_to_thread_safe_module(module);
                // SAFETY: ORC takes ownership of both the responsibility and
                // module when the transform layer is asked to emit them.
                unsafe {
                    let layer = LLVMOrcLLJITGetIRTransformLayer(self.jit);
                    LLVMOrcIRTransformLayerEmit(layer, responsibility, module);
                }
            }
            Err(error) => {
                self.push_error(error);
                // SAFETY: failure completes the responsibility; it is then
                // disposed exactly once as required by the ORC C API.
                unsafe {
                    LLVMOrcMaterializationResponsibilityFailMaterialization(responsibility);
                    LLVMOrcDisposeMaterializationResponsibility(responsibility);
                }
            }
        }
    }
}

extern "C" fn materialize_callback(
    context: *mut c_void,
    responsibility: LLVMOrcMaterializationResponsibilityRef,
) {
    // No Rust unwind may cross the C ABI. A panic is converted into an ORC
    // materialization failure and reported through the ordinary error channel.
    let result = catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: every custom materialization unit is registered with the
        // stable boxed `MaterializerState` pointer owned by `OrcJit`.
        unsafe { (&mut *(context as *mut MaterializerState)).materialize(responsibility) };
    }));
    if result.is_err() {
        // SAFETY: same state and responsibility invariants as above. The panic
        // happened before the callback completed, so fail the responsibility.
        unsafe {
            let state = &mut *(context as *mut MaterializerState);
            state.push_error("lazy materializer panicked");
            LLVMOrcMaterializationResponsibilityFailMaterialization(responsibility);
            LLVMOrcDisposeMaterializationResponsibility(responsibility);
        }
    }
}

extern "C" fn discard_callback(
    _context: *mut c_void,
    _dylib: LLVMOrcJITDylibRef,
    _symbol: llvm_sys::orc2::LLVMOrcSymbolStringPoolEntryRef,
) {
}

extern "C" fn destroy_callback(_context: *mut c_void) {}

extern "C" fn error_reporter(context: *mut c_void, error: LLVMErrorRef) {
    // SAFETY: ORC calls this with the boxed state installed in the execution
    // session and transfers ownership of `error` to the reporter.
    unsafe {
        let state = &mut *(context as *mut MaterializerState);
        state.push_error(take_error(error));
    }
}

extern "C" fn optimize_transform(
    _context: *mut c_void,
    module: *mut llvm_sys::orc2::LLVMOrcThreadSafeModuleRef,
    _responsibility: LLVMOrcMaterializationResponsibilityRef,
) -> LLVMErrorRef {
    // SAFETY: ORC supplies a live ThreadSafeModule slot. The nested callback
    // runs under that module's context lock.
    unsafe { LLVMOrcThreadSafeModuleWithModuleDo(*module, optimize_module, ptr::null_mut()) }
}

extern "C" fn optimize_module(
    _context: *mut c_void,
    module: llvm_sys::prelude::LLVMModuleRef,
) -> LLVMErrorRef {
    const PIPELINE: &[u8] = b"default<O2>\0";
    // SAFETY: `module` is locked by `LLVMOrcThreadSafeModuleWithModuleDo`.
    // Target-independent O2 IR passes accept a null target machine; native
    // code generation subsequently uses the O2 machine configured for LLJIT.
    unsafe {
        let options = LLVMCreatePassBuilderOptions();
        let error = LLVMRunPasses(module, PIPELINE.as_ptr().cast(), ptr::null_mut(), options);
        LLVMDisposePassBuilderOptions(options);
        error
    }
}

/// A single-threaded ORC session supporting per-function lazy materialization.
///
/// The supplied [`OrcContext`] is transferred to ORC. The JIT releases it after
/// all pending modules have been destroyed.
pub(crate) struct OrcJit {
    jit: LLVMOrcLLJITRef,
    dylib: LLVMOrcJITDylibRef,
    stubs: LLVMOrcIndirectStubsManagerRef,
    call_through: LLVMOrcLazyCallThroughManagerRef,
    state: Box<MaterializerState>,
}

impl OrcJit {
    pub(crate) fn new(context: &OrcContext) -> Result<Self, String> {
        Target::initialize_native(&InitializationConfig::default())
            .map_err(|error| format!("failed to initialize native LLVM target: {error}"))?;

        let jit = create_o2_jit()?;
        // SAFETY: `jit` is live after successful construction and owns both
        // returned references.
        let (dylib, triple, data_layout, execution_session) = unsafe {
            let triple = CStr::from_ptr(LLVMOrcLLJITGetTripleString(jit)).to_owned();
            let data_layout = CStr::from_ptr(LLVMOrcLLJITGetDataLayoutStr(jit)).to_owned();
            (
                LLVMOrcLLJITGetMainJITDylib(jit),
                triple,
                data_layout,
                LLVMOrcLLJITGetExecutionSession(jit),
            )
        };
        // SAFETY: the target triple comes from this LLJIT instance.
        let stubs = unsafe { LLVMOrcCreateLocalIndirectStubsManager(triple.as_ptr()) };
        if stubs.is_null() {
            // SAFETY: construction succeeded and no ORC child owns `jit` yet.
            unsafe {
                let _ = LLVMOrcDisposeLLJIT(jit);
            }
            return Err("failed to create ORC indirect stubs manager".to_string());
        }
        let mut call_through = ptr::null_mut();
        // SAFETY: all arguments belong to the same live ORC execution session.
        // A stub whose materialization fails branches to the error-handler
        // address in place of its body, so the handler must never return.
        let call_through_result = unsafe {
            check_error(LLVMOrcCreateLocalLazyCallThroughManager(
                triple.as_ptr(),
                execution_session,
                materialization_failed as *const () as u64,
                &mut call_through,
            ))
        };
        if let Err(error) = call_through_result {
            // SAFETY: these objects were created above and have not been shared.
            unsafe {
                LLVMOrcDisposeIndirectStubsManager(stubs);
                let _ = LLVMOrcDisposeLLJIT(jit);
            }
            return Err(error);
        }

        let raw_context = context.transfer()?;
        // SAFETY: `OrcContext::transfer` gives this thread-safe wrapper sole
        // ownership of the raw context.
        let thread_safe_context =
            unsafe { LLVMOrcCreateNewThreadSafeContextFromLLVMContext(raw_context) };
        let mut state = Box::new(MaterializerState {
            jit,
            context: thread_safe_context,
            data_layout,
            requests: HashMap::default(),
            callback: ptr::null_mut(),
            errors: Vec::new(),
        });
        // SAFETY: `state` is boxed and remains at this address until after the
        // execution session is disposed in `Drop`.
        unsafe {
            LLVMOrcExecutionSessionSetErrorReporter(
                execution_session,
                error_reporter,
                state.as_mut() as *mut MaterializerState as *mut c_void,
            );
            LLVMOrcIRTransformLayerSetTransform(
                LLVMOrcLLJITGetIRTransformLayer(jit),
                optimize_transform,
                ptr::null_mut(),
            );
        }

        Ok(Self {
            jit,
            dylib,
            stubs,
            call_through,
            state,
        })
    }

    pub(crate) fn add_eager_module(&mut self, module: OrcModule) -> Result<(), String> {
        let thread_safe = self.state.transfer_to_thread_safe_module(module);
        // SAFETY: the module and dylib belong to this JIT. On success ownership
        // transfers to LLJIT; on error it remains here and is disposed below.
        let result = unsafe {
            llvm_sys::orc2::lljit::LLVMOrcLLJITAddLLVMIRModule(self.jit, self.dylib, thread_safe)
        };
        if result.is_null() {
            Ok(())
        } else {
            // SAFETY: failed addition leaves ownership with the caller.
            unsafe { LLVMOrcDisposeThreadSafeModule(thread_safe) };
            // SAFETY: `result` is an owned LLVM error.
            Err(unsafe { take_error(result) })
        }
    }

    pub(crate) fn define_absolute(
        &mut self,
        symbols: impl IntoIterator<Item = (String, usize)>,
    ) -> Result<(), String> {
        let mut pairs = symbols
            .into_iter()
            .map(|(name, address)| {
                let name = c_string(&name)?;
                // SAFETY: the returned pool entry is retained and ownership is
                // immediately transferred to `LLVMOrcAbsoluteSymbols`.
                let name = unsafe { LLVMOrcLLJITMangleAndIntern(self.jit, name.as_ptr()) };
                Ok(LLVMOrcCSymbolMapPair {
                    Name: name,
                    Sym: LLVMJITEvaluatedSymbol {
                        Address: address as u64,
                        Flags: callable_flags(),
                    },
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        // SAFETY: the materialization unit takes ownership of every retained
        // symbol-pool entry in `pairs`; the Vec storage remains Rust-owned.
        let unit = unsafe { LLVMOrcAbsoluteSymbols(pairs.as_mut_ptr(), pairs.len()) };
        self.define(unit)
    }

    /// [`register_lazy_group`](Self::register_lazy_group) for one function.
    /// Production callers always register groups; the single-symbol form
    /// remains as the minimal harness for the materialization tests.
    #[cfg(test)]
    pub(crate) fn register_lazy(&mut self, symbol: &str) -> Result<LazyFunction, String> {
        self.register_lazy_group(std::slice::from_ref(&symbol.to_string()))?;
        Ok(LazyFunction {
            symbol: symbol.to_string(),
            implementation: lazy_implementation_symbol(symbol),
        })
    }

    /// Register a GROUP of lazily materialized functions: every symbol keeps
    /// its own call-through stub (callers defer per function exactly as
    /// before), but all of the group's implementations are claimed by one
    /// materialization unit, satisfied by one emitted module that defines
    /// them all. Entering any member's stub therefore compiles the whole
    /// group at once, amortizing the per-module fixed cost (pass-pipeline
    /// setup, instruction selection, linking) that dominates when many small
    /// functions materialize individually.
    pub(crate) fn register_lazy_group(&mut self, symbols: &[String]) -> Result<(), String> {
        if symbols.is_empty() {
            return Ok(());
        }
        let mut provided = Vec::with_capacity(symbols.len());
        for symbol in symbols {
            let request = LazyFunction {
                symbol: symbol.clone(),
                implementation: lazy_implementation_symbol(symbol),
            };
            let impl_name = c_string(&request.implementation)?;
            // SAFETY: this retained entry is consumed by the custom unit below.
            let impl_entry = unsafe { LLVMOrcLLJITMangleAndIntern(self.jit, impl_name.as_ptr()) };
            // Read the linker-mangled spelling before transferring the entry.
            // SAFETY: `impl_entry` is retained and points at a NUL-terminated pool string.
            let linker_name = unsafe {
                CStr::from_ptr(LLVMOrcSymbolStringPoolEntryStr(impl_entry))
                    .to_string_lossy()
                    .into_owned()
            };
            self.state.requests.insert(linker_name, request);
            provided.push(LLVMOrcCSymbolFlagsMapPair {
                Name: impl_entry,
                Flags: callable_flags(),
            });
        }
        let unit_name = c_string(&format!("lazy:{}+{}", symbols[0], symbols.len() - 1))?;
        // SAFETY: the unit takes ownership of every retained entry in
        // `provided`; the callback context points at stable boxed state owned
        // by this JIT.
        let implementation_unit = unsafe {
            LLVMOrcCreateCustomMaterializationUnit(
                unit_name.as_ptr(),
                self.state.as_mut() as *mut MaterializerState as *mut c_void,
                provided.as_mut_ptr(),
                provided.len(),
                ptr::null_mut(),
                materialize_callback,
                discard_callback,
                destroy_callback,
            )
        };
        self.define(implementation_unit)?;

        let mut aliases = Vec::with_capacity(symbols.len());
        for symbol in symbols {
            let public_name = c_string(symbol)?;
            let implementation_name = c_string(&lazy_implementation_symbol(symbol))?;
            // SAFETY: both retained entries are consumed by `LLVMOrcLazyReexports`.
            aliases.push(unsafe {
                LLVMOrcCSymbolAliasMapPair {
                    Name: LLVMOrcLLJITMangleAndIntern(self.jit, public_name.as_ptr()),
                    Entry: LLVMOrcCSymbolAliasMapEntry {
                        Name: LLVMOrcLLJITMangleAndIntern(self.jit, implementation_name.as_ptr()),
                        Flags: callable_flags(),
                    },
                }
            });
        }
        // SAFETY: all managers and the source dylib belong to this live JIT;
        // the unit takes ownership of the retained alias entries.
        let aliases = unsafe {
            LLVMOrcLazyReexports(
                self.call_through,
                self.stubs,
                self.dylib,
                aliases.as_mut_ptr(),
                aliases.len(),
            )
        };
        self.define(aliases)
    }

    pub(crate) fn lookup(&mut self, symbol: &str) -> Result<usize, String> {
        let symbol = c_string(symbol)?;
        let mut address = 0;
        // SAFETY: `symbol` is an unmangled LLVM IR name and `address` is valid
        // output storage for this live JIT.
        unsafe {
            check_error(LLVMOrcLLJITLookup(self.jit, &mut address, symbol.as_ptr()))?;
        }
        self.check_reported_errors()?;
        Ok(address as usize)
    }

    pub(crate) fn with_materializer<R>(
        &mut self,
        materializer: &mut Materializer<'_>,
        body: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let mut materializer = materializer;
        // The guard restores the previous slot even when `body` unwinds, so a
        // panicking run never leaves a pointer to the dead `materializer`
        // borrow installed on the session.
        let _restore = CallbackRestore {
            slot: &mut self.state.callback,
            previous: self.state.callback,
        };
        self.state.callback =
            &mut materializer as *mut &mut Materializer<'_> as *mut c_void as *mut ();
        body(self)
    }

    pub(crate) fn check_reported_errors(&mut self) -> Result<(), String> {
        if self.state.errors.is_empty() {
            Ok(())
        } else {
            // These errors reach the caller, so the fatal mirror no longer
            // needs to replay them.
            if let Ok(mut mirror) = FATAL_ERRORS.lock() {
                mirror.clear();
            }
            Err(std::mem::take(&mut self.state.errors).join("\n"))
        }
    }

    fn define(&mut self, unit: LLVMOrcMaterializationUnitRef) -> Result<(), String> {
        if unit.is_null() {
            return Err("LLVM ORC returned a null materialization unit".to_string());
        }
        // SAFETY: on success the dylib takes ownership; on failure it remains
        // ours and is disposed below.
        let error = unsafe { LLVMOrcJITDylibDefine(self.dylib, unit) };
        if error.is_null() {
            Ok(())
        } else {
            // SAFETY: definition failure leaves the unit with the caller.
            unsafe { LLVMOrcDisposeMaterializationUnit(unit) };
            // SAFETY: `error` is an owned LLVM error.
            Err(unsafe { take_error(error) })
        }
    }
}

fn create_o2_jit() -> Result<LLVMOrcLLJITRef, String> {
    // Construct LLJIT from an O2 target-machine template. This sets native
    // instruction selection independently from the O2 IR transform above.
    unsafe {
        let triple = LLVMGetDefaultTargetTriple();
        let cpu = LLVMGetHostCPUName();
        let features = LLVMGetHostCPUFeatures();
        let mut target = ptr::null_mut();
        let mut target_error = ptr::null_mut();
        if LLVMGetTargetFromTriple(triple, &mut target, &mut target_error) != 0 {
            let error = if target_error.is_null() {
                "failed to resolve native LLVM target".to_string()
            } else {
                let error = CStr::from_ptr(target_error).to_string_lossy().into_owned();
                LLVMDisposeMessage(target_error);
                error
            };
            LLVMDisposeMessage(features);
            LLVMDisposeMessage(cpu);
            LLVMDisposeMessage(triple);
            return Err(error);
        }
        let machine = LLVMCreateTargetMachine(
            target,
            triple,
            cpu,
            features,
            LLVMCodeGenOptLevel::LLVMCodeGenLevelDefault,
            LLVMRelocMode::LLVMRelocDefault,
            LLVMCodeModel::LLVMCodeModelJITDefault,
        );
        LLVMDisposeMessage(features);
        LLVMDisposeMessage(cpu);
        LLVMDisposeMessage(triple);
        if machine.is_null() {
            return Err("failed to create O2 LLVM target machine".to_string());
        }

        // Each constructor consumes its input: the target builder disposes the
        // target machine, then LLJIT construction disposes the LLJIT builder.
        let target_builder = LLVMOrcJITTargetMachineBuilderCreateFromTargetMachine(machine);
        let builder = LLVMOrcCreateLLJITBuilder();
        LLVMOrcLLJITBuilderSetJITTargetMachineBuilder(builder, target_builder);
        let mut jit = ptr::null_mut();
        check_error(LLVMOrcCreateLLJIT(&mut jit, builder))?;
        Ok(jit)
    }
}

impl Drop for OrcJit {
    fn drop(&mut self) {
        // LLVM's C example destroys the call-through helpers before LLJIT, then
        // releases the local thread-safe-context reference after LLJIT has
        // dropped every module that shares it.
        unsafe {
            LLVMOrcDisposeIndirectStubsManager(self.stubs);
            LLVMOrcDisposeLazyCallThroughManager(self.call_through);
            let error = LLVMOrcDisposeLLJIT(self.jit);
            if !error.is_null() {
                self.state.push_error(take_error(error));
            }
            LLVMOrcDisposeThreadSafeContext(self.state.context);
        }
    }
}

/// Restores the materializer-callback slot of a [`MaterializerState`] on drop,
/// so [`OrcJit::with_materializer`] unwinds cleanly.
struct CallbackRestore {
    slot: *mut *mut (),
    previous: *mut (),
}

impl Drop for CallbackRestore {
    fn drop(&mut self) {
        // SAFETY: `slot` points into the boxed `MaterializerState`, which the
        // guard's owner (`with_materializer`) borrows for longer than the
        // guard lives.
        unsafe { *self.slot = self.previous };
    }
}

fn callable_flags() -> LLVMJITSymbolFlags {
    LLVMJITSymbolFlags {
        GenericFlags: LLVMJITSymbolGenericFlags::LLVMJITSymbolGenericFlagsExported as u8
            | LLVMJITSymbolGenericFlags::LLVMJITSymbolGenericFlagsCallable as u8,
        TargetFlags: 0,
    }
}

fn c_string(value: &str) -> Result<CString, String> {
    CString::new(value).map_err(|_| format!("LLVM symbol contains NUL: `{value}`"))
}

unsafe fn check_error(error: LLVMErrorRef) -> Result<(), String> {
    if error.is_null() {
        Ok(())
    } else {
        // SAFETY: the non-null error is owned by the caller.
        Err(unsafe { take_error(error) })
    }
}

unsafe fn take_error(error: LLVMErrorRef) -> String {
    // SAFETY: the caller transfers one live LLVM error. Getting its message
    // consumes the error and returns an owned C string.
    let message = unsafe { LLVMGetErrorMessage(error) };
    if message.is_null() {
        return "unknown LLVM ORC error".to_string();
    }
    // SAFETY: `message` remains valid until disposed immediately below.
    let rendered = unsafe { CStr::from_ptr(message) }
        .to_string_lossy()
        .into_owned();
    // SAFETY: `message` is the allocation returned by LLVMGetErrorMessage.
    unsafe { LLVMDisposeErrorMessage(message) };
    rendered
}

#[cfg(test)]
mod tests {
    use inkwell::context::Context;

    use super::*;

    fn constant_module<'ctx>(context: &'ctx Context, name: &str, value: u64) -> OrcModule {
        let module = context.create_module(name);
        let ty = context.i32_type().fn_type(&[], false);
        let function = module.add_function(name, ty, None);
        let builder = context.create_builder();
        builder.position_at_end(context.append_basic_block(function, "entry"));
        builder
            .build_return(Some(&context.i32_type().const_int(value, false)))
            .unwrap();
        OrcModule::from_inkwell(module)
    }

    /// A lazy alias materializes only the body selected by executed control
    /// flow. Repeated calls use the patched stub without invoking Rust again.
    #[test]
    fn lazy_reexport_materializes_on_first_call() {
        let context = OrcContext::new();
        let mut jit = OrcJit::new(&context).expect("ORC JIT");
        let foo = jit.register_lazy("foo").expect("foo stub");
        jit.register_lazy("bar").expect("bar stub");

        let entry_module = context.context().create_module("entry_module");
        let i32t = context.context().i32_type();
        let callee_ty = i32t.fn_type(&[], false);
        let entry_ty = i32t.fn_type(&[i32t.into()], false);
        let entry = entry_module.add_function("entry", entry_ty, None);
        let foo_decl = entry_module.add_function("foo", callee_ty, None);
        let bar_decl = entry_module.add_function("bar", callee_ty, None);
        let builder = context.context().create_builder();
        let start = context.context().append_basic_block(entry, "start");
        let call_foo = context.context().append_basic_block(entry, "call_foo");
        let call_bar = context.context().append_basic_block(entry, "call_bar");
        builder.position_at_end(start);
        let choose_foo = builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                entry.get_nth_param(0).unwrap().into_int_value(),
                i32t.const_zero(),
                "choose_foo",
            )
            .unwrap();
        builder
            .build_conditional_branch(choose_foo, call_foo, call_bar)
            .unwrap();
        builder.position_at_end(call_foo);
        let foo_value = builder
            .build_call(foo_decl, &[], "foo_value")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap();
        builder.build_return(Some(&foo_value)).unwrap();
        builder.position_at_end(call_bar);
        let bar_value = builder
            .build_call(bar_decl, &[], "bar_value")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap();
        builder.build_return(Some(&bar_value)).unwrap();
        jit.add_eager_module(OrcModule::from_inkwell(entry_module))
            .expect("entry module");

        let mut generated = Vec::new();
        let mut materialize = |request: &LazyFunction| {
            generated.push(request.symbol.clone());
            let value = if request == &foo { 11 } else { 22 };
            Ok(constant_module(
                context.context(),
                &request.implementation,
                value,
            ))
        };
        type Entry = unsafe extern "C" fn(i32) -> i32;
        let result = jit.with_materializer(&mut materialize, |jit| {
            let address = jit.lookup("entry").expect("entry address");
            // SAFETY: `entry` was emitted above with the matching C ABI.
            let entry: Entry = unsafe { std::mem::transmute(address) };
            // SAFETY: the JIT and callback remain installed for every call.
            let first = unsafe { entry(0) };
            let second = unsafe { entry(0) };
            let third = unsafe { entry(1) };
            (first, second, third)
        });

        assert_eq!(result, (22, 22, 11));
        assert_eq!(generated, ["bar", "foo"]);
        jit.check_reported_errors().expect("no asynchronous errors");
    }

    /// A grouped registration keeps one stub per symbol but materializes the
    /// whole group on the first call to any member: the one emitted module
    /// defines every implementation, and a later call to another member finds
    /// its body already linked without invoking Rust again.
    #[test]
    fn lazy_group_materializes_once_for_all_members() {
        let context = OrcContext::new();
        let mut jit = OrcJit::new(&context).expect("ORC JIT");
        jit.register_lazy_group(&["foo".to_string(), "bar".to_string()])
            .expect("group stubs");

        let entry_module = context.context().create_module("entry_module");
        let i32t = context.context().i32_type();
        let callee_ty = i32t.fn_type(&[], false);
        let entry_ty = i32t.fn_type(&[i32t.into()], false);
        let entry = entry_module.add_function("entry", entry_ty, None);
        let foo_decl = entry_module.add_function("foo", callee_ty, None);
        let bar_decl = entry_module.add_function("bar", callee_ty, None);
        let builder = context.context().create_builder();
        let start = context.context().append_basic_block(entry, "start");
        let call_foo = context.context().append_basic_block(entry, "call_foo");
        let call_bar = context.context().append_basic_block(entry, "call_bar");
        builder.position_at_end(start);
        let choose_foo = builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                entry.get_nth_param(0).unwrap().into_int_value(),
                i32t.const_zero(),
                "choose_foo",
            )
            .unwrap();
        builder
            .build_conditional_branch(choose_foo, call_foo, call_bar)
            .unwrap();
        builder.position_at_end(call_foo);
        let foo_value = builder
            .build_call(foo_decl, &[], "foo_value")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap();
        builder.build_return(Some(&foo_value)).unwrap();
        builder.position_at_end(call_bar);
        let bar_value = builder
            .build_call(bar_decl, &[], "bar_value")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap();
        builder.build_return(Some(&bar_value)).unwrap();
        jit.add_eager_module(OrcModule::from_inkwell(entry_module))
            .expect("entry module");

        let mut generated = Vec::new();
        let mut materialize = |request: &LazyFunction| {
            generated.push(request.symbol.clone());
            // One module defining BOTH implementations, whichever was asked.
            let module = context.context().create_module("group");
            let ty = context.context().i32_type().fn_type(&[], false);
            for (name, value) in [("foo", 11u64), ("bar", 22u64)] {
                let function = module.add_function(&lazy_implementation_symbol(name), ty, None);
                let builder = context.context().create_builder();
                builder.position_at_end(context.context().append_basic_block(function, "entry"));
                builder
                    .build_return(Some(&context.context().i32_type().const_int(value, false)))
                    .unwrap();
            }
            Ok(OrcModule::from_inkwell(module))
        };
        type Entry = unsafe extern "C" fn(i32) -> i32;
        let result = jit.with_materializer(&mut materialize, |jit| {
            let address = jit.lookup("entry").expect("entry address");
            // SAFETY: `entry` was emitted above with the matching C ABI.
            let entry: Entry = unsafe { std::mem::transmute(address) };
            // SAFETY: the JIT and callback remain installed for every call.
            let first = unsafe { entry(0) };
            let second = unsafe { entry(1) };
            (first, second)
        });

        assert_eq!(result, (22, 11));
        assert_eq!(generated, ["bar"]);
        jit.check_reported_errors().expect("no asynchronous errors");
    }
}
