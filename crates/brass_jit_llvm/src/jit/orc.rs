//! A small owning wrapper over LLVM ORC's C API.
//!
//! LLVM's C API does not expose `LLLazyJIT`, but it does expose the lower-level
//! pieces it is built from: custom materialization units, lazy reexports, and
//! indirect stubs. This module combines those pieces so Brass can generate one
//! function group only when its call-through stub is entered for the first
//! time. All raw ownership transfer is kept in this module; callers deal in
//! owning [`OrcModule`] values. Pending IR belongs to the session, so runtime
//! registration and materialization never borrow the compiler reentrantly.

use fxhash::FxHashMap as HashMap;
use std::cell::{Cell, RefCell};
use std::ffi::{CStr, CString, c_void};
use std::mem::ManuallyDrop;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::ptr;
use std::rc::Rc;
use std::sync::{Arc, OnceLock};

use super::objcache::{ObjectStore, TargetIdentity};

use inkwell::module::Module;
use inkwell::targets::{InitializationConfig, Target};
use llvm_sys::bit_writer::LLVMWriteBitcodeToMemoryBuffer;
use llvm_sys::core::{
    LLVMCreateMemoryBufferWithMemoryRangeCopy, LLVMDisposeMemoryBuffer, LLVMDisposeMessage,
    LLVMDisposeModule, LLVMGetBufferSize, LLVMGetBufferStart, LLVMSetDataLayout,
};
use llvm_sys::error::{LLVMDisposeErrorMessage, LLVMErrorRef, LLVMGetErrorMessage};
use llvm_sys::orc2::lljit::{
    LLVMOrcCreateLLJIT, LLVMOrcCreateLLJITBuilder, LLVMOrcDisposeLLJIT,
    LLVMOrcLLJITBuilderSetJITTargetMachineBuilder, LLVMOrcLLJITGetDataLayoutStr,
    LLVMOrcLLJITGetExecutionSession, LLVMOrcLLJITGetIRTransformLayer, LLVMOrcLLJITGetMainJITDylib,
    LLVMOrcLLJITGetObjLinkingLayer, LLVMOrcLLJITGetObjTransformLayer, LLVMOrcLLJITGetTripleString,
    LLVMOrcLLJITLookup, LLVMOrcLLJITMangleAndIntern, LLVMOrcLLJITRef,
};
use llvm_sys::orc2::{
    LLVMJITEvaluatedSymbol, LLVMJITSymbolFlags, LLVMJITSymbolGenericFlags, LLVMOrcAbsoluteSymbols,
    LLVMOrcCSymbolAliasMapEntry, LLVMOrcCSymbolAliasMapPair, LLVMOrcCSymbolFlagsMapPair,
    LLVMOrcCSymbolMapPair, LLVMOrcCreateCustomMaterializationUnit,
    LLVMOrcCreateLocalIndirectStubsManager, LLVMOrcCreateLocalLazyCallThroughManager,
    LLVMOrcCreateNewThreadSafeContextFromLLVMContext, LLVMOrcCreateNewThreadSafeModule,
    LLVMOrcDisposeIndirectStubsManager, LLVMOrcDisposeLazyCallThroughManager,
    LLVMOrcDisposeMaterializationResponsibility, LLVMOrcDisposeMaterializationUnit,
    LLVMOrcDisposeSymbols, LLVMOrcDisposeThreadSafeContext,
    LLVMOrcExecutionSessionSetErrorReporter, LLVMOrcIRTransformLayerEmit,
    LLVMOrcIRTransformLayerSetTransform, LLVMOrcIndirectStubsManagerRef, LLVMOrcJITDylibDefine,
    LLVMOrcJITDylibRef, LLVMOrcJITTargetMachineBuilderCreateFromTargetMachine,
    LLVMOrcLazyCallThroughManagerRef, LLVMOrcLazyReexports,
    LLVMOrcMaterializationResponsibilityFailMaterialization,
    LLVMOrcMaterializationResponsibilityGetRequestedSymbols,
    LLVMOrcMaterializationResponsibilityRef, LLVMOrcMaterializationUnitRef, LLVMOrcObjectLayerEmit,
    LLVMOrcObjectTransformLayerSetTransform, LLVMOrcSymbolStringPoolEntryStr,
    LLVMOrcThreadSafeContextRef, LLVMOrcThreadSafeModuleWithModuleDo,
};
use llvm_sys::target_machine::{
    LLVMCodeGenOptLevel, LLVMCodeModel, LLVMCreateTargetMachine, LLVMGetDefaultTargetTriple,
    LLVMGetHostCPUFeatures, LLVMGetHostCPUName, LLVMGetTargetFromTriple, LLVMRelocMode,
};
use llvm_sys::transforms::pass_builder::{
    LLVMCreatePassBuilderOptions, LLVMDisposePassBuilderOptions, LLVMRunPasses,
};

type Materializer<'a> = dyn FnMut(&LazyFunction) -> Result<OrcModule, String> + 'a;

static OPT_TIER: OnceLock<OptTier> = OnceLock::new();

/// The optimization tier shared by LLVM IR passes and native instruction
/// selection. Cold compilation defaults to O0; `BRASS_OPT=2` opts into O2.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OptTier {
    O0,
    O2,
}

impl OptTier {
    /// Returns the process-wide optimization tier selected by `BRASS_OPT`.
    /// The environment is sampled once so every module in a run uses the same
    /// pass pipeline, instruction-selection level, and lazy group sizing.
    pub(crate) fn from_env() -> Self {
        *OPT_TIER.get_or_init(|| match std::env::var("BRASS_OPT") {
            Ok(value) if value == "2" => Self::O2,
            _ => Self::O0,
        })
    }
}

/// The host CPU name and feature string instruction selection targets.
fn target_cpu_identity() -> Option<(String, String)> {
    // SAFETY: LLVM returns independently allocated, NUL-terminated messages;
    // each is copied before being disposed exactly once below.
    unsafe {
        let cpu = LLVMGetHostCPUName();
        let features = LLVMGetHostCPUFeatures();
        if cpu.is_null() || features.is_null() {
            if !cpu.is_null() {
                LLVMDisposeMessage(cpu);
            }
            if !features.is_null() {
                LLVMDisposeMessage(features);
            }
            return None;
        }
        let identity = (
            CStr::from_ptr(cpu).to_string_lossy().into_owned(),
            CStr::from_ptr(features).to_string_lossy().into_owned(),
        );
        LLVMDisposeMessage(cpu);
        LLVMDisposeMessage(features);
        Some(identity)
    }
}

/// Keeps a context alive for both code generation and one ORC session. The
/// shared owner releases it only after the backend and this wrapper are gone.
pub struct OrcContext {
    owner: Rc<ContextOwner>,
    transferred: Cell<bool>,
}

struct ContextOwner {
    context: ManuallyDrop<inkwell::context::Context>,
    thread_safe: LLVMOrcThreadSafeContextRef,
}

impl OrcContext {
    /// Allocate the context used by a single backend and its ORC session.
    /// Keep this wrapper alive until the backend has been dropped.
    pub fn new() -> Self {
        let context = ManuallyDrop::new(inkwell::context::Context::create());
        // SAFETY: the new thread-safe wrapper takes ownership of this context;
        // ContextOwner disposes that wrapper after its last Rust owner drops.
        let thread_safe =
            unsafe { LLVMOrcCreateNewThreadSafeContextFromLLVMContext(context.raw()) };
        Self {
            owner: Rc::new(ContextOwner {
                context,
                thread_safe,
            }),
            transferred: Cell::new(false),
        }
    }

    pub(crate) fn context(&self) -> &inkwell::context::Context {
        &self.owner.context
    }

    fn transfer(&self) -> Result<Rc<ContextOwner>, String> {
        if self.transferred.replace(true) {
            Err("LLVM context was transferred to ORC twice".to_string())
        } else {
            Ok(self.owner.clone())
        }
    }
}

impl Default for OrcContext {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for ContextOwner {
    fn drop(&mut self) {
        // SAFETY: the last Rust owner releases its one thread-safe wrapper.
        // LLVM modules retain their own shared references until disposed.
        unsafe { LLVMOrcDisposeThreadSafeContext(self.thread_safe) };
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
/// to ORC. Modules emitted in the session context transfer without serialization.
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

/// Main-thread state shared by lookup and synchronous LLVM callbacks. Each
/// RefCell borrow ends before an LLVM call that may materialize dependencies.
/// JIT -> pp_resolve -> driver -> ORC lookup can therefore run while the driver
/// owns LlvmCodegen: materialization needs only this independent allocation.
struct MaterializerState {
    jit: LLVMOrcLLJITRef,
    context: LLVMOrcThreadSafeContextRef,
    raw_context: llvm_sys::prelude::LLVMContextRef,
    data_layout: CString,
    requests: RefCell<HashMap<String, (LazyFunction, String)>>,
    pending: RefCell<HashMap<String, OrcModule>>,
    target: TargetIdentity,
    capture: Box<ObjectCapture>,
    callback: Cell<*mut ()>,
    errors: RefCell<Vec<String>>,
}

/// A separate allocation lets LLVM's synchronous transform callbacks access
/// capture state without borrowing the materializer currently emitting IR.
/// Taking the marker at capture time excludes support objects linked later.
struct ObjectCapture {
    store: Option<Arc<ObjectStore>>,
    current: RefCell<Option<(String, String)>>,
    tier: OptTier,
    preoptimized: RefCell<fxhash::FxHashSet<usize>>,
    #[cfg(test)]
    optimized: Cell<usize>,
    #[cfg(test)]
    captured: Cell<usize>,
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
    fn push_error(&self, error: impl Into<String>) {
        let error = error.into();
        if let Ok(mut mirror) = FATAL_ERRORS.lock() {
            mirror.push(error.clone());
        }
        self.errors.borrow_mut().push(error);
    }

    fn transfer_to_thread_safe_module(
        &self,
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

    fn lookup_object(&self, module: &OrcModule, symbol: &str) -> CacheLookup {
        let Some(store) = &self.capture.store else {
            return CacheLookup::Miss(None);
        };
        // SAFETY: Rust still owns this module. Bitcode is copied into hashes
        // before the independent serialization buffer is disposed. The layout
        // matches the one used when transferring a miss to the IR layer.
        let (optimized_key, session_key) = unsafe {
            let raw = module.raw.expect("live ORC module");
            LLVMSetDataLayout(raw, self.data_layout.as_ptr());
            let buffer = LLVMWriteBitcodeToMemoryBuffer(raw);
            if buffer.is_null() {
                tracing::debug!(target: "brass::perf", symbol, "jit cache bitcode unavailable");
                return CacheLookup::Miss(None);
            }
            let bitcode = std::slice::from_raw_parts(
                LLVMGetBufferStart(buffer).cast(),
                LLVMGetBufferSize(buffer),
            );
            let optimized = store.key(&self.target, OptTier::O2, bitcode);
            let session = match self.capture.tier {
                OptTier::O0 => store.key(&self.target, OptTier::O0, bitcode),
                OptTier::O2 => optimized.clone(),
            };
            LLVMDisposeMemoryBuffer(buffer);
            (optimized, session)
        };
        let object = store.load(&optimized_key, symbol).or_else(|| {
            (self.capture.tier != OptTier::O2)
                .then(|| store.load(&session_key, symbol))
                .flatten()
        });
        if let Some(object) = object {
            CacheLookup::Hit(object)
        } else {
            CacheLookup::Miss(Some(session_key))
        }
    }

    fn materialize(&self, responsibility: LLVMOrcMaterializationResponsibilityRef) {
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
                .borrow()
                .get(&name)
                .cloned()
                .ok_or_else(|| format!("unregistered lazy implementation `{name}`"));
            request.and_then(|(request, first_symbol)| {
                tracing::trace!(target: "brass::perf", symbol = %request.symbol,
                    "back/orc-materialize");
                // Release the queue borrow before emission can re-enter ORC.
                let pending = self.pending.borrow_mut().remove(&first_symbol);
                if let Some(module) = pending {
                    return Ok((module, first_symbol));
                }
                if self.callback.get().is_null() {
                    return Err(format!(
                        "lazy module for `{}` is unavailable",
                        request.symbol
                    ));
                }
                // SAFETY: the test-only callback is scoped by with_materializer;
                // production materialization exclusively consumes pending modules.
                let callback =
                    unsafe { &mut *(self.callback.get() as *mut &mut Materializer<'static>) };
                callback(&request).map(|module| (module, first_symbol))
            })
        };
        // SAFETY: ownership of the requested-symbol array belongs to this
        // callback and must be released exactly once.
        unsafe { LLVMOrcDisposeSymbols(symbols) };

        match result {
            Ok((module, symbol)) => {
                let key = match self.lookup_object(&module, &symbol) {
                    CacheLookup::Hit(object) => {
                        // The object replaces the whole group, so its IR can
                        // be dropped before linking begins.
                        drop(module);
                        // SAFETY: the buffer copies the validated object.
                        // ObjectLayerEmit owns buffer and responsibility. The
                        // linking layer bypasses capture on cache hits.
                        unsafe {
                            let buffer = LLVMCreateMemoryBufferWithMemoryRangeCopy(
                                object.as_ptr().cast(),
                                object.len(),
                                c"cached-object".as_ptr(),
                            );
                            LLVMOrcObjectLayerEmit(
                                LLVMOrcLLJITGetObjLinkingLayer(self.jit),
                                responsibility,
                                buffer,
                            );
                        }
                        return;
                    }
                    CacheLookup::Miss(key) => key,
                };
                *self.capture.current.borrow_mut() = key.map(|key| (key, symbol));
                let module = self.transfer_to_thread_safe_module(module);
                // SAFETY: ORC takes ownership of both the responsibility and
                // module when the transform layer is asked to emit them.
                unsafe {
                    let layer = LLVMOrcLLJITGetIRTransformLayer(self.jit);
                    LLVMOrcIRTransformLayerEmit(layer, responsibility, module);
                }
                // Emission is synchronous. A failed compilation may not have
                // reached the object transform, so clear its marker as well.
                self.capture.current.borrow_mut().take();
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

enum CacheLookup {
    Hit(Vec<u8>),
    Miss(Option<String>),
}

extern "C" fn capture_object(
    context: *mut c_void,
    buffer: *mut llvm_sys::prelude::LLVMMemoryBufferRef,
) -> LLVMErrorRef {
    // C callbacks cannot unwind. A cache failure must leave LLVM's original
    // buffer untouched so native emission continues normally.
    let _ = catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: the boxed capture state lives until LLJIT is disposed; LLVM
        // owns the live buffer throughout this synchronous callback.
        let capture = unsafe { &*(context as *const ObjectCapture) };
        let current = capture.current.borrow_mut().take();
        if let (Some(store), Some((key, symbol))) = (&capture.store, current) {
            let bytes = unsafe {
                std::slice::from_raw_parts(
                    LLVMGetBufferStart(*buffer).cast(),
                    LLVMGetBufferSize(*buffer),
                )
            };
            let object = bytes.to_vec();
            #[cfg(test)]
            capture.captured.set(capture.captured.get() + 1);
            store.publish(&key, &symbol, &object);
        }
    }));
    ptr::null_mut()
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
        unsafe { (&*(context as *const MaterializerState)).materialize(responsibility) };
    }));
    if result.is_err() {
        // SAFETY: same state and responsibility invariants as above. The panic
        // happened before the callback completed, so fail the responsibility.
        unsafe {
            let state = &*(context as *const MaterializerState);
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
        let state = &*(context as *const MaterializerState);
        state.push_error(take_error(error));
    }
}

extern "C" fn optimize_transform(
    context: *mut c_void,
    module: *mut llvm_sys::orc2::LLVMOrcThreadSafeModuleRef,
    _responsibility: LLVMOrcMaterializationResponsibilityRef,
) -> LLVMErrorRef {
    // SAFETY: ORC supplies a live ThreadSafeModule slot. The nested callback
    // runs under that module's context lock.
    unsafe { LLVMOrcThreadSafeModuleWithModuleDo(*module, optimize_module, context) }
}

extern "C" fn optimize_module(
    context: *mut c_void,
    module: llvm_sys::prelude::LLVMModuleRef,
) -> LLVMErrorRef {
    // SAFETY: both transforms share the session's stable capture allocation.
    let capture = unsafe { &*(context as *const ObjectCapture) };
    if capture.preoptimized.borrow_mut().remove(&(module as usize)) {
        return ptr::null_mut();
    }
    #[cfg(test)]
    capture.optimized.set(capture.optimized.get() + 1);
    let pipeline: &[u8] = match capture.tier {
        OptTier::O0 => b"default<O0>\0",
        OptTier::O2 => b"default<O2>\0",
    };
    // SAFETY: `module` is locked by `LLVMOrcThreadSafeModuleWithModuleDo`.
    // Target-independent default pipelines accept a null target machine;
    // native code generation subsequently uses the matching tier configured
    // for LLJIT.
    unsafe {
        let options = LLVMCreatePassBuilderOptions();
        let error = LLVMRunPasses(module, pipeline.as_ptr().cast(), ptr::null_mut(), options);
        LLVMDisposePassBuilderOptions(options);
        error
    }
}

/// A single-threaded ORC session supporting per-function lazy materialization.
///
/// The supplied [`OrcContext`] is shared with ORC. The JIT releases its reference
/// after all pending modules have been destroyed.
pub(crate) struct OrcJit {
    jit: LLVMOrcLLJITRef,
    dylib: LLVMOrcJITDylibRef,
    stubs: LLVMOrcIndirectStubsManagerRef,
    call_through: LLVMOrcLazyCallThroughManagerRef,
    state: Box<MaterializerState>,
    _context: Rc<ContextOwner>,
}

/// Owns the helpers created before an [`OrcJit`] has all of its required
/// resources. Releasing it transfers the complete set to the finished session.
struct OrcConstruction {
    jit: LLVMOrcLLJITRef,
    stubs: LLVMOrcIndirectStubsManagerRef,
    call_through: LLVMOrcLazyCallThroughManagerRef,
}

impl OrcConstruction {
    fn release(
        mut self,
    ) -> (
        LLVMOrcLLJITRef,
        LLVMOrcIndirectStubsManagerRef,
        LLVMOrcLazyCallThroughManagerRef,
    ) {
        let helpers = (self.jit, self.stubs, self.call_through);
        self.jit = ptr::null_mut();
        self.stubs = ptr::null_mut();
        self.call_through = ptr::null_mut();
        helpers
    }
}

impl Drop for OrcConstruction {
    fn drop(&mut self) {
        // SAFETY: every non-null handle is still owned by this construction.
        unsafe {
            if !self.stubs.is_null() {
                LLVMOrcDisposeIndirectStubsManager(self.stubs);
            }
            if !self.call_through.is_null() {
                LLVMOrcDisposeLazyCallThroughManager(self.call_through);
            }
            if !self.jit.is_null() {
                let _ = LLVMOrcDisposeLLJIT(self.jit);
            }
        }
    }
}

impl OrcJit {
    /// Creates an ORC session with process-wide cache configuration and tier.
    /// The store is independent of the caller's checking or IR preparation path.
    #[cfg(test)]
    pub(crate) fn new(context: &OrcContext) -> Result<Self, String> {
        Self::with_cache(context, ObjectStore::from_env(), OptTier::from_env())
    }

    pub(crate) fn with_cache(
        context: &OrcContext,
        store: Option<Arc<ObjectStore>>,
        tier: OptTier,
    ) -> Result<Self, String> {
        Target::initialize_native(&InitializationConfig::default())
            .map_err(|error| format!("failed to initialize native LLVM target: {error}"))?;

        let (cpu, features) = target_cpu_identity()
            .ok_or_else(|| "failed to read LLVM target CPU identity".to_string())?;
        tracing::debug!(target: "brass::perf", ?tier, "JIT session tier");
        let jit = create_jit(tier, &cpu, &features)?;
        let mut construction = OrcConstruction {
            jit,
            stubs: ptr::null_mut(),
            call_through: ptr::null_mut(),
        };
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
        construction.stubs = unsafe { LLVMOrcCreateLocalIndirectStubsManager(triple.as_ptr()) };
        if construction.stubs.is_null() {
            return Err("failed to create ORC indirect stubs manager".to_string());
        }
        // SAFETY: all arguments belong to the same live ORC execution session.
        // A stub whose materialization fails branches to the error-handler
        // address in place of its body, so the handler must never return.
        let call_through_result = unsafe {
            check_error(LLVMOrcCreateLocalLazyCallThroughManager(
                triple.as_ptr(),
                execution_session,
                materialization_failed as *const () as u64,
                &mut construction.call_through,
            ))
        };
        call_through_result?;

        let context = context.transfer()?;
        let raw_context = context.context.raw();
        let thread_safe_context = context.thread_safe;
        let state = Box::new(MaterializerState {
            jit,
            context: thread_safe_context,
            raw_context,
            data_layout,
            requests: RefCell::default(),
            pending: RefCell::default(),
            target: TargetIdentity {
                triple: triple.to_string_lossy().into_owned(),
                cpu,
                features,
            },
            capture: Box::new(ObjectCapture {
                store,
                current: RefCell::new(None),
                tier,
                preoptimized: RefCell::default(),
                #[cfg(test)]
                optimized: Cell::new(0),
                #[cfg(test)]
                captured: Cell::new(0),
            }),
            callback: Cell::new(ptr::null_mut()),
            errors: RefCell::default(),
        });
        // SAFETY: `state` is boxed and remains at this address until after the
        // execution session is disposed in `Drop`.
        unsafe {
            LLVMOrcExecutionSessionSetErrorReporter(
                execution_session,
                error_reporter,
                state.as_ref() as *const MaterializerState as *mut c_void,
            );
            LLVMOrcIRTransformLayerSetTransform(
                LLVMOrcLLJITGetIRTransformLayer(jit),
                optimize_transform,
                state.capture.as_ref() as *const ObjectCapture as *mut c_void,
            );
            LLVMOrcObjectTransformLayerSetTransform(
                LLVMOrcLLJITGetObjTransformLayer(jit),
                capture_object,
                state.capture.as_ref() as *const ObjectCapture as *mut c_void,
            );
        }

        let (jit, stubs, call_through) = construction.release();
        Ok(Self {
            jit,
            dylib,
            stubs,
            call_through,
            state,
            _context: context,
        })
    }

    /// Copy IR into the session-owned context. Codegen may keep borrowing its
    /// original context and module after finalization; ORC owns this copy alone.
    pub(crate) fn copy_module(&self, module: &Module<'_>) -> Result<OrcModule, String> {
        let mut raw = ptr::null_mut();
        // SAFETY: both contexts and the serialization buffer are live. Parsing
        // creates a fresh module owned by OrcModule in the session's context.
        unsafe {
            let context = self.state.raw_context;
            let copied = LLVMWriteBitcodeToMemoryBuffer(module.as_mut_ptr());
            let failed =
                llvm_sys::bit_reader::LLVMParseBitcodeInContext2(context, copied, &mut raw);
            LLVMDisposeMemoryBuffer(copied);
            if failed != 0 {
                return Err("failed to import JIT bitcode".into());
            }
        }
        Ok(OrcModule { raw: Some(raw) })
    }

    /// Transfer a session-context module directly. EngineCodegen callers with
    /// an independent context instead import a copy before dropping the original.
    pub(crate) fn own_module(&self, module: Module<'_>) -> Result<OrcModule, String> {
        // SAFETY: the owned module is live and its context is compared only for
        // identity with the context retained by this session.
        if unsafe { llvm_sys::core::LLVMGetModuleContext(module.as_mut_ptr()) }
            == self.state.raw_context
        {
            Ok(OrcModule::from_inkwell(module))
        } else {
            self.copy_module(&module)
        }
    }

    /// Register helper definitions themselves, without call-through aliases.
    /// Their unit uses the same pending queue, content key, and materialization
    /// path as groups. Linking a group may synchronously materialize this unit;
    /// the group's capture marker has already been taken by its own object.
    pub(crate) fn add_helpers(&self, symbols: &[String], module: OrcModule) -> Result<(), String> {
        let first = symbols.first().ok_or("empty helper module")?;
        self.state
            .pending
            .borrow_mut()
            .insert(first.clone(), module);
        self.register_implementations(symbols, false)
    }

    /// Own a prepared group before registering its stubs. The materializer only
    /// accesses this session's state, never the compiler or driver resolver.
    pub(crate) fn add_lazy_group(
        &self,
        symbols: &[String],
        module: OrcModule,
    ) -> Result<(), String> {
        let first = symbols.first().ok_or("empty lazy group")?;
        self.state
            .pending
            .borrow_mut()
            .insert(first.clone(), module);
        self.register_lazy_group(symbols)
    }

    pub(crate) fn tier(&self) -> OptTier {
        self.state.capture.tier
    }

    /// Whole-module EngineCodegen already ran its established IR passes. Skip
    /// the transform once for this copy while retaining O2 instruction selection.
    pub(crate) fn add_optimized_module(&self, module: OrcModule) -> Result<(), String> {
        self.state
            .capture
            .preoptimized
            .borrow_mut()
            .insert(module.raw.expect("live ORC module") as usize);
        self.add_eager_module(module)
    }

    pub(crate) fn add_eager_module(&self, module: OrcModule) -> Result<(), String> {
        let thread_safe = self.state.transfer_to_thread_safe_module(module);
        // SAFETY: the module and dylib belong to this JIT. LLJIT consumes the
        // thread-safe module on every return path.
        let result = unsafe {
            llvm_sys::orc2::lljit::LLVMOrcLLJITAddLLVMIRModule(self.jit, self.dylib, thread_safe)
        };
        if result.is_null() {
            Ok(())
        } else {
            // SAFETY: `result` is an owned LLVM error.
            Err(unsafe { take_error(result) })
        }
    }

    pub(crate) fn define_absolute(
        &self,
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
    pub(crate) fn register_lazy(&self, symbol: &str) -> Result<LazyFunction, String> {
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
    pub(crate) fn register_lazy_group(&self, symbols: &[String]) -> Result<(), String> {
        if symbols.is_empty() {
            return Ok(());
        }
        self.register_implementations(symbols, true)?;

        self.register_aliases(symbols)
    }

    /// Claim either hidden group implementations or directly callable helpers.
    /// The input order fixes the unit's identity and the pending-module key.
    fn register_implementations(&self, symbols: &[String], lazy: bool) -> Result<(), String> {
        let mut provided = Vec::with_capacity(symbols.len());
        for symbol in symbols {
            let request = LazyFunction {
                symbol: symbol.clone(),
                implementation: if lazy {
                    lazy_implementation_symbol(symbol)
                } else {
                    symbol.clone()
                },
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
            self.state
                .requests
                .borrow_mut()
                .insert(linker_name, (request, symbols[0].clone()));
            provided.push(LLVMOrcCSymbolFlagsMapPair {
                Name: impl_entry,
                Flags: callable_flags(),
            });
        }
        let kind = if lazy { "lazy" } else { "helpers" };
        let unit_name = c_string(&format!("{kind}:{}+{}", symbols[0], symbols.len() - 1))?;
        // SAFETY: the unit takes ownership of every retained entry in
        // `provided`; the callback context points at stable boxed state owned
        // by this JIT.
        let implementation_unit = unsafe {
            LLVMOrcCreateCustomMaterializationUnit(
                unit_name.as_ptr(),
                self.state.as_ref() as *const MaterializerState as *mut c_void,
                provided.as_mut_ptr(),
                provided.len(),
                ptr::null_mut(),
                materialize_callback,
                discard_callback,
                destroy_callback,
            )
        };
        self.define(implementation_unit)
    }

    fn register_aliases(&self, symbols: &[String]) -> Result<(), String> {
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

    pub(crate) fn lookup(&self, symbol: &str) -> Result<usize, String> {
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

    #[cfg(test)]
    pub(crate) fn with_materializer<R>(
        &self,
        materializer: &mut Materializer<'_>,
        body: impl FnOnce(&Self) -> R,
    ) -> R {
        let mut materializer = materializer;
        // The guard restores the previous slot even when `body` unwinds, so a
        // panicking run never leaves a pointer to the dead `materializer`
        // borrow installed on the session.
        let _restore = CallbackRestore {
            slot: &self.state.callback,
            previous: self.state.callback.get(),
        };
        self.state
            .callback
            .set(&mut materializer as *mut &mut Materializer<'_> as *mut c_void as *mut ());
        body(self)
    }

    pub(crate) fn check_reported_errors(&self) -> Result<(), String> {
        if self.state.errors.borrow().is_empty() {
            Ok(())
        } else {
            // These errors reach the caller, so the fatal mirror no longer
            // needs to replay them.
            if let Ok(mut mirror) = FATAL_ERRORS.lock() {
                mirror.clear();
            }
            Err(std::mem::take(&mut *self.state.errors.borrow_mut()).join("\n"))
        }
    }

    fn define(&self, unit: LLVMOrcMaterializationUnitRef) -> Result<(), String> {
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

/// Configures LLJIT's target machine for the selected optimization tier.
fn create_jit(tier: OptTier, cpu: &str, features: &str) -> Result<LLVMOrcLLJITRef, String> {
    let cpu = c_string(cpu)?;
    let features = c_string(features)?;
    // SAFETY: LLVM owns each returned handle until explicitly transferred or
    // disposed below; the builder consumes its target machine and configuration.
    unsafe {
        let triple = LLVMGetDefaultTargetTriple();
        if triple.is_null() {
            return Err("failed to read LLVM target triple".to_string());
        }
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
            LLVMDisposeMessage(triple);
            return Err(error);
        }
        let codegen_level = match tier {
            OptTier::O0 => LLVMCodeGenOptLevel::LLVMCodeGenLevelNone,
            OptTier::O2 => LLVMCodeGenOptLevel::LLVMCodeGenLevelDefault,
        };
        let machine = LLVMCreateTargetMachine(
            target,
            triple,
            cpu.as_ptr(),
            features.as_ptr(),
            codegen_level,
            LLVMRelocMode::LLVMRelocPIC,
            LLVMCodeModel::LLVMCodeModelJITDefault,
        );
        LLVMDisposeMessage(triple);
        if machine.is_null() {
            return Err("failed to create LLVM target machine".to_string());
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
        self.state.pending.get_mut().clear();
        // LLVM's C example destroys the call-through helpers before LLJIT, then
        // releases the local thread-safe-context reference after LLJIT has
        // dropped every module that shares it.
        // SAFETY: these handles are owned solely by this session. Pending Rust
        // modules were dropped above before releasing their context.
        unsafe {
            LLVMOrcDisposeIndirectStubsManager(self.stubs);
            LLVMOrcDisposeLazyCallThroughManager(self.call_through);
            let error = LLVMOrcDisposeLLJIT(self.jit);
            if !error.is_null() {
                self.state.push_error(take_error(error));
            }
        }
    }
}

/// Restores the materializer-callback slot of a [`MaterializerState`] on drop,
/// so [`OrcJit::with_materializer`] unwinds cleanly.
#[cfg(test)]
struct CallbackRestore<'a> {
    slot: &'a Cell<*mut ()>,
    previous: *mut (),
}

#[cfg(test)]
impl Drop for CallbackRestore<'_> {
    fn drop(&mut self) {
        self.slot.set(self.previous);
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

    fn run_cached_group(store: Arc<ObjectStore>, tier: OptTier) -> (i32, usize, usize) {
        let context = OrcContext::new();
        let jit = OrcJit::with_cache(&context, Some(store), tier).unwrap();
        jit.register_lazy_group(&["foo".into(), "bar".into()])
            .unwrap();
        // The eager support module must never acquire the lazy group's marker.
        jit.add_eager_module(constant_module(context.context(), "support", 7))
            .unwrap();
        jit.lookup("support").unwrap();
        let before = jit.state.capture.optimized.get();
        let mut materialize = |_: &LazyFunction| {
            let module = context.context().create_module("cached-group");
            let ty = context.context().i32_type().fn_type(&[], false);
            for (name, value) in [("foo", 11), ("bar", 22)] {
                let function = module.add_function(&lazy_implementation_symbol(name), ty, None);
                let builder = context.context().create_builder();
                builder.position_at_end(context.context().append_basic_block(function, "entry"));
                builder
                    .build_return(Some(&context.context().i32_type().const_int(value, false)))
                    .unwrap();
            }
            Ok(OrcModule::from_inkwell(module))
        };
        let result = jit.with_materializer(&mut materialize, |jit| {
            // SAFETY: these functions were emitted with the matching C ABI.
            let foo: unsafe extern "C" fn() -> i32 =
                unsafe { std::mem::transmute(jit.lookup("foo").unwrap()) };
            let bar: unsafe extern "C" fn() -> i32 =
                unsafe { std::mem::transmute(jit.lookup("bar").unwrap()) };
            unsafe { foo() + bar() }
        });
        jit.check_reported_errors().unwrap();
        assert!(jit.state.capture.current.borrow().is_none());
        (
            result,
            jit.state.capture.optimized.get() - before,
            jit.state.capture.captured.get(),
        )
    }

    /// A fresh session links a whole cached group without optimization or
    /// instruction selection; corrupt payloads are removed and recompiled.
    #[test]
    fn native_group_cache_reuses_and_repairs_objects() {
        let directory = super::super::objcache::TestDirectory::new();
        let store = ObjectStore::isolated(directory.0.clone(), u64::MAX);
        assert_eq!(run_cached_group(store.clone(), OptTier::O0), (33, 1, 1));
        assert_eq!(run_cached_group(store.clone(), OptTier::O0), (33, 0, 0));
        let paths: Vec<_> = std::fs::read_dir(&directory.0)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect();
        assert_eq!(paths.len(), 1, "only the lazy group is captured");
        let path = &paths[0];
        let good = std::fs::read(path).unwrap();
        let mut corrupt = good.clone();
        *corrupt.last_mut().unwrap() ^= 1;
        std::fs::write(path, corrupt).unwrap();
        let key = path.file_stem().unwrap().to_str().unwrap();
        assert!(store.load(key, "foo").is_none());
        assert!(!path.exists());
        assert_eq!(run_cached_group(store.clone(), OptTier::O0), (33, 1, 1));
        assert_eq!(std::fs::read(path).unwrap(), good);
        assert_eq!(run_cached_group(store, OptTier::O0), (33, 0, 0));
    }

    /// Runs a lazy group whose body calls `support`, a function defined by an
    /// eager module that has not been materialized yet, so linking the group's
    /// object materializes the support module reentrantly. Returns the result
    /// and how many objects this session captured.
    fn run_group_with_reentrant_support(
        store: Arc<ObjectStore>,
        helper: Option<u64>,
    ) -> (i32, usize) {
        let context = OrcContext::new();
        let jit = OrcJit::with_cache(&context, Some(store), OptTier::O0).unwrap();
        jit.register_lazy_group(&["caller".into()]).unwrap();
        if let Some(value) = helper {
            jit.add_helpers(
                &["support".into()],
                constant_module(context.context(), "support", value),
            )
            .unwrap();
        } else {
            jit.add_eager_module(constant_module(context.context(), "support", 7))
                .unwrap();
        }
        let mut materialize = |request: &LazyFunction| {
            let ctx = context.context();
            let module = ctx.create_module("reentrant-group");
            let ty = ctx.i32_type().fn_type(&[], false);
            let support = module.add_function("support", ty, None);
            let caller = module.add_function(&request.implementation, ty, None);
            let builder = ctx.create_builder();
            builder.position_at_end(ctx.append_basic_block(caller, "entry"));
            let value = builder
                .build_call(support, &[], "support")
                .unwrap()
                .try_as_basic_value()
                .unwrap_basic()
                .into_int_value();
            let sum = builder
                .build_int_add(value, ctx.i32_type().const_int(30, false), "sum")
                .unwrap();
            builder.build_return(Some(&sum)).unwrap();
            Ok(OrcModule::from_inkwell(module))
        };
        let result = jit.with_materializer(&mut materialize, |jit| {
            // SAFETY: `caller` was emitted with this exact C ABI.
            let caller: unsafe extern "C" fn() -> i32 =
                unsafe { std::mem::transmute(jit.lookup("caller").unwrap()) };
            unsafe { caller() }
        });
        jit.check_reported_errors().unwrap();
        (result, jit.state.capture.captured.get())
    }

    /// The capture marker belongs to the group's own object: a module that is
    /// first compiled while the group's object is being linked must not be
    /// stored under the group's key. A second session therefore links the
    /// cached group object and still resolves `support` from its own module.
    #[test]
    fn native_group_cache_ignores_reentrant_dependency_objects() {
        let directory = super::super::objcache::TestDirectory::new();
        let store = ObjectStore::isolated(directory.0.clone(), u64::MAX);
        assert_eq!(
            run_group_with_reentrant_support(store.clone(), None),
            (37, 1)
        );
        assert_eq!(std::fs::read_dir(&directory.0).unwrap().count(), 1);
        assert_eq!(run_group_with_reentrant_support(store, None), (37, 0));
        assert_eq!(std::fs::read_dir(&directory.0).unwrap().count(), 1);
    }

    /// A direct helper materializes while its caller's object links, and both
    /// objects get their own keys. Changing only helper bitcode must reuse the
    /// caller while replacing the helper, including when the caller is a hit.
    #[test]
    fn direct_helpers_cache_their_own_bitcode_during_reentrant_linking() {
        let directory = super::super::objcache::TestDirectory::new();
        let store = ObjectStore::isolated(directory.0.clone(), u64::MAX);
        assert_eq!(
            run_group_with_reentrant_support(store.clone(), Some(7)),
            (37, 2)
        );
        assert_eq!(
            run_group_with_reentrant_support(store.clone(), Some(7)),
            (37, 0)
        );
        assert_eq!(
            run_group_with_reentrant_support(store.clone(), Some(8)),
            (38, 1)
        );
        assert_eq!(run_group_with_reentrant_support(store, Some(8)), (38, 0));
        assert_eq!(std::fs::read_dir(&directory.0).unwrap().count(), 3);
    }

    /// O2 sessions never use O0 objects; O0 sessions prefer O2 even when an O0
    /// entry exists (the unused O0 file's mtime is left untouched).
    #[test]
    fn native_group_cache_prefers_o2() {
        let directory = super::super::objcache::TestDirectory::new();
        let store = ObjectStore::isolated(directory.0.clone(), u64::MAX);
        assert_eq!(run_cached_group(store.clone(), OptTier::O0), (33, 1, 1));
        let o0 = std::fs::read_dir(&directory.0)
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
            .path();
        assert_eq!(run_cached_group(store.clone(), OptTier::O2), (33, 1, 1));
        assert_eq!(run_cached_group(store.clone(), OptTier::O2), (33, 0, 0));
        std::fs::File::open(&o0)
            .unwrap()
            .set_modified(std::time::UNIX_EPOCH)
            .unwrap();
        assert_eq!(run_cached_group(store, OptTier::O0), (33, 0, 0));
        assert_eq!(
            std::fs::metadata(o0).unwrap().modified().unwrap(),
            std::time::UNIX_EPOCH
        );
    }

    /// A lazy alias materializes only the body selected by executed control
    /// flow. Repeated calls use the patched stub without invoking Rust again.
    #[test]
    fn lazy_reexport_materializes_on_first_call() {
        let context = OrcContext::new();
        let jit = OrcJit::new(&context).expect("ORC JIT");
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
        let jit = OrcJit::new(&context).expect("ORC JIT");
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

    /// Typed ABI arithmetic remains callable through ORC with unboxed i32
    /// arguments, including signed values.
    #[test]
    fn typed_int32_function_jits_and_runs() {
        let context = OrcContext::new();
        let ctx = context.context();
        let module = ctx.create_module("typed_add");
        let abi = crate::layout::Abi::new(ctx);
        let i32t = brass_hir::Type::Int(brass_hir::IntKind::I32);
        let f = module.add_function(
            "add_i32",
            abi.typed_fn_type(&[i32t.clone(), i32t.clone()], &i32t),
            None,
        );
        let builder = ctx.create_builder();
        builder.position_at_end(ctx.append_basic_block(f, "entry"));
        let sum = builder
            .build_int_add(
                f.get_nth_param(0).unwrap().into_int_value(),
                f.get_nth_param(1).unwrap().into_int_value(),
                "sum",
            )
            .unwrap();
        builder.build_return(Some(&sum)).unwrap();
        let jit = OrcJit::new(&context).expect("ORC JIT");
        jit.add_eager_module(OrcModule::from_inkwell(module))
            .expect("add module");
        // SAFETY: the function above has precisely the i32(i32, i32) C ABI.
        let add: extern "C" fn(i32, i32) -> i32 =
            unsafe { std::mem::transmute(jit.lookup("add_i32").unwrap()) };
        assert_eq!(add(2, 3), 5);
        assert_eq!(add(-1, 41), 40);
    }

    /// A session accepts a pending group after native startup code has already
    /// executed. Looking up its implementation immediately consumes that group.
    #[test]
    fn session_runs_a_group_registered_after_startup() {
        let context = OrcContext::new();
        let jit = OrcJit::new(&context).expect("ORC JIT");
        jit.add_eager_module(constant_module(context.context(), "seed", 7))
            .unwrap();
        // SAFETY: constant_module emits the i32() C ABI and jit remains live.
        let seed: extern "C" fn() -> i32 =
            unsafe { std::mem::transmute(jit.lookup("seed").unwrap()) };
        assert_eq!(seed(), 7);
        let body = lazy_implementation_symbol("answer");
        jit.add_lazy_group(
            &["answer".into()],
            constant_module(context.context(), &body, 42),
        )
        .unwrap();
        // SAFETY: the newly registered body also has the i32() C ABI.
        let answer: extern "C" fn() -> i32 =
            unsafe { std::mem::transmute(jit.lookup(&body).unwrap()) };
        assert!(jit.state.pending.borrow().is_empty());
        assert_eq!(answer(), 42);
        assert_eq!(seed(), 7);
    }

    /// A rejected second context transfer leaves the first ORC session usable.
    #[test]
    fn repeated_context_transfer_is_rejected_cleanly() {
        let context = OrcContext::new();
        let jit = OrcJit::new(&context).expect("first ORC JIT");
        assert!(OrcJit::new(&context).is_err());

        let module = constant_module(context.context(), "answer", 42);
        jit.add_eager_module(module).expect("answer module");
        let address = jit.lookup("answer").expect("answer address");
        // SAFETY: the generated constant function has this exact ABI.
        let answer: unsafe extern "C" fn() -> i32 = unsafe { std::mem::transmute(address) };
        assert_eq!(unsafe { answer() }, 42);
    }
}
