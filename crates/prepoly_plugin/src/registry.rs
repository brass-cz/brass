//! The function registry a plugin fills in [`crate::PrepolyLib::entry`].

use crate::value::{FromValue, IntoOutcome, Value, ValueType};

type Adapter = Box<dyn Fn(Vec<Value>) -> Result<Value, String> + Send + Sync>;

/// One function a plugin exposes: the metadata Prepoly's front end reads
/// (name, doc, signature) plus the callable adapter. Built by
/// [`crate::export!`] (which captures the Rust doc comment and parameter
/// names) or by [`Registry::function`] for undocumented closures.
pub struct FunctionDecl {
    pub(crate) name: String,
    pub(crate) doc: Option<String>,
    pub(crate) param_names: Vec<String>,
    pub(crate) param_types: Vec<ValueType>,
    pub(crate) ret: ValueType,
    pub(crate) fallible: bool,
    pub(crate) adapter: Adapter,
}

impl FunctionDecl {
    /// Assemble a declaration from its parts. Plugin authors normally go
    /// through [`crate::export!`]; this is the escape hatch behind it.
    pub fn new<A, F: PluginFn<A>>(name: &str, doc: Option<String>, f: F) -> FunctionDecl {
        let (param_types, ret, fallible) = F::signature();
        let param_names = (0..param_types.len()).map(|i| format!("a{i}")).collect();
        FunctionDecl {
            name: name.to_string(),
            doc,
            param_names,
            param_types,
            ret,
            fallible,
            adapter: f.into_adapter(),
        }
    }

    /// Replace the auto-generated `a0, a1, ...` parameter names (editor
    /// tooling shows these). Extra names are ignored; missing ones keep the
    /// generated name.
    pub fn with_param_names(mut self, names: &[&str]) -> FunctionDecl {
        for (slot, name) in self.param_names.iter_mut().zip(names) {
            *slot = (*name).to_string();
        }
        self
    }

    /// The signature encoding of [`crate::raw::RawFunction::sig`].
    pub(crate) fn sig_string(&self) -> String {
        let mut s = String::new();
        for t in &self.param_types {
            t.write_code(&mut s);
        }
        s.push(':');
        self.ret.write_code(&mut s);
        if self.fallible {
            s.push('!');
        }
        s
    }
}

/// Collects the functions a library exposes. Passed to
/// [`crate::PrepolyLib::entry`]; anything registered becomes importable from
/// Prepoly under the name it was registered with (a leading `_` keeps a
/// function private to editor tooling and imports, matching Prepoly's
/// convention).
#[derive(Default)]
pub struct Registry {
    pub(crate) decls: Vec<FunctionDecl>,
}

impl Registry {
    pub fn new() -> Registry {
        Registry::default()
    }

    /// Register a declaration built by [`crate::export!`]/[`crate::decl!`]
    /// (doc comment and parameter names included).
    pub fn export(&mut self, decl: FunctionDecl) -> &mut Self {
        self.decls.push(decl);
        self
    }

    /// Register a bare function or closure under `name`, without a doc
    /// comment and with generated parameter names. Prefer [`crate::export!`]
    /// for anything user-facing.
    pub fn function<A, F: PluginFn<A>>(&mut self, name: &str, f: F) -> &mut Self {
        self.export(FunctionDecl::new(name, None, f))
    }
}

/// A Rust callable whose signature maps onto plugin values: every parameter
/// is [`FromValue`] and the return is [`IntoOutcome`]. Implemented for `Fn`s
/// of up to 8 arguments; `A` is the argument-tuple marker that lets the
/// blanket impls coexist.
pub trait PluginFn<A>: Send + Sync + 'static {
    /// `(parameter types, return type, fallible)`.
    fn signature() -> (Vec<ValueType>, ValueType, bool);
    fn into_adapter(self) -> Adapter;
}

macro_rules! plugin_fn {
    ($($arg:ident),*) => {
        impl<F, R, $($arg,)*> PluginFn<($($arg,)*)> for F
        where
            F: Fn($($arg),*) -> R + Send + Sync + 'static,
            R: IntoOutcome,
            $($arg: FromValue,)*
        {
            fn signature() -> (Vec<ValueType>, ValueType, bool) {
                (
                    vec![$(<$arg as FromValue>::value_type()),*],
                    <R as IntoOutcome>::value_type(),
                    R::FALLIBLE,
                )
            }

            fn into_adapter(self) -> Adapter {
                Box::new(move |args: Vec<Value>| {
                    #[allow(unused_mut, unused_variables)]
                    let mut it = args.into_iter();
                    $(
                        #[allow(non_snake_case)]
                        let $arg = $arg::from_value(
                            it.next().ok_or_else(|| "missing argument".to_string())?,
                        )?;
                    )*
                    self($($arg),*).into_outcome()
                })
            }
        }
    };
}

plugin_fn!();
plugin_fn!(A1);
plugin_fn!(A1, A2);
plugin_fn!(A1, A2, A3);
plugin_fn!(A1, A2, A3, A4);
plugin_fn!(A1, A2, A3, A4, A5);
plugin_fn!(A1, A2, A3, A4, A5, A6);
plugin_fn!(A1, A2, A3, A4, A5, A6, A7);
plugin_fn!(A1, A2, A3, A4, A5, A6, A7, A8);
