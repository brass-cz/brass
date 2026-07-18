//! A generic lexical scope chain used for name resolution by later passes
//! (type checking and code generation).

use fxhash::FxHashMap as HashMap;

pub struct Scope<T> {
    frames: Vec<HashMap<String, T>>,
}

impl<T> Default for Scope<T> {
    fn default() -> Self {
        Scope {
            frames: vec![HashMap::default()],
        }
    }
}

impl<T> Scope<T> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self) {
        self.frames.push(HashMap::default());
    }

    pub fn pop(&mut self) {
        self.frames.pop();
    }

    pub fn define(&mut self, name: &str, value: T) {
        self.frames
            .last_mut()
            .unwrap()
            .insert(name.to_string(), value);
    }

    /// Look up a name from the innermost scope outward.
    pub fn lookup(&self, name: &str) -> Option<&T> {
        self.frames.iter().rev().find_map(|f| f.get(name))
    }

    pub fn in_scope(&self, name: &str) -> bool {
        self.lookup(name).is_some()
    }
}
