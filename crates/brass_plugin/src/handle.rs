use std::collections::HashMap;
use std::fmt;
use std::sync::{Mutex, MutexGuard};

/// A failure to access a plugin's process-local handle table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HandleError {
    /// A prior panic occurred while the table lock was held.
    Poisoned,
    /// Every positive `i64` handle has been issued.
    Exhausted,
    /// The requested handle is not live in this table.
    Missing(i64),
}

impl fmt::Display for HandleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Poisoned => f.write_str("the handle table is poisoned"),
            Self::Exhausted => f.write_str("the handle table is exhausted"),
            Self::Missing(handle) => write!(f, "handle {handle} does not exist"),
        }
    }
}

impl std::error::Error for HandleError {}

struct State<T> {
    next: i64,
    entries: HashMap<i64, T>,
}

/// Process-local storage for values represented as `i64` across the plugin ABI.
///
/// Handles start at one, are never reused, and are allocated while holding the
/// same lock that publishes the value. Consumers choose whether removing a
/// handle ends its lifetime or whether entries remain available for the
/// process lifetime.
pub struct HandleTable<T> {
    state: Mutex<State<T>>,
}

impl<T> HandleTable<T> {
    /// Create an empty table whose first inserted value receives handle one.
    pub fn new() -> Self {
        Self {
            state: Mutex::new(State {
                next: 1,
                entries: HashMap::new(),
            }),
        }
    }

    /// Insert `value` and return a fresh handle that identifies it.
    pub fn insert(&self, value: T) -> Result<i64, HandleError> {
        let mut state = self.lock()?;
        let handle = state.next;
        state.next = handle.checked_add(1).ok_or(HandleError::Exhausted)?;
        state.entries.insert(handle, value);
        Ok(handle)
    }

    /// Clone the value behind `handle`, releasing the table lock before return.
    pub fn get_cloned(&self, handle: i64) -> Result<T, HandleError>
    where
        T: Clone,
    {
        self.lock()?
            .entries
            .get(&handle)
            .cloned()
            .ok_or(HandleError::Missing(handle))
    }

    /// Run `op` with mutable access to the value behind `handle`.
    ///
    /// The table lock stays held for the call, so use [`Self::get_cloned`] with
    /// an `Arc` value when an operation may block or perform substantial work.
    pub fn with_mut<R>(&self, handle: i64, op: impl FnOnce(&mut T) -> R) -> Result<R, HandleError> {
        let mut state = self.lock()?;
        state
            .entries
            .get_mut(&handle)
            .map(op)
            .ok_or(HandleError::Missing(handle))
    }

    /// Remove and return the value behind `handle`, ending that handle's life.
    pub fn remove(&self, handle: i64) -> Result<T, HandleError> {
        self.lock()?
            .entries
            .remove(&handle)
            .ok_or(HandleError::Missing(handle))
    }

    fn lock(&self) -> Result<MutexGuard<'_, State<T>>, HandleError> {
        self.state.lock().map_err(|_| HandleError::Poisoned)
    }
}

impl<T> Default for HandleTable<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Handles remain unique after removal, so a stale value can never regain
    /// access to a later entry that happened to occupy the same numeric slot.
    #[test]
    fn removed_handles_are_not_reused() {
        let table = HandleTable::new();
        let first = table.insert(String::from("first")).expect("insert");
        assert_eq!(table.remove(first).expect("remove"), "first");

        let second = table.insert(String::from("second")).expect("insert");
        assert_ne!(first, second);
        assert_eq!(table.get_cloned(second).expect("lookup"), "second");
        assert_eq!(table.get_cloned(first), Err(HandleError::Missing(first)));
    }

    /// In-place access supports stateful handles without exposing the backing
    /// map or requiring a second lock around every stored value.
    #[test]
    fn mutable_access_updates_the_stored_value() {
        let table = HandleTable::new();
        let handle = table.insert(vec![1]).expect("insert");
        table
            .with_mut(handle, |values| values.extend([2, 3]))
            .expect("mutate");
        assert_eq!(table.get_cloned(handle).expect("lookup"), vec![1, 2, 3]);
    }
}
