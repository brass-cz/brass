//! Ordered observations with shared, immutable child windows.

use std::rc::Rc;

/// A sequence whose child windows are shared instead of copied into parents.
/// Mutation copies only a shared root; completed descendants stay shared.
#[derive(Clone)]
pub(super) struct Chunks<T: Clone>(Rc<Node<T>>);

#[derive(Clone)]
struct Node<T: Clone> {
    parts: Vec<Part<T>>,
    len: usize,
}

#[derive(Clone)]
enum Part<T: Clone> {
    Items(Vec<T>),
    Child(Rc<Node<T>>),
}

impl<T: Clone> Default for Chunks<T> {
    fn default() -> Self {
        Self(Rc::new(Node {
            parts: Vec::new(),
            len: 0,
        }))
    }
}

impl<T: Clone> Chunks<T> {
    /// Append one observation after all existing child windows.
    pub(super) fn push(&mut self, value: T) {
        let node = Rc::make_mut(&mut self.0);
        node.len += 1;
        if let Some(Part::Items(items)) = node.parts.last_mut() {
            items.push(value);
        } else {
            node.parts.push(Part::Items(vec![value]));
        }
    }

    /// Append a completed child without cloning its observations.
    pub(super) fn append(&mut self, child: &Self) {
        if !child.is_empty() {
            let node = Rc::make_mut(&mut self.0);
            node.len += child.len();
            node.parts.push(Part::Child(Rc::clone(&child.0)));
        }
    }

    /// The number of observations, including nested windows.
    pub(super) fn len(&self) -> usize {
        self.0.len
    }

    /// Whether the sequence has no observations.
    pub(super) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Borrow observations in their original depth-first recording order.
    pub(super) fn iter(&self) -> Iter<'_, T> {
        Iter {
            parts: vec![self.0.parts.iter()],
            items: [].iter(),
        }
    }

    /// Index a sequence made flat by the replay deduplication pass.
    pub(super) fn flat_at(&self, index: usize) -> &T {
        match self.0.parts.as_slice() {
            [Part::Items(items)] => &items[index],
            _ => unreachable!("deduplicated observations occupy one flat chunk"),
        }
    }
}

impl<T: Clone> FromIterator<T> for Chunks<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let items: Vec<T> = iter.into_iter().collect();
        Self(Rc::new(Node {
            len: items.len(),
            parts: vec![Part::Items(items)],
        }))
    }
}

impl<T: Clone> Extend<T> for Chunks<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        iter.into_iter().for_each(|value| self.push(value));
    }
}

/// Iterative traversal keeps native stack use independent of journal depth.
pub(super) struct Iter<'a, T: Clone> {
    parts: Vec<std::slice::Iter<'a, Part<T>>>,
    items: std::slice::Iter<'a, T>,
}

impl<'a, T: Clone> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(item) = self.items.next() {
                return Some(item);
            }
            match self.parts.last_mut()?.next() {
                Some(Part::Items(items)) => self.items = items.iter(),
                Some(Part::Child(child)) => self.parts.push(child.parts.iter()),
                None => {
                    self.parts.pop();
                }
            }
        }
    }
}

impl<T: Clone> Drop for Node<T> {
    fn drop(&mut self) {
        let mut children = Vec::new();
        let drain = |node: &mut Self, children: &mut Vec<Rc<Self>>| {
            for part in node.parts.drain(..) {
                if let Part::Child(child) = part {
                    children.push(child);
                }
            }
        };
        drain(self, &mut children);
        while let Some(child) = children.pop() {
            if let Ok(mut node) = Rc::try_unwrap(child) {
                // The node's destructor sees no child links after draining.
                drain(&mut node, &mut children);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    struct Counted(Rc<Cell<usize>>, usize);

    impl Clone for Counted {
        fn clone(&self) -> Self {
            self.0.set(self.0.get() + 1);
            Self(Rc::clone(&self.0), self.1)
        }
    }

    #[test]
    fn nested_windows_share_observations_and_keep_order() {
        let clones = Rc::new(Cell::new(0));
        let mut child = Chunks::default();
        child.push(Counted(Rc::clone(&clones), 2));
        let mut parent = Chunks::default();
        parent.push(Counted(Rc::clone(&clones), 1));
        parent.append(&child);
        parent.push(Counted(Rc::clone(&clones), 3));
        assert_eq!(clones.get(), 0);
        assert_eq!(parent.iter().map(|v| v.1).collect::<Vec<_>>(), [1, 2, 3]);
        // A probe can mutate its own root without changing the live checker.
        let mut probe = child.clone();
        probe.push(Counted(Rc::clone(&clones), 4));
        assert_eq!(child.len(), 1);
        assert_eq!(parent.iter().map(|v| v.1).collect::<Vec<_>>(), [1, 2, 3]);
        assert_eq!(probe.len(), 2);
    }

    #[test]
    fn deep_windows_iterate_and_drop_without_recursive_stack_growth() {
        let mut journal: Chunks<usize> = [7].into_iter().collect();
        for _ in 0..20_000 {
            let mut parent = Chunks::default();
            parent.append(&journal);
            journal = parent;
        }
        assert_eq!(journal.iter().copied().collect::<Vec<_>>(), [7]);
        drop(journal);
    }
}
