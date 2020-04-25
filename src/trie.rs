//! An implementation of a trie, for use in resolving commands
//!
//! Currently a work in progress

use std::fmt::{self, Debug};
use std::{mem, slice};

use crate::prelude::*;
use serde::Serializer;

#[derive(Debug)]
pub struct Trie<K, T> {
    /// The actual structure of the trie. This value will be `None` if there are no nodes, and
    /// `Some(..)` if there are any. It's an `Option` like this because `Node` has no way of
    /// representing a lack of children (aside from an empty list, but that's a mediocre way of
    /// doing it).
    inner: Option<Node<K, T>>,

    /// The cache should allow us to adjust the complexity of a few operations, namely reducing
    /// them from O(n^2) to O(n)
    // ^ TODO: Which ones?
    cache: Option<Cache<K, T>>,
}

unsafe impl<K: Send, T: Send> Send for Trie<K, T> {}

#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum Node<K, T> {
    Leaf {
        key: Vec<K>,
        value: T,
    },
    List {
        /// The total number of all children of the current `Node`
        size: usize,

        /// The list of immediate children of the `Node`, with their keys
        ///
        /// Normally, elements in the list will be paired with the next value of `K` to distinguish
        /// their key in the trie. If there is a leaf Node with a key equal to the common prefix of
        /// these children, it will be keyed with `None` in this list.
        ///
        /// As such, the following invariant holds: Any element in this list stored with `None` as
        /// its first element in the pair will be a Leaf node, and so [`extract`] will be safe
        /// to call.
        ///
        /// [`extract`]: #method.extract
        children: Vec<(Option<K>, Node<K, T>)>,
    },
}

struct Cache<K, T> {
    prefix: Vec<K>,

    // Note that this reference must *always* be non-null
    //
    // This is a *const instead of NonNull because NonNull can be mistakenly used mutably, which
    // this should never be.
    ptr: *const Node<K, T>,
}

impl<K: Debug, T: Debug> Debug for Cache<K, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // It *should* always be safe to dereference self.ptr, but we add this additional level of
        // checking just to ensure this is true when debugging.
        let ptr = match self.ptr.is_null() {
            true => {
                log::error!("Trie cache pointer is null!");
                None
            }
            false => Some(unsafe { &*self.ptr }),
        };

        f.debug_struct("Cache")
            .field("prefix", &self.prefix)
            .field("ptr_value", &(self.ptr as usize))
            .field("ptr", &ptr)
            .finish()
    }
}

impl<K: Clone + Ord, T> Trie<K, T> {
    /// Creates a `Trie` from an iterator of key-value pairs by repeated insertion
    pub fn from_iter<I: Iterator<Item = (Vec<K>, T)>>(mut iter: I) -> Self {
        let (key, value) = match iter.next() {
            None => {
                return Trie {
                    inner: None,
                    cache: None,
                }
            }
            Some(pair) => pair,
        };

        let mut node = Node::Leaf { key, value };

        for (k, i) in iter {
            node.insert(k, i, 0);
        }

        Self {
            inner: Some(node),
            cache: None,
        }
    }

    /// Inserts the given key-value pair into the trie, returning the value previously at the key
    ///
    /// If there was not a value at the key previously, this will return `None`.
    pub fn insert(&mut self, key: Vec<K>, value: T) -> Option<T> {
        match self.inner.as_mut() {
            None => {
                self.inner = Some(Node::Leaf { key, value });
                None
            }
            Some(n) => n.insert(key, value, 0),
        }
    }

    /// Produces an iterator over all key-value pairs whose keys start with the given prefix
    ///
    /// This iterator is fully lazy, so the only cost of initializing is finding the root node.
    pub fn iter_all_prefix<'a>(&'a self, key: &[K]) -> Iter<'a, K, T> {
        self.find(key).map(Node::iter).unwrap_or_else(Iter::empty)
    }

    /// Searches for a `Node` with the given key prefix, returning it if it exists
    pub fn find(&self, key: &[K]) -> Option<&Node<K, T>> {
        self.inner.as_ref()?.find(key, 0)
    }

    /// Retrieves the value corresponding to the given key
    ///
    /// If the given key corresponds to the *unique prefix* of a different key, the value for
    /// that key will be returned instead of `None`.
    ///
    /// If there is no unique value defined for the given key, this function will return `None`.
    pub fn get<'a>(&'a self, key: &[K]) -> Option<&'a T> {
        match self.find(key)? {
            Node::Leaf { value, .. } => Some(value),
            Node::List { children, .. } => {
                Some(children.iter().find(|(k, _)| k.is_none())?.1.extract())
            }
        }
    }
}

impl<K: Clone + Ord, T: Clone> Trie<K, T> {
    fn clone_as_vec(&self) -> Vec<(Vec<K>, T)> {
        self.iter_all_prefix(&[])
            .map(|(key, val)| (key.into(), val.clone()))
            .collect()
    }
}

impl<K: Clone + Ord, T> Node<K, T> {
    /// Attempts to extract the Node's value
    ///
    /// This is the fallible version of [`extract`].
    ///
    /// The semantics here are important; this will return a value in either of two cases:
    /// 1. `self` is a leaf node
    /// 2. `self` is a [`List`] node, but contains a leaf node at its level
    ///
    /// This method will always succeed if [`self.size()`] equals one - in that case the infallible
    /// version may be safely used instead.
    ///
    /// [`List`]: #variant.List
    /// [`self.size()`]: #method.size
    /// [`extract`]: #method.extract
    pub fn try_extract(&self) -> Option<&T> {
        match self {
            Self::Leaf { value, .. } => Some(value),
            Self::List { children, .. } => match children.first() {
                Some((None, leaf)) => Some(leaf.extract()),
                _ => None,
            },
        }
    }

    /// Extracts a node's value
    ///
    /// This is the infallible version of [`try_extract`]; the semantics are documented there.
    ///
    /// [`try_extract`]: #method.try_extract
    pub fn extract(&self) -> &T {
        self.try_extract().unwrap()
    }

    /// Returns an iterator over all children
    // ^ TODO: Clarify that it's recursive (kinda) -- it only yields leaves
    pub fn iter(&self) -> Iter<K, T> {
        Iter {
            size: self.size(),
            inner: InnerIter::Single(self),
        }
    }

    /// Returns the total number of leaf nodes reachable from this `Node`
    ///
    /// This function takes O(1).
    pub fn size(&self) -> usize {
        match self {
            Self::Leaf { .. } => 1,
            Self::List { size, .. } => *size,
        }
    }

    fn find(&self, prefix: &[K], depth: usize) -> Option<&Self> {
        let p = prefix.first();
        if p.is_none() {
            // If the key is empty, we found a node! we'll return this one
            return Some(self);
        }

        match self {
            Node::Leaf { key, .. } => match key.len() >= depth && &key[depth..] == prefix {
                true => Some(self),
                false => None,
            },
            Node::List { children, .. } => {
                // Search the list for the first value in the prefix
                let idx = children
                    .binary_search_by_key(&p, |(k, _)| k.as_ref())
                    .ok()?;

                children[idx].1.find(&prefix[1..], depth + 1)
            }
        }
    }

    /// A helper function for use inside `insert`.
    ///
    /// It is extracted as a separate function so that `insert` may be more readable.
    fn join(
        mut old_key: Vec<K>,
        mut old_val: T,
        mut new_key: Vec<K>,
        mut new_val: T,
        depth: usize,
    ) -> (Self, Option<T>) {
        // If the new key is equal to the old one, we just replace it
        if old_key[depth..] == new_key[depth..] {
            return (
                Node::Leaf {
                    key: new_key,
                    value: new_val,
                },
                Some(old_val),
            );
        }

        // Otherwise, we need to create a new list. This will effectively be of type
        // List(List(List(...(List(old, new))...))), where we have as many lists as needed to get to
        // the point where the keys differ.
        //
        // We'll first find how far beyond the current depth the two keys match.
        // We'll also put the *shorter* of the two keys into `old_key`

        if old_key.len() > new_key.len() {
            mem::swap(&mut old_key, &mut new_key);
            mem::swap(&mut old_val, &mut new_val);
        }

        // count how many *more* values they share
        let count = old_key[depth..]
            .iter()
            .zip(new_key[depth..].iter())
            .take_while(|(x, y)| x == y)
            .count();

        // If all of `old_key` is included within `new_key`, then we give it a key of None in the
        // constructed list
        //
        // We'll denote {old,new}_k as the key in the constructed list.
        //
        // if depth + count == old_key.len() then None
        let old_k = old_key.get(depth + count).cloned();
        // We know that `new_key` won't be equal to `old_key` because that's
        // checked above.
        let new_k = Some(new_key[depth + count].clone());

        let old_key_cloned = old_key.clone();

        // We need to store whether `old_key` goes first for two reasons:
        // 1. To maintain the ordering in the list
        // 2. To get around the borrow-checker; we can't make this comparison later
        let old_key_first = old_k.is_none() || &old_key[depth..] < &new_key[depth..];

        let old_node = Node::Leaf {
            key: old_key,
            value: old_val,
        };

        let new_node = Node::Leaf {
            key: new_key,
            value: new_val,
        };

        // We're going to wrap this in nodes `count` times to fill up the list
        let list = match old_key_first {
            true => vec![(old_k, old_node), (new_k, new_node)],
            false => vec![(new_k, new_node), (old_k, old_node)],
        };
        let mut replace_node = Node::List {
            size: 2,
            children: list,
        };

        // At each step, we wrap replace_node with the values from the two keys that are equal. In
        // most cases, this will not be *any* values, but we need to be able to handle the cases
        // that *do* include some.
        for k in old_key_cloned.into_iter().skip(depth).take(count).rev() {
            replace_node = Node::List {
                size: 2,
                children: vec![(Some(k), replace_node)],
            }
        }

        (replace_node, None)
    }

    fn insert(&mut self, new_key: Vec<K>, new_val: T, depth: usize) -> Option<T> {
        match self {
            Node::Leaf { .. } => {
                // we'll take ownership over the contents of `self` by swapping in a filler value
                let repl = Self::List {
                    size: 0,
                    children: Vec::new(),
                };

                let (key, val) = match mem::replace(self, repl) {
                    Node::Leaf { key, value } => (key, value),
                    _ => unreachable!(),
                };

                // we'll join these together
                let (this, ret) = Self::join(key, val, new_key, new_val, depth);
                *self = this;
                ret
            }

            Node::List { children, size } => {
                let pre = new_key.get(depth);
                match children.binary_search_by_key(&pre, |(k, _)| k.as_ref()) {
                    Ok(idx) => {
                        let ret = children[idx].1.insert(new_key, new_val, depth + 1);
                        if ret.is_none() {
                            *size += 1;
                        }
                        ret
                    }

                    Err(idx) => {
                        let pre_cloned = pre.cloned();

                        let new_leaf = Node::Leaf {
                            key: new_key,
                            value: new_val,
                        };

                        children.insert(idx, (pre_cloned, new_leaf));
                        *size += 1;
                        None
                    }
                }
            }
        }
    }
}

/// An iterator over the children of a `Node`.
#[derive(Debug)]
pub struct Iter<'a, K, T> {
    size: usize,
    inner: InnerIter<'a, K, T>,
}

#[derive(Debug)]
enum InnerIter<'a, K, T> {
    Single(&'a Node<K, T>),
    Stack(Vec<slice::Iter<'a, (Option<K>, Node<K, T>)>>),
}

impl<'a, K, T> Iter<'a, K, T> {
    /// Produces an empty iterator
    fn empty() -> Self {
        Self {
            size: 0,
            inner: InnerIter::Stack(Vec::new()),
        }
    }
}

impl<'a, K, T> InnerIter<'a, K, T> {
    fn unwrap_stack(&mut self) -> &mut Vec<slice::Iter<'a, (Option<K>, Node<K, T>)>> {
        match self {
            Self::Stack(stack) => stack,
            _ => panic!("Attempted to `unwrap_stack` an InnerIter that was not a stack"),
        }
    }
}

impl<'a, K, T> Iterator for Iter<'a, K, T> {
    type Item = (&'a [K], &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        let stack = match &mut self.inner {
            InnerIter::Stack(stack) => stack,

            // Iterators are typically constructed from a single node, so we need to handle that
            // here.
            InnerIter::Single(node) => match node {
                Node::Leaf { key, value } => {
                    *self = Self::empty();
                    return Some((key, value));
                }
                Node::List { children, size } => {
                    *self = Self {
                        size: *size,
                        inner: InnerIter::Stack(vec![children.iter()]),
                    };

                    self.inner.unwrap_stack()
                }
            },
        };

        let mut cur_iter = stack.pop()?;
        let item = loop {
            match cur_iter.next() {
                None => cur_iter = stack.pop()?,
                Some((_, node)) => {
                    stack.push(cur_iter);
                    match node {
                        Node::Leaf { key, value } => break (key.as_ref(), value),
                        Node::List { children, .. } => {
                            cur_iter = children.iter();
                        }
                    }
                }
            }
        };

        self.size -= 1;
        Some(item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<'a, K, T> ExactSizeIterator for Iter<'a, K, T> {}

/// Instead of deserializing the Trie directly, this converts it to a `Vec` first
impl<K: Clone + Ord + Serialize, T: Clone + Serialize> Serialize for Trie<K, T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let v = self.clone_as_vec();
        Serialize::serialize(&v, serializer)
    }
}

#[cfg(test)]
#[rustfmt::skip]
mod tests {
    use super::*;

    // A helper function so that we can use the same "complex" trie in multiple places
    fn generate_complex() -> Trie<u8, char> {
        // Commented to the right is the list, but sorted
        let input: Vec<(Vec<u8>, char)> = vec![
            (vec![0, 4, 1], 'a'),  //  (vec![       ], 'l'),
            (vec![0, 4   ], 'b'),  //  (vec![0, 4   ], 'b'),
            (vec![8      ], 'c'),  //  (vec![0, 4, 1], 'a'),
            (vec![6, 3, 1], 'd'),  //  (vec![0, 8, 7], 'e'),
            (vec![0, 8, 7], 'e'),  //  (vec![1, 4, 8], 'i'),
            (vec![4, 7, 8], 'f'),  //  (vec![4, 7, 8], 'f'),
            (vec![9, 6, 9], 'g'),  //  (vec![6      ], 'j'),
            (vec![7, 9, 5], 'h'),  //  (vec![6, 3   ], 'k'),
            (vec![1, 4, 8], 'i'),  //  (vec![6, 3, 1], 'd'),
            (vec![6      ], 'j'),  //  (vec![7, 9, 5], 'h'),
            (vec![6, 3,  ], 'k'),  //  (vec![8      ], 'c'),
            (vec![       ], 'l'),  //  (vec![9, 6, 9], 'g'),
        ];

        Trie::from_iter(input.into_iter())
    }

    #[test]
    fn new_simple() {
        let expected = Node::List {
            size: 4,
            children: vec![
                (Some(0), Node::List {
                    size: 2,
                    children: vec![
                        (None,    Node::Leaf { key: vec![0],    value: 'a' }),
                        (Some(1), Node::Leaf { key: vec![0, 1], value: 'b' }),
                    ],
                }),
                (Some(1), Node::List {
                    size: 2,
                    children: vec![
                        (None,    Node::Leaf { key: vec![1],    value: 'c' }),
                        (Some(1), Node::Leaf { key: vec![1, 1], value: 'd' }),
                    ],
                })
            ],
        };

        let input: Vec<(Vec<u8>, char)> = vec![
            (vec![0],    'a'),
            (vec![0, 1], 'b'),
            (vec![1],    'c'),
            (vec![1, 1], 'd'),
        ];

        let trie = Trie::from_iter(input.into_iter());
        assert_eq!(trie.inner, Some(expected))
    }

    #[test]
    fn new_complex() {
        let expected = Node::List {
            size: 12,
            children: vec![
                (None, Node::Leaf { key: vec![], value: 'l' }),
                (Some(0), Node::List {
                    size: 3,
                    children: vec![
                        (Some(4), Node::List {
                            size: 2,
                            children: vec![
                                (None,    Node::Leaf { key: vec![0,4  ], value: 'b' }),
                                (Some(1), Node::Leaf { key: vec![0,4,1], value: 'a' }),
                            ]
                        }),
                        (Some(8), Node::Leaf { key: vec![0,8,7], value: 'e' })
                    ]
                }),
                (Some(1), Node::Leaf { key: vec![1, 4, 8], value: 'i' }),
                (Some(4), Node::Leaf { key: vec![4, 7, 8], value: 'f' }),
                (Some(6), Node::List {
                    size: 3,
                    children: vec![
                        (None,    Node::Leaf { key: vec![6], value: 'j' }),
                        (Some(3), Node::List {
                            size: 2,
                            children: vec![
                                (None,    Node::Leaf { key: vec![6, 3   ], value: 'k' }),
                                (Some(1), Node::Leaf { key: vec![6, 3, 1], value: 'd' }),
                            ]
                        }),
                    ]
                }),
                (Some(7), Node::Leaf { key: vec![7, 9, 5], value: 'h' }),
                (Some(8), Node::Leaf { key: vec![8      ], value: 'c' }),
                (Some(9), Node::Leaf { key: vec![9, 6, 9], value: 'g' }),
            ],
        };

        let trie = generate_complex();
        assert_eq!(trie.inner, Some(expected))
    }

    #[test]
    fn find_simple() {
        let trie = generate_complex();

        let finds: Vec<(Vec<u8>, Option<Node<u8,char>>)> = vec![
            /*
            (vec![6], Some(Node::List {
            })),
            */
            (vec![8, 0], None),
        ];

        for (i, (key, node)) in finds.iter().enumerate() {
            let found = trie.find(&key);
            if found != node.as_ref() {
                println!("Failed at iteration {}:", i);
                assert_eq!(node.as_ref(), found);
            }
        }
    }
}
