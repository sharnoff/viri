//! An implementation of a trie, for use in resolving commands
//!
//! Currently a work in progress

use std::collections::{hash_map, HashMap};
use std::fmt::{self, Debug};
use std::hash::Hash;
use std::{iter, mem, ptr, slice};

use serde::{Serialize, Serializer};

#[derive(Debug)]
pub struct Trie<K: Debug + Clone + Eq + Hash, T: Debug> {
    inner: Option<NodeKind<K, T>>,
    cache: Option<Cache<K, T>>,
}

unsafe impl<K: Debug + Clone + Eq + Hash + Send, T: Debug + Send> Send for Trie<K, T> {}

#[derive(Debug)]
pub struct Node<K: Debug + Clone + Eq + Hash, T: Debug> {
    n_children: usize,
    kind: NodeKind<K, T>,
}

// This is just a guess - it should be benchmarked at some later date
const MAX_NODE_LIST_SIZE: usize = 10;

#[derive(Debug)]
pub enum NodeKind<K: Debug + Clone + Eq + Hash, T: Debug> {
    // These options are None when one value ends and no others exist
    Map(HashMap<Option<K>, Node<K, T>>),
    List(Vec<(Option<K>, Node<K, T>)>),
    Leaf(Vec<K>, T),
}

struct Cache<K: Debug + Clone + Eq + Hash, T: Debug> {
    prefix: Vec<K>,

    // Note that this reference must *always* be non-null
    // We use a *const instead of NonNull because NonNull can be mistakenly used mutably, which
    // this should never be.
    ptr: *const NodeKind<K, T>,
}

impl<K: Debug + Clone + Eq + Hash + Debug, T: Debug> Debug for Cache<K, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // It *should* always be safe to dereference self.ptr, but we add this additional level of
        // checking just to ensure this is true when debugging.
        let ptr = match self.ptr.is_null() {
            true => None,
            false => Some(unsafe { &*self.ptr }),
        };

        f.debug_struct("Cache")
            .field("prefix", &self.prefix)
            .field("ptr_value", &(self.ptr as usize))
            .field("ptr", &ptr)
            .finish()
    }
}

impl<K: Debug + Clone + Eq + Hash, T: Debug> Trie<K, T> {
    pub fn from_iter<I: Iterator<Item = (Vec<K>, T)>>(mut iter: I) -> Self {
        let (key, item) = match iter.next() {
            None => {
                return Trie {
                    inner: None,
                    cache: None,
                }
            }
            Some(pair) => pair,
        };

        let mut node = NodeKind::Leaf(key, item);

        for (k, i) in iter {
            node.insert(k, i, 0);
        }

        Self {
            inner: Some(node),
            cache: None,
        }
    }

    // Panics if key.is_empty()
    pub fn insert(&mut self, key: Vec<K>, item: T) -> Option<T> {
        if key.is_empty() {
            panic!("Trie keys must have length ≥ 1");
        }

        match self.inner.as_mut() {
            None => {
                self.inner = Some(NodeKind::Leaf(key, item));
                None
            }
            Some(n) => n.insert(key, item, 0),
        }
    }

    pub fn find(&self, key: &[K]) -> Option<&NodeKind<K, T>> {
        self.inner.as_ref()?.find(key, 0)
    }

    pub fn iter_all_prefix<'a>(
        &'a self,
        key: &[K],
    ) -> Box<dyn 'a + ExactSizeIterator<Item = (&'a [K], &'a T)>> {
        type I<'b, K, T> = Box<dyn 'b + ExactSizeIterator<Item = (&'b [K], &'b T)>>;
        self.find(key)
            .map(|node| Box::new(node.children_iter()) as I<'a, K, T>)
            .unwrap_or_else(|| Box::new(iter::empty()) as I<'a, K, T>)
    }

    pub fn get<'a>(&'a self, key: &[K]) -> Option<&'a T> {
        match self.find(key)? {
            NodeKind::Leaf(_, t) => Some(t),
            NodeKind::List(v) => Some(v.iter().find(|(k, _)| k.is_none())?.1.kind.unwrap_leaf()),
            NodeKind::Map(m) => Some(m.get(&None)?.kind.unwrap_leaf()),
        }
    }

    fn clone_as_vec(&self) -> Vec<(Vec<K>, T)> {
        todo!()
    }
}

impl<K: Debug + Clone + Eq + Hash, T: Debug> Node<K, T> {
    fn leaf(key: Vec<K>, val: T) -> Self {
        Node {
            n_children: 1,
            kind: NodeKind::Leaf(key, val),
        }
    }
}

impl<K: Debug + Clone + Eq + Hash, T: Debug> NodeKind<K, T> {
    fn unwrap_leaf(&self) -> &T {
        match self {
            Self::Leaf(_, t) => t,
            _ => panic!("Tried to `unwrap_leaf` a non-leaf node"),
        }
    }

    fn children_iter(&self) -> NodeChildrenIter<K, T> {
        let size = self.count_children();

        NodeChildrenIter {
            size,
            stack: vec![NodeKindIter::Node(Some(self))],
        }
    }

    // This function is only intended ofr use inside `insert`. It has been extracted here so that
    // the body of `insert` may be more readable. This function has the requirement that it *MUST*
    // not panic, due to where it is used inside `insert`.
    fn join(
        mut old_key: Vec<K>,
        mut old_val: T,
        mut new_key: Vec<K>,
        mut new_val: T,
        depth: usize,
    ) -> (Self, Option<T>) {
        // If the new key is equal to the old one, we just replace it
        if old_key[depth..] == new_key[depth..] {
            return (NodeKind::Leaf(new_key, new_val), Some(old_val));
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

        let old_node = Node {
            n_children: 1,
            kind: NodeKind::Leaf(old_key, old_val),
        };

        let new_node = Node {
            n_children: 1,
            kind: NodeKind::Leaf(new_key, new_val),
        };

        // We're going to wrap this in nodes `count` times to fill up the list
        let mut replace_node = NodeKind::List(vec![(old_k, old_node), (new_k, new_node)]);

        // At each step, we wrap replace_node with the values from the two keys that are equal. In
        // most cases, this will not be *any* values, but we need to be able to handle the cases
        // that *do* include some.
        for k in old_key_cloned.into_iter().skip(depth).take(count).rev() {
            let n = Node {
                n_children: 2,
                kind: replace_node,
            };

            replace_node = NodeKind::List(vec![(Some(k), n)]);
        }

        (replace_node, None)
    }

    fn insert(&mut self, key: Vec<K>, val: T, depth: usize) -> Option<T> {
        // A helper function to simplify the recursion. This handles all of the logic aroun calling
        // `insert` on the *Node* below.
        let recurse =
            |node: &mut Node<K, T>, prefix: &Option<K>, key: Vec<K>, val: T, depth: usize| {
                // we only want to increase the depth if there *is* a prefix - there won't be in cases
                // where the node for a certain value is stored as the `None` entry in a Vec/Map
                let d = match prefix.is_some() {
                    true => depth + 1,
                    false => depth,
                };

                let ret = node.kind.insert(key, val, d);

                // If we don't get a value back, we didn't replace anything. I.e. we added something,
                // so we should increment the number of children
                if ret.is_none() {
                    node.n_children += 1;
                }
                ret
            };

        let replace = move |this: Self, _: ()| -> (Self, Option<T>) {
            match this {
                NodeKind::Leaf(old_key, old_val) => Self::join(old_key, old_val, key, val, depth),
                NodeKind::Map(mut m) => {
                    // try to find a node with the prefix new_key
                    let pre = key.get(depth).cloned();
                    let ret = match m.get_mut(&pre) {
                        Some(node) => recurse(node, &pre, key, val, depth),
                        None => {
                            m.insert(pre, Node::leaf(key, val));
                            None
                        }
                    };

                    (NodeKind::Map(m), ret)
                }
                NodeKind::List(mut v) => {
                    let pre = key.get(depth).cloned();
                    let ret = match v.iter_mut().find(|(k, _)| k == &pre) {
                        Some((_, node)) => recurse(node, &pre, key, val, depth),
                        None => {
                            v.push((pre, Node::leaf(key, val)));
                            None
                        }
                    };

                    if v.len() < MAX_NODE_LIST_SIZE {
                        (NodeKind::List(v), ret)
                    } else {
                        (NodeKind::Map(v.into_iter().collect()), ret)
                    }
                }
            }
        };

        unsafe { replace_with(self, (), replace) }
    }

    fn find(&self, key: &[K], depth: usize) -> Option<&Self> {
        // If the key is empty, we found a node! we'll return this one.
        if key.len() <= depth {
            return Some(self);
        }

        let k = Some(&key[depth]);

        match self {
            NodeKind::Leaf(ks, _) => {
                if ks.len() <= depth || ks[depth..] != key[depth..] {
                    return None;
                } else {
                    Some(self)
                }
            }
            NodeKind::List(v) => {
                // Search the list for the first value in the prefix
                v.iter()
                    .find(|(c, _)| c.as_ref() == k)?
                    .1
                    .kind
                    .find(key, depth + 1)
            }
            NodeKind::Map(m) => m.get(&k.cloned())?.kind.find(key, depth + 1),
        }
    }

    fn count_children(&self) -> usize {
        match self {
            NodeKind::Leaf(_, _) => 1,
            NodeKind::Map(m) => m.iter().map(|(_, node)| node.n_children).sum(),
            NodeKind::List(v) => v.iter().map(|(_, node)| node.n_children).sum(),
        }
    }
}

#[derive(Debug)]
struct NodeChildrenIter<'a, K: Debug + Clone + Eq + Hash, T: Debug> {
    size: usize,
    stack: Vec<NodeKindIter<'a, K, T>>,
}

#[derive(Debug)]
enum NodeKindIter<'a, K: Debug + Clone + Eq + Hash, T: Debug> {
    Map(hash_map::Iter<'a, Option<K>, Node<K, T>>),
    List(slice::Iter<'a, (Option<K>, Node<K, T>)>),
    Node(Option<&'a NodeKind<K, T>>),
}

impl<'a, K: 'a + Debug + Clone + Eq + Hash, T: 'a + Debug> Iterator for NodeChildrenIter<'a, K, T> {
    type Item = (&'a [K], &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        // FIXME: The correctness of this function hasn't been verified - one dead simple bug has
        // been fixed already, so there may be more.

        let mut cur_iter = Some(self.stack.pop()?);

        // This will be set by the loop - cur_iter is Some when item is None
        let mut item: Option<Self::Item> = None;
        while item.is_none() {
            let mut cur = cur_iter.take().unwrap();

            let next_node_opt = match &mut cur {
                NodeKindIter::Map(m) => m.next().map(|(_, n)| &n.kind),
                NodeKindIter::List(v) => v.next().map(|(_, n)| &n.kind),
                &mut NodeKindIter::Node(n) => n,
            };

            if let Some(node) = next_node_opt {
                match node {
                    NodeKind::Leaf(ks, t) => item = Some((&ks, &t)),
                    NodeKind::Map(m) => {
                        self.stack.push(cur);
                        cur_iter = Some(NodeKindIter::Map(m.iter()))
                    }
                    NodeKind::List(v) => {
                        self.stack.push(cur);
                        cur_iter = Some(NodeKindIter::List(v.iter()))
                    }
                }
            }
        }

        self.size -= 1;
        item
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<'a, K: 'a + Debug + Clone + Eq + Hash, T: 'a + Debug> ExactSizeIterator
    for NodeChildrenIter<'a, K, T>
{
}

/// Instead of deserializing the Trie directly, this converts it to a `Vec` first
impl<K: Debug + Clone + Eq + Hash + Serialize, T: Debug + Clone + Serialize> Serialize
    for Trie<K, T>
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let v = self.clone_as_vec();
        Serialize::serialize(&v, serializer)
    }
}

/// A helper function inspired by [RFC#1736]: "`core::mem::replace_with` for temporarily moving out
/// of ownership".
///
/// The actual function is partially taken from [this commit], adapted for ergonomics based on the
/// idea of [this comment].
///
/// There are certain safety concerns listed in the discusion of the RFC - primarily that the
/// program should abort on panic inside `replace_with`. I've instead made this an unsafe function
/// with the requirement that the passed function *MUST NOT PANIC*. If this is not obeyed, the
/// moved value may be dropped twice during unwinding.
///
/// [RFC#1736]: https://github.com/rust-lang/rfcs/pull/1736
/// [this commit]: https://github.com/rust-lang/rust/pull/36186/commits/ab9cb7fa2af5d17ba08f49c798565c513a905e3c
/// [this comment]: https://github.com/rust-lang/rfcs/pull/1736#issuecomment-292969474
unsafe fn replace_with<T, A, R, F>(val: &mut T, arg: A, replace: F) -> R
where
    F: FnOnce(T, A) -> (T, R),
{
    let old = ptr::read(&*val);
    let (new, ret) = replace(old, arg);
    std::ptr::write(val, new);
    ret
}
