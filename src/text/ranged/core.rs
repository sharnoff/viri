//! Wrapper module for the [`Ranged`] type
//!
//! Information about the purpose that [`Ranged`] serves is available in the type's documentation.

use crate::utils::{DebugPtr, MapDeref, MapDerefMut, MappedGuard};
use std::cell::{self, RefCell};
use std::cmp::Ordering::{self, Equal, Greater, Less};
use std::collections::BTreeSet;
use std::fmt::{self, Debug, Formatter};
use std::marker::PhantomData;
use std::ops::{AddAssign, Deref, DerefMut, Range, SubAssign};
use std::rc::{Rc, Weak};
use std::{mem, thread};

use super::RangedIndex;

/// A compact representation of tagged ranges
///
/// This type essentially serves as a better representation of `Vec<T>`, where large ranges of the
/// vector may be the same. The operations on this type guarnatee logarithmic average-case
/// time-complexity (and better space requirements!) for the sorts of operations that would be
/// linear on the equivalent vector -- like performing a diff-like replacement operation. The
/// tradeoff here is of course that lookups have cost *O(log(n))* instead of *O(1)*.
///
/// Internally, we're using a structure that's essentially just a splay tree, which guarantees that
/// the last accessed node is the root. More information on how this works is available in the
/// internal documentation.
///
// @def "`Ranged` is splay tree" v0
///
/// The primary consequence of using a splay tree is that nearly all operations can modify the
/// tree, so methods that might otherwise take `&self` for soemthing like a b-tree instead take
/// `&mut self` here.
///
/// ## Parameters
///
/// This type is *incredibly* customizable -- typically too much for direct usage. The full set of
/// features include:
///
/// * Accumulators across ranges, with searching for the first index at a given accumulated value
/// * Direct indexing to retrieve the value at a position
/// * Custom index types -- not just `usize`
/// * Stable node references to retrieve indexes after shifting
///
/// Accumulators typically occur when there's something we're counting from each range. The best
/// example of this is with newlines -- searching for the first index with a particular accumulated
/// value then gives the byte position at the start of the `n`th line. We do this exact thing in
/// the implementation of [`TextTree`].
///
/// Custom index types are also useful in a few cases -- also in the implementation of
/// [`TextTree`]. Using (line, byte index) pairs allow us to have values assigned to particular
/// ranges or points within that.
///
/// Node references are a bit of a niche feature. There's some use cases where it's incredibly
/// helpful (i.e. allows a reduction of `O(n)` to `O(log n)`) to be able to go in the reverse
/// direction -- from a slice back to its position. Node references *can* be a little finnicky
/// sometimes, if not used carefully. More details are available in the relevant
/// [documentation](NodeRef).
///
/// For more information on any of the above, refer to the [`AccumulatorSlice`] and [`RangedIndex`]
/// traits, or the [`NodeRef`] type.
///
/// ## Defaults
///
/// In the majority of cases, having access to all of these features just causes more boilerplate
/// than it's worth. To make the typical case more ergonomic, there's a couple other types
/// provided.
///
/// [`StdRanged`] provides for the "standard" usage pattern of this type, more in line with the
/// original intent -- only providing the "direct indexing" feature from above. This type uses the
/// [`Slice`] and [`IndexedSlice`] traits for customization.
///
/// [`Constant`] implements [`IndexedSlice`] for the simplest case: uniform ranges of values
/// without any special behavior.
///
/// [`TextTree`]: crate::text::objects::TextTree
/// [`StdRanged`]: super::StdRanged
/// [`Slice`]: super::Slice
/// [`IndexedSlice`]: super::IndexedSlice
/// [`Constant`]: super::Constant
#[derive(Debug)]
pub struct Ranged<Acc, Idx, Delta, S> {
    size: Idx,
    // The root is always `Some(_)` if `size != 0`. It's equal to `None` in certain cases, i.e.
    // whenever `size = 0`. We also will sometimes `.take()` it in order to temporarily extract an
    // owned `Ranged` from a `&mut Ranged`.
    root: Option<OwnedNode<Acc, Idx, Delta, S>>,
    // Helper value to store the default accumulator. This is kept in case the accumulator happens
    // to be particularly expensive to construct -- we want to minimize unnecessary calls to
    // `Acc::default()`
    //
    // This value is always kept as `Some(_)` between method calls, though `replace_with`
    // temporarily moves out of it.
    default_acc: Option<Acc>,
}

impl<Acc, Idx, Delta, S> Clone for Ranged<Acc, Idx, Delta, S>
where
    Acc: Clone,
    Idx: Clone,
    Delta: Clone,
    S: Clone,
{
    fn clone(&self) -> Self {
        Ranged {
            size: self.size.clone(),
            root: self.root.as_ref().map(|r| r.deep_clone(None)),
            default_acc: self.default_acc.clone(),
        }
    }
}

/// A stable reference to a particular node in a [`Ranged`]
///
/// These are produced by the [`insert_ref`] or [`index_ref`] methods on `Ranged`, and remain valid
/// so long as range corresponding to the node is not fully removed from the tree. In the case
/// where the node *is* removed from the tree, it can be easy to accidentally keep the node as
/// valid, but in a different tree.
///
/// `NodeRef`s essentially act as weak pointers to a node in the tree. Significant effort is made
/// to ensure that they continue to be valid when the tree changes, however the reference will
/// immediately become invalid if or when the owning `Ranged` is dropped.
///
/// The remainder of this documentation covers a few implementation details.
///
/// ## Redirection
///
/// In the event that two nodes in the tree are joined, `NodeRef`s to either will be changed to
/// point to the same node. This is internally implemented with temporary redirection, and so
/// accessing the node behind a `NodeRef` may incur a one-time cost of one additional dereference
/// for each joining. Accessing a redirected node will overwrite the `NodeRef` to point to the new
/// one.
///
/// Please note that it *is* possible for a sequence of node joins and splits to cause a `NodeRef`
/// to point to a different but equal (i.e. `join`-able) node in an equal version of the tree. This
/// can occur even in simple cases -- to demonstrate let's see an example, with distinct node given
/// unqiue names:
///
/// ```text
/// initial state:
///   |---- A ----|-- B --|---- C ----|
/// remove B, causing A & C join:
///   |----------- A -----------|
/// insert B again, D splits off from A:
///   |---- A ----|-- B --|---- D ----|
/// ```
///
/// In this example, any references that originally pointed to `C` will finish by pointing to `A`.
/// The new node, `D` is viewed as distinct from the `C` that was originally joined into `A`.
///
/// There are no plans to change this behavior -- your best option is to just be careful about any
/// usage of `NodeRef`s if this could affect you.
///
/// ## Deallocation
///
/// Much work has gone into ensuring that `NodeRef`s do not keep the full tree alive. Any remaining
/// node references that exist when the base `Ranged` is dropped will prevent the individual
/// *allocations* for their nodes from being deallocated, but the entire contents of the tree will
/// otherwise drop. This is essentially the same as what you can expect using either of the
/// standard library's weak pointers.
///
/// ## Send/Sync bounds
///
/// This type does not implement `Send` or `Sync` because it internally uses an [`rc::Weak`]. If
/// your usage of this type restricts access so that only a single thread at a time may own **all**
/// node references for a particular tree (including the tree itself!), then it is safe to
/// implement `Send` or `Sync` on a wrapper type. [`StdRanged`] does this, because `NodeRef`s are
/// not exposed there. There are no checks here that this invariant is upheld, aside from the racy
/// runtime borrow checks from [`RefCell`].
///
/// It is not possible to safely expose any of the functionality from a `NodeRef` in a concurrent
/// fashion directly. Do not attempt to do so. If this functionality is required, wrap the entire
/// data structure in a `Mutex` and implement your own node references using that, that *are*
/// thread-safe.
///
/// [`StdRanged`]: super::StdRanged
/// [`insert_ref`]: Ranged::insert_ref
/// [`index_ref`]: Ranged::index_ref
/// [`rc::Weak`]: Weak
//
// Internal notes:
//
// We always guarantee that - if a `NodeRef` is still valid - the node it points to will contain
// the address of reference in its `RefSet`. This means we can always confidently remove the
// reference from a redirected node when we update.
pub struct NodeRef<Acc, Idx, Delta, S> {
    inner: Weak<RefCell<MaybeNode<Acc, Idx, Delta, S>>>,
}

impl<Acc, Idx, Delta, S> Clone for NodeRef<Acc, Idx, Delta, S> {
    fn clone(&self) -> Self {
        NodeRef {
            inner: self.inner.clone(),
        }
    }
}

impl<Acc, Idx, Delta, S> Drop for NodeRef<Acc, Idx, Delta, S> {
    fn drop(&mut self) {
        // The implementation of `Drop` serves to clean up any redirected nodes if there's no more
        // references pointing to them. Because redirected nodes internally use `NodeRef`s as well
        // to redirect, this will occur all the way down a chain of unused redirects.
        //
        // The central idea here is that -- if our NodeRef happens to point to a redirected node,
        // AND there's no other NodeRefs remaining that point to it, then we can remove the last
        // strong reference for that node from the node it points to.

        match self.inner.weak_count() {
            // weak_count = 0 if the node has already been deallocated already
            0 => return,
            // weak_count = 1 if this `NodeRef` is the last thing referencing it
            1 => (),
            // weak_count > 1 if there's other active `NodeRef`s. We should allow this to stay
            // as-is
            _ => return,
        }

        if let Some(node_rc) = self.inner.upgrade() {
            // We want to avoid double-panicking in the destructor here. If we aren't already
            // panicking, then we can go ahead and just grab the guard, but if we are we'll just
            // silently exit -- it could be that some other invariant already messed this up.
            //
            // Helper macro to panic if the thread isn't already panicking.
            macro_rules! ensure_panic {
                ($($ts:tt)*) => {{
                    if !thread::panicking() {
                        panic!($($ts)*);
                    } else {
                        return;
                    }
                }};
            }

            let guard = match node_rc.try_borrow() {
                Ok(g) => g,
                Err(e) => ensure_panic!("failed to borrow node: {}", e),
            };

            let redirect_ref = match &*guard {
                MaybeNode::Redirected(r, _) => r,
                // Don't worry about counts for nodes that aren't redirected
                MaybeNode::Base(_) => return,
                MaybeNode::Temp => ensure_panic!("dropped invalid `NodeRef`: points to `Temp`"),
            };

            let redirect_rc = match redirect_ref.inner.upgrade() {
                Some(rc) => rc,
                None => ensure_panic!("redirect points to dropped node"),
            };

            let mut r_guard = match redirect_rc.try_borrow_mut() {
                Ok(g) => g,
                Err(e) => ensure_panic!("failed to borrow node: {}", e),
            };

            match &mut *r_guard {
                MaybeNode::Redirected(_, refs) | MaybeNode::Base(Node { refs, .. }) => {
                    refs.set.remove(&RefSetItem(node_rc.clone()));
                }
                MaybeNode::Temp => ensure_panic!("redirect points to `Temp`"),
            }
        }
    }
}

impl<S> NodeRef<S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S>
where
    S: AccumulatorSlice,
    S::Idx: Debug,
{
    /// Returns whether the `NodeRef` points to a currently valid node
    ///
    /// In general, we call a node valid if the [`Ranged`] containing it has not been dropped.
    ///
    /// If the `NodeRef` is invalid, most other methods on it may panic as a result. When accessing
    /// the `NodeRef` separately from the `Ranged` containing its node, it's generally a good idea
    /// to call this method first to check that the `NodeRef` is still valid.
    pub fn is_valid(&self) -> bool {
        // If the strong count is > 0, we'll be able to upgrade the pointer -- that's all that's
        // required for us to know that it's valid
        self.inner.strong_count() > 0
    }

    /// Returns the current global index corresponding to the start of the node
    ///
    /// ## Panics
    ///
    /// This method panics if the [`Ranged`] containing the node has been dropped or if the node
    /// has been removed. This can be checked with the [`is_valid`] method.
    ///
    /// [`is_valid`]: Self::is_valid
    pub fn current_index(&mut self) -> S::Idx {
        assert!(self.is_valid());
        self.collapse_redirects();

        let mut node_ref = self.inner.upgrade().unwrap();

        let mut delta = S::Idx::ZERO_DELTA;
        loop {
            let guard = node_ref.borrow();
            let node = guard.as_node_ref();
            S::Idx::delta_add_assign(&mut delta, node.offset_from_parent);
            match &node.parent {
                None => break,
                Some(p) => {
                    let r = p.upgrade().unwrap();
                    drop(guard);
                    node_ref = r;
                }
            }
        }

        // We'd really *like* to perform a splay operation here after getting the index. But
        // unfortunately, the splay operation requires a &mut OwnedNode, usually coming from the
        // actual field of `Ranged` itself, through a `&mut Ranged`. We don't currently have the
        // facilities for that, and adding it in would require some kind of redirection for the
        // root node, which is a not-insignificant cost that would have to be evaluated.
        //
        // So for now, we accept that we don't splay on this operation. This will eventually change
        // in the future. (TODO-ALG)
        S::Idx::from_delta(delta)
    }

    /// Returns the current size of the referenced node
    ///
    /// ## Panics
    ///
    /// This method panics if the [`Ranged`] containing the node has been dropped or if the node
    /// has been removed. This can be checked with the [`is_valid`] method.
    ///
    /// [`is_valid`]: Self::is_valid
    pub fn size(&self) -> S::Idx {
        self.inner
            .upgrade()
            .expect("invalid node reference")
            .borrow()
            .as_node_ref()
            .size
    }

    /// (*Internal*) Collapses any redirection that might be present in a node that this one
    /// references
    fn collapse_redirects(&mut self) {
        let this_rc = self.inner.upgrade().unwrap();

        let mut initial_guard = this_rc.borrow_mut();

        // We keep `last` around so that we can remove it from the `RefSet` in the next node;
        // it'll be redirected with `final_overwrite`.
        //
        // In the case that `next` is our final node, we might just end up removing `last` and
        // adding it back when we add everything from `final_overwrite`.
        let (mut last, mut next) = match &mut *initial_guard {
            MaybeNode::Base(_) => return,
            MaybeNode::Temp => panic!("`NodeRef` points to temp node"),
            MaybeNode::Redirected(n, _) => (
                this_rc.clone(),
                n.inner.upgrade().expect("redirected to invalid node"),
            ),
        };

        // A list of all of the nodes that we traverse through in our redirection. For the most
        // part, we'll allow the destructors to run and clean this up, even though there might be
        // ways to do it that are more efficient.
        let mut traversed = vec![this_rc.clone()];

        // We need to eagerly drop `initial_guard` here; otherwise we run into borrowing conflicts
        // if we've added `this_rc` to `final_overwrite`.
        drop(initial_guard);

        loop {
            let next_weak = Rc::downgrade(&next);
            let mut guard = next.borrow_mut();
            match &mut *guard {
                MaybeNode::Base(_) => {
                    // For every node we've traversed, set it to point instead at the new value.
                    // We've already removed the strong references from their redirection, and so
                    // all that remains are the references in `traversed` -- we'll add those to
                    // `n.refs` in order to finalize the redirection.

                    // We need to temporarily give up our hold on `guard`. It could be the case
                    // that - in the course of dropping a `NodeRef` we overwrite - we need to
                    // remove some *other* reference from `next`.
                    //
                    // We'll re-acquire this after the loop.
                    drop(guard);

                    for rc in traversed.iter() {
                        println!("traversed[..] = {:p}", Rc::as_ptr(&rc));
                        match &mut *rc.borrow_mut() {
                            MaybeNode::Redirected(r, _) => {
                                *r = NodeRef {
                                    inner: next_weak.clone(),
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    *self = NodeRef { inner: next_weak };

                    let mut guard = next.borrow_mut();
                    let n = match &mut *guard {
                        MaybeNode::Base(n) => n,
                        _ => unreachable!(),
                    };
                    n.refs.set.extend(traversed.into_iter().map(RefSetItem));
                    return;
                }
                MaybeNode::Temp => panic!("`NodeRef` redirected to temp node"),
                MaybeNode::Redirected(n, refs) => {
                    traversed.push(next.clone());

                    refs.set.remove(&RefSetItem(last));
                    let new_next = n.inner.upgrade().expect("redirected to invalid node");
                    drop(guard);
                    last = next;
                    next = new_next;
                }
            }
        }
    }

    /// (*Internal*) Constructs a `NodeRef` from an owned reference to the `Node`
    fn from_owned(owned: &OwnedSNode<S>) -> Self {
        NodeRef {
            inner: owned.weak(),
        }
    }
}

/// (*Internal*) Singular, "owned" references to [`Node`]s for use only as child pointers in the
/// tree
///
/// This type is only used within the tree to represent child nodes. It's similar to the
/// publicly-exposd [`NodeRef`], but the guaranteed semantics are significantly different. While
/// `NodeRef` permits some redirection (and thus accessing takes a `&mut NodeRef` to overwrite the
/// pointer), we expect all `OwnedNode`s to have no redirection. The methods on this type therefore
/// reflect that difference.
struct OwnedNode<Acc, Idx, Delta, S> {
    inner: Rc<RefCell<MaybeNode<Acc, Idx, Delta, S>>>,
}

impl<Acc, Idx, Delta, S> Debug for OwnedNode<Acc, Idx, Delta, S>
where
    Acc: Debug,
    Idx: Debug,
    Delta: Debug,
    S: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // We're essentially implementing the debug info for `Node` here as well, because we want
        // to be able to give the correct address for the node.
        //
        // The reason we have to do this (and why we can't just use the &Node that gets passed to
        // `Debug`) is because the address given for Rc/Weak::as_ptr is offset from the address
        // inside of the `RefCell`. We could ignore that and output addresses that aren't *quite*
        // right, but it's not worth the possibility of getting all confused about why the
        // addresses are slightly off (again).

        let this = self.get();
        f.debug_struct("Node")
            .field("<addr>", &DebugPtr(Rc::as_ptr(&self.inner)))
            .field(
                "parent",
                &this.parent.as_ref().map(|p| DebugPtr(p.as_ptr())),
            )
            .field("refs", &this.refs)
            .field("offset_from_parent", &this.offset_from_parent)
            .field("size", &this.size)
            .field("val", &this.val)
            .field("acc", &this.acc)
            .field("total_accumulated", &this.total_accumulated)
            .field("left", &this.left)
            .field("right", &this.right)
            .finish()
    }
}

// Helper type for `OwnedNode::get`. It's extracted out here because it's... a bit big.
type OwnedNodeRef<'r, Acc, Idx, Delta, S> = MappedGuard<
    cell::Ref<'r, MaybeNode<Acc, Idx, Delta, S>>,
    fn(&MaybeNode<Acc, Idx, Delta, S>) -> &Node<Acc, Idx, Delta, S>,
>;

impl<Acc, Idx, Delta, S> OwnedNode<Acc, Idx, Delta, S> {
    /// Creates a new `OwnedNode` from the given `Node`
    fn new(node: Node<Acc, Idx, Delta, S>) -> Self {
        OwnedNode {
            inner: Rc::new(RefCell::new(MaybeNode::Base(node))),
        }
    }

    /// Creates a new, temporary `OwnedNode` that can be set by [`set_temp`].
    ///
    /// [`set_temp`]: Self::set_temp
    fn temporary() -> Self {
        OwnedNode {
            inner: Rc::new(RefCell::new(MaybeNode::Temp)),
        }
    }

    /// Sets the value of a temporary node (created by [`temporary`])
    ///
    /// [`temporary`]: Self::temporary
    fn set_temp(&mut self, node: Node<Acc, Idx, Delta, S>) {
        let mut guard = self.inner.borrow_mut();

        match &*guard {
            MaybeNode::Temp => (),
            _ => panic!("called `OwnedNode::set_temp` on non-temp node"),
        }

        *guard = MaybeNode::Base(node);
    }

    /// Performs a "shallow" clone of the reference, returning another `OwnedNode` pointing to the
    /// same allocation
    fn shallow_clone(&self) -> Self {
        OwnedNode {
            inner: self.inner.clone(),
        }
    }

    /// Returns a weak reference to the underlying allocation. Analagous to [`Rc::downgrade`].
    fn weak(&self) -> Weak<RefCell<MaybeNode<Acc, Idx, Delta, S>>> {
        Rc::downgrade(&self.inner)
    }

    /// Provides a reference to the inner [`Node`]
    ///
    /// We can't return `impl Deref` here because usage in `Ranged::iter` requires being able to
    /// name the type.
    #[track_caller]
    fn get<'a>(&'a self) -> OwnedNodeRef<'a, Acc, Idx, Delta, S> {
        let guard = self.inner.borrow();

        // We could just directly map the guard, but it's better to panic early if we're given bad
        // input, so we check that first.
        match &*guard {
            MaybeNode::Base(_) => guard.map_guard(MaybeNode::as_node_ref),
            MaybeNode::Redirected(_, _) => panic!("called `get` on `Redirected` node"),
            MaybeNode::Temp => panic!("called `get` on `Temp` node"),
        }
    }

    /// Provides a mutable reference to the inner [`Node`]
    #[track_caller]
    fn get_mut<'a>(&'a mut self) -> impl 'a + DerefMut<Target = Node<Acc, Idx, Delta, S>> {
        let guard = self.inner.borrow_mut();

        // We could just directly map the guard, but it's better to panic early if we're given bad
        // input, so we check that first.
        match &*guard {
            MaybeNode::Base(_) => {
                guard.map_mut_guard(MaybeNode::as_node_ref, MaybeNode::as_node_mut)
            }
            MaybeNode::Redirected(_, _) => panic!("called `get_mut` on `Redirected` node"),
            MaybeNode::Temp => panic!("called `get_mut` on `Temp` node"),
        }
    }

    /// Extracts the inner [`Node`], replacing it with a [`MaybeNode::Temp`]
    ///
    /// Taking the value out of the node puts it in an invalid state. Before using any other
    /// methods, *some* value must be returned with the [`set`] method.
    ///
    /// ## Panics
    ///
    /// This method panics if the current value of the node is not `MaybeNode::Base`.
    ///
    /// [`set`]: Self::set
    #[track_caller]
    fn take(&mut self) -> Node<Acc, Idx, Delta, S> {
        match self.inner.replace(MaybeNode::Temp) {
            MaybeNode::Base(n) => n,
            MaybeNode::Redirected(_, _) => panic!("called `take` on `Redirected` node"),
            MaybeNode::Temp => panic!("called `take` on `Temp` node"),
        }
    }

    /// Sets the value of the inner [`Node`]; the counterpart to [`take`]
    ///
    /// ## Panics
    ///
    /// This method panics if the current value of the node is not `MaybeNode::Temp`.
    ///
    /// [`take`]: Self::take
    fn set(&mut self, node: MaybeNode<Acc, Idx, Delta, S>) {
        match self.inner.replace(node) {
            MaybeNode::Temp => (),
            MaybeNode::Redirected(_, _) => panic!("called `set` on `Redirected` node"),
            MaybeNode::Base(_) => panic!("called `set` on `Base` node"),
        }
    }

    /// Helper method for mapping an `Option<OwnedNode>` to `Option<&Node>`
    ///
    /// ## Panics
    ///
    /// This method panics if the node is in an invalid state, as described by [`get`].
    ///
    /// [`get`]: Self::get
    fn map_ref(this: &Option<Self>) -> Option<impl '_ + Deref<Target = Node<Acc, Idx, Delta, S>>> {
        this.as_ref().map(Self::get)
    }

    /// Helper method for mapping an `Option<OwnedNode>` to `Option<&mut Node>`
    ///
    /// Technically speaking, we don't actually need `this` to be a mutable reference, because
    /// everything's behind `RefCell`s anyways. But there's utility in opting-in to the borrow
    /// checking that `RefCell`s allow us to ignore, so that's why we have this.
    ///
    /// ## Panics
    ///
    /// This method panics if the node is in an invalid state, as described by [`get_mut`].
    ///
    /// [`get_mut`]: Self::get_mut
    fn map_mut(
        this: &mut Option<Self>,
    ) -> Option<impl '_ + DerefMut<Target = Node<Acc, Idx, Delta, S>>> {
        this.as_mut().map(Self::get_mut)
    }
}

/// (*Internal*) The representation of a node that's expected to be present
///
/// We use this type to support all of the different operations that we've already described at
/// length, in the documentation of [`NodeRef`]. Briefly: in most cases, accessing the inner node
/// will be done simply with `MaybeNode::Base`. If a node is joined with another, the removed node
/// is replaced by `MaybeNode::Redirected` to give access to the new node.
///
/// Under certain conditions, we also replace the value with `Temp` in order to temporarily take
/// ownership of the underlying `Node`, e.g. to pass the underlying `AccumulatorSlice` by value to
/// some other method.
enum MaybeNode<Acc, Idx, Delta, S> {
    // The actual node itself
    Base(Node<Acc, Idx, Delta, S>),
    // A node that has since been joined with another; this reference now gives the address of that
    // node.
    //
    // Note that, to keep with the restrictions on `NodeRef` in its internal documentation, the
    // node that we have a reference to here *also* contains a pointer to this value in its
    // `RefSet`.
    Redirected(NodeRef<Acc, Idx, Delta, S>, RefSet<Acc, Idx, Delta, S>),
    // A temporary value that's sometimes used in order to take ownership over the contents of a
    // `Node` without requiring any memory-unsafe operations.
    Temp,
}

// A `RefSet` is our method of storing the set of redirected nodes that are pointing at this one,
// so that they cannot be dropped with `NodeRef`s pointing to them
struct RefSet<Acc, Idx, Delta, S> {
    set: BTreeSet<RefSetItem<MaybeNode<Acc, Idx, Delta, S>>>,
}

impl<Acc, Idx, Delta, S> Debug for RefSet<Acc, Idx, Delta, S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut map = f.debug_map();
        for it in &self.set {
            map.key(&DebugPtr(Rc::as_ptr(&it.0))).value(it);
        }
        map.finish()
    }
}

impl<Acc, Idx, Delta, S> Default for RefSet<Acc, Idx, Delta, S> {
    fn default() -> Self {
        RefSet {
            set: BTreeSet::new(),
        }
    }
}

// A single item in a `RefSet`.
//
// This is a newtype so that we can have a special implementation of `Ord` that simply compares the
// addresses of the pointers.
struct RefSetItem<N>(Rc<RefCell<N>>);

impl<Acc, Idx, Delta, S> Debug for RefSetItem<MaybeNode<Acc, Idx, Delta, S>> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        struct Dbg<T>(T);

        impl<'a, Acc, Idx, Delta, S> Debug for Dbg<&'a Rc<RefCell<MaybeNode<Acc, Idx, Delta, S>>>> {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                let guard = self.0.borrow();

                match &*guard {
                    MaybeNode::Temp => f.write_str("Temp"),
                    MaybeNode::Base(_) => f.write_str("Base(_)"),
                    MaybeNode::Redirected(node_ref, refs) => f
                        .debug_struct("Redirected")
                        .field("to", &DebugPtr(node_ref.inner.as_ptr()))
                        .field("refs", refs)
                        .finish(),
                }
            }
        }

        Dbg(&self.0).fmt(f)
    }
}

impl<N> PartialEq for RefSetItem<N> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl<N> Eq for RefSetItem<N> {}

impl<N> PartialOrd for RefSetItem<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<N> Ord for RefSetItem<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        // The inner type of `self.0` is `Rc<RefCell<N>>`, so we want to compare the references to
        // the `RefCell<N>`.
        ((&*self.0) as *const RefCell<N>).cmp(&((&*other.0) as *const RefCell<N>))
    }
}

impl<Acc, Idx, Delta, S> MaybeNode<Acc, Idx, Delta, S> {
    /// Returns a reference to the underlying `Node`, assuming that this is a `MaybeNode::Base`
    ///
    /// ## Panics
    ///
    /// This method *assumes* that the value is a `MaybeNode::Base`. It will still panic if that is
    /// not the case, but does not make it particularly informative.
    fn as_node_ref(&self) -> &Node<Acc, Idx, Delta, S> {
        match self {
            MaybeNode::Base(n) => n,
            _ => unreachable!(),
        }
    }

    /// Returns a mutable reference to the underlyig `Node`, assuming that this is a
    /// `MaybeNode::Base`
    ///
    /// ## Panics
    ///
    /// This method *assumes* that the value is a `MaybeNode::Base`. It will still panic if that is
    /// not the case, but does not make it particularly informative.
    fn as_node_mut(&mut self) -> &mut Node<Acc, Idx, Delta, S> {
        match self {
            MaybeNode::Base(n) => n,
            _ => unreachable!(),
        }
    }
}

/// (*Internal*) Helper type alias for the type of pointers to a parent node
type ParentPointer<Acc, Idx, Delta, S> = Weak<RefCell<MaybeNode<Acc, Idx, Delta, S>>>;

/// (*Internal*) An individual node in the [`Ranged`] splay tree
struct Node<Acc, Idx, Delta, S> {
    left: Option<OwnedNode<Acc, Idx, Delta, S>>,
    right: Option<OwnedNode<Acc, Idx, Delta, S>>,

    // All of the external `NodeRef`s that are referencing this node
    refs: RefSet<Acc, Idx, Delta, S>,

    // The parent of this node, if it exists. We only use a `Weak` here in order to allow
    // deallocation; the reference should always be valid.
    //
    // Additionally, the `MaybeNode` will always be `MaybeNode::Base`
    parent: Option<ParentPointer<Acc, Idx, Delta, S>>,
    // The offset from this node's parent, if it exists. If this node has no parent, then
    // `offset_from_parent` corresponds to the absolute position of the node.
    offset_from_parent: Delta,

    // The size of the range contained by this node -- not including `left` or `right`.
    size: Idx,
    // The `AccumulatorSlice` itself
    val: S,
    // The accumulated value across the full range
    acc: Acc,

    // The total accumulated value from `acc` and both the left and right subtree.
    // Essentially: left.total_accumulated + acc + right.total_accumulated
    total_accumulated: Acc,
}

impl<Acc, Idx, Delta, S> OwnedNode<Acc, Idx, Delta, S>
where
    Acc: Clone,
    Idx: Clone,
    Delta: Clone,
    S: Clone,
{
    /// Creates a "deep clone" of the `Node`, copying the entire subtree rooted at the node with
    /// fresh allocations
    ///
    /// This method is only intended to be called from within the implementation of [`Clone`] for
    /// [`Ranged`] (or recursively, as part of this method).
    ///
    /// Because of the way this method uses itself, `parent` is not expected to point to a valid
    /// node at first (i.e. it may be a `Temp` node).
    fn deep_clone(&self, parent: Option<ParentPointer<Acc, Idx, Delta, S>>) -> Self {
        // We start by creating a temporary node to pass as a parent pointer.
        //
        // After cloning the left and right subtrees, we replace the actual contents of the node.
        let mut new = OwnedNode::temporary();
        let this_ptr = Some(new.weak());

        let this = self.get();

        // Actually clone the node. We don't have to worry about borrow conflicts with `new`
        // because cloning children doesn't actually access the parent pointer.
        new.set_temp(Node {
            left: this.left.as_ref().map(|n| n.deep_clone(this_ptr.clone())),
            right: this.right.as_ref().map(|n| n.deep_clone(this_ptr)),
            // Note: `refs` is empty because the cloned node is fundamentally a different node --
            // references to it *shouldn't* transfer.
            refs: RefSet::default(),
            parent,
            // In general, setting `offset_from_parent` to the same is correct. Because cloning
            // `OwnedNode`s never exists in a vacuum -- it's always as part of another call to
            // `deep_clone` or cloning the tree itself.
            offset_from_parent: this.offset_from_parent.clone(),
            size: this.size.clone(),
            val: this.val.clone(),
            acc: this.acc.clone(),
            total_accumulated: this.total_accumulated.clone(),
        });

        new
    }
}

/// An abstraction over values that can represent a single region in a [`Ranged`]
///
/// ## Why does this trait exist?
///
/// When using a [`Ranged`], it's sometimes the case that the values stored in an individual range
/// have some predictable variance (like an increasing counter for each element, for example). We
/// still want to be able to have the benefits of [`Ranged`] when these variations are known
/// beforehand, so this trait provides a layer of abstraction over indexing, splitting, and joining
/// ranges -- as well as a few other things.
///
/// ## Accumulation
///
/// This is a feature that only makes sense in certain contexts. For example: in a [`TextTree`], we
/// want to have a way to go from byte indexes to line numbers. Our implementation of
/// `AccumulatorSlice` there treats each slice as some number of lines, with the accumulator
/// counting the number of lines before each slice.
///
/// Fetching the accumulated value at a point is done with the [`accumulated_at`] method on
/// [`Ranged`].
///
/// [`TextTree`]: crate::text::objects::TextTree
/// [`accumulated_at`]: Ranged::accumulated_at
pub trait AccumulatorSlice: Sized {
    /// Representation of an index, used both for the starting position of a slice and an index
    /// within it
    type Idx: RangedIndex;

    /// The value provided by indexing
    ///
    /// It may not always make sense to provide an indexed value; in these cases, the [`NoIndex`]
    /// type is provided as an empty type to make this explicit.
    ///
    /// [`NoIndex`]: super::NoIndex
    type IndexedValue: Sized;

    /// Returns the value at the given offset `idx` inside of the slice
    ///
    /// The absolute position of the start of the slice is provided as `base_idx`.
    fn index(&self, base_idx: Self::Idx, idx: Self::Idx) -> Self::IndexedValue;

    /// An accumulator for values
    ///
    /// If your implementation of `AccumulatorSlice` does not need an accumulator, you may wish to
    /// provide [`NoAccumulator`] here; it is a unit type that provides dummy implementations of
    /// the required traits.
    ///
    /// ## Precise usage semantics
    ///
    /// The implementation of `AddAssign` on the accumulator need not be commutative, though it
    /// must be associative. In other words, `x + y` can be different from `y + x`, but
    /// `x + (y + z)` should always be the same as `(x + y) + z`. All usage of this implementation
    /// will `add_assign` to the accumulator from a lower index. Usage of `SubAssign` will
    /// similarly only subtract the first or last portion of an accumulated range -- i.e. for any
    /// accumulated value over the range `i..k`, we'll only ever subtract an accumulator over
    /// `i..j` or `j..k` from it, with `i <= j < k`.
    ///
    /// The value provided by `Default` should be the identity and valid in any position relative
    /// to a value it's being added to.
    ///
    /// These features don't typically matter, but it becomes relevant for certain accumulators --
    /// like the implementation of [`RelativeSet`], for example.
    ///
    /// [`NoAccumulator`]: super::NoAccumulator
    type Accumulator: Default + Clone + AddAssign + SubAssign;

    /// Returns the value of `Self::Accumulator` that is present at a point within the slice
    ///
    /// Note that this method should be compatible with `split`. Essentially, that for any slice
    /// and index within it:
    /// ```
    /// let original_acc = slice.accumulated(len);
    /// let rhs = slice.split(idx);
    /// assert!(original_acc == slice.accumulated(idx) + rhs.accumulated(len - idx));
    /// ```
    ///
    /// It may be the case that `idx` is equal to the length of the slice.
    ///
    /// As an example, we we might have an implementation of `AccumulatorSlice` tracking the number of
    /// newlines, which would simply return the number of lines corresponding to the slice.
    fn accumulated(&self, base_idx: Self::Idx, idx: Self::Idx) -> Self::Accumulator;

    /// Returns the index within the slice at which the accumulated value occurs
    ///
    /// If `index_of_accumulated(base, acc)` returns some `idx`, it must always be the case that
    /// `accumulated(base, idx)` returns the original `acc`. This relation is not required the
    /// other way around.
    ///
    /// The returned index may be equal to at most the size of the slice.
    fn index_of_accumulated(&self, base_idx: Self::Idx, acc: Self::Accumulator) -> Self::Idx;

    /// Cuts the range in two at the given index, returning the upper half
    ///
    /// This is analogous to [`slice::split_at`], but instead modifies the receiver and returns
    /// only the second half of the tuple. As such, after calling this method, `self` should
    /// correspond to `[0, idx)` in the starting range, and the returned value should be
    /// `[idx, len)`.
    ///
    /// The `base` index gives the starting index of *this* range in the full tree, with the
    /// desired splitting point at exactly `base + idx` in the tree.
    ///
    /// ## Guarantees
    ///
    /// This method is never called with `idx = 0` or `idx = size`. This should not be assumed in
    /// an unsafe way, but this method may panic if that is the case.
    fn split_at(&mut self, base_idx: Self::Idx, idx: Self::Idx) -> Self;

    /// Attempts to join the two ranges, returning the original pair as given if unable to
    ///
    /// The values provided are always such that the position of `self` is immediately before
    /// `other`.
    ///
    /// It will often be the case that implementing this function is not required for correct
    /// behavior; the default implementation just returns `Err((self, other))`. It does, however,
    /// tend to ensure that the tree remains smaller.
    fn try_join(self, other: Self) -> Result<Self, (Self, Self)> {
        Err((self, other))
    }
}

// Helper type alias for talking about owned nodes, because they have many type parameters
//
// The reason we have <S as AccumulatorSlice> throughout instead of S: AccumulatorSlice at the
// beginning is because the compiler gives us a warning otherwise:
//   warning: bounds on generic parameters are not enforced in type aliases
//     ...
//   help: the bound will not be checked when the type alias is used, and should be removed
// We're sacrificing a little cleanliness to get rid of warnings.
type OwnedSNode<S> = OwnedNode<
    <S as AccumulatorSlice>::Accumulator,
    <S as AccumulatorSlice>::Idx,
    <<S as AccumulatorSlice>::Idx as RangedIndex>::Delta,
    S,
>;

// Same as `OwnedSNode`, but for the nodes themselves.
type SNode<S> = Node<
    <S as AccumulatorSlice>::Accumulator,
    <S as AccumulatorSlice>::Idx,
    <<S as AccumulatorSlice>::Idx as RangedIndex>::Delta,
    S,
>;

impl<S> Ranged<S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S>
where
    S: AccumulatorSlice,
    S::Idx: Debug,
{
    /// Creates a new `Ranged` with the given size and initial filled range
    ///
    /// Explicitly constructing a `Ranged` with a size of zero is best done with the [`new_empty`]
    /// method, which is internally called by this method when applicable.
    ///
    /// [`new_empty`]: Self::new_empty
    pub fn new(init: S, size: S::Idx) -> Self {
        // In general, we expect that node sizes are non-zero. We need to explicitly check for that
        // here to ensure that we don't mess up the tree as a result.
        if size == S::Idx::ZERO {
            return Self::new_empty();
        }

        let acc = init.accumulated(S::Idx::ZERO, size);

        Ranged {
            size,
            root: Some(OwnedNode::new(Node {
                left: None,
                right: None,
                refs: RefSet::default(),
                parent: None,
                offset_from_parent: S::Idx::ZERO_DELTA,
                size,
                val: init,
                acc: acc.clone(),
                total_accumulated: acc,
            })),
            default_acc: Some(S::Accumulator::default()),
        }
    }

    /// Creates a new `Ranged` with a size of zero
    ///
    /// To create a `Ranged` with a non-zero initial size, see [`Ranged::new`].
    pub fn new_empty() -> Self {
        Ranged {
            size: S::Idx::ZERO,
            root: None,
            default_acc: Some(S::Accumulator::default()),
        }
    }

    /// Returns the length of the set of values this represents -- i.e the smallest index we don't
    /// have a value for
    pub fn size(&self) -> S::Idx {
        self.size
    }

    // Provides an immutable reference to the root node
    fn root(&self) -> impl '_ + Deref<Target = SNode<S>> {
        #[cfg(debug_assertions)]
        if self.size == S::Idx::ZERO {
            panic!("cannot get root node while tree is empty");
        }

        self.root
            .as_ref()
            .expect("root node is in invalid state")
            .get()
    }

    // Provides a mutable guard for the contents of the root node
    fn root_mut(&mut self) -> impl '_ + DerefMut<Target = SNode<S>> {
        #[cfg(debug_assertions)]
        if self.size == S::Idx::ZERO {
            panic!("cannot get root node while tree is empty");
        }

        self.root
            .as_mut()
            .expect("root node is in invalid state")
            .get_mut()
    }

    // Returns an immutable reference to the `OwnedNode` at the root of the tree, panicking if the
    // tree is empty.
    fn root_ref(&self) -> &OwnedSNode<S> {
        #[cfg(debug_assertions)]
        if self.size == S::Idx::ZERO {
            panic!("cannot get root node while tree is empty");
        }

        self.root.as_ref().expect("root node is in invalid state")
    }

    // Returns a mutable reference to the `OwnedNode` at the root of the tree, panicking if the
    // tree is empty.
    fn root_ref_mut(&mut self) -> &mut OwnedSNode<S> {
        #[cfg(debug_assertions)]
        if self.size == S::Idx::ZERO {
            panic!("cannot get root node while tree is empty");
        }

        self.root.as_mut().expect("root node is in invalid state")
    }

    // Returns whether the root node contains the given index
    fn root_contains(&self, idx: S::Idx) -> bool {
        // If the tree is empty, we don't contain the index
        if self.root.is_none() {
            return false;
        }

        let start = self.root_pos();
        let end = start.add(self.root().size);

        (start..end).contains(&idx)
    }

    // Returns the position of the root node
    fn root_pos(&self) -> S::Idx {
        if self.root.is_none() {
            debug_assert!(self.size == S::Idx::ZERO);
            self.size
        } else {
            S::Idx::from_delta(self.root().offset_from_parent)
        }
    }

    /// (*Internal*) Replaces `self` with `Self::new_empty()` in order to tempoarily provide
    /// ownership of the existing value
    ///
    /// The replacement value is not unsafe in any way; remaining operations may simply fail if
    /// `self` is left in that state.
    #[rustfmt::skip]
    fn temp_extract(&mut self) -> Self {
        mem::replace(self, Self::new_empty())
    }

    /// Inserts the slice with the given size into the tree at the index
    ///
    /// This is a convenience function; its definition is simply:
    ///
    /// ```ignore
    /// // Given: index, size, values
    /// let insertion = Ranged::new(values, size);
    /// self.replace(index..index, insertion);
    /// ```
    ///
    /// ## Panics
    ///
    /// This method can panic under certain conditions. These are given in the documentation for
    /// [`replace`].
    ///
    /// [`replace`]: Self::replace
    pub fn insert(&mut self, index: S::Idx, size: S::Idx, values: S) {
        let insertion = Ranged::new(values, size);
        self.replace(index..index, insertion);
    }

    /// Inserts the slice, returning a reference to the inserted values
    ///
    /// If `size` is zero, the returned [`NodeRef`] will always be invalid.
    ///
    /// For more information, refer to [`insert`](Self::insert) and [`NodeRef`].
    pub fn insert_ref(
        &mut self,
        index: S::Idx,
        size: S::Idx,
        values: S,
    ) -> NodeRef<S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S> {
        let insertion = Ranged::new(values, size);
        let weak = insertion
            .root
            .as_ref()
            .map(OwnedNode::weak)
            .unwrap_or_else(Weak::new);

        self.replace(index..index, insertion);

        NodeRef { inner: weak }
    }

    /// Replaces the given range with a new set of values, shifting all later indexes by the
    /// appropriate amount
    ///
    /// This operation replaces the values within a given range with the ones provided by the new
    /// `Ranged`, returning the previous values that were there. The range being replaced need not
    /// have the same size as the values inserted.
    ///
    /// ## Panics
    ///
    /// This method panics under a couple conditions:
    /// * if `range.start` is greater than `range.end`,
    /// * if `range.end` is greater than `self.size()`, or
    /// * if the size after insertion would be greater than `usize::MAX / 2` (or whatever the
    ///   chosen maximum for `Idx` is)
    // @req "Ranged::replace requires less than usize::MAX / 2" v0
    pub fn replace(&mut self, range: Range<S::Idx>, values: Self) -> Self {
        let mut previous = None;
        self.replace_with(range, |p| {
            previous = Some(p);
            values
        });
        previous.unwrap()
    }

    /// A version of [`Ranged::replace`] that allows replacement to be constructed from the values
    /// being replaced.
    ///
    /// There are certain cases where this is useful. To use a trivial example, this method allows
    /// the following to be rewritten to use only one `replace` operation instead of two:
    /// ```
    /// # #[derive(PartialEq, Eq)] struct MyWrapper;
    /// # impl MyWrapper { fn from<T>(val: T) -> Self { MyWrapper } }
    /// #
    /// # let mut r = StdRanged::new(Constant(None), 10);
    /// // Extract the values from that range
    /// let new_val = ranged.replace(3..6, StdRanged::new(Constant(None), 3));
    /// // And then use them to create the new ones
    /// ranged.replace(3..6, StdRanged::new(Constant(MyWrapper::from(new_val)), 4));
    /// ```
    /// But we can rewrite this as:
    /// ```
    /// # #[derive(PartialEq, Eq)] struct MyWrapper;
    /// # impl MyWrapper { fn from<T>(val: T) -> Self { MyWrapper } }
    /// #
    /// # let mut ranged = Ranged::new(Constant(None), 10);
    /// ranged.replace_with(3..6, |vs| StdRanged::new(Constant(MyWrapper::from(vs)), 4));
    /// ```
    ///
    /// ## Panics
    ///
    /// This has the same panic conditions as [`replace`](Self::replace).
    pub fn replace_with(&mut self, range: Range<S::Idx>, func: impl FnOnce(Self) -> Self) {
        if range.start > range.end {
            panic!("invalid range {:?}..{:?}", range.start, range.end);
        } else if range.end > self.size {
            panic!(
                "index out of bounds: range.end {:?} >= size {:?}",
                range.end, self.size
            );
        }

        debug_assert!((self.size == S::Idx::ZERO) == self.root.is_none());

        // The rest of this function will assume that we have a `root` we can extract from. If
        // that's not the case, then we should just return quickly.
        if self.root.is_none() {
            // We already know that `self` empty; there's no use trying to extract out the specific
            // value in `self` to pass to `func` if `new_empty()` will do just as well.
            *self = func(Self::new_empty());
            return;
        }

        // Temp value, storing the default accumulator. We move it out of self so that we can hold
        // references to `self.root_mut()` across modifying this value.
        //
        // We'll put it back at the end:
        //   @req "Ranged::replace_with re-set self.default_acc at end" v0
        let mut default_acc = self.default_acc.take();
        debug_assert!(default_acc.is_some());

        // The expected sizes of the regions to the left and right of the range, stored for later
        // so that we can accurately re-build the final `Ranged`
        let left_size = range.start;
        let right_size = self.size.sub(range.end);

        // Extract the values from before the range:
        Self::splay(self.root_ref_mut(), range.start, &mut default_acc);

        // We always set `left.offset_from_parent` to be equal to `-left.size`, which will be
        // correct if it's being added to an existing root node.
        let mut left = if range.start == S::Idx::ZERO {
            None
        } else if range.start == self.size {
            // If the range *starts* at the end of the set of values, then we can just take the
            // entire root as `left`. We'll have to check for this later.
            self.size = S::Idx::ZERO;
            self.root.take().map(|mut n| {
                let mut g = n.get_mut();
                // left.offset_from_parent = -left_size; -- as given above
                g.offset_from_parent = S::Idx::delta_from(S::Idx::ZERO, g.size);
                drop(g);
                n
            })
        } else if self.root_contains(range.start.decrement()) {
            // If the node containing `range.start` has other values beneath it, then we need to
            // split the range.
            //
            // |-------- root --------|
            //               |---- range ----|
            // |- left_size -|

            let root_pos = self.root_pos();

            let mut sub_left = self.root_mut().left.take();
            let left_size = range.start.sub(self.root_pos());

            self.size.sub_assign(range.start);
            let mut root = self.root_mut();
            root.size.sub_assign(left_size);

            // we set offset_from_parent to zero here because we just removed all of the nodes up
            // to range.start
            root.offset_from_parent = S::Idx::ZERO_DELTA;

            // Because we're removing part of the root, we need to shift the location of
            // root.right:
            if let Some(mut n) = OwnedNode::map_mut(&mut root.right) {
                S::Idx::delta_sub_assign_idx(&mut n.offset_from_parent, left_size);
            }

            // Split the left off from the root:
            let mut left_val = root.val.split_at(root_pos, left_size);
            mem::swap(&mut left_val, &mut root.val);
            // Transfer all of the node references to the new left node
            let left_refs = mem::take(&mut root.refs);

            // Acknowledge that we've taken some of the accumulated value out of the root - we're
            // putting it into `lhs_acc`.
            let lhs_acc = left_val.accumulated(root_pos, left_size);
            root.acc -= lhs_acc.clone();

            let mut lhs_total_accumulated = lhs_acc.clone();

            let mut temp_return = OwnedNode::temporary();

            if let Some(mut l) = OwnedNode::map_mut(&mut sub_left) {
                // > lhs_accumulated += l.total_accumulated.clone();
                Self::add_acc(
                    l.total_accumulated.clone(),
                    &mut lhs_total_accumulated,
                    &mut default_acc,
                );
                l.parent = Some(temp_return.weak());
            }
            root.total_accumulated -= lhs_total_accumulated.clone();

            // offset_from_parent = -left_size
            let mut offset_from_parent = S::Idx::ZERO_DELTA;
            S::Idx::delta_sub_assign_idx(&mut offset_from_parent, left_size);

            temp_return.set_temp(Node {
                left: sub_left,
                right: None,
                refs: left_refs,
                // We don't know what the new root will be, so we leave this as `None` for the time
                // being. If we end up placing this as the new root, `None` will be correct.
                // Otherwise, we'll have to set the parent anyways.
                parent: None,
                offset_from_parent,
                size: left_size,
                val: left_val,
                acc: lhs_acc,
                total_accumulated: lhs_total_accumulated,
            });

            Some(temp_return)
        } else {
            // This branch corresponds to the case where `range.start` is aligned with the starting
            // index of a node. We want to leave `self` containing the set of values corresonding
            // to `range`, so we extract out the left-hand side, which we know corresponds to
            // indexes below `range.start`.
            self.size.sub_assign(self.root_pos());
            let mut root = self.root_mut();
            root.offset_from_parent = S::Idx::ZERO_DELTA;

            root.left.take().map(|mut n| {
                let mut g = n.get_mut();
                root.total_accumulated -= g.total_accumulated.clone();
                g.parent = None;
                drop(g);
                n
            })
        };

        // We just shifted everything by removing the nodes up to `range.start`. We'll store the
        // "new" end index in `end`, even though it's just the length of the range.
        let end = range.end.sub(range.start);

        // It's possible that the operation to get `left` removed the root. If that's the case,
        // then we can't do any more accessing to get the `right`; we'll have to skip this part.
        let mut right = None;

        if self.root.is_some() {
            // Extract the values from after the range
            Self::splay(self.root_ref_mut(), end, &mut default_acc);

            right = if end == self.size {
                None
            } else if end == S::Idx::ZERO {
                // If the range has length zero, then we want to take the entire root node `right`.
                self.size = S::Idx::ZERO;
                // Because the value of `right.offset_from_parent` will always depend on the size
                // of the root node it's being assigned to, we'll just set it to zero. We'll use
                // this fact later.
                self.root.take().map(|mut n| {
                    n.get_mut().offset_from_parent = S::Idx::ZERO_DELTA;
                    n
                })
            } else if self.root_contains(end.decrement()) {
                let mut sub_right = self.root_mut().right.take();

                // self.root_pos()
                //       |--------- root node ----------|
                // |------- range -------|
                //       |- rhs_in_node -|- right_size -|

                // In order to keep the tree valid, we previously *fully* removed the left-hand side of
                // the tree, so that the new "zero" is at the starting point of the range.
                let root_pos = self.root_pos().add(range.start);

                // right_size = self.root_pos() + self.root().pair.size - end
                let right_size = self.root_pos().add(self.root().size).sub(end);
                let mut root = self.root_mut();
                let rhs_in_node = root.size.sub(right_size);

                let rhs_val = root.val.split_at(root_pos, rhs_in_node);
                let rhs_acc = rhs_val.accumulated(root_pos.add(rhs_in_node), right_size);
                root.acc -= rhs_acc.clone();

                let mut rhs_total_accumulated = rhs_acc.clone();

                let mut temp_return = OwnedNode::temporary();

                if let Some(mut n) = OwnedNode::map_mut(&mut sub_right) {
                    S::Idx::delta_sub_assign_idx(&mut n.offset_from_parent, rhs_in_node);
                    rhs_total_accumulated += n.total_accumulated.clone();
                    n.parent = Some(temp_return.weak());
                }
                root.total_accumulated -= rhs_total_accumulated.clone();

                root.size = rhs_in_node;

                temp_return.set_temp(Node {
                    left: None,
                    right: sub_right,
                    refs: RefSet::default(),
                    // We'll set the parent later if we need to, once we know the new root
                    parent: None,
                    // The offset doesn't actually matter here - we just set it to zero as a
                    // temporary value.
                    offset_from_parent: S::Idx::ZERO_DELTA,
                    size: right_size,
                    val: rhs_val,
                    acc: rhs_acc,
                    total_accumulated: rhs_total_accumulated,
                });

                Some(temp_return)
            } else {
                // This branch corresponds to the case where the the index corresponding to the end
                // of the range occurs *just* beyond the current root.
                //
                // In this case, we've just splayed the tree so that the root contains the part
                // after the range that we want to remove. So we have to set the new root to
                // `self.root.left`, and adjust offsets to compensate.
                //
                // Thankfully, we happen to know that the root node *must* exist at this point, so
                // we at least have something to work with here. We also don't need to bother about
                // setting the size of `self`, because we're just about to do that below this
                // block.
                let mut root = self.root_mut();
                let lhs = root.left.take().map(|mut lhs| {
                    // Guard for lhs:
                    let mut l_g = lhs.get_mut();
                    // The new root's offset can be calculated based on the current root:
                    //
                    //    |---------- current root position ----------|
                    //    |>>>>>>>>>>>>>>> root offset >>>>>>>>>>>>>>>|--- root node ---|
                    //    |---- lhs position ----|<<<< lhs offset <<<<|
                    //                           |--- lhs node ---|
                    //
                    // We want to go from lhs.offset_from_parent = "lhs offset" to "lhs position",
                    // so we can just subtract the offset from the current root's position. In this
                    // case though, the offset is negative, so we're actually adding it.
                    S::Idx::delta_add_assign(&mut l_g.offset_from_parent, root.offset_from_parent);
                    root.total_accumulated -= l_g.total_accumulated.clone();
                    l_g.parent = None;
                    drop(l_g);
                    lhs
                });

                // For `root` itself, we promised above that all values of `right` will have
                // `offset_from_parent = 0`, so we need to set that now.
                root.offset_from_parent = S::Idx::ZERO_DELTA;

                // Then, just swap in `lhs` as the new root and return the right-hand side as
                // `right`.
                drop(root);
                mem::replace(&mut self.root, lhs)
            };
        }

        // Fully adjust the remaining size of the `Ranged`.
        self.size = range.end.sub(range.start);

        // `self` is now done. In order to get its replacement, we need to pass it by value. To do
        // this, we'll temporarily swap it out with a filler `Ranged`:
        *self = func(self.temp_extract());

        // @def "Ranged::replace requires less than usize::MAX / 2" v0
        if left_size.add(self.size()).add(right_size) >= S::Idx::MAX_SIZE {
            panic!(
                "`Ranged` would be too big! cannot represent a size larger than {}",
                S::Idx::max_size_debug_str(),
            );
        }

        // Having replaced `self`, we can now re-attach the subtrees on either side that we
        // previously extracted.

        // Add `left`:
        if let Some(root) = self.root.as_mut() {
            // We only actually want to modify the root if we have a `left` side to add back.
            // Otherwise, there isn't much to do.
            let mut maybe_guard = OwnedNode::map_mut(&mut left);
            if let Some(left_guard) = maybe_guard.as_mut() {
                // We have to add to the root position before calling `splay` in order for the base
                // indexes passed to calls to `AccumulatorSlice::accumulated` to be valid.
                //
                // Otherwise, this would really just be `Self::splay(root, 0, ..)`, in order to align the
                // tree so that there's nothing to the left of the root.
                S::Idx::delta_add_assign_idx(&mut root.get_mut().offset_from_parent, left_size);
                Self::splay(root, left_size, &mut default_acc);

                let root_weak_ref = root.weak();
                left_guard.parent = Some(root_weak_ref);

                let mut root_guard = root.get_mut();
                debug_assert!(root_guard.left.is_none());

                // > root.total_accumulated += left.total_accumulated.clone();
                Self::add_acc(
                    left_guard.total_accumulated.clone(),
                    &mut root_guard.total_accumulated,
                    &mut default_acc,
                );

                // Finally add `left` to the root:
                drop(maybe_guard);
                root_guard.left = left;
                drop(root_guard);
                self.size.add_assign(left_size);
                *self = self.temp_extract().try_join_left(&mut default_acc);
            }
        } else if let Some(mut left) = left {
            let mut left_guard = left.get_mut();

            // Because we're adding back `left` as the root node, we have to carefully update its
            // position. However `left` was previously extracted, it is the furthest-to-the-right
            // node in its subtree.
            //
            // We can therefore calculate its position by simply subtracting its size from the
            // previously-stored `left_size`:
            debug_assert!(left_guard.right.is_none());

            // delta_from(x, 0) = "convert x to type Delta"
            left_guard.offset_from_parent =
                S::Idx::delta_from(left_size.sub(left_guard.size), S::Idx::ZERO);
            drop(left_guard);
            self.size = left_size;
            self.root = Some(left);
        }

        // Add `right`:
        if let Some(root) = self.root.as_mut() {
            // Same deal as with `left`: we only need to do something if there is actually a right
            // node to add
            let mut maybe_guard = OwnedNode::map_mut(&mut right);
            if let Some(right_guard) = maybe_guard.as_mut() {
                let size = self.size;
                Self::splay(root, size, &mut default_acc);

                let root_weak_ref = root.weak();
                right_guard.parent = Some(root_weak_ref);

                let mut root_guard = root.get_mut();
                debug_assert!(root_guard.right.is_none());

                // right.offset_from_parent is always equal to zero, so this addition just sets it
                // equal to `root.pair.size`.
                S::Idx::delta_add_assign_idx(&mut right_guard.offset_from_parent, root_guard.size);
                root_guard.total_accumulated += right_guard.total_accumulated.clone();

                drop(maybe_guard);
                root_guard.right = right;
                drop(root_guard);
                self.size.add_assign(right_size);
                *self = self.temp_extract().try_join_right(&mut default_acc);
            }
        } else if let Some(mut right) = right {
            let mut right_guard = right.get_mut();

            // Similarly to adding left:
            // We know that `right` is the left-most node in its subtree. Because there isn't
            // already a root, we can just set its offset as zero, as it's now *globally* the
            // left-most node.
            debug_assert!(right_guard.left.is_none());
            right_guard.offset_from_parent = S::Idx::ZERO_DELTA;
            drop(right_guard);
            self.size = right_size;
            self.root = Some(right);
        }

        // And then we're done!
        // @def "Ranged::replace_with re-set self.default_acc at end" v0
        self.default_acc = default_acc;
    }

    /// (*Internal*)
    //
    // We pass in `default_acc` because this method is called at a point in `Ranged::replace_with`
    // where the accumulator is temporarily extracted outside of `self.default_acc`.
    fn try_join_left(mut self, default_acc: &mut Option<S::Accumulator>) -> Self {
        if self.root().left.is_none() {
            return self;
        }

        let root_pos = self.root_pos();

        // The first thing we're going to do is actually to splay the left-hand side individually
        // so that there isn't anything to the right of the left-hand node. This means that it'll
        // be easier to join the two because we won't need to search for a replacement.
        //
        // It's often going to be the case that, when this method is called, the left-hand node is
        // already going to be without any right child.
        let mut left: OwnedSNode<_> = self.root_mut().left.take().unwrap();

        if left.get().right.is_some() {
            // If there is a right subchild, we need to move it so that the highest index is at the
            // root.
            //
            // We also need to *temporarily* increase the offset for `left` in order to provide the
            // correct base indexes on calls to `AccumulatorSlice::accumulated`. After doing this,
            // we'll subtract the same `offset_from_parent` in order to reset this temporary
            // addition.
            S::Idx::delta_add_assign(
                &mut left.get_mut().offset_from_parent,
                self.root().offset_from_parent,
            );
            Self::splay(&mut left, root_pos.decrement(), &mut self.default_acc);

            let mut left_guard = left.get_mut();
            debug_assert!(left_guard.right.is_none());

            // And then return the (new) left node's offset to be relative to the root
            S::Idx::delta_sub_assign(
                &mut left_guard.offset_from_parent,
                self.root().offset_from_parent,
            )
        }

        let root_ref: &mut OwnedSNode<_> = self.root_ref_mut();

        let mut temp_root: SNode<_> = root_ref.take();
        let mut temp_left: SNode<_> = left.take();

        match temp_left.val.try_join(temp_root.val) {
            // If there's an error, we just put things back to where they were before
            Err((left_val, root_val)) => {
                temp_left.val = left_val;
                left.set(MaybeNode::Base(temp_left));

                temp_root.val = root_val;
                temp_root.left = Some(left);
                root_ref.set(MaybeNode::Base(temp_root));
            }
            // If they *do* join, we have to stick the nodes back together
            Ok(single) => {
                let left_size = temp_left.size;
                S::Idx::delta_sub_assign_idx(&mut temp_root.offset_from_parent, left_size);

                // Because we've shifted the position of the root back, we need to also need to
                // shift the right child
                if let Some(mut n) = OwnedNode::map_mut(&mut temp_root.right) {
                    S::Idx::delta_add_assign_idx(&mut n.offset_from_parent, left_size);
                }

                temp_root.size.add_assign(left_size);
                temp_root.val = single;
                Self::add_acc(temp_left.acc, &mut temp_root.acc, default_acc);

                temp_root.left = temp_left.left.map(|mut n| {
                    n.get_mut().parent = Some(root_ref.weak());
                    n
                });

                // Set up `left` as redirecting to `root` -- we need to ensure that any `NodeRef`s
                // that point to `left` will continue to function as intended.
                //
                // We only need to do this if there are existing `NodeRef`s to `left`, which we can
                // detect by the weak count. At this point, both of the node's children should be
                // dropped or `None`,
                if Rc::weak_count(&left.inner) != 0 {
                    debug_assert!(temp_left.right.is_none());

                    temp_root.refs.set.insert(RefSetItem(left.inner.clone()));
                    let root_node_ref = NodeRef::from_owned(&root_ref);
                    left.set(MaybeNode::Redirected(root_node_ref, temp_left.refs));
                }

                root_ref.set(MaybeNode::Base(temp_root));
            }
        }

        self
    }

    /// (*Internal*)
    fn try_join_right(mut self, default_acc: &mut Option<S::Accumulator>) -> Self {
        // This method is essentially the same as `try_join_left`, where the only changes are to
        // account for being to the right, not to the left of the root node. For a commentary on
        // the structure, refer to that method immediately above.

        if self.root().right.is_none() {
            return self;
        }

        let root_pos = self.root_pos();
        let mut right: OwnedSNode<_> = self.root_mut().right.take().unwrap();

        if right.get().left.is_some() {
            let root = self.root();
            S::Idx::delta_add_assign(
                &mut right.get_mut().offset_from_parent,
                root.offset_from_parent,
            );
            Self::splay(&mut right, root_pos.add(root.size), default_acc);

            let mut right_guard = right.get_mut();
            debug_assert!(right_guard.left.is_none());
            S::Idx::delta_sub_assign(&mut right_guard.offset_from_parent, root.offset_from_parent);
        }

        let root_ref: &mut OwnedSNode<_> = self.root_ref_mut();

        let mut temp_root: SNode<_> = root_ref.take();
        let mut temp_right: SNode<_> = right.take();

        match (temp_root.val).try_join(temp_right.val) {
            Err((root_val, right_val)) => {
                temp_right.val = right_val;
                right.set(MaybeNode::Base(temp_right));

                temp_root.val = root_val;
                temp_root.right = Some(right);
                root_ref.set(MaybeNode::Base(temp_root));
            }
            Ok(single) => {
                let root_size = temp_root.size;
                temp_root.size.add_assign(temp_right.size);
                temp_root.val = single;
                temp_root.acc.add_assign(temp_right.acc);

                temp_root.right = temp_right.right.map(|mut n| {
                    let mut guard = n.get_mut();
                    S::Idx::delta_add_assign_idx(&mut guard.offset_from_parent, root_size);
                    guard.parent = Some(root_ref.weak());
                    drop(guard);
                    n
                });

                if Rc::weak_count(&right.inner) != 0 {
                    debug_assert!(temp_right.left.is_none());

                    temp_root.refs.set.insert(RefSetItem(right.inner.clone()));
                    let root_node_ref = NodeRef::from_owned(&root_ref);
                    right.set(MaybeNode::Redirected(root_node_ref, temp_right.refs));
                }

                root_ref.set(MaybeNode::Base(temp_root));
            }
        }

        self
    }

    /// Creates an iterator over all of the ranges, in order
    ///
    /// This function can be used with [`clone_range`](Self::clone_range) to iterate over a smaller
    /// range.
    pub fn iter<'a>(
        &'a self,
    ) -> impl 'a + Iterator<Item = (impl 'a + Deref<Target = S>, Range<S::Idx>)> {
        struct Iter<'r, Acc, Idx, Delta, S> {
            // The root is `Some` only on the first iteration
            root: Option<OwnedNode<Acc, Idx, Delta, S>>,
            // Stack of nodes and their position
            stack: Vec<(Idx, OwnedNode<Acc, Idx, Delta, S>)>,
            // We attach a lifetime to the iterator in order to ensure that the structure of the
            // tree doesn't change out from underneath us
            marker: PhantomData<&'r ()>,
        }

        // Helper type for implmenting deref going `OwnedNode` -> `S`.
        //
        // This uses unsafety in the implementation, because `borrow` conceptually borrows from
        // `owned`, even though it is only accessing *through* `owned`.
        //
        // It's theoretically possible to implement this in safe rust, but only if you traverse the
        // entire tree to get to each referenced node. That solution would be O(n^2), which is
        // obviously not acceptable, unfortunately.
        //
        // So we're using this for now, though we may later create a custom `RefCell`
        // implementation that directly supports guards that go through common pointer types by
        // accessing their values each time. (TODO-ALG/TODO-FEATURE)
        //
        // We could also instead just include `borrow`: we know that the tree shouldn't change out
        // from underneath us, so we could embrace the unsafety even more and do away with all of
        // the refcounts. But... single-threaded refcounts are pretty fast anyways, and so it
        // probably wouldn't matter much.
        struct NodeDeref<'r, Acc, Idx, Delta, S> {
            owned: OwnedNode<Acc, Idx, Delta, S>,
            // Invariant: `borrow` always points to the same node as `owned`. Because `owned` has a
            // strong reference to the data, we know that `borrow` will remain valid at least as
            // long as `owned` is alive.
            borrow: OwnedNodeRef<'r, Acc, Idx, Delta, S>,
        }

        impl<'r, Acc, Idx, Delta, S> Deref for NodeDeref<'r, Acc, Idx, Delta, S> {
            type Target = S;

            fn deref(&self) -> &S {
                &self.borrow.val
            }
        }

        impl<'r, S> Iter<'r, S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S>
        where
            S: AccumulatorSlice,
            S::Idx: Debug,
        {
            fn push_lefts(
                &mut self,
                root_parent_pos: S::Idx,
                root: OwnedNode<S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S>,
            ) {
                let mut pos = root_parent_pos;
                let mut r = Some(root);
                while let Some(n) = r {
                    pos = Ranged::stack_pos(pos, &*n.get());
                    r = n.get().left.as_ref().map(|n| n.shallow_clone());
                    self.stack.push((pos, n));
                }
            }
        }

        impl<'r, S> Iterator for Iter<'r, S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S>
        where
            S: 'r + AccumulatorSlice,
            S::Idx: Debug,
        {
            type Item = (
                NodeDeref<'r, S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S>,
                Range<S::Idx>,
            );

            fn next(&mut self) -> Option<Self::Item> {
                if let Some(r) = self.root.take() {
                    self.push_lefts(S::Idx::ZERO, r);
                }

                match self.stack.pop() {
                    Some((pos, owned)) => {
                        let g = owned.get();
                        if let Some(r) = g.right.as_ref() {
                            self.push_lefts(pos, r.shallow_clone());
                        }

                        let range = pos..pos.add(g.size);
                        // SAFETY: We've described above, in the comments for `NodeDeref` why this
                        // has to be unsafe. This is simply lifetime extension, so that the
                        // original lifetime (which is tied to `owned`) doesn't get tied up when we
                        // try to place `borrow` into a struct alongside `owned`.
                        let borrow = unsafe {
                            mem::transmute::<OwnedNodeRef<_, _, _, _>, OwnedNodeRef<_, _, _, _>>(g)
                        };
                        Some((NodeDeref { owned, borrow }, range))
                    }
                    None => None,
                }
            }
        }

        let iter: Iter<'a, _, _, _, _> = Iter {
            root: self.root.as_ref().map(|n| n.shallow_clone()),
            stack: Vec::new(),
            marker: PhantomData,
        };

        iter
    }

    /// Returns the total value of the accumulator at the given index
    ///
    /// This is essentially the sum of all the accumulated values for slices that occur before
    /// `idx` - including the range of the slice containing `idx`.
    ///
    /// Accumulators are a pretty niche feature. They're primarily used for tracking things like
    /// line numbers by byte index, where there are relativeliy few lines compared to the number of
    /// bytes and we want to quickly go from one to the other.
    ///
    /// If you're curious to use them, they're heavily used as part of the implementation of
    /// [`TextTree`], and the internals are well-documented there.
    ///
    /// ## Panics
    ///
    /// This method will panic if the index is out of bounds.
    ///
    /// [`TextTree`]: crate::text::objects::TextTree
    pub fn accumulated_at(&mut self, mut idx: S::Idx) -> S::Accumulator {
        if idx > self.size() {
            panic!(
                "index out of bounds: the index is {:?} but the size is {:?}",
                idx,
                self.size()
            )
        } else if idx == S::Idx::ZERO {
            // Explicitly handle accumulation at index zero, in case we don't actually have a root.
            return S::Accumulator::default();
        }

        Self::splay(self.root.as_mut().unwrap(), idx, &mut self.default_acc);
        let root_pos = self.root_pos();
        idx.sub_assign(root_pos);

        let r = OwnedNode::map_ref(&mut self.root).unwrap();
        let mut acc = r.val.accumulated(root_pos, idx);
        if let Some(lhs) = OwnedNode::map_ref(&r.left) {
            // > acc += lhs.total_accumulated.clone();
            Self::add_acc(
                lhs.total_accumulated.clone(),
                &mut acc,
                &mut self.default_acc,
            );
        }

        acc
    }

    /// Returns the total value of the accumulator across the entire tree
    pub fn total_accumulated(&self) -> S::Accumulator {
        self.root().total_accumulated.clone()
    }

    // Helper function to change an index by the offset in the node
    fn stack_pos(base: S::Idx, node: &SNode<S>) -> S::Idx {
        base.apply_delta(node.offset_from_parent)
    }

    // Helper function to add `lower` to `upper`. This function exists because we guarantee that
    // accumulators are only added as `lower += upper`. There's some cases where it's particularly
    // difficult to do that, so we handle the case where we'd like to say `*upper += lower` here.
    fn add_acc(
        mut lower: S::Accumulator,
        upper: &mut S::Accumulator,
        default: &mut Option<S::Accumulator>,
    ) {
        lower += mem::replace(upper, default.take().unwrap());
        *default = Some(mem::replace(upper, lower));
    }

    // Performs the 'splay' operation to bubble the region containing the index to the root This is
    // pretty much just adapted from the implementation in Alex Crichton's splay-rs
    //
    // Note that we largely don't use any of the interior mutability provided by the `RefCell`s
    // here -- we swap around what's being referenced instead of swapping the things at those
    // references. It's why we take a `&mut OwnedNode` to replace instead of just writing to what's
    // at that node. This distinction means that `NodeRef`s *are* actually guaranteed to be stable,
    // instead of just
    fn splay(node: &mut OwnedSNode<S>, idx: S::Idx, default_acc: &mut Option<S::Accumulator>) {
        let original_parent = node.get_mut().parent.take();

        let mut newleft: Option<OwnedSNode<S>> = None;
        let mut newright: Option<OwnedSNode<S>> = None;

        struct Entry<'a, S: AccumulatorSlice> {
            kind: EntryKind<'a, S>,
            parent_pos: S::Idx,
        }

        enum EntryKind<'a, S: AccumulatorSlice> {
            Base(&'a mut Option<OwnedSNode<S>>),
            Left(OwnedSNode<S>),
            Right(OwnedSNode<S>),
        }

        impl<'a, S: AccumulatorSlice> Entry<'a, S> {
            // fills in the "hole" in the entry, in the appropriate place. panics if it already has
            // a node there
            fn set_node(&mut self, mut node: Option<OwnedSNode<S>>) {
                match &mut self.kind {
                    EntryKind::Base(hole) => {
                        if let Some(mut n) = OwnedNode::map_mut(&mut node) {
                            n.parent = None;
                        }

                        debug_assert!(hole.is_none());
                        // double-dereference because we matched on `&mut EntryKind::Base(&mut _)`.
                        **hole = node;
                    }
                    EntryKind::Left(n) => {
                        if let Some(mut l) = OwnedNode::map_mut(&mut node) {
                            l.parent = Some(n.weak());
                        }

                        let mut g = n.get_mut();
                        debug_assert!(g.left.is_none());
                        g.left = node;
                    }
                    EntryKind::Right(n) => {
                        if let Some(mut r) = OwnedNode::map_mut(&mut node) {
                            r.parent = Some(n.weak());
                        }

                        let mut g = n.get_mut();
                        debug_assert!(g.right.is_none());
                        g.right = node;
                    }
                }
            }

            // Moves the hole the entry corresponds to
            fn shift_with(&mut self, kind: impl FnOnce(OwnedSNode<S>) -> EntryKind<'a, S>) {
                let node = match &self.kind {
                    EntryKind::Base(n) => n.as_ref().unwrap().shallow_clone(),
                    EntryKind::Left(n) => n.get().left.as_ref().unwrap().shallow_clone(),
                    EntryKind::Right(n) => n.get().right.as_ref().unwrap().shallow_clone(),
                };

                self.kind = kind(node);
            }

            fn has_hole(&self) -> bool {
                match &self.kind {
                    EntryKind::Base(opt) => opt.is_none(),
                    EntryKind::Left(n) => n.get().left.is_none(),
                    EntryKind::Right(n) => n.get().right.is_none(),
                }
            }
        }

        // We need to set `parent_pos` equal to `usize::MAX / 2` because adjusting positions down
        // must always result in something non-negative.
        //
        // @req "Ranged::replace requires less than usize::MAX / 2" v0
        let mut l = Entry {
            kind: EntryKind::Base(&mut newleft),
            parent_pos: S::Idx::MAX_SIZE,
        };
        let mut r = Entry {
            kind: EntryKind::Base(&mut newright),
            parent_pos: S::Idx::MAX_SIZE,
        };

        macro_rules! assert_valid {
            ($node:expr) => {{
                if let Some(left) = OwnedNode::map_ref(&$node.left) {
                    debug_assert!(left.offset_from_parent < S::Idx::ZERO_DELTA);
                }
                if let Some(right) = OwnedNode::map_ref(&$node.right) {
                    debug_assert!(S::Idx::from_delta(right.offset_from_parent) >= $node.size);
                }
            }};
        }

        macro_rules! swap_option_parents {
            ($($n:expr, $old:expr => $new:expr;)+) => {{
                $($n.as_mut().map(|n| Self::swap_parent(&mut *n.get_mut(), $old, $new));)+
            }}
        }

        // helper macro for setting the parent of a node
        macro_rules! setp {
            ($node:expr, $parent:expr) => {{
                let mut n = $node;
                if let Some(mut node) = OwnedNode::map_mut(&mut n) {
                    node.parent = $parent;
                }
                n
            }};
        }

        loop {
            // "node_g" stands for "node guard". We use the "_g" suffix here to indicate guards,
            // for simplicity.
            let mut node_g = node.get_mut();
            let mut node_pos = S::Idx::from_delta(node_g.offset_from_parent);

            match idx.cmp_in_range(node_pos..node_pos.add(node_g.size)) {
                Equal => break,
                Less => {
                    // Note: the "parent" of `left` is expected to be `node_pos`.
                    let mut left = node_g.left.take().expect("expected lower value");
                    let mut left_g = left.get_mut();
                    left_g.parent = None;

                    node_g.total_accumulated -= left_g.total_accumulated.clone();
                    let mut left_pos = Self::stack_pos(node_pos, &*left_g);
                    drop((left_g, node_g));

                    // rotate this node right if necessary
                    if idx < left_pos {
                        let node_weak = node.weak();
                        let (mut left_g, mut node_g) = (left.get_mut(), node.get_mut());

                        // set node.left = left.right
                        let mut maybe_guard = OwnedNode::map_mut(&mut left_g.right);
                        if let Some(n) = maybe_guard.as_mut() {
                            Self::swap_parent(&mut *n, left_pos, node_pos);
                            // > node.total_accumulated += n.total_accumulated.clone();
                            Self::add_acc(
                                n.total_accumulated.clone(),
                                &mut node_g.total_accumulated,
                                default_acc,
                            );
                            let n_acc = n.total_accumulated.clone();
                            drop(maybe_guard);
                            left_g.total_accumulated -= n_acc;
                        } else {
                            // Need to ensure that `maybe_guard` is adequately dropped in both
                            // cases.
                            drop(maybe_guard);
                        }
                        node_g.left = setp!(left_g.right.take(), Some(node_weak));
                        assert_valid!(node_g);

                        // swap left & node:
                        //
                        // node.offset_from_parent = -left.offset_from_parent;
                        node_g.offset_from_parent = S::Idx::ZERO_DELTA;
                        S::Idx::delta_sub_assign(
                            &mut node_g.offset_from_parent,
                            left_g.offset_from_parent,
                        );
                        // left.offset_from_parent = left_pos as Idx;
                        left_g.offset_from_parent = left_pos.delta_from(S::Idx::ZERO);

                        drop((left_g, node_g));

                        mem::swap(&mut left, node);
                        mem::swap(&mut node_pos, &mut left_pos);
                        let node_weak = node.weak();
                        let mut node_g = node.get_mut();
                        let mut left_g = left.get_mut();
                        assert_valid!(node_g);

                        // set node.right = left; node.right is currently None because we took
                        // left.right earlier
                        debug_assert!(node_g.right.is_none());
                        // `left`'s parent position is still correct; we don't need to update it
                        // here. We *do* need to update the actual parent, though.
                        node_g.total_accumulated += left_g.total_accumulated.clone();
                        left_g.parent = Some(node_weak);
                        drop(left_g);
                        node_g.right = Some(left);

                        match mem::replace(&mut node_g.left, None) {
                            Some(mut l) => {
                                let mut g = l.get_mut();
                                g.parent = None;
                                node_g.total_accumulated -= g.total_accumulated.clone();
                                drop(g);
                                left = l;
                            }
                            None => break,
                        }
                    }

                    let (mut left_g, mut node_g) = (left.get_mut(), node.get_mut());

                    // Broadly: *r = Some(replace(node, left));
                    //          r = &mut r.as_mut().unwrap().left;
                    //
                    // Prepare `left` to replace `node`.
                    Self::swap_parent(&mut *left_g, node_pos, S::Idx::ZERO);
                    // Prepare `node` to replace `*r`
                    Self::swap_parent(&mut *node_g, S::Idx::ZERO, r.parent_pos);
                    debug_assert!(left_g.parent.is_none());
                    debug_assert!(node_g.parent.is_none());

                    drop((left_g, node_g));

                    let new_r = mem::replace(node, left);
                    r.parent_pos = Self::stack_pos(r.parent_pos, &*new_r.get());
                    // The following two lines are equivalent to:
                    //   *r.node = Some(new_r);
                    //   r.node = &mut r.node.left; (ignoring unwrapping)
                    r.set_node(Some(new_r));
                    r.shift_with(EntryKind::Left);
                    debug_assert!(r.has_hole());
                }
                Greater => {
                    // We might sometimes have `idx` equal to one greater than
                    let mut right = match node_g.right.take() {
                        Some(n) => n,
                        None => break,
                    };
                    let mut right_g = right.get_mut();
                    right_g.parent = None;
                    node_g.total_accumulated -= right_g.total_accumulated.clone();
                    let mut right_pos = Self::stack_pos(node_pos, &*right_g);

                    let upper_bound = right_pos.add(right_g.size);
                    drop((right_g, node_g));

                    // Rotate left if necessary
                    if idx >= upper_bound {
                        let node_weak = node.weak();
                        let (mut right_g, mut node_g) = (right.get_mut(), node.get_mut());

                        // set node.right = right.left
                        let mut maybe_guard = OwnedNode::map_mut(&mut right_g.left);
                        if let Some(n) = maybe_guard.as_mut() {
                            Self::swap_parent(&mut *n, right_pos, node_pos);
                            node_g.total_accumulated += n.total_accumulated.clone();
                            let n_acc = n.total_accumulated.clone();
                            drop(maybe_guard);
                            right_g.total_accumulated -= n_acc;
                        } else {
                            drop(maybe_guard);
                        }

                        node_g.right = setp!(right_g.left.take(), Some(node_weak));
                        assert_valid!(node_g);

                        // swap right & node:
                        //
                        // node.offset_from_parent = -right.offset_from_parent;
                        node_g.offset_from_parent = S::Idx::ZERO_DELTA;
                        S::Idx::delta_sub_assign(
                            &mut node_g.offset_from_parent,
                            right_g.offset_from_parent,
                        );
                        // right.offset_from_parent = right_pos as Idx;
                        right_g.offset_from_parent = right_pos.delta_from(S::Idx::ZERO);

                        drop((right_g, node_g));

                        mem::swap(&mut right, node);
                        mem::swap(&mut node_pos, &mut right_pos);
                        let node_weak = node.weak();
                        let mut node_g = node.get_mut();
                        assert_valid!(node_g);

                        // set node.left = right; node.left is currently None because we took
                        // right.left earlier
                        debug_assert!(node_g.left.is_none());
                        // `right`'s parent position is still correct; we don't need to update it
                        // here. We *do* need to update the actual parent though.
                        right.get_mut().parent = Some(node_weak);
                        node_g.left = Some(right);

                        match mem::replace(&mut node_g.right, None) {
                            Some(mut r) => {
                                r.get_mut().parent = None;
                                right = r;
                            }
                            None => break,
                        }
                    }

                    let (mut right_g, mut node_g) = (right.get_mut(), node.get_mut());

                    // Broadly: *l = Some(replace(node, right));
                    //          l = &mut l.as_mut().unwrap().right;
                    //
                    // Prepare `right` to replace `node`.
                    Self::swap_parent(&mut *right_g, node_pos, S::Idx::ZERO);
                    // Prepare `node` to replace `*l`
                    Self::swap_parent(&mut *node_g, S::Idx::ZERO, l.parent_pos);
                    debug_assert!(right_g.parent.is_none());
                    debug_assert!(node_g.parent.is_none());

                    drop((right_g, node_g));

                    let new_l = mem::replace(node, right);
                    l.parent_pos = Self::stack_pos(l.parent_pos, &*new_l.get());
                    // The following two lines are equivalent to:
                    //   *l.node = Some(new_l);
                    //   l.node = &mut l.node.right; (ignoring unwrapping)
                    l.set_node(Some(new_l));
                    l.shift_with(EntryKind::Right);
                    debug_assert!(l.has_hole());
                }
            }
        }

        let mut node_g = node.get_mut();
        let node_pos = Self::stack_pos(S::Idx::ZERO, &*node_g);
        swap_option_parents! {
            node_g.left, node_pos => l.parent_pos;
            node_g.right, node_pos => r.parent_pos;
        }

        debug_assert!(l.has_hole());
        debug_assert!(r.has_hole());
        l.set_node(node_g.left.take());
        r.set_node(node_g.right.take());

        // We need to adjust the "parent" of `new{left,right}` here because we initially set their
        // positions to `usize::MAX / 2`
        // @req "Ranged::replace requires less than usize::MAX / 2" v0
        swap_option_parents! {
            newright, S::Idx::MAX_SIZE => node_pos;
            newleft, S::Idx::MAX_SIZE => node_pos;
        }

        // As we went through earlier, we were assigning to sub-nodes of `newleft` and `newright`.
        // These didn't properly set the accumulator, so we need to correct that now. However... if
        // the accumulator is zero-sized (which may be quite possible), there isn't any data it
        // *could* store; we should skip this step.
        if mem::size_of::<S::Accumulator>() != 0 {
            // We only need to take O(log(n)) steps on each one, because we only set the right-hand
            // sub-nodes of `newleft` and the left-hand sub-nodes of `newright`. Any other node
            // will already have the correct accumulator, as guaranteed above, during the body of
            // the loop.
            //
            // We'll store all of the accumulators in a stack, so that we add up the contributions
            // from the side we need to recalculate.

            let root_pos = S::Idx::from_delta(node_g.offset_from_parent);
            node_g.total_accumulated = node_g.acc.clone();

            // Helper function for debugging.
            fn make_str<T>(this: &T, label: &str) -> String {
                match crate::utils::MaybeDbg::maybe_dbg(this) {
                    Some(s) => format!(", {} = {}", label, s),
                    None => String::new(),
                }
            }

            // Handle `newleft`, recursing down on `.right`
            let mut stack = vec![];
            let mut stack_node = newleft.as_ref().map(|n| n.shallow_clone());
            let mut node_pos = root_pos;
            while let Some(mut n) = stack_node.take() {
                let mut g = n.get_mut();
                node_pos = Self::stack_pos(node_pos, &*g);
                g.total_accumulated = g.acc.clone();
                if let Some(a) = OwnedNode::map_ref(&g.left).map(|l| l.total_accumulated.clone()) {
                    // > n.total_accumulated += l.total_accumulated.clone();
                    Self::add_acc(a, &mut g.total_accumulated, default_acc);
                }

                if let Some(r) = g.right.as_ref() {
                    stack_node = Some(r.shallow_clone());
                }

                drop(g);
                stack.push(n);
            }

            let mut acc = S::Accumulator::default();
            while let Some(mut n) = stack.pop() {
                let mut g = n.get_mut();
                g.total_accumulated += acc;
                acc = g.total_accumulated.clone();
            }

            // > node.total_accumulated += acc;
            Self::add_acc(acc, &mut node_g.total_accumulated, default_acc);

            // Repeat for `newright`, recursing down on `.left`
            stack_node = newright.as_ref().map(|n| n.shallow_clone());
            node_pos = root_pos;
            while let Some(mut n) = stack_node.take() {
                let mut g = n.get_mut();
                node_pos = Self::stack_pos(node_pos, &*g);
                g.total_accumulated = g.acc.clone();
                if let Some(a) =
                    OwnedNode::map_mut(&mut g.right).map(|r| r.total_accumulated.clone())
                {
                    g.total_accumulated += a;
                }

                if let Some(l) = g.left.as_ref() {
                    stack_node = Some(l.shallow_clone());
                }

                drop(g);
                stack.push(n);
            }

            acc = S::Accumulator::default();
            while let Some(mut n) = stack.pop() {
                let mut g = n.get_mut();
                // > g.total_accumulated += acc;
                Self::add_acc(acc, &mut g.total_accumulated, default_acc);
                acc = g.total_accumulated.clone();
            }

            node_g.total_accumulated += acc;
        }

        drop(node_g);
        let node_weak = node.weak();
        let mut node_g = node.get_mut();

        if let Some(n) = newleft.as_mut() {
            n.get_mut().parent = Some(node_weak.clone());
        }
        if let Some(n) = newright.as_mut() {
            n.get_mut().parent = Some(node_weak);
        }

        node_g.left = newleft;
        node_g.right = newright;
        node_g.parent = original_parent;
    }

    // Helper function for `splay`: Sets the offset from parent of this node as if the parent's
    // position switched from `old_pos` to `new_pos`
    fn swap_parent(node: &mut SNode<S>, old_pos: S::Idx, new_pos: S::Idx) {
        // old
        //  |---- offset ----|
        //                  pos
        //        |- offset -|
        //       new
        //
        // old + old_offset = pos; new + new_offset = pos
        // ∴ new_offset = old_offset + old - new
        S::Idx::delta_add_assign(&mut node.offset_from_parent, old_pos.delta_from(new_pos));
    }

    /// Provides the value corresponding to the given index
    ///
    /// ## Panics
    ///
    /// This method will panic if `idx` is greater than or equal to [`self.size()`](Self::size), or
    /// if the implementation of [`AccumulatorSlice`] panics from its indexing method.
    pub fn index(&mut self, mut idx: S::Idx) -> S::IndexedValue {
        if idx > self.size() {
            panic!(
                "index out of bounds: the index is {:?} but the size is {:?}",
                idx,
                self.size()
            )
        }

        Self::splay(self.root.as_mut().unwrap(), idx, &mut self.default_acc);
        let root_pos = self.root_pos();
        idx.sub_assign(root_pos);
        self.root().val.index(root_pos, idx)
    }

    /// Produces a reference to the node containing the given index
    ///
    /// If the tree is empty, the returned reference is guaranteed to be invalid.
    ///
    /// ## Panics
    ///
    /// This method will panic if `idx` is greater than or equal to [`self.size()`](Self::size), or
    /// if the implementation of [`AccumulatorSlice`] panics from its indexing method.
    pub fn index_ref(
        &mut self,
        idx: S::Idx,
    ) -> NodeRef<S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S> {
        if idx > self.size() {
            panic!(
                "index out of bounds: the index is {:?} but the size is {:?}",
                idx,
                self.size()
            )
        } else if self.size == S::Idx::ZERO {
            return NodeRef { inner: Weak::new() };
        }

        Self::splay(self.root.as_mut().unwrap(), idx, &mut self.default_acc);
        NodeRef {
            inner: self.root_ref().weak(),
        }
    }
}

impl<S> Ranged<S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S>
where
    S: AccumulatorSlice,
    S::Idx: Debug,
    S::Accumulator: Ord,
{
    /// Returns the index at which the accumulator increases to the specified value
    ///
    /// The implementation of `Ord` on `S::Accumulator` should function "like integers", to phrase
    /// it simply. For correctness, this method also relies on the accumulator being "unsigned" --
    /// i.e. that the value of the accumulator can never decreases by expanding some range of the
    /// tree.
    ///
    /// Formally, this requires that:
    ///
    /// > For all `i` < `j` <= `self.size()`, `self.accumulated_at(i)` < `self.accumulated_at(j)`
    ///
    /// Alongside the above assumption that:
    ///
    /// > For all `x` and `y`, `x` <= `x` + `y`
    ///
    /// In addition to the requirements listed in the documentation for
    /// [`AccumulatorSlice::Accumulator`].
    ///
    /// ## Panics
    ///
    /// This method panics if `acc` is outside the range of the accumulator.
    pub fn index_of_accumulated(&self, mut acc: S::Accumulator) -> S::Idx {
        let default_acc = S::Accumulator::default();

        if self.root.is_none() {
            if acc != default_acc {
                panic!("`index_of_accumulated` called on empty `Ranged` with non-zero accumulator");
            } else {
                return S::Idx::ZERO;
            }
        }

        let mut idx = self.root_pos();
        let mut node = self.root_ref().shallow_clone();
        let mut running_acc = S::Accumulator::default();

        loop {
            let guard = node.get();

            if let Some(n) = guard.left.as_ref() {
                let g = n.get();
                // lhs_total = running_acc + n.total_accumulated
                let mut lhs_total = running_acc.clone();
                lhs_total += g.total_accumulated.clone();
                if lhs_total >= acc {
                    idx = Self::stack_pos(idx, &*g);
                    let n_shallow_clone = n.shallow_clone();
                    drop(g);
                    drop(guard);
                    node = n_shallow_clone;
                    // Don't increment `running_acc`, because it only contains the accumulator that
                    // we've "committed" to.
                    continue;
                }
            }

            if let Some(n) = guard.right.as_ref() {
                let g = n.get();
                // pre_rhs_total = running_acc + node.total_accumulated - n.total_accumulated
                let mut pre_rhs_total = running_acc.clone();
                pre_rhs_total += guard.total_accumulated.clone();
                pre_rhs_total -= g.total_accumulated.clone();

                if pre_rhs_total < acc {
                    idx = Self::stack_pos(idx, &*g);
                    let n_shallow_clone = n.shallow_clone();
                    drop(g);
                    drop(guard);
                    node = n_shallow_clone;
                    // Because we want `running_acc` to give everything that occurs before the
                    // subtree rooted at this node, and `pre_rhs_total` gives everything before the
                    // right-hand node, we set it to the right-hand node.
                    running_acc = pre_rhs_total;
                    continue;
                }
            }

            // If it's not the left or right-hand node, then it must be in the middle. We'll
            // double-check that the accumulator is still valid.
            break;
        }

        let guard = node.get();

        let mut after_val_acc = guard.acc.clone();
        after_val_acc += running_acc.clone();
        assert!(running_acc < acc);
        assert!(after_val_acc >= acc);

        acc -= running_acc;
        let within_idx = guard.val.index_of_accumulated(idx, acc);
        assert!(within_idx <= guard.size);

        idx.add(within_idx)
    }
}

impl<S> Ranged<S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S>
where
    S: Clone + AccumulatorSlice,
    S::Idx: Debug,
{
    /// Extracts and clones a range of the values
    pub fn clone_range(&mut self, range: Range<S::Idx>) -> Self {
        let mut val = None;
        self.replace_with(range, |r| {
            val = Some(r.clone());
            r
        });
        val.unwrap()
    }
}

trait CmpInRange: Sized {
    fn cmp_in_range(self, range: Range<Self>) -> Ordering;
}

impl<T: Ord> CmpInRange for T {
    fn cmp_in_range(self, range: Range<T>) -> Ordering {
        if self < range.start {
            Less
        } else if self >= range.end {
            Greater
        } else {
            Equal
        }
    }
}

#[cfg(test)]
impl<S> Ranged<S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S>
where
    S: AccumulatorSlice,
    S::Idx: Debug,
{
    fn print_node(
        node: Option<&OwnedSNode<S>>,
        parent_pos: S::Idx,
        prefix: &str,
        lower: &str,
    ) -> String {
        fn make_str<T>(this: &T, label: &str) -> String {
            match crate::utils::MaybeDbg::maybe_dbg(this) {
                Some(s) => format!("{} = {}", label, s),
                None => String::new(),
            }
        }

        match node {
            None => format!("{}<empty>", prefix),
            Some(n) => {
                let g = n.get();
                let pos = Self::stack_pos(parent_pos, &*g);

                let top_info = format!(
                    "{}@{:?} ({:?}): {}, size = {:?}, {}, {}, {}",
                    prefix,
                    DebugPtr(Rc::as_ptr(&n.inner)),
                    g.parent.as_ref().map(|p: &Weak<_>| DebugPtr(p.as_ptr())),
                    make_str(&g.offset_from_parent, "offset"),
                    g.size,
                    make_str(&g.val, "val"),
                    make_str(&g.val.accumulated(pos, g.size), "acc"),
                    make_str(&g.total_accumulated, "total_acc"),
                );
                let left_prefix = format!("{} ├─ left: ", lower);
                let left_lower = format!("{} │  ", lower);
                let left_info = Self::print_node(g.left.as_ref(), pos, &left_prefix, &left_lower);

                let right_prefix = format!("{} └─ right: ", lower);
                let right_lower = format!("{}    ", lower);
                let right_info =
                    Self::print_node(g.right.as_ref(), pos, &right_prefix, &right_lower);

                format!("{}\n{}\n{}", top_info, left_info, right_info)
            }
        }
    }

    pub fn print_tree(&self) -> String {
        format!(
            "--- Print Tree ---\nsize: {:?}\n{}\n---  End Tree  ---",
            self.size,
            Self::print_node(self.root.as_ref(), S::Idx::ZERO, "root: ", ""),
        )
    }
}

#[cfg(test)]
impl<S> Ranged<S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S>
where
    S: AccumulatorSlice,
    S::Idx: Debug,
    S::Accumulator: Debug + PartialEq,
    Self: std::panic::RefUnwindSafe,
{
    // Checks that the `Ranged` represents a valid set of ranges
    fn assert_valid(&self, print_on_panic: bool) {
        let func = || {
            if self.size != S::Idx::ZERO {
                let root = &self.root.as_ref().unwrap();
                Self::assert_valid_node(root, true, S::Idx::ZERO..self.size, S::Idx::ZERO, None);
            } else {
                assert!(self.root.is_none());
            }
        };

        if let Err(e) = std::panic::catch_unwind(func) {
            if print_on_panic {
                println!("invalid tree:\n{}", self.print_tree());
            }
            std::panic::resume_unwind(e);
        }
    }

    fn assert_valid_node(
        node: &OwnedSNode<S>,
        is_root: bool,
        within_range: Range<S::Idx>,
        parent_pos: S::Idx,
        parent: Option<&OwnedSNode<S>>,
    ) {
        use crate::utils::OpaqueOption;

        // Check that the recursion is valid
        assert!(is_root || !within_range.contains(&parent_pos));

        let guard = node.get();

        // Check that the parent is correct. This does a pointer comparison in the way you'd
        // expect.
        match (guard.parent.as_ref(), parent) {
            (None, None) => (),
            (Some(a), Some(b)) => assert!(a.ptr_eq(&b.weak())),
            (a, b) => panic!(
                "mismatched parents: node has {:?}, should be {:?}",
                OpaqueOption::new(&a),
                OpaqueOption::new(&b)
            ),
        }

        // And then on to the actual node checks.
        assert!(guard.size != S::Idx::ZERO);
        let pos = Self::stack_pos(parent_pos, &*guard);
        assert!(within_range.contains(&pos));
        let end_pos = pos.add(guard.size);
        assert!(end_pos <= within_range.end);

        let mut running_accumulator = guard.val.accumulated(pos, guard.size);
        assert_eq!(running_accumulator, guard.acc);

        if let Some(n) = guard.left.as_ref() {
            let new_range = within_range.start..pos;
            assert!(!new_range.is_empty());
            Self::assert_valid_node(&n, false, new_range, pos, Some(node));
            // > running_accumulator += n.total_accumulated.clone();
            Self::add_acc(
                n.get().total_accumulated.clone(),
                &mut running_accumulator,
                &mut Some(S::Accumulator::default()),
            );
        } else {
            assert_eq!(pos, within_range.start);
        }

        if let Some(n) = guard.right.as_ref() {
            let new_range = end_pos..within_range.end;
            assert!(!new_range.is_empty());
            Self::assert_valid_node(&n, false, new_range, pos, Some(node));
            running_accumulator += n.get().total_accumulated.clone();
        } else {
            assert_eq!(end_pos, within_range.end);
        }

        assert_eq!(running_accumulator, guard.total_accumulated);
    }
}

#[cfg(test)]
mod tests {
    use super::{AccumulatorSlice, Ranged};
    use itertools::Itertools;
    use std::fmt::Debug;
    use std::ops::{AddAssign, SubAssign};
    use std::panic::{RefUnwindSafe, UnwindSafe};
    use std::sync::Mutex;

    type TestRanged = Ranged<Acc, usize, isize, Slice>;

    // Unsafe? Yeah maybe. But we're only providing this implementation in tests, so we can get
    // away with it. It's for diagnostics.
    impl RefUnwindSafe for TestRanged {}
    impl UnwindSafe for TestRanged {}

    #[derive(Clone, Debug)]
    struct Slice {
        // Two slices with the same `name` can merge.
        name: char,
        // The accumulator for this slice, containing the values stored at each index. We can
        // retrieve the total size of the slice by counting the number of values in `acc`.
        acc: Acc,
    }

    impl Slice {
        // Helper method to return the size of the slice
        fn size(&self) -> usize {
            self.acc.vals.len()
        }
    }

    // Accumulator type for `Slice`.
    //
    // This type is specifically designed test that the various invariants guaranteed by the docs
    // on `AccumulatorSlice::Accumulator` are actually upheld across all of the tree operations.
    //
    // We define the accumulated value for a single index as a single `u8`, with the promise that
    // these values are strictly increasing across the full range of the tree -- they're typically
    // *mostly* sequential, but we sometimes have gaps in order to be able to insert more
    // in-between.
    //
    // The accumulated value across a range is then the full list of values for each index in the
    // range. This *does* mean that tree operations can now be worst-case O(n^2), but that doesn't
    // matter so much in testing -- especially for small values.
    //
    // Also: the derived implementation of `Default` works nicely to produce an accumulator that
    // corresponds to no values.
    #[derive(Clone, Debug, Default, PartialEq)]
    struct Acc {
        vals: Vec<u8>,
    }

    #[rustfmt::skip]
    impl AccumulatorSlice for Slice {
        type Idx = usize;

        type IndexedValue = char;
        fn index(&self, _base: usize, _idx: usize) -> char { self.name }

        // Our accumulation is pretty contrived; essentially we're counting the sum of the
        // character's numbers from 'a': so 'a' is 1, 'b' is 2, etc.
        type Accumulator = Acc;
        fn accumulated(&self, _base: usize, _idx: usize) -> Acc {
            self.acc.clone()
        }
        fn index_of_accumulated(&self, _base: usize, acc: Acc) -> usize {
            let idx = acc.vals.len();
            assert_eq!(self.acc.vals[..idx], acc.vals);

            idx
        }

        fn split_at(&mut self, _base: usize, idx: usize) -> Self {
            // These values are provided by the "Guarantees" section of AccumulatorSlice::split_at,
            // which says that `split_at` is never called with 0 or size.
            assert!(idx != 0);
            assert!(idx != self.size());

            Slice {
                name: self.name,
                acc: Acc {
                    vals: self.acc.vals.drain(idx..).collect(),
                },
            }
        }
        fn try_join(mut self, other: Self) -> Result<Self, (Self, Self)> {
            if self.name == other.name {
                // We expect that the accumulators' values are aligned nicely, because of the order
                // of the arguments.
                assert!(
                    self.acc.last_val() < other.acc.first_val(),
                    "self = {:?}, other = {:?}",
                    self,
                    other,
                );

                self.acc.vals.extend(other.acc.vals);
                Ok(self)
            } else {
                Err((self, other))
            }
        }
    }

    impl AddAssign for Acc {
        fn add_assign(&mut self, other: Acc) {
            // The documentation of `AccumulatorSlice::Accumulator` provides that this method will
            // only ever be called with `self` occuring before `other` -- i.e. at a lower position.
            // We can't test that they're directly neighboring, because we sometimes have initial
            // gaps, but they should be. We'll also expect that they don't overlap.
            //
            // Check for defaults because we'll want to get the first and last values in a moment.
            if self.is_default() {
                *self = other;
                return;
            } else if other.is_default() {
                return;
            }

            assert!(self.last_val() < other.first_val());
            self.vals.extend(other.vals);
        }
    }

    impl SubAssign for Acc {
        fn sub_assign(&mut self, other: Acc) {
            // The documentation of `AccumulatorSlice::Accumulator` says that we're always
            // subtracting from *one* of the sides. So either `self.start == other.start`, or
            // `self.end == other.end`. Ideally, we wouldn't have both of these be true, but...
            // it's not strictly required.
            if self.is_default() {
                assert!(other.is_default());
                return;
            } else if other.is_default() {
                return;
            }

            let start_align = self.first_val() == other.first_val();
            let end_align = self.last_val() == other.last_val();

            // temp values, in case of error
            let self_vals_cloned = self.vals.clone();
            let other_vals_cloned = other.vals.clone();

            if start_align {
                let first_i = other.vals.len();
                self.vals
                    .drain(..first_i)
                    .zip(other.vals)
                    .for_each(|(x, y)| {
                        assert_eq!(
                            x, y,
                            "self.vals = {:?}, other.vals = {:?}",
                            self_vals_cloned, other_vals_cloned
                        );
                    });
            } else if end_align {
                let last_i = self.vals.len() - other.vals.len();
                self.vals
                    .drain(last_i..)
                    .zip(other.vals)
                    .for_each(|(x, y)| {
                        assert_eq!(
                            x, y,
                            "self.vals = {:?}, other.vals = {:?}",
                            self_vals_cloned, other_vals_cloned
                        );
                    });
            } else {
                panic!("unaligned ranges. self = {:?}, other = {:?}", self, other);
            }
        }
    }

    impl Acc {
        // Creates a new `Acc` with the given starting value and size.
        //
        // This populates `self.vals` with length `size`, where `self.vals[0] = start`. The pairs
        // from `skips` are used to jump over a range of values. Let's do an example:
        //
        //   If `start = i` and skips has some `(j, k)`, then this indicates that the final array
        //   `vals` will contain the sequence:
        //
        //     [i, i+1, ..., j-1, j+k, j+k+1, ...]
        //
        //   Essentially, the pair `(j, k)` indicates to skip over `k` values instead of going to
        //   `j`.
        //
        // If there's multiple values in `skips`, each pair is treated individually as above; i.e.
        // earlier jumps don't change the *value* at which later jumps occur.
        fn new(start: u8, size: usize, skips: &[(u8, u8)]) -> Self {
            let mut vals = Vec::with_capacity(size);

            let mut i = start;
            let mut sk_i = 0;

            while vals.len() < size {
                // If we're supposed to skip at this index, do so.
                if let Some(&(j, k)) = skips.get(sk_i) {
                    assert!(i <= j);
                    if i == j {
                        i += k;
                        sk_i += 1;
                    }
                }

                vals.push(i);
                i += 1;
            }

            assert!(sk_i == skips.len());
            Acc { vals }
        }

        fn is_default(&self) -> bool {
            self.vals.is_empty()
        }

        fn first_val(&self) -> u8 {
            self.vals[0]
        }

        fn last_val(&self) -> u8 {
            self.vals[self.vals.len() - 1]
        }
    }

    // Define a couple helper methods for generating `Ranged`s and testing equality
    impl TestRanged {
        // `sized` tuples are: (size, name, start pos, skips)
        //
        // For more about the relationship between size, start pos, and skips, refer to `Acc::new`.
        fn from_sizes(sizes: &[(usize, char, u8, &[(u8, u8)])]) -> TestRanged {
            let mut this = Ranged::new_empty();

            println!("{}", this.print_tree());
            for &(size, x, rel_pos, skips) in sizes {
                let i = this.size();
                let slice = Slice {
                    name: x,
                    acc: Acc::new(rel_pos, size, skips),
                };
                this.insert(i, size, slice);
                println!("{}", this.print_tree());
            }

            this
        }

        // The tuple in `sizes` is briefly described in `from_sizes()`.
        fn assert_matches(&self, sizes: &[(usize, char, u8, &[(u8, u8)])]) {
            self.assert_valid(true);

            let mut so_far = 0;
            for (i, (x, r)) in self.iter().enumerate() {
                assert_eq!(so_far, r.start);
                assert!(i < sizes.len());
                assert_eq!(r.len(), x.size());
                let (s, y, p, skips) = sizes[i];
                assert_eq!(r.len(), s);
                assert_eq!(x.name, y);
                assert_eq!(x.acc, Acc::new(p, s, skips));
                so_far = r.end;
            }
        }
    }

    // Execute the given test function for all generations of a `Ranged` with the given input
    // sizes.
    //
    // This is to ensure that various tests pass, regardless of the input structure of the tree. We
    // do this by accessing each range after creating the tree, testing all permutations of the
    // access pattern.
    //
    // The tuple in `initial_sizes` is briefly described in `from_sizes()`.
    fn do_all_perms<Func>(initial_sizes: &[(usize, char, u8, &[(u8, u8)])], test: Func)
    where
        Func: Fn(TestRanged),
        for<'a> &'a Func: UnwindSafe,
    {
        const MAX_PERM_LEN: usize = 6;

        assert!(
            initial_sizes.len() <= MAX_PERM_LEN,
            "too many sizes to generate all permutations"
        );

        let base = Ranged::from_sizes(initial_sizes);

        // The starting indexes of each size:
        let mut idx = 0;
        let indexes = initial_sizes.iter().map(|&(size, _, _, _)| {
            let old = idx;
            idx += size;
            old
        });

        for idxs in indexes.permutations(initial_sizes.len()) {
            let r = Mutex::new(base.clone());

            for &i in &idxs {
                let last_tree = r.lock().unwrap().print_tree();

                if let Err(e) = std::panic::catch_unwind(|| {
                    r.lock().unwrap().index(i);
                    r.lock().unwrap().assert_valid(false);
                }) {
                    println!("panicked with indexing order {:?} at index {}", idxs, i);
                    let g = match r.lock() {
                        Err(e) => e.into_inner(),
                        Ok(g) => g,
                    };
                    println!("last tree:\n{}", last_tree);
                    println!("current:\n{}", g.print_tree());
                    std::panic::resume_unwind(e);
                }
            }

            let r = r.into_inner().unwrap();
            let cloned = r.clone();
            if let Err(e) = std::panic::catch_unwind(|| test(cloned)) {
                println!("panicked with indexing order {:?}", idxs);
                println!("last tree:\n{}", r.print_tree());
                std::panic::resume_unwind(e);
            }
        }
    }

    // Helper type for getting type inference to work properly
    type Tuples<'a> = &'a [(usize, char, u8, &'a [(u8, u8)])];

    #[test]
    fn permuted_access() {
        let sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];
        do_all_perms(sizes, |r| r.assert_matches(sizes));
    }

    #[test]
    fn empty_replace() {
        let empty = Ranged::new_empty();

        let sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];
        do_all_perms(sizes, |replacement| {
            let mut e = empty.clone();
            e.replace(0..0, replacement).assert_matches(&[]);
            e.assert_matches(sizes);
        });
    }

    #[test]
    fn insert_start() {
        let sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];
        let insert = Ranged::from_sizes(&sizes[0..1]);
        do_all_perms(&sizes[1..], |mut ranged| {
            ranged.replace(0..0, insert.clone()).assert_matches(&[]);
            ranged.assert_matches(sizes);
        });
    }

    #[test]
    fn insert_middle_aligned() {
        let start_sizes: Tuples = &[(4, 'a', 0, &[]), (5, 'c', 7, &[]), (2, 'd', 12, &[])];
        let end_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];

        let insert = Ranged::from_sizes(&[(3, 'b', 4, &[])]);
        do_all_perms(start_sizes, |mut ranged| {
            ranged.replace(4..4, insert.clone()).assert_matches(&[]);
            ranged.assert_matches(end_sizes);
        });
    }

    #[test]
    fn insert_middle_unaligned() {
        let start_sizes: Tuples = &[(5, 'c', 0, &[(3, 3)]), (2, 'd', 8, &[])];
        let end_sizes: Tuples = &[
            (3, 'c', 0, &[]),
            (3, 'b', 3, &[]),
            (2, 'c', 6, &[]),
            (2, 'd', 8, &[]),
        ];

        let insert = Ranged::from_sizes(&[(3, 'b', 3, &[])]);
        do_all_perms(&start_sizes, |mut ranged| {
            ranged.replace(3..3, insert.clone()).assert_matches(&[]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn insert_end() {
        let sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];
        let insert = Ranged::from_sizes(&sizes[3..4]);
        do_all_perms(&sizes[..3], |mut ranged| {
            ranged.replace(12..12, insert.clone()).assert_matches(&[]);
            ranged.assert_matches(sizes);
        });
    }

    #[test]
    fn replace_start_aligned() {
        let start_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 5, &[]),
            (5, 'c', 8, &[]),
            (2, 'd', 13, &[]),
        ];
        let end_sizes: Tuples = &[
            (5, 'e', 0, &[]),
            (3, 'b', 5, &[]),
            (5, 'c', 8, &[]),
            (2, 'd', 13, &[]),
        ];
        let replacement = Ranged::from_sizes(&[(5, 'e', 0, &[])]);
        do_all_perms(start_sizes, |mut ranged| {
            ranged
                .replace(0..4, replacement.clone())
                .assert_matches(&[(4, 'a', 0, &[])]);
            ranged.assert_matches(end_sizes);
        });
    }

    #[test]
    fn replace_start_unaligned() {
        let start_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];
        let end_sizes: Tuples = &[
            (3, 'e', 0, &[]),
            (1, 'b', 6, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];
        let replacement = Ranged::from_sizes(&[(3, 'e', 0, &[])]);
        do_all_perms(start_sizes, |mut ranged| {
            ranged
                .replace(0..6, replacement.clone())
                .assert_matches(&[(4, 'a', 0, &[]), (2, 'b', 4, &[])]);
            ranged.assert_matches(end_sizes);
        });
    }

    #[test]
    fn replace_middle_unaligned() {
        let start_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];
        let end_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (2, 'b', 4, &[]),
            (3, 'e', 6, &[]),
            (3, 'c', 9, &[]),
            (2, 'd', 12, &[]),
        ];
        let replacement = Ranged::from_sizes(&[(3, 'e', 6, &[])]);
        do_all_perms(start_sizes, |mut ranged| {
            ranged
                .replace(6..9, replacement.clone())
                .assert_matches(&[(1, 'b', 6, &[]), (2, 'c', 7, &[])]);
            ranged.assert_matches(end_sizes);
        });
    }

    #[test]
    fn replace_middle_aligned_left() {
        let start_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 8, &[]),
            (2, 'd', 13, &[]),
        ];
        let end_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (3, 'e', 7, &[]),
            (3, 'c', 10, &[]),
            (2, 'd', 13, &[]),
        ];
        let replacement = Ranged::from_sizes(&[(3, 'e', 7, &[])]);
        do_all_perms(start_sizes, |mut ranged| {
            ranged
                .replace(7..9, replacement.clone())
                .assert_matches(&[(2, 'c', 8, &[])]);
            ranged.assert_matches(end_sizes);
        });
    }

    #[test]
    fn replace_middle_aligned_right() {
        let start_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 9, &[]),
            (2, 'd', 14, &[]),
        ];
        let end_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (2, 'b', 4, &[]),
            (3, 'e', 6, &[]),
            (5, 'c', 9, &[]),
            (2, 'd', 14, &[]),
        ];
        let replacement = Ranged::from_sizes(&[(3, 'e', 6, &[])]);
        do_all_perms(start_sizes, |mut ranged| {
            ranged
                .replace(6..7, replacement.clone())
                .assert_matches(&[(1, 'b', 6, &[])]);
            ranged.assert_matches(end_sizes);
        });
    }

    #[test]
    fn replace_middle_aligned_both() {
        let start_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];
        let end_sizes: Tuples = &[(4, 'a', 0, &[]), (3, 'e', 5, &[]), (2, 'd', 12, &[])];
        let replacement = Ranged::from_sizes(&[(3, 'e', 5, &[])]);
        do_all_perms(start_sizes, |mut ranged| {
            ranged
                .replace(4..12, replacement.clone())
                .assert_matches(&[(3, 'b', 4, &[]), (5, 'c', 7, &[])]);
            ranged.assert_matches(end_sizes);
        });
    }

    #[test]
    fn replace_end_aligned() {
        let start_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];
        let end_sizes: Tuples = &[(4, 'a', 0, &[]), (3, 'b', 4, &[]), (2, 'e', 7, &[])];
        let replacement = Ranged::from_sizes(&[(2, 'e', 7, &[])]);
        do_all_perms(start_sizes, |mut ranged| {
            ranged
                .replace(7..14, replacement.clone())
                .assert_matches(&[(5, 'c', 7, &[]), (2, 'd', 12, &[])]);
            ranged.assert_matches(end_sizes);
        });
    }

    #[test]
    fn replace_end_unaligned() {
        let start_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];
        let end_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (2, 'c', 7, &[]),
            (2, 'e', 9, &[]),
        ];
        let replacement = Ranged::from_sizes(&[(2, 'e', 9, &[])]);
        do_all_perms(&start_sizes, |mut ranged| {
            ranged
                .replace(9..14, replacement.clone())
                .assert_matches(&[(3, 'c', 9, &[]), (2, 'd', 12, &[])]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn join_both_ends() {
        // The relative positions don't increase here because we need both (3, 'b') and (1, 'b') to
        // have the same position in order to join.
        let start_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (2, 'c', 7, &[]),
            (1, 'b', 9, &[]),
            (2, 'd', 10, &[]),
        ];
        let end_sizes: Tuples = &[(4, 'a', 0, &[]), (5, 'b', 4, &[(8, 1)]), (2, 'd', 10, &[])];
        let replacement = Ranged::from_sizes(&[(2, 'b', 6, &[])]);
        do_all_perms(&start_sizes, |mut ranged| {
            ranged
                .replace(6..9, replacement.clone())
                .assert_matches(&[(1, 'b', 6, &[]), (2, 'c', 7, &[])]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn clone_range_unaligned() {
        let start_sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (2, 'c', 7, &[]),
            (5, 'd', 12, &[]),
        ];
        do_all_perms(&start_sizes, |mut ranged| {
            ranged
                .clone_range(5..8)
                .assert_matches(&[(2, 'b', 5, &[]), (1, 'c', 7, &[])]);
        });
    }

    #[test]
    fn normal_refs_deallocated() {
        // Tests that our references are properly invalid once the tree is dropped. We want to be
        // sure that the
        let sizes: Tuples = &[
            (4, 'a', 0, &[]),
            (3, 'b', 4, &[]),
            (5, 'c', 7, &[]),
            (2, 'd', 12, &[]),
        ];

        let mut ranged = Ranged::from_sizes(sizes);

        let refs = [0, 4, 7, 12]
            .iter()
            .map(|&i| {
                let mut r = ranged.index_ref(i);
                assert!(r.current_index() == i);
                r
            })
            .collect::<Vec<_>>();

        drop(ranged);

        for r in refs {
            assert!(!r.is_valid());
        }
    }
}
