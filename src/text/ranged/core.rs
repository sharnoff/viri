//! Wrapper module for the [`Ranged`] type
//!
//! Information about the purpose that [`Ranged`] serves is available in the type's documentation.

use std::cmp::Ordering::{self, Equal, Greater, Less};
use std::fmt::Debug;
use std::mem;
use std::ops::{AddAssign, Range, SubAssign};

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
/// For more information, refer to the [`AccumulatorSlice`] and [`RangedIndex`] traits.
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
/// [`TextTree`]: crate::text::objects::TextTree;
/// [`StdRanged`]: super::StdRanged
/// [`Slice`]: super::Slice
/// [`IndexedSlice`]: super::IndexedSlice
#[derive(Clone)]
pub struct Ranged<Acc, Idx, Delta, S> {
    size: Idx,
    // The root is always `Some(_)` when the structure is in a valid state. We allow it to be
    // `None` so that we can temporarily extract an owned `Ranged` from a `&mut Ranged`
    root: Option<Box<Node<Acc, Idx, Delta, S>>>,
}

/// (*Internal*) A helper type for a [`Node`]; a value paired with its size
///
/// This really could have been flattened into the [`Node`] struct itself; the reason it isn't is
/// because having a `size` field in a node might cause confusion; it could be misinterpreted as
/// the total size of all children, which it is not.
#[derive(Clone)]
struct SizePair<S, Idx> {
    val: S,
    size: Idx,
}

/// (*Internal*) An individual node in the [`Ranged`] splay tree
#[derive(Clone)]
struct Node<Acc, Idx, Delta, S> {
    left: Option<Box<Node<Acc, Idx, Delta, S>>>,
    right: Option<Box<Node<Acc, Idx, Delta, S>>>,
    pair: SizePair<S, Idx>,
    offset_from_parent: Delta,
    // The total accumulated value from `pair.val` and both sub-trees.
    total_accumulated: Acc,
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
/// `AccumulatorSlice`
/// there treats each slice as some number of lines, with the accumulator counting the number of
/// lines before each slice.
///
/// Fetching the accumulated value at a point is done with the [`accumulated_at`] method on
/// [`Ranged`].
///
/// [`TextTree`]: crate::text::objects::TextTree;
///
/// ## Other things to note
///
/// There a couple implementations of this trait provided for you; [`Constant`] and a blanket
/// implementation on [`Option`]. The implementation on [`Option`] works in the expected way: it
/// behaves like [`Constant`] when the values are `None`, and otherwise defers to the underlying
/// ranges.
pub trait AccumulatorSlice: Sized {
    /// Representation of an index, used both for the starting position of a slice and an index
    /// within it
    type Idx: RangedIndex;

    /// The value provided by indexing
    ///
    /// It may not always make sense to provide an indexed value; in these cases, the [`NoIndex`]
    /// type is provided an empty type to make this explicit.
    type IndexedValue: Sized;

    /// Returns the value at the given offset `idx` inside of the slice
    ///
    /// The absolute position of the start of the slice is provided as `base_idx`.
    fn index(&self, base_idx: Self::Idx, idx: Self::Idx) -> Self::IndexedValue;

    /// An accumulator for values
    ///
    /// The implementation of `AddAssign` on the accumulator is expected to be commutative and
    /// associative -- i.e. that `x + y = y + x` and `(x + y) + z = x + (y + z)`. This should
    /// typically be true *anyways* for most sensible accumulators, but it's worth stating
    /// explicitly. The implementation of `SubAssign` should similarly reflect these expectations.
    ///
    /// The value provided by `Default` should be the identity.
    ///
    /// If your implementation of `AccumulatorSlice` does not need an accumulator, you may wish to
    /// provide [`NoAccumulator`] here; it is a unit type that provides dummy implementations of
    /// the required traits.
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

// Helper type alias for talking about nodes, because they have many parameters
//
// The reason we have <S as AccumulatorSlice> throughout instead of S: AccumulatorSlice at the
// beginning is because the compiler gives us a warning otherwise:
//   warning: bounds on generic parameters are not enforced in type aliases
//     ...
//   help: the bound will not be checked when the type alias is used, and should be removed
// We're sacrificing a little cleanliness to get rid of warnings.
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
    pub fn new(init: S, size: S::Idx) -> Self {
        Ranged {
            size,
            root: Some(Box::new(Node {
                left: None,
                right: None,
                pair: SizePair { val: init, size },
                offset_from_parent: S::Idx::ZERO_DELTA,
                total_accumulated: S::Accumulator::default(),
            })),
        }
    }

    /// Returns the length of the set of values this represents -- i.e the smallest index we don't
    /// have a value for
    pub fn size(&self) -> S::Idx {
        self.size
    }

    // Provides an immutable reference to the root node
    fn root(&self) -> &SNode<S> {
        self.root.as_ref().expect("root node is in invalid state")
    }

    // Provides a mutable reference to the root node
    fn root_mut(&mut self) -> &mut Box<SNode<S>> {
        self.root.as_mut().expect("root node is in invalid state")
    }

    // Returns whether the root node contains the given index
    fn root_contains(&self, idx: S::Idx) -> bool {
        let start = self.root_pos();
        let end = start.add(self.root().pair.size);

        (start..end).contains(&idx)
    }

    // Returns the position of the root node
    fn root_pos(&self) -> S::Idx {
        S::Idx::from_delta(self.root().offset_from_parent)
    }

    /// (*Internal*) Temporarily puts `self` in an invalid state in order to provide ownership of it
    ///
    /// The invalid state given is not unsafe in any way; it is simply that operations will fail if
    /// `self` is left in that state.
    #[rustfmt::skip]
    fn temp_extract(&mut self) -> Self {
        mem::replace(self, Ranged { size: S::Idx::ZERO, root: None })
    }

    /// The only "insertion" operation provided
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

        // The expected sizes of the regions to the left and right of the range, stored for later
        // so that we can accurately re-build the final `Ranged`
        let left_size = range.start;
        let right_size = self.size.sub(range.end);

        // Extract the values from before the range:
        Self::splay(self.root_mut(), range.start);

        let left = if range.start == S::Idx::ZERO {
            None
        } else if self.root_contains(range.start.decrement()) {
            // |-------- root --------|
            //               |---- range ----|
            // |- left_size -|

            let root_pos = self.root_pos();

            let sub_left = self.root_mut().left.take();
            let left_size = range.start.sub(self.root_pos());

            self.size.sub_assign(range.start);
            let root = self.root_mut();
            root.pair.size.sub_assign(left_size);

            // we set offset_from_parent to zero here because we just removed all of the nodes up
            // to range.start
            root.offset_from_parent = S::Idx::ZERO_DELTA;

            // Because we're removing part of the root, we need to shift the location of
            // root.right:
            if let Some(n) = root.right.as_mut() {
                S::Idx::delta_sub_assign_idx(&mut n.offset_from_parent, left_size);
            }

            // Split the left off from the root:
            let mut left_val = root.pair.val.split_at(root_pos, left_size);
            mem::swap(&mut left_val, &mut root.pair.val);

            // Acknowledge that we've taken some of the accumulated value out of the root - we're
            // putting it into `lhs_accumulated`.
            let mut lhs_accumulated = left_val.accumulated(root_pos, left_size);

            if let Some(l) = sub_left.as_ref() {
                lhs_accumulated += l.total_accumulated.clone();
            }
            root.total_accumulated -= lhs_accumulated.clone();

            // offset_from_parent = -left_size
            let mut offset_from_parent = S::Idx::ZERO_DELTA;
            S::Idx::delta_sub_assign_idx(&mut offset_from_parent, left_size);

            Some(Box::new(Node {
                pair: SizePair {
                    size: left_size,
                    val: left_val,
                },
                left: sub_left,
                right: None,
                offset_from_parent,
                total_accumulated: lhs_accumulated,
            }))
        } else {
            self.size.sub_assign(self.root_pos());
            let root = self.root_mut();
            root.offset_from_parent = S::Idx::ZERO_DELTA;

            root.left.take().map(|n| {
                root.total_accumulated -= n.total_accumulated.clone();
                n
            })
        };

        // Extract the values from after the range
        // We need to move range.end to account for having just shifted everything by removing the
        // nodes up to range.start
        let end = range.end.sub(range.start); // end = range.len()
        let r = self.root_mut();
        // last_idx = end_idx.saturating_sub(1);
        let last_idx = match end == S::Idx::ZERO {
            true => end,
            false => end.decrement(),
        };
        Self::splay(r, last_idx);

        let mut right = if end == self.size {
            None
        } else if self.root_contains(end) {
            let mut sub_right = self.root_mut().right.take();

            // self.root_pos()
            //       |--------- root node ----------|
            // |------- range -------|
            //       |- rhs_in_node -|- right_size -|

            // In order to keep the tree valid, we previously *fully* removed the left-hand side of
            // the tree, so that the new "zero" is at the starting point of the range.
            let root_pos = self.root_pos().add(range.start);

            // right_size = self.root_pos() + self.root().pair.size - end
            let right_size = self.root_pos().add(self.root().pair.size).sub(end);
            let root = self.root_mut();
            let rhs_in_node = root.pair.size.sub(right_size);

            let rhs_val = root.pair.val.split_at(root_pos, rhs_in_node);
            let mut rhs_accumulated = rhs_val.accumulated(root_pos.add(rhs_in_node), right_size);

            if let Some(n) = sub_right.as_mut() {
                S::Idx::delta_sub_assign_idx(&mut n.offset_from_parent, rhs_in_node);
                rhs_accumulated += n.total_accumulated.clone();
            }
            root.total_accumulated -= rhs_accumulated.clone();

            root.pair.size = rhs_in_node;

            Some(Box::new(Node {
                pair: SizePair {
                    size: right_size,
                    val: rhs_val,
                },
                left: None,
                right: sub_right,
                offset_from_parent: S::Idx::ZERO_DELTA,
                total_accumulated: rhs_accumulated,
            }))
        } else {
            let root = self.root_mut();
            root.right.take().map(|mut n| {
                S::Idx::delta_sub_assign_idx(&mut n.offset_from_parent, root.pair.size);
                root.total_accumulated -= n.total_accumulated.clone();
                n
            })
        };

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

        // Having replaced `self`, we can now re-attach the sub-trees on either side that we
        // previously extracted.

        // Add `left`:
        let mut root = self.root_mut();
        S::Idx::delta_add_assign_idx(&mut root.offset_from_parent, left_size);
        Self::splay(root, left_size);
        debug_assert!(root.left.is_none());
        if let Some(n) = left.as_ref() {
            root.total_accumulated += n.total_accumulated.clone();
        }
        root.left = left;
        self.size.add_assign(left_size);
        *self = self.temp_extract().try_join_left();

        // Add `right`:
        let size = self.size;
        root = self.root_mut();
        Self::splay(root, size);
        debug_assert!(root.right.is_none());
        if let Some(n) = right.as_mut() {
            S::Idx::delta_add_assign_idx(&mut n.offset_from_parent, root.pair.size);
            root.total_accumulated += n.total_accumulated.clone();
        }
        root.right = right;
        self.size.add_assign(right_size);
        *self = self.temp_extract().try_join_right();

        // And then we're done!
    }

    /// (*Internal*)
    fn try_join_left(mut self) -> Self {
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
        let mut left = self.root_mut().left.take().unwrap();

        if left.right.is_some() {
            // If there is a right subchild, we need to move it so that the highest index is at the
            // root.

            // Set the offset to start at zero
            S::Idx::delta_add_assign(&mut left.offset_from_parent, self.root().offset_from_parent);
            Self::splay(&mut left, root_pos.decrement());
            debug_assert!(left.right.is_none());

            // And then return the (new) left node's offset to be relative to the root
            S::Idx::delta_sub_assign(&mut left.offset_from_parent, self.root().offset_from_parent)
        }

        let mut root = self.root.take().expect("root node is in invalid state");
        match left.pair.val.try_join(root.pair.val) {
            // If there's an error, we just put things back to where they were before
            Err((left_val, root_val)) => {
                left.pair.val = left_val;
                root.pair.val = root_val;
                root.left = Some(left);
            }
            // If they *do* join, we have to stick the nodes back together
            Ok(single) => {
                let left_size = left.pair.size;
                S::Idx::delta_sub_assign_idx(&mut root.offset_from_parent, left_size);

                // Because we've shifted the position of the root back, we need to also need to
                // shift the right child
                if let Some(n) = root.right.as_mut() {
                    S::Idx::delta_add_assign_idx(&mut n.offset_from_parent, left_size);
                }

                root.pair.size.add_assign(left_size);
                root.pair.val = single;
                root.left = left.left;
            }
        }

        self.root = Some(root);
        self
    }

    /// (*Internal*)
    fn try_join_right(mut self) -> Self {
        // This method is essentially the same as `try_join_left`, where the only changes are to
        // account for being to the right, not to the left of the root node. For a commentary on
        // the structure, refer to that method immediately above.

        if self.root().right.is_none() {
            return self;
        }

        let root_pos = self.root_pos();
        let mut right = self.root_mut().right.take().unwrap();

        if right.left.is_some() {
            S::Idx::delta_add_assign(
                &mut right.offset_from_parent,
                self.root().offset_from_parent,
            );
            Self::splay(&mut right, root_pos.add(self.root().pair.size));
            debug_assert!(right.left.is_none());
            S::Idx::delta_sub_assign(
                &mut right.offset_from_parent,
                self.root().offset_from_parent,
            );
        }

        let mut root = self.root.take().expect("root node is in invalid state");
        match (root.pair.val).try_join(right.pair.val) {
            Err((root_val, right_val)) => {
                root.pair.val = root_val;
                right.pair.val = right_val;
                root.right = Some(right);
            }
            Ok(single) => {
                let root_size = root.pair.size;
                root.pair.size.add_assign(right.pair.size);
                root.pair.val = single;
                root.right = right.right.map(|mut n| {
                    S::Idx::delta_add_assign_idx(&mut n.offset_from_parent, root_size);
                    n
                });
            }
        }

        self.root = Some(root);
        self
    }

    /// Creates an iterator over all of the ranges, in order
    ///
    /// This function can be used with [`clone_range`](Self::clone_range) to iterate over a smaller
    /// range.
    pub fn iter<'a>(&'a self) -> impl 'a + Iterator<Item = (&'a S, Range<S::Idx>)> {
        struct Iter<'a, S: AccumulatorSlice> {
            // The root is `Some` only on the first iteration
            root: Option<&'a SNode<S>>,
            // Stack of nodes and their position
            stack: Vec<(S::Idx, &'a SNode<S>)>,
        }

        impl<'a, S> Iter<'a, S>
        where
            S: AccumulatorSlice,
            S::Idx: Debug,
        {
            fn push_lefts(&mut self, root_parent_pos: S::Idx, root: &'a SNode<S>) {
                let mut pos = root_parent_pos;
                let mut r = Some(root);
                while let Some(n) = r {
                    pos = <Ranged<_, _, _, _>>::stack_pos(pos, &*n);
                    self.stack.push((pos, n));
                    r = n.left.as_ref().map(|b| b.as_ref());
                }
            }
        }

        impl<'a, S> Iterator for Iter<'a, S>
        where
            S: AccumulatorSlice,
            S::Idx: Debug,
        {
            type Item = (&'a S, Range<S::Idx>);

            fn next(&mut self) -> Option<Self::Item> {
                if let Some(r) = self.root {
                    self.push_lefts(S::Idx::ZERO, &r);
                    self.root = None;
                }

                match self.stack.pop() {
                    Some((pos, n)) => {
                        if let Some(r) = n.right.as_ref() {
                            self.push_lefts(pos, r);
                        }
                        let range = pos..pos.add(n.pair.size);
                        Some((&n.pair.val, range))
                    }
                    None => None,
                }
            }
        }

        let iter: Iter<S> = Iter {
            root: match self.size == S::Idx::ZERO {
                true => None,
                false => Some(self.root()),
            },
            stack: Vec::new(),
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
    /// [`TextTree`]: crate::text::objects::TextTree;
    pub fn accumulated_at(&mut self, mut idx: S::Idx) -> S::Accumulator {
        if idx > self.size() {
            panic!(
                "index out of bounds: the index is {:?} but the size is {:?}",
                idx,
                self.size()
            )
        }

        Self::splay(self.root_mut(), idx);
        let root_pos = self.root_pos();
        idx.sub_assign(root_pos);

        let r = self.root();
        let mut acc = r.pair.val.accumulated(root_pos, idx);
        if let Some(lhs) = r.left.as_ref() {
            acc += lhs.total_accumulated.clone();
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

    // Performs the 'splay' operation to bubble the region containing the index to the root This is
    // pretty much just adapted from the implementation in Alex Crichton's splay-rs
    //
    // The `root_offset` parameter gives us an amount to add to the position of the root node. We
    // typically use this mid-replacement, so that it's still a valid tree passed to `splay`, but
    // we can pass the correct index of each slice to their functions.
    fn splay(node: &mut Box<SNode<S>>, idx: S::Idx) {
        let mut newleft: Option<Box<SNode<S>>> = None;
        let mut newright: Option<Box<SNode<S>>> = None;

        // Parameterized by `N` here for the node;
        struct Entry<'a, I, N> {
            node: &'a mut Option<Box<N>>,
            parent_pos: I,
        }

        // We need to set `parent_pos` equal to `usize::MAX / 2` because adjusting positions down
        // must always result in something non-negative.
        //
        // @req "Ranged::replace requires less than usize::MAX / 2" v0
        let mut l = Entry {
            node: &mut newleft,
            parent_pos: S::Idx::MAX_SIZE,
        };
        let mut r = Entry {
            node: &mut newright,
            parent_pos: S::Idx::MAX_SIZE,
        };

        macro_rules! assert_valid {
            ($node:expr) => {{
                if let Some(left) = $node.left.as_ref() {
                    debug_assert!(left.offset_from_parent < S::Idx::ZERO_DELTA);
                }
                if let Some(right) = $node.right.as_ref() {
                    debug_assert!(S::Idx::from_delta(right.offset_from_parent) >= $node.pair.size);
                }
            }};
        }

        macro_rules! swap_option_parents {
            ($($n:expr, $old:expr => $new:expr;)+) => {{
                $($n.as_mut().map(|n| Self::swap_parent(n, $old, $new));)+
            }}
        }

        loop {
            let mut node_pos = S::Idx::from_delta(node.offset_from_parent);

            match idx.cmp_in_range(node_pos..node_pos.add(node.pair.size)) {
                Equal => break,
                Less => {
                    // Note: the "parent" of `left` is expected to be `node_pos`.
                    let mut left = node.left.take().expect("expected lower value");
                    node.total_accumulated -= left.total_accumulated.clone();
                    let mut left_pos = Self::stack_pos(node_pos, &left);

                    // rotate this node right if necessary
                    if idx < left_pos {
                        // set node.left = left.right
                        let left_acc = &mut left.total_accumulated; // TODO-RFC#2229
                        left.right.as_mut().map(|n| {
                            Self::swap_parent(n, left_pos, node_pos);
                            *left_acc -= n.total_accumulated.clone();
                            node.total_accumulated += n.total_accumulated.clone();
                        });
                        node.left = left.right.take();
                        assert_valid!(node);

                        // swap left & node:
                        //
                        // node.offset_from_parent = -left.offset_from_parent;
                        node.offset_from_parent = S::Idx::ZERO_DELTA;
                        S::Idx::delta_sub_assign(
                            &mut node.offset_from_parent,
                            left.offset_from_parent,
                        );
                        // left.offset_from_parent = left_pos as Idx;
                        left.offset_from_parent = left_pos.delta_from(S::Idx::ZERO);
                        mem::swap(&mut left, node);
                        mem::swap(&mut node_pos, &mut left_pos);
                        assert_valid!(node);

                        // set node.right = left; node.right is currently None because we took
                        // left.right earlier
                        debug_assert!(node.right.is_none());
                        // `left`'s "parent" is still correct; we don't need to update it here.
                        node.total_accumulated += left.total_accumulated.clone();
                        node.right = Some(left);

                        match mem::replace(&mut node.left, None) {
                            Some(l) => {
                                #[allow(unused_assignments)]
                                {
                                    // Here, left_pos is never read -- that's mostly fine, but we
                                    // want to have this statement here either way for consistency.
                                    left_pos = Self::stack_pos(node_pos, &l);
                                }
                                node.total_accumulated -= l.total_accumulated.clone();
                                left = l;
                            }
                            None => break,
                        }
                    }

                    // Broadly: *r = Some(replace(node, left));
                    //          r = &mut r.as_mut().unwrap().left;
                    //
                    // Prepare `left` to replace `node`.
                    Self::swap_parent(&mut left, node_pos, S::Idx::ZERO);
                    // Prepare `node` to replace `*r`
                    Self::swap_parent(node, S::Idx::ZERO, r.parent_pos);
                    let new_r = mem::replace(node, left);
                    r.parent_pos = Self::stack_pos(r.parent_pos, &new_r);
                    *r.node = Some(new_r);
                    r.node = &mut r.node.as_mut().unwrap().left;
                    debug_assert!(r.node.is_none());
                }
                Greater => {
                    // We might sometimes have `idx` equal to one greater than
                    let mut right = match node.right.take() {
                        Some(n) => n,
                        None => break,
                    };
                    node.total_accumulated -= right.total_accumulated.clone();
                    let mut right_pos = Self::stack_pos(node_pos, &right);

                    // Rotate left if necessary
                    if idx >= right_pos.add(right.pair.size) {
                        // set node.right = right.left
                        let right_acc = &mut right.total_accumulated; // TODO-RFC#2229
                        right.left.as_mut().map(|n| {
                            Self::swap_parent(n, right_pos, node_pos);
                            *right_acc -= n.total_accumulated.clone();
                            node.total_accumulated += n.total_accumulated.clone();
                        });
                        node.right = right.left.take();
                        assert_valid!(node);

                        // swap right & node:
                        //
                        // node.offset_from_parent = -right.offset_from_parent;
                        node.offset_from_parent = S::Idx::ZERO_DELTA;
                        S::Idx::delta_sub_assign(
                            &mut node.offset_from_parent,
                            right.offset_from_parent,
                        );
                        // right.offset_from_parent = right_pos as Idx;
                        right.offset_from_parent = right_pos.delta_from(S::Idx::ZERO);
                        mem::swap(&mut right, node);
                        mem::swap(&mut node_pos, &mut right_pos);
                        assert_valid!(node);

                        // set node.left = right; node.left is currently None because we took
                        // right.left earlier
                        debug_assert!(node.left.is_none());
                        // `right`'s "parent" is still correct; we don't need to update it here
                        node.left = Some(right);

                        match mem::replace(&mut node.right, None) {
                            Some(r) => {
                                #[allow(unused_assignments)]
                                {
                                    // Here, right_pos is never read -- that's mostly fine, but we
                                    // want to have this statement here either way for consistency.
                                    right_pos = Self::stack_pos(node_pos, &r);
                                }
                                right = r;
                            }
                            None => break,
                        }
                    }

                    // Broadly: *l = Some(replace(node, right));
                    //          l = &mut l.as_mut().unwrap().right;
                    //
                    // Prepare `right` to replace `node`.
                    Self::swap_parent(&mut right, node_pos, S::Idx::ZERO);
                    // Prepare `node` to replace `*l`
                    Self::swap_parent(node, S::Idx::ZERO, l.parent_pos);
                    let new_l = mem::replace(node, right);
                    l.parent_pos = Self::stack_pos(l.parent_pos, &new_l);
                    *l.node = Some(new_l);
                    l.node = &mut l.node.as_mut().unwrap().right;
                    debug_assert!(l.node.is_none());
                }
            }
        }

        let node_pos = Self::stack_pos(S::Idx::ZERO, &node);
        // TODO-RFC#2229 can't come fast enough... :(
        let l_parent_pos = l.parent_pos;
        let r_parent_pos = r.parent_pos;
        swap_option_parents! {
            l.node, l_parent_pos => node_pos;
            r.node, r_parent_pos => node_pos;
            node.left, node_pos => l_parent_pos;
            node.right, node_pos => r_parent_pos;
        }

        mem::swap(l.node, &mut node.left);
        mem::swap(r.node, &mut node.right);

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

            let root_pos = S::Idx::from_delta(node.offset_from_parent);
            node.total_accumulated = node.pair.val.accumulated(root_pos, node.pair.size);

            // Helper function for debugging.
            fn make_str<T>(this: &T, label: &str) -> String {
                match crate::utils::MaybeDbg::maybe_dbg(this) {
                    Some(s) => format!(", {} = {}", label, s),
                    None => String::new(),
                }
            }

            // Handle `newleft`, recursing down on `.right`
            let mut stack = vec![];
            let mut stack_node = &mut newleft;
            let mut node_pos = root_pos;
            while let Some(n) = stack_node.as_mut() {
                node_pos = Self::stack_pos(node_pos, &*n);
                n.total_accumulated = n.pair.val.accumulated(node_pos, n.pair.size);
                if let Some(l) = n.left.as_ref() {
                    n.total_accumulated += l.total_accumulated.clone();
                }

                stack.push(&mut n.total_accumulated);
                stack_node = &mut n.right;
            }

            let mut acc = S::Accumulator::default();
            while let Some(a) = stack.pop() {
                *a += acc;
                acc = a.clone();
            }

            node.total_accumulated += acc;

            // Repeat for `newright`, recursing down on `.left`
            stack_node = &mut newright;
            node_pos = root_pos;
            while let Some(n) = stack_node.as_mut() {
                node_pos = Self::stack_pos(node_pos, &*n);
                n.total_accumulated = n.pair.val.accumulated(node_pos, n.pair.size);
                if let Some(r) = n.right.as_ref() {
                    n.total_accumulated += r.total_accumulated.clone();
                }

                stack.push(&mut n.total_accumulated);
                stack_node = &mut n.left;
            }

            acc = S::Accumulator::default();
            while let Some(a) = stack.pop() {
                *a += acc;
                acc = a.clone();
            }

            node.total_accumulated += acc;
        }

        node.left = newleft;
        node.right = newright;
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

        Self::splay(self.root_mut(), idx);
        let root_pos = self.root_pos();
        idx.sub_assign(root_pos);
        self.root().pair.val.index(root_pos, idx)
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
    /// [`RangeSlice::Accumulator`].
    ///
    /// ## Panics
    ///
    /// This method panics if `acc` is outside the range of the accumulator.
    pub fn index_of_accumulated(&self, mut acc: S::Accumulator) -> S::Idx {
        let mut idx = self.root_pos();
        let mut node = self.root();
        let mut running_acc = S::Accumulator::default();

        loop {
            if let Some(n) = node.left.as_ref() {
                // lhs_total = running_acc + n.total_accumulated
                let mut lhs_total = running_acc.clone();
                lhs_total += n.total_accumulated.clone();
                if lhs_total >= acc {
                    node = n;
                    idx = Self::stack_pos(idx, &*n);
                    // Don't increment `running_acc`, because it only contains the accumulator that
                    // we've "committed" to.
                    continue;
                }
            }

            if let Some(n) = node.right.as_ref() {
                // pre_rhs_total = running_acc + node.total_accumulated - n.total_accumulated
                let mut pre_rhs_total = running_acc.clone();
                pre_rhs_total += node.total_accumulated.clone();
                pre_rhs_total -= n.total_accumulated.clone();

                if pre_rhs_total < acc {
                    node = n;
                    idx = Self::stack_pos(idx, &*n);
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

        let mut after_val_acc = node.pair.val.accumulated(idx, node.pair.size);
        after_val_acc += running_acc.clone();
        assert!(running_acc < acc);
        assert!(after_val_acc >= acc);

        acc -= running_acc;
        let within_idx = node.pair.val.index_of_accumulated(idx, acc);
        assert!(within_idx <= node.pair.size);

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

#[cfg(test)]
impl<S> Ranged<S::Accumulator, S::Idx, <S::Idx as RangedIndex>::Delta, S>
where
    S: AccumulatorSlice,
    S::Idx: Debug,
{
    fn print_node(
        node: Option<&Box<SNode<S>>>,
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
                let pos = Self::stack_pos(parent_pos, &*n);

                let top_info = format!(
                    "{}{}, size = {:?}, {}, {}, {}",
                    prefix,
                    make_str(&n.offset_from_parent, "offset"),
                    n.pair.size,
                    make_str(&n.pair.val, "val"),
                    make_str(&n.pair.val.accumulated(pos, n.pair.size), "acc"),
                    make_str(&n.total_accumulated, "total_acc"),
                );
                let left_prefix = format!("{} ├─ left: ", lower);
                let left_lower = format!("{} │  ", lower);
                let left_info = Self::print_node(n.left.as_ref(), pos, &left_prefix, &left_lower);

                let right_prefix = format!("{} └─ right: ", lower);
                let right_lower = format!("{}    ", lower);
                let right_info =
                    Self::print_node(n.right.as_ref(), pos, &right_prefix, &right_lower);

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
{
    // Checks that the `Ranged` represents a valid set of ranges
    fn assert_valid(&self) {
        let root = &self.root.as_ref().unwrap();
        if self.size != S::Idx::ZERO {
            Self::assert_valid_node(root, true, S::Idx::ZERO..self.size, S::Idx::ZERO);
        } else {
            assert_eq!(root.pair.size, S::Idx::ZERO);
            assert!(root.left.is_none());
            assert!(root.right.is_none());
        }
    }

    fn assert_valid_node(
        node: &SNode<S>,
        is_root: bool,
        within_range: Range<S::Idx>,
        parent_pos: S::Idx,
    ) {
        // Check that the recursion is valid
        assert!(is_root || !within_range.contains(&parent_pos));

        // And then on to the actual node checks.
        assert!(node.pair.size != S::Idx::ZERO);
        let pos = Self::stack_pos(parent_pos, node);
        assert!(within_range.contains(&pos));
        let end_pos = pos.add(node.pair.size);
        assert!(end_pos <= within_range.end);

        let mut running_accumulator = node.pair.val.accumulated(pos, node.pair.size);

        if let Some(n) = node.left.as_ref() {
            let new_range = within_range.start..pos;
            assert!(!new_range.is_empty());
            Self::assert_valid_node(&n, false, new_range, pos);
            running_accumulator += n.total_accumulated.clone();
        } else {
            assert_eq!(pos, within_range.start);
        }

        if let Some(n) = node.right.as_ref() {
            let new_range = end_pos..within_range.end;
            assert!(!new_range.is_empty());
            Self::assert_valid_node(&n, false, new_range, pos);
            running_accumulator += n.total_accumulated.clone();
        } else {
            assert_eq!(end_pos, within_range.end);
        }

        assert_eq!(running_accumulator, node.total_accumulated);
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
mod tests {
    use super::{AccumulatorSlice, Ranged};
    use itertools::Itertools;
    use std::fmt::{self, Debug, Formatter};
    use std::panic::UnwindSafe;
    use std::sync::Mutex;

    type TestRanged = Ranged<u64, usize, isize, Slice>;

    #[derive(Copy, Clone)]
    struct Slice(char);

    impl Debug for Slice {
        fn fmt(&self, f: &mut Formatter) -> fmt::Result {
            self.0.fmt(f)
        }
    }

    #[rustfmt::skip]
    impl AccumulatorSlice for Slice {
        type Idx = usize;

        type IndexedValue = char;
        fn index(&self, _base: usize, _idx: usize) -> char { self.0 }

        // Our accumulation is pretty contrived; essentially we're counting the sum of the
        // character's numbers from 'a': so 'a' is 1, 'b' is 2, etc.
        type Accumulator = u64;
        fn accumulated(&self, _base: usize, idx: usize) -> u64 {
            match self.0 {
                c @ 'a'..='z' => (c as u8 - b'a' + 1) as u64 * (idx as u64),
                '-' => 27 * idx as u64,
                '_' => 28 * idx as u64,
                _ => panic!("unexpected character used in test: {:?}", self.0),
            }
        }
        fn index_of_accumulated(&self, _base: usize, acc: u64) -> usize {
            let multiplier = match self.0 {
                c @ 'a'..='z' => (c as u8 - b'a' + 1) as u64,
                '-' => 27,
                '_' => 28,
                _ => panic!("unexpected character usedin test: {:?}", self.0),
            };
            assert!(acc % multiplier == 0);
            (acc / multiplier) as usize
        }
        fn split_at(&mut self, _base: usize, _idx: usize) -> Self { *self }
        fn try_join(self, other: Self) -> Result<Self, (Self, Self)> {
            if other.0 == self.0 {
                Ok(self)
            } else {
                Err((self, other))
            }
        }
    }

    // Define a couple helper methods for generating `Ranged`s and testing equality
    impl TestRanged {
        fn from_sizes(default: char, sizes: &[(usize, char)]) -> TestRanged {
            let mut this = Ranged::new(Slice(default), 0);

            for &(s, x) in sizes {
                println!("{}", this.print_tree());

                let i = this.size();
                this.replace(i..i, Ranged::new(Slice(x), s));
            }

            this
        }

        fn assert_matches(&self, sizes: &[(usize, char)]) {
            self.assert_valid();

            let mut so_far = 0;
            for (i, (x, r)) in self.iter().enumerate() {
                assert_eq!(so_far, r.start);
                assert!(i < sizes.len());
                let (s, y) = sizes[i];
                assert_eq!(r.len(), s);
                assert_eq!(x.0, y);
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
    fn do_all_perms<Func>(default: char, initial_sizes: &[(usize, char)], test: Func)
    where
        Func: Fn(TestRanged),
        for<'a> &'a Func: UnwindSafe,
    {
        const MAX_PERM_LEN: usize = 6;

        assert!(
            initial_sizes.len() <= MAX_PERM_LEN,
            "too many sizes to generate all permutations"
        );

        let base = Ranged::from_sizes(default, initial_sizes);

        // The starting indexes of each size:
        let mut idx = 0;
        let indexes = initial_sizes.iter().map(|&(size, _)| {
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
                    r.lock().unwrap().assert_valid();
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
                println!("{}", r.print_tree());
                std::panic::resume_unwind(e);
            }
        }
    }

    #[test]
    fn permuted_access() {
        let sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        do_all_perms('-', &sizes, |r| r.assert_matches(&sizes));
    }

    #[test]
    fn empty_replace() {
        let empty = Ranged::new(Slice('-'), 0);

        let sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        do_all_perms('_', &sizes, |replacement| {
            let mut e = empty.clone();
            e.replace(0..0, replacement).assert_matches(&[]);
            e.assert_matches(&sizes);
        });
    }

    #[test]
    fn insert_start() {
        let sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        let insert = Ranged::from_sizes('-', &sizes[0..1]);
        do_all_perms('-', &sizes[1..], |mut ranged| {
            ranged.replace(0..0, insert.clone()).assert_matches(&[]);
            ranged.assert_matches(&sizes);
        });
    }

    #[test]
    fn insert_middle_aligned() {
        let start_sizes = vec![(4, 'a'), (5, 'c'), (2, 'd')];
        let end_sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];

        let insert = Ranged::from_sizes('-', &[(3, 'b')]);
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged.replace(4..4, insert.clone()).assert_matches(&[]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn insert_middle_unaligned() {
        let start_sizes = vec![(5, 'c'), (2, 'd')];
        let end_sizes = vec![(3, 'c'), (3, 'b'), (2, 'c'), (2, 'd')];

        let insert = Ranged::from_sizes('-', &[(3, 'b')]);
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged.replace(3..3, insert.clone()).assert_matches(&[]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn insert_end() {
        let sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        let insert = Ranged::from_sizes('-', &sizes[3..4]);
        do_all_perms('-', &sizes[..3], |mut ranged| {
            ranged.replace(12..12, insert.clone()).assert_matches(&[]);
            ranged.assert_matches(&sizes);
        });
    }

    #[test]
    fn replace_start_aligned() {
        let start_sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        let end_sizes = vec![(5, 'e'), (3, 'b'), (5, 'c'), (2, 'd')];
        let replacement = Ranged::from_sizes('-', &[(5, 'e')]);
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged
                .replace(0..4, replacement.clone())
                .assert_matches(&[(4, 'a')]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn replace_start_unaligned() {
        let start_sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        let end_sizes = vec![(3, 'e'), (1, 'b'), (5, 'c'), (2, 'd')];
        let replacement = Ranged::from_sizes('-', &[(3, 'e')]);
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged
                .replace(0..6, replacement.clone())
                .assert_matches(&[(4, 'a'), (2, 'b')]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn replace_middle_unaligned() {
        let start_sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        let end_sizes = vec![(4, 'a'), (2, 'b'), (3, 'e'), (3, 'c'), (2, 'd')];
        let replacement = Ranged::from_sizes('-', &[(3, 'e')]);
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged
                .replace(6..9, replacement.clone())
                .assert_matches(&[(1, 'b'), (2, 'c')]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn replace_middle_aligned_left() {
        let start_sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        let end_sizes = vec![(4, 'a'), (3, 'b'), (3, 'e'), (3, 'c'), (2, 'd')];
        let replacement = Ranged::from_sizes('-', &[(3, 'e')]);
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged
                .replace(7..9, replacement.clone())
                .assert_matches(&[(2, 'c')]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn replace_middle_aligned_right() {
        let start_sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        let end_sizes = vec![(4, 'a'), (2, 'b'), (3, 'e'), (5, 'c'), (2, 'd')];
        let replacement = Ranged::from_sizes('-', &[(3, 'e')]);
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged
                .replace(6..7, replacement.clone())
                .assert_matches(&[(1, 'b')]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn replace_middle_aligned_both() {
        let start_sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        let end_sizes = vec![(4, 'a'), (3, 'e'), (2, 'd')];
        let replacement = Ranged::from_sizes('-', &[(3, 'e')]);
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged
                .replace(4..12, replacement.clone())
                .assert_matches(&[(3, 'b'), (5, 'c')]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn replace_end_aligned() {
        let start_sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        let end_sizes = vec![(4, 'a'), (3, 'b'), (2, 'e')];
        let replacement = Ranged::from_sizes('-', &[(2, 'e')]);
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged
                .replace(7..14, replacement.clone())
                .assert_matches(&[(5, 'c'), (2, 'd')]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn replace_end_unaligned() {
        let start_sizes = vec![(4, 'a'), (3, 'b'), (5, 'c'), (2, 'd')];
        let end_sizes = vec![(4, 'a'), (3, 'b'), (2, 'c'), (2, 'e')];
        let replacement = Ranged::from_sizes('-', &[(2, 'e')]);
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged
                .replace(9..14, replacement.clone())
                .assert_matches(&[(3, 'c'), (2, 'd')]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn join_both_ends() {
        let start_sizes = vec![(4, 'a'), (3, 'b'), (2, 'c'), (1, 'b'), (2, 'd')];
        let end_sizes = vec![(4, 'a'), (5, 'b'), (2, 'd')];
        let replacement = Ranged::from_sizes('-', &[(2, 'b')]);
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged
                .replace(6..9, replacement.clone())
                .assert_matches(&[(1, 'b'), (2, 'c')]);
            ranged.assert_matches(&end_sizes);
        });
    }

    #[test]
    fn clone_range_unaligned() {
        let start_sizes = vec![(4, 'a'), (3, 'b'), (2, 'c'), (5, 'd')];
        do_all_perms('-', &start_sizes, |mut ranged| {
            ranged
                .clone_range(5..8)
                .assert_matches(&[(2, 'b'), (1, 'c')]);
        });
    }
}
