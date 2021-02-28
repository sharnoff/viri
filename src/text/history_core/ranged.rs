//! Wrapper module for the [`Ranged`] type, used in the implementation of [`EditHistory`]
//!
//! Information about the purpose that [`Ranged`] serves is available in the type's documentation.

use std::cmp::Ordering::{self, Equal, Greater, Less};
use std::mem;
use std::ops::Range;

/// A compact representation of uniquely-tagged byte ranges
///
/// This type essentially serves as a better representation of `Vec<T>`, where large ranges of the
/// vector might be the same. The operations on this type guarantee logarithmic time-complexity
/// (and better space requirements!) for the sorts of vector operations that would be linear - like
/// performing a diff-like replacement operation. The tradeoff here is that lookups for the value
/// belonging to a particular index has cost *O(log(n))* instead of *O(1)*.
///
/// This time-complexity tradeoff isn't even *that* bad, though -- internally, we use a structure
/// that's essentially a splay tree, which guarantees constant time lookups for the last node
/// checked. More information on how this works is available in the internal documentation.
///
/// The primary consequence of using a splay tree is that all operations modify the tree, so the
/// methods that might otherwise take `&self` for something like a `BTreeMap` instead take
/// `&mut self` here.
///
/// ## Possible generic type parameters
///
// TODO-DOC: This paragraph needs some heavy reworking
///
/// In order to allow certain features, the type we provide ranges of is actually slightly nuanced.
/// For ranges that are entirely homogenous, the [`Constant`] wrapper type should suffice.
/// Otherwise, the [`RangeSlice`] trait provides an abstraction over the sorts of types that can be
/// used here, supporting both cloning and splitting part-way through.
//
// TODO-DOC - we *really* need some internal documentation here
#[derive(Clone)]
pub struct Ranged<S> {
    size: usize,
    // The root is always `Some(_)` when the structure is in a valid state. We allow it to be
    // `None` so that we can temporarily pass a `&mut Ranged` by value.
    root: Option<Box<Node<S>>>,
}

/// (*Internal*) A helper type for a [`Node`]; a value paired with its size
///
/// This really could have been flattened into the [`Node`] struct itself; the reason it isn't is
/// because having a `size` field in a node might cause confusion; it could be misinterpreted as
/// the total size of all children, which it is not.
#[derive(Clone)]
struct SizePair<S> {
    val: S,
    size: usize,
}

/// (*Internal*) An individual node in the [`Ranged`] splay tree
#[derive(Clone)]
struct Node<S> {
    left: Option<Box<Node<S>>>,
    right: Option<Box<Node<S>>>,
    pair: SizePair<S>,
    offset_from_parent: isize,
}

/// A simple wrapper type that provides an implementation of [`RangeSlice`] for homogenous ranges
///
/// ## When to use this type
///
/// If the regions in your [`Ranged`] instance don't have varying underlying values, this type
/// should do the job. It allows each range to be treated as representing a single value.
///
/// ## When *not* to use this type
///
/// If there's any variation within ranges that you want to preserve, this type can't do it. Those
/// cases are typically fairly specific, so the best solution to implement [`RangeSlice`] yourself
/// - it's generally not too bad.
#[derive(Debug, Copy, Clone)]
pub struct Constant<T>(pub T);

/// An abstraction over values that can represent a single region in a [`Ranged`]
///
/// ## Why does this trait exist?
///
/// When using a [`Ranged`], it's sometimes the case that the values stored in an individual range
/// have some predictable variance (like an increasing counter for each element, for example). We
/// still want to be able to have the benefits of [`Ranged`] when these variations are known
/// beforehand, so this trait provides a layer of abstraction over indexing, splitting, and joining
/// ranges.
///
/// ## Other things to note
///
/// There a couple implementations of this trait provided for you; [`Constant`] and a blanket
/// implementation on [`Option`]. The implementation on [`Option`] works in the expected way: it
/// behaves like [`Constant`] when the values are `None`, and otherwise defers to the underlying
/// ranges
pub trait RangeSlice: Sized {
    /// Cuts the range in two at the given index, returning the upper half
    ///
    /// This is analogous to [`slice::split_at`], but instead modifies the receiver and returns
    /// only the second half of the tuple. As such, after calling this method, `self` should
    /// correspond to `[0, idx)` in the starting range, and the returned value should be
    /// `[idx,len)`.
    ///
    /// The length of the slice is provided for convenience; it will always be the case that `idx`
    /// is less than the length of the range, though this should not be assumed for unsafe code.
    fn split_at(&mut self, idx: usize) -> Self;

    /// Attempts to join the two ranges, returning the original pair as given if unable to
    ///
    /// The values provided are always such that the position of `self` is immediately before
    /// `other`, with `self_size` equal to the size of the range that `self` represents.
    ///
    /// You do not need to implement this function for correct beahvior; the default implementation
    /// always returns `Err((self, other))`. It does, however, keep the tree smaller (at a low
    /// extra on each [`replace`] operation).
    ///
    /// [`replace`]: Ranged::replace
    fn try_join(self, self_size: usize, other: Self) -> Result<Self, (Self, Self)> {
        Err((self, other))
    }
}

/// A [`RangeSlice`] that supports indexing
///
/// This is very similar [`std::ops::Index`], but it's provided here so that any implementations
/// for usage with a [`Ranged`] need not be widely accessible.
///
/// The methods from [`RangeSlice`] are additionally copied over, so that only one implementation
/// is necessary; a blanket impementation of [`RangeSlice`] for all [`IndexedRangeSlice`] is
/// provided.
pub trait IndexedRangeSlice: RangeSlice {
    /// The value provided after indexing
    type Value: Sized;

    /// Gets the value at offset `idx` from the base of the range
    fn index(&self, idx: usize) -> Self::Value;

    /// See [`RangeSlice::split_at`]
    fn split_at(&mut self, idx: usize) -> Self;

    /// See [`RangeSlice::try_join`]
    fn try_join(self, self_size: usize, other: Self) -> Result<Self, (Self, Self)> {
        Err((self, other))
    }
}

impl<S: IndexedRangeSlice> RangeSlice for S {
    fn split_at(&mut self, idx: usize) -> Self {
        <Self as IndexedRangeSlice>::split_at(self, idx)
    }

    fn try_join(self, self_size: usize, other: Self) -> Result<Self, (Self, Self)> {
        <Self as IndexedRangeSlice>::try_join(self, self_size, other)
    }
}

impl<T: Clone + PartialEq> RangeSlice for Constant<T> {
    fn split_at(&mut self, _idx: usize) -> Self {
        self.clone()
    }

    fn try_join(self, _self_size: usize, other: Self) -> Result<Self, (Self, Self)> {
        match self.0 == other.0 {
            true => Ok(self),
            false => Err((self, other)),
        }
    }
}

impl<S: RangeSlice> RangeSlice for Option<S> {
    fn split_at(&mut self, idx: usize) -> Self {
        Some(self.as_mut()?.split_at(idx))
    }

    fn try_join(self, self_size: usize, other: Self) -> Result<Self, (Self, Self)> {
        match (self, other) {
            (None, None) => Ok(None),
            (Some(x), Some(y)) => match x.try_join(self_size, y) {
                Ok(s) => Ok(Some(s)),
                Err((x, y)) => Err((Some(x), Some(y))),
            },
            tuple => Err(tuple),
        }
    }
}

impl<S: RangeSlice> Ranged<S> {
    /// Creates a new [`Ranged<S>`] with the given size and initial filled range
    pub fn new(init: S, size: usize) -> Self {
        Ranged {
            size,
            root: Some(Box::new(Node {
                left: None,
                right: None,
                pair: SizePair { val: init, size },
                offset_from_parent: 0,
            })),
        }
    }

    /// Returns the length of the set of values this represents
    pub fn size(&self) -> usize {
        self.size
    }

    // Provides an immutable reference to the root node
    fn root(&self) -> &Node<S> {
        self.root.as_ref().expect("root node is in invalid state")
    }

    // Provides a mutable reference to the root node
    fn root_mut(&mut self) -> &mut Box<Node<S>> {
        self.root.as_mut().expect("root node is in invalid state")
    }

    // Returns whether the root node contains the given index
    fn root_contains(&self, idx: usize) -> bool {
        let start = self.root_pos();
        let end = start + self.root().pair.size;

        (start..end).contains(&idx)
    }

    // Returns the position of the root node
    fn root_pos(&self) -> usize {
        self.root().offset_from_parent as usize
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
    /// * if the size after insertion would be greater than `usize::MAX / 2`
    // @req "Ranged::replace requires less than usize::MAX / 2" v0
    pub fn replace(&mut self, range: Range<usize>, values: Self) -> Self {
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
    /// # let mut r = Ranged::new(Constant(None), 10);
    /// // Extract the values from that range
    /// let new_val = ranged.replace(3..6, Ranged::new(Constant(None), 3));
    /// // And then use them to create the new ones
    /// ranged.replace(3..6, Ranged::new(Constant(MyWrapper::from(new_val)), 4));
    /// ```
    /// But we can rewrite this as:
    /// ```
    /// # #[derive(PartialEq, Eq)] struct MyWrapper;
    /// # impl MyWrapper { fn from<T>(val: T) -> Self { MyWrapper } }
    /// #
    /// # let mut ranged = Ranged::new(Constant(None), 10);
    /// ranged.replace_with(3..6, |vs| Ranged::new(Constant(MyWrapper::from(vs)), 4));
    /// ```
    ///
    /// ## Panics
    ///
    /// This has the same panic conditions as [`replace`](Self::replace).
    pub fn replace_with(&mut self, range: Range<usize>, func: impl FnOnce(Self) -> Self) {
        if range.start > range.end {
            panic!("invalid range {}..{}", range.start, range.end);
        } else if range.end > self.size {
            panic!(
                "index out of bounds: range.end {} >= size {}",
                range.end, self.size
            );
        }

        // The expected sizes of the regions to the left and right of the range, stored for later
        // so that we can accurately re-build the final `Ranged`
        let left_size = range.start;
        let right_size = self.size - range.end;

        // Extract the values from before the range:
        splay(self.root_mut(), range.start);

        let left = if range.start == 0 {
            None
        } else if self.root_contains(range.start - 1) {
            // |-------- root --------|
            //               |---- range ----|
            // |- left_size -|

            let sub_left = self.root_mut().left.take();
            let left_size = range.start - self.root_pos();

            self.root_mut().pair.size -= left_size;
            self.size -= range.start;
            // we set offset_from_parent to zero here because we just removed all of the nodes up
            // to range.start
            self.root_mut().offset_from_parent = 0_isize;

            // Because we're removing part of the root, we need to shift the location of
            // root.right:
            if let Some(n) = self.root_mut().right.as_mut() {
                n.offset_from_parent -= left_size as isize;
            }

            // Split the left off from the root:
            let mut left_val = self.root_mut().pair.val.split_at(left_size);
            mem::swap(&mut left_val, &mut self.root_mut().pair.val);

            Some(Box::new(Node {
                pair: SizePair {
                    size: left_size,
                    val: left_val,
                },
                left: sub_left,
                right: None,
                offset_from_parent: -(left_size as isize),
            }))
        } else {
            self.size -= self.root_pos();
            let root = self.root_mut();
            root.offset_from_parent = 0_isize;

            root.left.take()
        };

        // Extract the values from after the range
        // We need to move range.end to account for having just shifted everything by removing the
        // nodes up to range.start
        let end = range.len();
        splay(self.root_mut(), end.saturating_sub(1));

        let mut right = if end == self.size {
            None
        } else if self.root_contains(end) {
            let mut sub_right = self.root_mut().right.take();

            // self.root_pos()
            //       |--------- root node ----------|
            // |------- range -------|
            //       |- rhs_in_node -|- right_size -|

            let right_size = self.root_pos() + self.root().pair.size - end;
            let rhs_in_node = self.root().pair.size - right_size;

            if let Some(n) = sub_right.as_mut() {
                n.offset_from_parent -= rhs_in_node as isize;
            }

            self.root_mut().pair.size = rhs_in_node;

            Some(Box::new(Node {
                pair: SizePair {
                    size: right_size,
                    val: self.root_mut().pair.val.split_at(rhs_in_node),
                },
                left: None,
                right: sub_right,
                offset_from_parent: 0,
            }))
        } else {
            self.size = end;
            let root = self.root_mut();
            root.right.take().map(|mut n| {
                n.offset_from_parent -= root.pair.size as isize;
                n
            })
        };

        self.size = range.len();

        // `self` is now done. In order to get its replacement, we need to pass it by value. To do
        // this, we'll temporarily swap it out with a filler `Ranged`:
        #[rustfmt::skip]
        fn temp_extract<S>(this: &mut Ranged<S>) -> Ranged<S> {
            mem::replace(this, Ranged { size: 0, root: None })
        }
        *self = func(temp_extract(self));

        // @def "Ranged::replace requires less than usize::MAX / 2" v0
        if left_size + self.size() + right_size >= usize::MAX / 2 {
            panic!(
                "`Ranged` would be too big! cannot represent a size larger than `usize::MAX / 2`"
            );
        }

        // Having replaced `self`, we can now re-attach the sub-trees on either side that we
        // previously extracted.

        // Add `left`:
        let mut root = self.root_mut();
        splay(root, 0);
        debug_assert!(root.left.is_none());
        root.left = left;
        root.offset_from_parent += left_size as isize;
        self.size += left_size;
        *self = temp_extract(self).try_join_left();

        // Add `right`:
        let size = self.size;
        root = self.root_mut();
        splay(root, size);
        debug_assert!(root.right.is_none());
        if let Some(n) = right.as_mut() {
            n.offset_from_parent += root.pair.size as isize;
        }
        root.right = right;
        self.size += right_size;
        *self = temp_extract(self).try_join_right();

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

        if !left.right.is_none() {
            // If there is a right subchild, we need to move it so that the highest index is at the
            // root.

            // Set the offset to start at zero
            left.offset_from_parent += self.root().offset_from_parent;
            splay(&mut left, root_pos - 1);
            debug_assert!(left.right.is_none());

            // And then return the (new) left node's offset to be relative to the root
            left.offset_from_parent -= self.root().offset_from_parent;
        }

        let mut root = self.root.take().expect("root node is in invalid state");
        match left.pair.val.try_join(left.pair.size, root.pair.val) {
            // If there's an error, we just put things back to where they were before
            Err((left_val, root_val)) => {
                left.pair.val = left_val;
                root.pair.val = root_val;
                root.left = Some(left);
            }
            // If they *do* join, we have to stick the nodes back together
            Ok(single) => {
                let left_size = left.pair.size;
                root.offset_from_parent -= left_size as isize;

                // Because we've shifted the position of the root back, we need to also need to
                // shift the right child
                if let Some(n) = root.right.as_mut() {
                    n.offset_from_parent += left_size as isize;
                }

                root.pair.size += left_size;
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

        if !right.left.is_none() {
            right.offset_from_parent += self.root().offset_from_parent;
            splay(&mut right, root_pos + self.root().pair.size);
            debug_assert!(right.left.is_none());
            right.offset_from_parent -= self.root().offset_from_parent;
        }

        let mut root = self.root.take().expect("root node is in invalid state");
        match (root.pair.val).try_join(root.pair.size, right.pair.val) {
            Err((root_val, right_val)) => {
                root.pair.val = root_val;
                right.pair.val = right_val;
                root.right = Some(right);
            }
            Ok(single) => {
                let root_size = root.pair.size;
                root.pair.size += right.pair.size;
                root.pair.val = single;
                root.right = right.right.map(|mut n| {
                    n.offset_from_parent += root_size as isize;
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
    pub fn iter<'a>(&'a self) -> impl 'a + Iterator<Item = (&'a S, Range<usize>)> {
        struct Iter<'a, S> {
            // The root is `Some` only on the first iteration
            root: Option<&'a Node<S>>,
            // Stack of nodes and their position
            stack: Vec<(usize, &'a Node<S>)>,
        }

        impl<'a, S> Iter<'a, S> {
            fn push_lefts(&mut self, root_parent_pos: usize, root: &'a Node<S>) {
                let mut pos = root_parent_pos;
                let mut r = Some(root);
                while let Some(n) = r {
                    pos = (pos as isize + n.offset_from_parent) as usize;
                    self.stack.push((pos, n));
                    r = n.left.as_ref().map(|b| b.as_ref());
                }
            }
        }

        impl<'a, S> Iterator for Iter<'a, S> {
            type Item = (&'a S, Range<usize>);

            fn next(&mut self) -> Option<Self::Item> {
                if let Some(r) = self.root {
                    self.push_lefts(0, &r);
                    self.root = None;
                }

                match self.stack.pop() {
                    Some((pos, n)) => {
                        if let Some(r) = n.right.as_ref() {
                            self.push_lefts(pos, r);
                        }
                        let range = pos..pos + n.pair.size;
                        Some((&n.pair.val, range))
                    }
                    None => None,
                }
            }
        }

        Iter {
            root: match self.size {
                0 => None,
                _ => Some(self.root()),
            },
            stack: Vec::new(),
        }
    }
}

impl<S: IndexedRangeSlice> Ranged<S> {
    /// Provides the value corresponding to the given index
    ///
    /// ## Panics
    ///
    /// This method will panic if `idx` is greater than or equal to [`self.size()`](Self::size), or
    /// if the implementation of [`RangeSlice`] panics from its indexing method.
    pub fn index(&mut self, mut idx: usize) -> S::Value {
        if idx > self.size() {
            panic!(
                "index out of bounds: the index is {} but the size is {}",
                idx,
                self.size()
            )
        }

        splay(self.root_mut(), idx);
        idx -= self.root_pos();
        self.root().pair.val.index(idx)
    }
}

impl<S: Clone + RangeSlice> Ranged<S> {
    /// Extracts and clones a range of the values
    pub fn clone_range(&mut self, range: Range<usize>) -> Self {
        let mut val = None;
        self.replace_with(range, |r| {
            val = Some(r.clone());
            r
        });
        val.unwrap()
    }
}

#[cfg(test)]
impl<S> Ranged<S> {
    fn print_node(node: &Option<Box<Node<S>>>, prefix: &str, lower: &str) {
        trait Dbg {
            fn make_str(&self) -> String;
        }

        impl<T> Dbg for T {
            default fn make_str(&self) -> String {
                String::new()
            }
        }

        impl<T: std::fmt::Debug> Dbg for T {
            fn make_str(&self) -> String {
                format!(", val = {:?}", self)
            }
        }

        match node {
            None => println!("{}<empty>", prefix),
            Some(n) => {
                println!(
                    "{}offset = {}, size = {}{}",
                    prefix,
                    n.offset_from_parent,
                    n.pair.size,
                    n.pair.val.make_str()
                );
                let left_prefix = format!("{}   ├─ left: ", lower);
                let left_lower = format!("{}   │  ", lower);
                Self::print_node(&n.left, &left_prefix, &left_lower);

                let right_prefix = format!("{}   └─ right: ", lower);
                let right_lower = format!("{}      ", lower);
                Self::print_node(&n.right, &right_prefix, &right_lower);
            }
        }
    }

    pub fn print_tree(&self) {
        println!("--- Print Tree ---");
        println!("size: {}", self.size);
        Self::print_node(&self.root, "root: ", "      ");
        println!("---  End Tree  ---");
    }

    // Checks that the `Ranged` represents a valid set of ranges
    fn assert_valid(&self) {
        fn assert_valid_node<S>(
            node: &Node<S>,
            is_root: bool,
            within_range: Range<usize>,
            parent_pos: usize,
        ) {
            // Check that the recursion is valid
            assert!(is_root || !within_range.contains(&parent_pos));

            // And then on to the actual node checks.
            assert!(node.pair.size != 0);
            let pos = (parent_pos as isize + node.offset_from_parent) as usize;
            assert!(within_range.contains(&pos));
            let end_pos = pos + node.pair.size;
            assert!(end_pos <= within_range.end);

            if let Some(n) = node.left.as_ref() {
                let new_range = within_range.start..pos;
                assert!(!new_range.is_empty());
                assert_valid_node(&n, false, new_range, pos);
            } else {
                assert_eq!(pos, within_range.start);
            }

            if let Some(n) = node.right.as_ref() {
                let new_range = end_pos..within_range.end;
                assert!(!new_range.is_empty());
                assert_valid_node(&n, false, new_range, pos);
            } else {
                assert_eq!(end_pos, within_range.end);
            }
        }

        let root = &self.root.as_ref().unwrap();
        if self.size != 0 {
            assert_valid_node(root, true, 0..self.size, 0);
        } else {
            assert_eq!(root.pair.size, 0);
            assert!(root.left.is_none());
            assert!(root.right.is_none());
        }
    }
}

// Performs the 'splay' operation to bubble the region containing the index to the root
// This is pretty much just adapted from the implementation in Alex Crichton's splay-rs
fn splay<S>(node: &mut Box<Node<S>>, idx: usize) {
    let mut newleft: Option<Box<Node<S>>> = None;
    let mut newright: Option<Box<Node<S>>> = None;

    struct Entry<'a, S> {
        node: &'a mut Option<Box<Node<S>>>,
        parent_pos: usize,
    }

    // This is intentionally backwards; we'll eventually set node.left = l and node.right = r
    //
    // We need to set `parent_pos` equal to `usize::MAX / 2` because adjusting positions down must
    // always result in something non-negative.
    //
    // @req "Ranged::replace requires less than usize::MAX / 2" v0
    let mut l = Entry {
        node: &mut newright,
        parent_pos: usize::MAX / 2,
    };
    let mut r = Entry {
        node: &mut newleft,
        parent_pos: usize::MAX / 2,
    };

    macro_rules! assert_valid {
        ($node:expr) => {{
            if let Some(left) = $node.left.as_ref() {
                debug_assert!(left.offset_from_parent < 0);
            }
            if let Some(right) = $node.right.as_ref() {
                debug_assert!(right.offset_from_parent >= $node.pair.size as isize);
            }
        }};
    }

    fn swap_parent<S>(node: &mut Node<S>, old_pos: usize, new_pos: usize) {
        // old
        //  |---- offset ----|
        //                  pos
        //        |- offset -|
        //       new
        //
        // old + old_offset = pos; new + new_offset = pos
        // ∴ new_offset = old_offset + old - new
        node.offset_from_parent += old_pos as isize - new_pos as isize;
    }

    macro_rules! swap_option_parents {
        ($($n:expr, $old:expr => $new:expr;)+) => {{
            $($n.as_mut().map(|n| swap_parent(n, $old, $new));)+
        }}
    }

    loop {
        let mut node_pos = node.offset_from_parent as usize;

        match idx.cmp_in_range(node_pos..node_pos + node.pair.size) {
            Equal => break,
            Less => {
                // Note: the "parent" of `left` is expected to be `node_pos`.
                let mut left = node.left.take().expect("expected lower value");
                let mut left_pos = stack_pos(node_pos, &left);

                // rotate this node right if necessary
                if idx < left_pos {
                    // set node.left = left.right
                    left.right
                        .as_mut()
                        .map(|n| swap_parent(n, left_pos, node_pos));
                    node.left = left.right.take();
                    assert_valid!(node);

                    // swap left & node:
                    node.offset_from_parent = -left.offset_from_parent;
                    left.offset_from_parent = left_pos as isize;
                    mem::swap(&mut left, node);
                    mem::swap(&mut node_pos, &mut left_pos);
                    assert_valid!(node);

                    // set node.right = left; node.right is currently None because we took
                    // left.right earlier
                    debug_assert!(node.right.is_none());
                    // `left`'s "parent" is still correct; we don't need to update it here.
                    node.right = Some(left);

                    match mem::replace(&mut node.left, None) {
                        Some(l) => {
                            #[allow(unused_assignments)]
                            {
                                // Here, left_pos is never read -- that's mostly fine, but we want
                                // to have this statement here either way for consistency.
                                left_pos = stack_pos(node_pos, &l);
                            }
                            left = l;
                        }
                        None => break,
                    }
                }

                // Broadly: *r = Some(replace(node, left));
                //          r = &mut r.as_mut().unwrap().left;
                //
                // Prepare `left` to replace `node`.
                swap_parent(&mut left, node_pos, 0);
                // Prepare `node` to replace `*r`
                swap_parent(node, 0, r.parent_pos);
                let new_r = mem::replace(node, left);
                r.parent_pos = stack_pos(r.parent_pos, &new_r);
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
                let mut right_pos = stack_pos(node_pos, &right);

                // Rotate left if necessary
                if idx >= right_pos + right.pair.size {
                    // set node.right = right.left
                    right
                        .left
                        .as_mut()
                        .map(|n| swap_parent(n, right_pos, node_pos));
                    node.right = right.left.take();
                    assert_valid!(node);

                    // swap right & node:
                    node.offset_from_parent = -right.offset_from_parent;
                    right.offset_from_parent = right_pos as isize;
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
                                // Here, right_pos is never read -- that's mostly fine, but we want
                                // to have this statement here either way for consistency.
                                right_pos = stack_pos(node_pos, &r);
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
                swap_parent(&mut right, node_pos, 0);
                // Prepare `node` to replace `*l`
                swap_parent(node, 0, l.parent_pos);
                let new_l = mem::replace(node, right);
                l.parent_pos = stack_pos(l.parent_pos, &new_l);
                *l.node = Some(new_l);
                l.node = &mut l.node.as_mut().unwrap().right;
                debug_assert!(l.node.is_none());
            }
        }
    }

    let node_pos = stack_pos(0, &node);
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
        newleft, usize::MAX / 2 => node_pos;
        newright, usize::MAX / 2 => node_pos;
    }

    node.left = newright;
    node.right = newleft;
}

fn stack_pos<S>(base: usize, node: &Node<S>) -> usize {
    (base as isize + node.offset_from_parent) as usize
}

trait CmpInRange {
    fn cmp_in_range(self, range: Range<usize>) -> Ordering;
}

impl CmpInRange for usize {
    fn cmp_in_range(self, range: Range<usize>) -> Ordering {
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
    use super::{IndexedRangeSlice, Ranged};
    use itertools::Itertools;
    use std::fmt::{self, Debug, Formatter};

    type TestRanged = Ranged<Slice>;

    #[derive(Copy, Clone)]
    struct Slice(char);

    impl Debug for Slice {
        fn fmt(&self, f: &mut Formatter) -> fmt::Result {
            self.0.fmt(f)
        }
    }

    #[rustfmt::skip]
    impl IndexedRangeSlice for Slice {
        type Value = char;
        fn index(&self, _idx: usize) -> char { self.0 }
        fn split_at(&mut self, _idx: usize) -> Self { *self }
        fn try_join(self, _size: usize, other: Self) -> Result<Self, (Self, Self)> {
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
        for<'a> &'a Func: std::panic::UnwindSafe,
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
            let mut r = base.clone();
            for &i in &idxs {
                r.index(i);
                r.assert_valid();
            }

            let cloned = r.clone();
            if let Err(e) = std::panic::catch_unwind(|| test(cloned)) {
                println!("panicked with indexing order {:?}", idxs);
                r.print_tree();
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
