//! Wrapper module for the [`RelativeSet`] type

use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Debug, Formatter};
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::Range;

use super::{AccumulatorSlice, NoAccumulator, NoIndex, NodeRef, Ranged, RangedIndex};

/// Set for values assigned to shifting positions
///
/// The above description is possibly a little confusing, so let's be a little more precise.
/// `RelativeSet` exists to solve a very particular problem:
///
/// > Suppose we have a set of values that are all assigned particular indexes in a large, sparse
/// > array. We want to be able to quickly determine the set of values in a range, in addition to
/// > being able to quickly find the index corresponding to a particular value.
/// >
/// > More importantly, we must also be able to quickly shift all indexes past a certain point by a
/// > particular amount -- akin to shifting line markers in a file when a new line is added.
///
/// This particular problem happens to come up in many different places, once you start looking.
/// It's not immediately obvious how to go about implementing an efficient solution, either. Most
/// solutions won't be able to remove *some* kind of `O(n)` bound on certain operations (indeed, it
/// may be impossible to design a solution without *any* `O(n)` time complexities).
///
/// Our solution happens to provide `log(n)` amortized cost for just about every operation. The
/// only exception is that removal of all the values in a range costs `O(max(k, log n))`, for `k`
/// values in the range and a total of `n` items in the set.
///
/// This particular problem happens to come up a lot in various places, and it isn't immediately
/// obvious how one might go about implementing an efficient solution. For this type, we happen to
/// provide `log(n)` amortized cost for every operation, by means of a few clever tricks.
///
/// The consequence of guaranteeing good algorithmic complexities is that this type does tend to be
/// much heavier-weight than one might initially expect. It's by no means *slow*, but it's
/// certainly not the best solution for small collections of values -- a simpler combination of
/// datastructures will tend to be better for that kind of thing. This type is designed to
/// elegantly handle *many* items -- not necessarily as the average case, but in case the usage
/// patterns of a larger component could necessitate it.
///
/// For more detailed information about the implementation, please see the internal comments.
///
/// ## Examples
///
/// A `RelativeSet` supports the set operations you'd expect, with values tagged by their index:
///
// @def "RelativeSet main doctests" v0
/// ```
/// // Let's just make a set of random editors:
/// let mut set = RelativeSet::new();
/// set.insert(1_usize, "Vim");
/// set.insert(2, "Emacs");
/// set.insert(7, "ne");
/// // We can also insert multiple values at the same index:
/// set.insert(5, "Nano");
/// set.insert(5, "Pico");
///
/// // And then we can retrieve the index of these values:
/// assert_eq!(set.index_of("Emacs"), Some(2));
/// assert_eq!(set.index_of("Nano"), Some(5));
/// assert_eq!(set.index_of("Vim"), Some(1));
///
/// // We can't get the index of values we don't have:
/// assert_eq!(set.index_of("vi"), None);
/// ```
///
/// But on top of this, we support dynamically shifting all of the elements in the set:
///
/// ```
/// # // Taken from above:
/// # let mut set = RelativeSet::new();
/// # set.insert(1_usize, "Vim"); set.insert(2, "Emacs");
/// # set.insert(5, "Nano"); set.insert(5, "Pico");
/// # set.insert(7, "ne");
/// // Continuing from above, suppose we want to clean up the collection.
/// // We have a bit of space between "Emacs" and "Nano"/"Pico" -- maybe
/// // we want to get rid of that space:
/// //
/// // (this method call replaces the range of indexes 3..5 with a blank
/// // slate of size zero. In other words: just delete 3..5)
/// set.clear_and_shift(3..5, 0);
///
/// // "Vim" and "Emacs" haven't changed places, but...
/// assert_eq!(set.index_of("Vim"), Some(1));
/// assert_eq!(set.index_of("Emacs"), Some(2));
/// // ... "Nano"/"Pico" and "ne" have been moved!
/// assert_eq!(set.index_of("Nano"), Some(3));
/// assert_eq!(set.index_of("Pico"), Some(3));
/// assert_eq!(set.index_of("ne"), Some(5));
/// ```
///
/// Some bits of this can get quite complicated -- the method documentation should hopefully help
/// clarify anything that's not clear.
//
// Implementation discussion! So glad you could join :)
//
// The general idea here is that we treat each "index" as a potential node in the underlying
// `Ranged` tree, and store values in individual slices for each index. Instead of separately
// storing slices that do and don't have values, though, we just treat each slice as only
// containing values at the start of its section.
//
// We also maintain references from each value to the node containing it, so that we can
// efficiently retrieve the index of the value -- those are stored in `refs`.
//
// From all of this, we end up using O(n) memory to represent n items, and it costs log(n) to
// insert, get index, and delete. When shifting, it costs min(log(n), k) with k as the number of
// elements removed, because we have to remove each of their entries from `refs`.
pub struct RelativeSet<Idx: RangedIndex, T> {
    ranged: Ranged<NoAccumulator, Idx, Idx::Delta, SetSlice<Idx, T>>,
    refs: HashMap<T, NodeRef<NoAccumulator, Idx, Idx::Delta, SetSlice<Idx, T>>>,
}

// SAFETY: One of the properties mentioned in the documentation of `Ranged` is that the only
// thread-unsafety comes from the possibility of `NodeRef`s being accessed from a different thread
// than the `Ranged` itself.
//
// Because the node references are entirely contained within this type and all operations are
// mutable, we know that the node reference will always be accessed from the same thread as the
// `Ranged` they belong to.
//
// We can therefore implement `Send` and `Sync` as long as `T` permits us to.
unsafe impl<Idx: Send + RangedIndex, T: Send> Send for RelativeSet<Idx, T> {}
unsafe impl<Idx: Sync + RangedIndex, T: Sync> Sync for RelativeSet<Idx, T> {}

////////////////////////////////////////////////////////////
// File structure:                                        //
// ---                                                    //
// * SetSlice                                             //
//   * SetSlice internal methods                          //
//   * SetSlice trait implementations                     //
// * RelativeSet public API                               //
// * RelativeSet trait implementations                    //
////////////////////////////////////////////////////////////

// In the implementation of `AccumulatorSlice` for `SetSlice`, treat each slice as having values
// only at the *start* of its range. In certain cases, e.g. when we need to extend the range of
// values represented by the set, we might temporarily pass around an empty `SetSlice` to signal to
// the `Ranged` that the length has increased by the appropriate amount (even if the empty slice
// just gets joined back to the last `SetSlice`).
struct SetSlice<Idx, T> {
    // TODO-PERF/TODO-FEATURE: In general, a hash set is a bit more expensive than we might want to
    // be using here, especially if we have many sparsely-distributed elements, with `SetSlice`s in
    // general having few elements each.
    vals: HashSet<T>,
    _idx: PhantomData<Idx>,
}

impl<Idx, T: Debug> Debug for SetSlice<Idx, T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.vals.fmt(f)
    }
}

impl<Idx, T> SetSlice<Idx, T> {
    fn new() -> Self {
        SetSlice {
            vals: HashSet::new(),
            _idx: PhantomData,
        }
    }

    // Returns whether the set is empty
    fn is_empty(&self) -> bool {
        self.vals.is_empty()
    }
}

impl<Idx, T: Hash + Eq> SetSlice<Idx, T> {
    // Adds the value to the set
    fn add(&mut self, val: T) {
        self.vals.insert(val);
    }

    // Removes the value from the set, panicking if it wasn't there in the first place
    fn remove(&mut self, val: &T) {
        self.vals.remove(val);
    }
}

#[rustfmt::skip]
impl<Idx: RangedIndex, T> AccumulatorSlice for SetSlice<Idx, T> {
    type Idx = Idx;
    type IndexedValue = NoIndex;

    fn index(&self, _base: Idx, _idx: Idx) -> NoIndex { NoIndex }

    type Accumulator = NoAccumulator;

    fn accumulated(&self, _base: Idx, _idx: Idx) -> NoAccumulator { NoAccumulator }

    fn index_of_accumulated(&self, _base: Idx, _acc: NoAccumulator) -> Idx {
        unreachable!()
    }

    // Splitting doesn't do anything different.
    fn split_at(&mut self, _base: Idx, _idx: Idx) -> Self { SetSlice::new() }

    // Joining fails unless `other` is empty. If `other` *is* empty, then we can simply use the
    // entire range of `self` to account for it.
    fn try_join(self, other: Self) -> Result<Self, (Self, Self)> {
        match other.is_empty() {
            true => Ok(self),
            false => Err((self, other)),
        }
    }
}

impl<Idx: RangedIndex, T> RelativeSet<Idx, T> {
    /// Creates a new, empty `RelativeSet`
    pub fn new() -> Self {
        RelativeSet {
            ranged: Ranged::new_empty(),
            refs: HashMap::new(),
        }
    }
}

impl<Idx: Debug + RangedIndex, T: Clone + Hash + Eq> RelativeSet<Idx, T> {
    /// Returns true if there are no items stored in the set
    ///
    /// The number of items in the set is given by the [`count`] method.
    ///
    /// ## Examples
    ///
    // @def "RelativeSet::is_empty doctests" v0
    /// ```
    /// let mut set = RelativeSet::new();
    /// assert!(set.is_empty());
    ///
    /// set.insert(1_usize, "Vim");
    /// set.insert(2, "Emacs");
    ///
    /// assert!(!set.is_empty());
    ///
    /// set.remove("Emacs");
    /// set.remove("Vim");
    ///
    /// assert!(set.is_empty());
    /// ```
    ///
    /// [`count`]: Self::count
    pub fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    /// Returns the number of items in the set
    ///
    /// To simply check whether the set is empty, the [`is_empty`] method is available.
    ///
    /// ## Examples
    ///
    // @def "RelativeSet::count doctests" v0
    /// ```
    /// let mut set = RelativeSet::new();
    /// assert!(set.is_empty());
    ///
    /// set.insert(1_usize, "Vim");
    /// assert_eq!(set.count(), 1);
    ///
    /// set.insert(2, "Emacs");
    /// set.insert(3, "Pico");
    /// assert_eq!(set.count(), 3);
    ///
    /// assert_eq!(set.remove_range(2..4).count(), 2);
    /// assert_eq!(set.count(), 1);
    /// ```
    ///
    /// [`is_empty`]: Self::is_empty
    pub fn count(&self) -> usize {
        self.refs.len()
    }

    /// Inserts the given value at the index, returning the previous index of the value, if it was
    /// already present
    ///
    /// If the item is already present in the set, this method replaces its location.
    ///
    /// ## Examples
    ///
    // @def "RelativeSet::insert doctests" v0
    /// ```
    /// let mut set = RelativeSet::new();
    /// assert_eq!(set.insert(1_usize, "Pico"), None);
    /// assert_eq!(set.insert(3, "Vim"), None);
    ///
    /// // Re-inserting an item returns its previous index:
    /// assert_eq!(set.insert(6, "Vim"), Some(3));
    /// ```
    pub fn insert(&mut self, idx: Idx, v: T) -> Option<Idx> {
        self.ensure_contains(idx);

        // First: remove the old version, if we have one.
        let old_idx = self.remove(&v);

        // Then, go about actually adding the item
        let mut new_ref = None;

        self.ranged
            .replace_with(idx..idx.increment(), |mut region| {
                let mut set = region.as_single_mut();
                // Add the value to the set for the index, which may be empty
                set.add(v.clone());
                drop(set);
                new_ref = Some(region.root_node_ref());

                region
            });

        self.refs.insert(v, new_ref.unwrap());

        old_idx
    }

    /// Returns the current index of the given item, if it's stored in the set
    ///
    /// To borrow from the documentation of [`HashMap::get`]:
    ///
    /// > The key may be any borrowed form of the map’s key type, but [`Hash`] and [`Eq`] on the
    /// > borrowed form must match those for the key type.
    ///
    /// It will usually suffice to set `S = T`, but other use cases are accounted for here.
    ///
    /// ## Examples
    ///
    // @def "RelativeSet::index_of doctests" v0
    /// ```
    /// let mut set = RelativeSet::new();
    /// set.insert(1_usize, "Vim");
    /// set.insert(5, "Nano");
    ///
    /// assert_eq!(set.index_of("Nano"), Some(5));
    /// assert_eq!(set.index_of("Vim"), Some(1));
    /// assert_eq!(set.index_of("vi"), None);
    /// ```
    pub fn index_of<S: ?Sized>(&mut self, item: &S) -> Option<Idx>
    where
        T: Borrow<S>,
        S: Hash + Eq,
    {
        let r = self.refs.get_mut(item)?;
        let idx = r.current_index();
        // Splay the tree, so that finding the index shares in the O(log n) amortized time
        // guarantee.
        self.ranged.index(idx);

        Some(idx)
    }

    /// Removes the given item, returning its previous index, if it was stored in the set
    ///
    /// ## Examples
    ///
    // @def "RelativeSet::remove doctests" v0
    /// ```
    /// let mut set = RelativeSet::new();
    /// set.insert(1_usize, "Emacs");
    /// set.insert(3, "Vim");
    ///
    /// assert_eq!(set.remove("Emacs"), Some(1));
    /// assert_eq!(set.remove("Nano"), None);
    /// ```
    pub fn remove<S: ?Sized>(&mut self, item: &S) -> Option<Idx>
    where
        T: Borrow<S>,
        S: Hash + Eq,
    {
        let (item, mut r) = self.refs.remove_entry(item)?;
        let idx = r.current_index();

        self.ranged
            .replace_with(idx..idx.increment(), |mut ranged| {
                // Remove the item from the set it belongs to
                ranged.as_single_mut().remove(&item);
                ranged
            });

        Some(idx)
    }

    /// Removes and returns all of the values from the given range and replaces that region with an
    /// empty one of the given size
    ///
    /// The returned `RelativeSet` is entirely valid, with its indexes starting zero where they
    /// previously started from `range.start`.
    ///
    /// All items in the set with indexes greater than `range.end` will have their positions
    /// shifted by `new_size - range.len()`, whichever direction that happens to be.
    ///
    /// A couple special cases are handled in [`remove_range`] and [`shift_right_from`].
    ///
    /// ## Runtime
    ///
    /// The runtime of this method is not `O(log n)`, like most others. Instead, it costs the
    /// minimum of `log n` and `k`, where `k` is the number of items in the returned set. So when
    /// removing ranges with relatively few items, it should still be approximately `log n`. This
    /// is just mentioned here as something to keep in mind, should it become relevant.
    ///
    /// ## Examples
    ///
    // @def "RelativeSet::clear_and_shift doctests" v0
    /// ```
    /// // Construct a small set of items, at various positions:
    /// let mut set = RelativeSet::new();
    /// set.insert(1_usize, "Emacs");
    ///
    /// set.insert(3, "Vim");
    /// set.insert(4, "vi");
    /// set.insert(4, "nvi");
    ///
    /// set.insert(6, "Nano");
    /// set.insert(6, "Pico");
    ///
    /// // We could also write `set.remove_range(2..6)` to perform
    /// // the same operation
    /// let mut extract = set.clear_and_shift(2..6, 0);
    /// assert_eq!(extract.index_of("Vim"), Some(1));
    /// assert_eq!(extract.index_of("vi"), Some(2));
    /// assert_eq!(extract.index_of("nvi"), Some(2));
    ///
    /// assert_eq!(set.index_of("Nano"), Some(2));
    /// assert_eq!(set.index_of("Pico"), Some(2));
    /// assert_eq!(set.index_of("Emacs"), Some(1));
    ///
    /// // We could equivalently use `set.shift_right_from(1, 10)`
    /// assert!(set.clear_and_shift(1..1, 10).is_empty());
    ///
    /// assert_eq!(set.index_of("Emacs"), Some(11));
    /// assert_eq!(set.index_of("Nano"), Some(12));
    /// ```
    ///
    /// [`remove_range`]: Self::remove_range
    /// [`shift_right_from`]: Self::shift_right_from
    pub fn clear_and_shift(&mut self, range: Range<Idx>, new_size: Idx) -> RelativeSet<Idx, T> {
        let replacement = Ranged::new(SetSlice::new(), new_size);

        let removed = self.ranged.replace(range, replacement);

        let mut refs = HashMap::new();
        for (slice, _) in removed.iter() {
            for v in slice.vals.iter() {
                let (v, r) = self.refs.remove_entry(v).unwrap();
                refs.insert(v, r);
            }
        }

        RelativeSet {
            ranged: removed,
            refs,
        }
    }

    /// Removes and returns the values stored in the given range
    ///
    /// This is analogous to calling [`clear_and_shift`] with a new size of zero, and doesn't
    /// implement any special behavior on top of that. For more information, refer to the
    /// documentation on that method.
    ///
    /// [`clear_and_shift`]: Self::clear_and_shift
    pub fn remove_range(&mut self, range: Range<Idx>) -> RelativeSet<Idx, T> {
        self.clear_and_shift(range, Idx::ZERO)
    }

    /// Shifts all of the values to the right of `idx` over by the amount given by `shift`
    ///
    /// More precisely, any element in the set with a position `x >= idx` will be mapped to a new
    /// position of `x + shift`. Note that this includes any elements that may be *at* `idx`.
    ///
    /// This is analogous to caling [`clear_and_shift`] with an empty range, and doesn't implement
    /// any special behavior on top of that. For more information, refer to the documentation on
    /// that method.
    ///
    /// [`clear_and_shift`]: Self::clear_and_shift
    pub fn shift_right_from(&mut self, idx: Idx, shift: Idx) {
        let removed = self.clear_and_shift(idx..idx, shift);
        debug_assert!(removed.is_empty());
    }
}

impl<Idx: Debug + RangedIndex, T: Hash + Eq> RelativeSet<Idx, T> {
    /// (*Internal*) Performs the necessary expansion of the underlying `Ranged` to ensure that we
    /// can place a value at `idx`
    ///
    /// The reason we use this method instead of saying for example, that the `Ranged` has as much
    /// size as it needs, is because we might then run into bounds issues if the logical range used
    /// by the set expands by too much.
    ///
    /// And sure, we could make a modification to `Ranged` so that the rightmost node always has
    /// unbounded size, but that would be a significant complication just to support a particular
    /// feature here that we can easily work around.
    fn ensure_contains(&mut self, idx: Idx) {
        // TODO-CORRECTNESS: In theory, it's possible for a series of insertions in this set to
        // cause the size of the underlying `ranged` to eventuallyyyyy reach usize::MAX / 2, or
        // whatever the upper limit is for the indexing type. This is maybe a bit of a ridiculous
        // case to accomodate, but the fundamental problem is that this bound is unrelated to the
        // actual indexes of the items. This should eventually be fixed.

        let size = self.ranged.size();

        // If there's enough room already, return. Do note that we can't allow `size == idx`,
        // because we need to access the range `idx .. idx + 1`
        if size >= idx.increment() {
            return;
        }

        // We want size >= idx + 1, so we add enough to get size = idx + 1. The amount we need to
        // increase is therefore:
        //     current size + increase = goal size = idx + 1
        //  => increase = idx + 1 - current size
        //
        let size_increase = idx.increment().sub(size);
        self.ranged.insert(size, size_increase, SetSlice::new());
    }
}

// All of the documentation tests from above, copied out into a module so that they get included in
// normal test.
//
// Each test is tagged with `@req` here, with `@def` provided above, in their definitions.
#[cfg(test)]
mod doctests {
    use super::*;

    // @req "RelativeSet main doctests" v0
    #[test]
    fn relative_set_main() {
        let mut set = RelativeSet::new();
        set.insert(1_usize, "Vim");
        set.insert(2, "Emacs");
        set.insert(7, "ne");
        set.insert(5, "Nano");
        set.insert(5, "Pico");

        assert_eq!(set.index_of("Emacs"), Some(2));
        assert_eq!(set.index_of("Nano"), Some(5));
        assert_eq!(set.index_of("Vim"), Some(1));
        assert_eq!(set.index_of("vi"), None);

        set.clear_and_shift(3..5, 0);
        assert_eq!(set.index_of("Vim"), Some(1));
        assert_eq!(set.index_of("Emacs"), Some(2));
        assert_eq!(set.index_of("Nano"), Some(3));
        assert_eq!(set.index_of("Pico"), Some(3));
        assert_eq!(set.index_of("ne"), Some(5));
    }

    // @req "RelativeSet::is_empty doctests" v0
    #[test]
    fn relative_set_is_empty() {
        let mut set = RelativeSet::new();
        assert!(set.is_empty());

        set.insert(1, "Vim");
        set.insert(2, "Emacs");

        assert!(!set.is_empty());

        set.remove("Emacs");
        set.remove("Vim");

        assert!(set.is_empty());
    }

    // @req "RelativeSet::count doctests" v0
    #[test]
    fn relative_set_count() {
        let mut set = RelativeSet::new();
        assert!(set.is_empty());

        set.insert(1_usize, "Vim");
        assert_eq!(set.count(), 1);

        set.insert(2, "Emacs");
        set.insert(3, "Pico");
        assert_eq!(set.count(), 3);

        let removed = set.clear_and_shift(2..4, 0);
        assert_eq!(removed.count(), 2);
        assert_eq!(set.count(), 1);
    }

    // @req "RelativeSet::insert doctests" v0
    #[test]
    fn relative_set_insert() {
        let mut set = RelativeSet::new();
        assert_eq!(set.insert(1_usize, "Pico"), None);
        assert_eq!(set.insert(3, "Vim"), None);

        assert_eq!(set.insert(6, "Vim"), Some(3));
    }

    // @req "RelativeSet::index_of doctests" v0
    #[test]
    fn relative_set_index_of() {
        let mut set = RelativeSet::new();
        set.insert(1_usize, "Vim");
        set.insert(5, "Nano");

        assert_eq!(set.index_of("Nano"), Some(5));
        assert_eq!(set.index_of("Vim"), Some(1));
        assert_eq!(set.index_of("vi"), None);
    }

    // @req "RelativeSet::remove doctests" v0
    #[test]
    fn relative_set_remove() {
        let mut set = RelativeSet::new();
        set.insert(1_usize, "Emacs");
        set.insert(3, "Vim");

        assert_eq!(set.remove("Emacs"), Some(1));
        assert_eq!(set.remove("Nano"), None);
    }

    // @req "RelativeSet::clear_and_shift doctests" v0
    #[test]
    fn relative_set_clear_and_shift() {
        let mut set = RelativeSet::new();
        set.insert(1_usize, "Emacs");

        set.insert(3, "Vim");
        set.insert(4, "vi");
        set.insert(4, "nvi");

        set.insert(6, "Nano");
        set.insert(6, "Pico");

        // We could also write `set.remove_range(2..6)` to perform
        // the same operation
        let mut extract = set.clear_and_shift(2..6, 0);
        assert_eq!(extract.index_of("Vim"), Some(1));
        assert_eq!(extract.index_of("vi"), Some(2));
        assert_eq!(extract.index_of("nvi"), Some(2));

        assert_eq!(set.index_of("Nano"), Some(2));
        assert_eq!(set.index_of("Pico"), Some(2));
        assert_eq!(set.index_of("Emacs"), Some(1));

        // We could equivalently use `set.shift_right_from(1, 10)`
        assert!(set.clear_and_shift(1..1, 10).is_empty());

        assert_eq!(set.index_of("Emacs"), Some(11));
        assert_eq!(set.index_of("Nano"), Some(12));
    }
}
