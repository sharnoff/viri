//! Wrapper module around [`StdRanged`] and associated traits

use super::{AccumulatorSlice, Ranged};
use std::ops::{AddAssign, Range, SubAssign};

/// The "standard" parameterization of a [`Ranged`], requiring simpler trait implementations
///
/// Please refer to the documentation on [`Ranged`] to see general information about the sorts of
/// problems that this type is designed to solve.
///
/// ## Differences from `Ranged`
///
/// This type is strictly more limited than `Ranged`, but that makes the API much more simple. The
/// indexing type is always `usize` here, and we also assume that `S` has no accumulator.
///
/// For all of the methods, we require that `S` implements [`Slice`] or [`IndexedSlice`], which are
/// simpler traits than [`AccumulatorSlice`].
///
/// All applicable methods are directly taken from [`Ranged`], with near-identical documentation.
#[derive(Clone)]
pub struct StdRanged<S> {
    inner: Ranged<NoAccumulator, usize, isize, S>,
}

/// A simple wrapper type that provides an implementation of [`IndexedSlice`] for homogenous ranges
///
/// ## When to use this type
///
/// If the regions in your [`Ranged`] instance don't have varying underlying values, this type
/// should do the job. It allows each range to be treated as representing a single value.
///
/// ## When *not* to use this type
///
/// If there's any variation within ranges or complex behavior that you want to preserve, this type
/// can't do it. Those cases are typically fairly specific, so the best solution to implement
/// [`Slice`]/[`IndexedSlice`]/[`AccumulatorSlice`] yourself - it's generally not too bad.
#[derive(Debug, Copy, Clone)]
pub struct Constant<T>(pub T);

/// A marker type for [`AccumulatorSlice`] implementations with no actual accumulator
///
/// This type is only really used to provide an implementation of [`AccumulatorSlice`] for types
/// implementing [`IndexedSlice`].
#[derive(Copy, Clone, Debug, Default)]
pub struct NoAccumulator;

/// A marker type for [`AccumulatorSlice`] or [`IndexedSlice`] implementations without a provided
/// value
///
/// This could in theory be any zero-sized type - this is just the one we happen to recommend, for
/// the sake of readability.
#[derive(Copy, Clone, Debug, Default)]
pub struct NoIndex;

#[rustfmt::skip]
impl AddAssign for NoAccumulator { fn add_assign(&mut self, _other: Self) {} }
#[rustfmt::skip]
impl SubAssign for NoAccumulator { fn sub_assign(&mut self, _other: Self) {} }

/// An abstraction over values that can represent a single region in a [`StdRanged`]
///
/// This is the simplest of the `*Slice` traits, and tends to correspond to the majority of use
/// cases. For more information, refer to [`AccumulatorSlice`] or [`IndexedSlice`].
///
/// A blanket implementation of both `AccumulatorSlice` and `IndexedSlice` is provided for any
/// `T: Slice`.
pub trait Slice: Sized {
    /// Cuts the range in two at the given index, returning the upper half
    ///
    /// This is analogous to [`slice::split_at`], but instead modifies the receiver and returns
    /// only the second half of the tuple. As such, after calling this method, `self` should
    /// correspond to `[0, idx)` in the starting range, and the returned value should be
    /// `[idx, len)`.
    fn split_at(&mut self, idx: usize) -> Self;

    /// Attempts to join the two ranges, returning the original pair as given if unable to
    ///
    /// The values provided are always such that the position of `self` is immediately before
    /// `other`.
    ///
    /// It will often be the case that implementing this function is not required for correct
    /// behavior; the default implementation just returns `Err((self, other))`. It does, however,
    /// tend to ensure that the tree remains smaller.
    fn try_join(self, other: Self) -> Result<Self, (Self, Self)>;
}

/// An abstraction over indexable values that represent a single region in a [`StdRanged`]
///
/// This trait is just a simpler version of [`AccumulatorSlice`]; more general information is
/// available there.
///
/// The two main ways this trait is simpler is by (1) only providing the index within the slice,
/// and (2) the restriction to `usize` as the index type.
///
/// A blanket implementation of [`AccumulatorSlice`] is provided for anything implementing this
/// trait, and this trait is also implemented for any type implementing [`Slice`].
pub trait IndexedSlice: Sized {
    /// The value provided by indexing
    ///
    /// If it doesn't make sense to provide an indexed value, just implement [`Slice`] instead;
    /// there is a blanket implementation of `IndexedSlice` for anything implementing `Slice`.
    type Value;

    /// Returns the value at the given offset `idx` inside of the slice
    fn index(&self, idx: usize) -> Self::Value;

    /// Cuts the range in two at the given index, returning the upper half
    ///
    /// This is analogous to [`slice::split_at`], but instead modifies the receiver and returns
    /// only the second half of the tuple. As such, after calling this method, `self` should
    /// correspond to `[0, idx)` in the starting range, and the returned value should be
    /// `[idx, len)`.
    fn split_at(&mut self, idx: usize) -> Self;

    /// Attempts to join the two ranges, returning the original pair as given if unable to
    ///
    /// The values provided are always such that the position of `self` is immediately before
    /// `other`.
    ///
    /// It will often be the case that implementing this function is not required for correct
    /// behavior; the default implementation just returns `Err((self, other))`. It does, however,
    /// tend to ensure that the tree remains smaller.
    fn try_join(self, other: Self) -> Result<Self, (Self, Self)>;
}

// NOTES:
//
// When we provide the export of `StdRanged`, all of the documentation is essentially just
// copy+pasted from the methods on `Ranged`.

impl<S: IndexedSlice> StdRanged<S> {
    /// Creates a new `StdRanged` with the given size and initial filled range
    pub fn new(init: S, size: usize) -> Self {
        StdRanged {
            inner: Ranged::new(init, size),
        }
    }

    /// Returns the length of the set of values this represents
    pub fn size(&self) -> usize {
        self.inner.size()
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
        StdRanged {
            inner: self.inner.replace(range, values.inner),
        }
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
    pub fn replace_with(&mut self, range: Range<usize>, func: impl FnOnce(Self) -> Self) {
        self.inner
            .replace_with(range, |inner| func(StdRanged { inner }).inner);
    }

    /// Creates an iterator over all of the ranges, in order
    ///
    /// This function can be used with [`clone_range`](Self::clone_range) to iterate over a smaller
    /// range.
    pub fn iter<'a>(&'a self) -> impl 'a + Iterator<Item = (&'a S, Range<usize>)> {
        self.inner.iter()
    }

    /// Provides the value corresponding to the given index
    ///
    /// ## Panics
    ///
    /// This method will panic if `idx` is greater than or equal to [`self.size()`](Self::size), or
    /// if the implementation of [`IndexedSlice`] panics from its indexing method.
    pub fn index(&mut self, idx: usize) -> S::Value {
        self.inner.index(idx)
    }
}

impl<S: IndexedSlice + Clone> StdRanged<S> {
    /// Extracts and clones a range of the values
    pub fn clone_range(&mut self, range: Range<usize>) -> Self {
        StdRanged {
            inner: self.inner.clone_range(range),
        }
    }
}

impl<T: Clone + PartialEq> IndexedSlice for Constant<T> {
    type Value = T;

    fn index(&self, idx: usize) -> T {
        self.0.clone()
    }

    fn split_at(&mut self, _idx: usize) -> Self {
        self.clone()
    }

    fn try_join(self, other: Self) -> Result<Self, (Self, Self)> {
        match self.0 == other.0 {
            true => Ok(self),
            false => Err((self, other)),
        }
    }
}

impl<S: Slice> IndexedSlice for S {
    type Value = NoIndex;

    fn index(&self, idx: usize) -> NoIndex {
        NoIndex
    }

    fn split_at(&mut self, idx: usize) -> Self {
        <Self as Slice>::split_at(self, idx)
    }

    fn try_join(self, other: Self) -> Result<Self, (Self, Self)> {
        <Self as Slice>::try_join(self, other)
    }
}

impl<S: IndexedSlice> AccumulatorSlice for S {
    type Idx = usize;

    type IndexedValue = <S as IndexedSlice>::Value;

    fn index(&self, _base: usize, idx: usize) -> Self::IndexedValue {
        <Self as IndexedSlice>::index(self, idx)
    }

    type Accumulator = NoAccumulator;

    fn accumulated(&self, _base: usize, _idx: usize) -> NoAccumulator {
        NoAccumulator
    }

    fn index_of_accumulated(&self, _base: usize, _acc: NoAccumulator) -> usize {
        0
    }

    fn split_at(&mut self, _base: usize, idx: usize) -> Self {
        <Self as IndexedSlice>::split_at(self, idx)
    }

    fn try_join(self, other: Self) -> Result<Self, (Self, Self)> {
        <Self as IndexedSlice>::try_join(self, other)
    }
}

impl<S: IndexedSlice> IndexedSlice for Option<S> {
    type Value = Option<S::Value>;

    fn index(&self, idx: usize) -> Self::Value {
        self.as_ref().map(|s| s.index(idx))
    }

    fn split_at(&mut self, idx: usize) -> Self {
        Some(self.as_mut()?.split_at(idx))
    }

    fn try_join(self, other: Self) -> Result<Self, (Self, Self)> {
        match (self, other) {
            (None, None) => Ok(None),
            (Some(x), Some(y)) => match x.try_join(y) {
                Ok(s) => Ok(Some(s)),
                Err((x, y)) => Err((Some(x), Some(y))),
            },
            tuple => Err(tuple),
        }
    }
}
