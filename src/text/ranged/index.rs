//! Wrapper module for the [`RangedIndex`] trait and associated implementations

/// Marker trait for types that can act as an index in a [`Ranged`]
///
/// Typically, `usize` is used as the implementor of this trait.
///
/// The methods here are given individually because the standard library doesn't supply the
/// necessary implementations of the traits that we'd otherwise use instead.
///
/// [`Ranged`]: super::Ranged
pub trait RangedIndex: Copy + Ord {
    /// The maximum allowed size of a [`Ranged`] indexed by this type
    ///
    /// This is typically equal to the maximum value of `Self` over two -- there must be a wide
    /// enough range of possible values beyond `MAX_SIZE` to represent `2 * (MAX_SIZE - 1)`.
    ///
    /// [`Ranged`]: super::Ranged
    const MAX_SIZE: Self;

    /// Returns a string used to display the maximum size
    ///
    /// For `usize`, for example, this is `"\`usize::MAX / 2\`"`
    // @req "<usize as RangedIndex>::max_size_debug_str() text" v0
    fn max_size_debug_str() -> &'static str;

    /// The zero'th index
    const ZERO: Self;

    /// A `Delta` equivalent to "zero" -- i.e. the difference between an index and itself
    const ZERO_DELTA: Self::Delta;

    /// A signed difference between two indexes
    ///
    /// For a type like `usize`, this is `isize`.
    type Delta: Copy + Ord;

    /// Returns the sum of `self` and `other`, essentially `self + other`
    fn add(self, other: Self) -> Self;

    /// Sets `*self = self.add(other)`. The default implmentation should usually suffice
    fn add_assign(&mut self, other: Self) {
        *self = self.add(other)
    }

    /// Returns the difference of `self` from `other`, essentially `self - other`
    ///
    /// ## Panics
    ///
    /// This method must panic if `other > self`.
    fn sub(self, other: Self) -> Self;

    /// Sets `*self = self.sub(other)`. The default implementation should usually suffice
    fn sub_assign(&mut self, other: Self) {
        *self = self.sub(other);
    }

    /// Produces the equivalent of subtracting one from this value
    ///
    /// This method is typically used to get the last index contained within a [`Range`], which is
    /// one less than the upper bound.
    ///
    /// ## Panics
    ///
    /// This method must panic if `self.is_zero()` is true.
    ///
    /// [`Range`]: std::ops::Range
    fn decrement(self) -> Self;

    /// Returns the result of applying the delta to `self`, equivalent to `self + del`
    ///
    /// ## Panics
    ///
    /// This method must panic if the result would be negative
    fn apply_delta(self, del: Self::Delta) -> Self;

    /// Returns the signed difference between `self` and `other`, equivalent to `self - other`
    ///
    /// It should always be the case that:
    /// ```ignore
    /// let d = self.delta_from(other);
    /// other.apply_delta(d) == self
    /// ```
    fn delta_from(self, other: Self) -> Self::Delta;

    /// Converts a `Delta` to the index, panicking if the delta is negative
    ///
    /// ## Panics
    ///
    /// This method *must* panic if `del` is negative.
    fn from_delta(del: Self::Delta) -> Self;

    /// Adds `other` to `del`, equivalent to `*del += other`
    fn delta_add_assign(del: &mut Self::Delta, other: Self::Delta);

    /// Subtracts `other` from `del`, equivalent to `*del -= other`
    fn delta_sub_assign(del: &mut Self::Delta, other: Self::Delta);

    /// Adds the index to the given `Delta`, equivalent to `*del += idx`
    fn delta_add_assign_idx(del: &mut Self::Delta, idx: Self);

    /// Subtracts the index from the given `Delta`, equivalent to `*del -= idx`
    fn delta_sub_assign_idx(del: &mut Self::Delta, idx: Self);
}

#[rustfmt::skip]
impl RangedIndex for usize {
    // @req "Ranged::replace requires less than usize::MAX / 2" v0
    const MAX_SIZE: usize = usize::MAX / 2;

    // @def "<usize as RangedIndex>::max_size_debug_str() text" v0
    fn max_size_debug_str() -> &'static str { "`usize::MAX / 2`" }

    const ZERO: usize = 0;
    const ZERO_DELTA: isize = 0;

    type Delta = isize;

    fn add(self, other: Self) -> Self { self + other }
    fn sub(self, other: Self) -> Self { self - other }
    fn decrement(self) -> Self { self - 1 }

    fn apply_delta(self, del: isize) -> Self { (self as isize + del) as usize }
    fn delta_from(self, other: Self) -> isize { self as isize - other as isize }
    fn from_delta(del: isize) -> Self { del as usize }

    fn delta_add_assign(del: &mut isize, other: isize) { *del += other }
    fn delta_sub_assign(del: &mut isize, other: isize) { *del -= other }
    fn delta_add_assign_idx(del: &mut isize, idx: Self) { *del += idx as isize }
    fn delta_sub_assign_idx(del: &mut isize, idx: Self) { *del -= idx as isize }
}
