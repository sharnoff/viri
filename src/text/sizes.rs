//! Utilities for a helper type in `text`
//!
//! This module defines the key type [`Sizes`].
//!
//! ## Motivation
//!
//! The `Sizes` type exists because some lines of text may contain characters encoded by multiple
//! bytes (in the case of UTF-8 encoded text), and some characters may have a width of greater than
//! a single column - among a couple other cases. `Sizes` tracks these non-standard characters so
//! that we can efficiently handle them. There are essentially two ways of going about this - either
//! storing the entire map from characters to location in a line's width, or storing them
//! individually. Currently, `Sizes` opts for the latter.
//!
//! These are described as "indexing schemes" for the sake of consistent terminology. The mapping
//! provided by `Sizes` goes from an "outer indexing scheme" to an inner one, where the outer
//! scheme consists of values which may be composed of some number of inner ones. For example: if we
//! model the relationship from characters to their byte encodings, each character has some number
//! of bytes, so the outer indexing scheme would be the characters and the inner one would be their
//! indices in whatever encoded text they represent.
//!
//! The `Sizes` type also has an associated type parameter - this is to allow data (e.g. color for
//! syntax highlighting) to be stored inside each outer index.
//!
//! [`Sizes`]: struct.Sizes.html

use std::ops::Range;

/// The raison d'etre of this sub-module
///
/// This type is explained in more detail at the [module level].
///
/// [module level]: index.html
// TODO: Allow a second option: to store *every* size we're tracking
#[derive(Debug, Clone)]
pub struct Sizes<T: Copy> {
    // Tracks individual occurances of non-standard sizes
    internal: Vec<SingleSize<T>>,
}

/// A singly mapped value with a non-standard inner index size
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct SingleSize<T: Copy> {
    /// The outer index of the value
    ///
    /// The distinction between inner and outer indexes is given at the module-level.
    outer_idx: usize,

    /// The *starting* inner index of the value
    ///
    /// The distinction between inner and outer indexes is given at the module-level.
    inner_idx: usize,

    /// The *inner* size of the value - i.e. the difference in inner indices between this value and
    /// the next.
    size: usize,

    /// The attached value for the index - typically the unit struct `()`
    data: T,
}

/// The result of indexing by inner index
///
/// The four fields here give the permutations of results from indexing a [`Sizes`] by *inner index*
/// (explained [in the module root]). Because inner indices may sometimes be in the middle of an
/// outer value, this serves to allow the distinction of rounding in either direction. Being "in
/// the middle" has a specific meaning here, so it will be elaborated upon briefly.
///
/// A sibling file in the this directory, 'sizes.rs-proof-2.png', gives some of the reasoning
/// behind why different types of `InnerIndexResult`s are returned under certain situations. Aside
/// from attempting to decipher that, a brief overview is simply this:
///
/// When indexing by some inner index `i`, either `i` is at the start of an outer value or it is
/// not. If and only if `i` is not at the start of an outer value, the rounding options will be
/// distinct. All other cases (including `i` being at the start of a non-standard value) will give
/// results with equal upper and lower rounding.
///
/// [`Sizes`]: struct.Sizes.html
/// [in the module root]: index.html
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct InnerIndexResult {
    /// The pair of indices corresponding to the value from rounding down
    pub round_down: IndexPair,

    /// The pair of indices corresponding to the value from rounding up
    pub round_up: IndexPair,
}

/// Represents a matching pair of indices for a single value, produced by indexing a [`Sizes`]
///
/// [`Sizes`]: struct.Sizes.html
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct IndexPair {
    /// The inner index
    pub inner: usize,
    /// The outer index
    pub outer: usize,
}

impl<T: Copy + std::fmt::Debug> Sizes<T> {
    /// Creates a new, blank `Sizes`
    pub const fn new() -> Self {
        Self {
            internal: Vec::new(),
        }
    }

    /// Adds a new, non-standard value to the end of the `Sizes` by its outer index
    pub fn append_by_outer_idx(&mut self, outer_idx: usize, size: usize, data: T) {
        let inner_idx = match self.internal.last() {
            None => outer_idx,
            Some(s) => {
                // A proof of this logic can be found in a neighboring file,
                // 'sizes.rs-proof-1.png'
                s.inner_idx + s.size + outer_idx - s.outer_idx - 1
            }
        };

        self.internal.push(SingleSize {
            outer_idx,
            inner_idx,
            size,
            data,
        });
    }

    /// Adds a new, non-standard value to the end of the `Sizes` by its inner index
    pub fn append_by_inner_idx(&mut self, inner_idx: usize, size: usize, data: T) {
        let outer_idx = match self.internal.last() {
            // If there aren't any previous non-standard values, the outer index will be equal to
            // the inner index
            None => inner_idx,
            Some(s) => {
                // A proof of this logic can be found in a neighboring file,
                // 'sizes.rs-proof-1.png'
                s.outer_idx + inner_idx + 1 - (s.inner_idx + s.size)
            }
        };

        self.internal.push(SingleSize {
            outer_idx,
            inner_idx,
            size,
            data,
        });
    }

    /// Attempts to retrieve the outer index corresponding to the given inner one
    ///
    /// More information is provided in the documentation for [`InnerIndexResult`].
    ///
    /// [`InnerIndexResult`]: struct.InnerIndexResult.html
    pub fn try_idx_from_inner(&self, idx: usize) -> InnerIndexResult {
        // This function contains a hefty bit of logic that is not immediately
        // obvious. Justification of that logic can be found in the neighboring file
        // 'sizes.rs-proof-2.png'

        match self.internal.binary_search_by_key(&idx, |s| s.inner_idx) {
            Ok(i) => {
                // If we actually find a value with the inner index, this is the
                // easiest case to handle! The index we were looking for was nicely
                // aligned at an unusual value.
                let s = self.internal[i];
                InnerIndexResult::exact(s.inner_idx, s.outer_idx)
            }
            Err(i) => {
                if i == 0 {
                    return InnerIndexResult::exact(idx, idx);
                }

                let s = self.internal[i - 1];

                if s.inner_idx + s.size <= idx {
                    let outer = s.outer_idx + idx - (s.inner_idx + s.size) + 1;
                    InnerIndexResult::exact(idx, outer)
                } else {
                    InnerIndexResult {
                        round_down: IndexPair {
                            inner: s.inner_idx,
                            outer: s.outer_idx,
                        },
                        round_up: IndexPair {
                            inner: s.inner_idx + s.size,
                            outer: s.outer_idx + 1,
                        },
                    }
                }
            }
        }
    }

    /// Gives the inner index corresponding to the given outer one
    pub fn idx_from_outer(&self, idx: usize) -> usize {
        match self.internal.binary_search_by_key(&idx, |s| s.outer_idx) {
            Ok(i) => {
                let s = self.internal[i];
                s.inner_idx
            }
            Err(i) => {
                if i == 0 {
                    return idx;
                }

                let s = self.internal[i - 1];
                let inner = s.inner_idx + s.size + (idx - s.outer_idx - 1);
                inner
            }
        }
    }

    /// Produces an iterator over the ranges of inner indices, alongside their values (if they
    /// exist)
    pub fn inner_regions<'a>(&'a self, inner_range: Range<usize>) -> InnerRegions<'a, T> {
        let start = self.try_idx_from_inner(inner_range.start).round_down.outer;

        // This function should never have a range given to it where the final value is zero, but
        // if that *does* happen, we'll allow it to pass with an empty range, isntead of panicking
        // on an underflow.
        let end = match inner_range.end {
            // if the provided range has 0 as the end (which it never should), we'll just short-cut
            // to have *our* end index as zero, instead of
            0 => 0,
            // We do these adjustments (-1, then +1) to ensure that the end is truly exclusive.
            e => self.try_idx_from_inner(e - 1).round_down.outer + 1,
        };

        let next_idx = (self.internal)
            .binary_search_by_key(&start, |s| s.outer_idx)
            .unwrap_or_else(|i| i);

        InnerRegions {
            sizes: self,
            start: inner_range.start,
            end: inner_range.end,
            remaining: start..end,
            next_idx,
        }
    }
}

impl InnerIndexResult {
    /// Produces an `InnerIndexResult` where the values from rounding up and down are identical
    ///
    /// This is mostly used as a shorthand in the [`try_idx_from_inner`] method on [`Sizes`].
    ///
    /// [`try_idx_from_inner`]: struct.Sizes.html#method.try_idx_from_inner
    /// [`Sizes`]: struct.Sizes.html
    fn exact(inner: usize, outer: usize) -> Self {
        Self {
            round_down: IndexPair { inner, outer },
            round_up: IndexPair { inner, outer },
        }
    }
}

impl IndexPair {
    /// Converts the index pair into a tuple of (inner, outer) indices
    ///
    /// This is provided for syntactic elegance of destructuring when getting both values is
    /// necessary.
    pub fn tuple(self) -> (usize, usize) {
        (self.inner, self.outer)
    }
}

/// An iterator over "regions" of inner values.
///
/// Where present, this corresponds to the outer indices. All inner indicies not directly under a
/// non-standard outer index will be grouped into larger regions, with a yielded value of `None`
/// alongside their range.
#[derive(Debug)]
pub struct InnerRegions<'a, T: Copy> {
    sizes: &'a Sizes<T>,

    /// The starting inner index, used to artificially shorten the first range given
    start: usize,
    /// The ending inner index, used to artificially shorten the last range given
    end: usize,
    /// The outer indicies that have yet to be used to produce a region.
    remaining: Range<usize>,
    /// The index of the next applicable element in the list of `SingleSize`s corresponding to the
    /// value of `remaining.start`
    next_idx: usize,
}

impl<'a, T: std::fmt::Debug + Copy> Iterator for InnerRegions<'a, T> {
    type Item = (Range<usize>, Option<T>);

    fn next(&mut self) -> Option<Self::Item> {
        // Just a simple case to handle for weird input
        if self.start >= self.end || self.remaining.start >= self.remaining.end {
            return None;
        }

        let (start, end, val) = loop {
            // If the next index is what we're looking for, we'll use the value and increment the
            // next index.
            //
            // This is - by far - the common case for the usage of this iterator.
            let exact_outer_idx = self.sizes.internal.get(self.next_idx).map(|s| s.outer_idx);
            if exact_outer_idx == Some(self.remaining.start) {
                let s = self.sizes.internal[self.next_idx];
                self.next_idx += 1;
                self.remaining.start += 1;
                break (s.inner_idx, s.inner_idx + s.size, Some(s.data));
            }

            // If we didn't have the value directly, we'll produce a range of inner values from
            // here to the start of the next outer value.
            //
            // If the index for the next `SingleSize` is equal to the length of the internal list,
            // we can just take all of the remaining inner values.
            match self.next_idx.checked_sub(1).map(|i| self.sizes.internal[i]) {
                // If the subtraction failed, `next_idx` is zero.
                None => {
                    // If there aren't any elements, we just give the entire range.
                    if self.sizes.internal.is_empty() {
                        let start = self.remaining.start;
                        self.remaining.start = self.remaining.end;
                        break (start, self.remaining.end, None);
                    }

                    // Otherwise, we look to the next outer index to get the end point for this
                    // region.
                    //
                    // The start is zero because we know we're at the beginning of the range.
                    // Similarly, the end is equal to the inner index of the first group
                    let start = 0;
                    let end = self.sizes.internal[self.next_idx].inner_idx;
                    self.remaining.start = self.sizes.internal[self.next_idx].outer_idx;
                    break (start, end, None);
                }

                // Otherwise, the range is relative to the previous, so we calculate the start in
                // this way. This is copied from `idx_from_outer`, in the `Err` case
                Some(s) => {
                    let start = s.inner_idx + s.size + (self.remaining.start - s.outer_idx - 1);

                    // Remember: for each region, we're collecting all of the space between entries
                    // for outer indices - the end goes to the next entry, if it exists.
                    let (end, rem) = match self.sizes.internal.get(self.next_idx) {
                        // No more values, so we'll just go straight to the end
                        None => (self.end, self.remaining.end),
                        Some(next) => (next.inner_idx, next.outer_idx),
                    };

                    self.remaining.start = rem;
                    break (start, end, None);
                }
            }
        };

        let range = start.max(self.start)..end.min(self.end);

        Some((range, val))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_regions() {
        // Test data:
        //
        // Outer on top, inner on bottom:
        // 0 1       2     3 4     5 6 7 8
        // | |       |     | |     | | | |
        // | |  <3>  | <4> | | <5> | | | |
        // | | | | | | | | | | | | | | | |
        // 0         5         10        15
        let expected = vec![
            (0..1, None),
            (1..5, Some(3)),
            (5..8, Some(4)),
            (8..9, None),
            (9..12, Some(5)),
            (12..15, None),
        ];

        let mut sizes: Sizes<i32> = Sizes::new();
        sizes.append_by_inner_idx(1, 4, 3);
        sizes.append_by_inner_idx(5, 3, 4);
        sizes.append_by_inner_idx(9, 3, 5);

        let regions = sizes.inner_regions(0..15).collect::<Vec<_>>();
        assert_eq!(regions, expected);
    }

    // This is an actual example that failed at one point, so this test is the remnant of debugging
    // that failure
    #[test]
    fn foo_bar() {
        // 0     1         2 3                                       4 5
        // |     |         | |                                       | | |
        // | <1> |   <2>   <3>                  <4>                  <5|6>
        // | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |
        // 0         5         10        15        20        25        30

        let expected = vec![
            (0..3, Some(1)),
            (3..8, Some(2)),
            (8..9, Some(3)),
            (9..28, Some(4)),
            (28..29, Some(5)),
            (29..30, Some(6)),
        ];

        let mut sizes: Sizes<i32> = Sizes::new();
        sizes.append_by_inner_idx(0, 3, 1);
        sizes.append_by_inner_idx(3, 5, 2);
        sizes.append_by_inner_idx(8, 1, 3);
        sizes.append_by_inner_idx(9, 19, 4);
        sizes.append_by_inner_idx(28, 1, 5);
        sizes.append_by_inner_idx(29, 1, 6);

        let regions = sizes.inner_regions(0..30).collect::<Vec<_>>();
        assert_eq!(regions, expected);
    }
}
