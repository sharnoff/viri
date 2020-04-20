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
//! [`Sizes`]: struct.Sizes.html

/// The raison d'etre of this sub-module
///
/// This type is explained in more detail at the [module level].
///
/// [module level]: index.html
// TODO: Allow a second option: to store *every* size we're tracking
#[derive(Debug, Clone)]
pub struct Sizes {
    // Tracks individual occurances of non-standard sizes
    internal: Vec<SingleSize>,
}

/// A singly mapped value with a non-standard inner index size
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct SingleSize {
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

impl Sizes {
    /// Creates a new, blank `Sizes`
    pub const fn new() -> Self {
        Self {
            internal: Vec::new(),
        }
    }

    /*
    // Note: Disabled because it wasn't used.

    /// Adds a new, non-standard value to the end of the [`Sizes`] by its outer index
    pub fn append_by_outer_idx(&mut self, outer_idx: usize, size: usize) {
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
        });
    }
    */

    /// Adds a new, non-standard value to the end of the [`Sizes`] by its inner index
    pub fn append_by_inner_idx(&mut self, inner_idx: usize, size: usize) {
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
