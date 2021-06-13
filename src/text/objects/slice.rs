//! Wrapper module for [`ByteSlice`]

use super::INLINE_SIZE;
use crate::text::ranged::{NoAccumulator, RangeSlice};
use crate::text::MaxVec;
use std::ops::{Deref, Range};
use std::sync::Arc;

/// A slice of bytes, inlined or reference-counted
///
/// Large `ByteSlice`s are represented by a range of an `Arc<[u8]>`, so that they can be
/// efficiently split into multiple pieces. Smaller sets of bytes (with length less than
/// [`INLINE_SIZE`]) are stored locally inside a [`MaxVec`], so that we don't "waste" heap
/// allocations on very small slices.
///
/// The primary ways to construct `ByteSlice`s are with the [`new`] and [`from_owned`] methods,
/// which automatically store the provided bytes locally if possible.
#[derive(Clone)]
pub struct ByteSlice(BsKind);

/// The internal representation of a `ByteSlice`
#[derive(Clone)]
enum BsKind {
    Ref {
        backing_array: Arc<[u8]>,
        // Storing the entire range here isn't *strictly* necessary for the implementation of
        // `RangeSlice`, but it's useful to have so that we can reconstruct
        range: Range<usize>,
    },
    Inline(MaxVec<u8, INLINE_SIZE>),
}

impl ByteSlice {
    /// Constructs a new `ByteSlice`, storing the bytes locally if possible.
    ///
    /// For slices that are already owned, [`from_owned`] should be used to avoid reallocation.
    ///
    /// [`from_owned`]: Self::from_owned
    pub fn new(bytes: &[u8]) -> Self {
        if bytes.len() <= INLINE_SIZE {
            ByteSlice(BsKind::Inline(MaxVec::from_slice(bytes)))
        } else {
            ByteSlice(BsKind::Ref {
                backing_array: Arc::from(Box::from(bytes)),
                range: 0..bytes.len(),
            })
        }
    }

    /// Constructs a new `ByteSlice` without reallocation
    ///
    /// This method does not guarantee that the `Box` is not dropped; it will still copy onto the
    /// stack for sufficiently small slices.
    ///
    /// For borrowed data, use the [`new`] method, which takes a `&[u8]`.
    ///
    /// [`new`]: Self::new
    pub fn from_owned(bytes: Box<[u8]>) -> Self {
        let len = bytes.len();

        if bytes.len() <= INLINE_SIZE {
            ByteSlice(BsKind::Inline(MaxVec::from_slice(&bytes)))
        } else {
            ByteSlice(BsKind::Ref {
                backing_array: Arc::from(bytes),
                range: 0..len,
            })
        }
    }

    /// Returns the length of the slice
    pub fn len(&self) -> usize {
        match &self.0 {
            BsKind::Ref { range, .. } => range.len(),
            BsKind::Inline(vec) => vec.len(),
        }
    }
}

impl RangeSlice for ByteSlice {
    type Accumulator = NoAccumulator;

    fn accumulated(&self, _base: usize, _idx: usize) -> NoAccumulator {
        NoAccumulator
    }

    fn index_of_accumulated(&self, _base: usize, _acc: NoAccumulator) -> usize {
        0
    }

    fn split_at(&mut self, _base: usize, idx: usize) -> Self {
        // There's a couple algorithmic notes here:
        //
        // If we're splitting an `Arc`-backed slice into one or more pieces that are smaller than
        // `INLINE_SIZE`, we'll still keep them as referencing the `Arc`. This is so that, if we
        // want to later re-join the pieces, we can allow them to reference the backing `Arc`.
        match &mut self.0 {
            BsKind::Ref {
                backing_array,
                range,
            } => {
                debug_assert!(range.contains(&idx));

                let new_range = range.start + idx..range.end;
                range.end = range.start + idx;

                ByteSlice(BsKind::Ref {
                    backing_array: backing_array.clone(),
                    range: new_range,
                })
            }
            BsKind::Inline(vec) => {
                let new_vec = MaxVec::from_slice(&vec[idx..]);
                let replacement = MaxVec::from_slice(&vec[..idx]);
                *vec = replacement;

                ByteSlice(BsKind::Inline(new_vec))
            }
        }
    }

    #[rustfmt::skip]
    fn try_join(self, self_size: usize, other: Self) -> Result<Self, (Self, Self)> {
        debug_assert!(self_size == self.len());

        // In joining, there's a couple things we'll do -- with a small amount of cheating
        // involved.
        //
        // If both of the slices correspond to the same reference, we'll join them -- but only if
        // their ranges are aligned correctly to do so.
        //
        // If they're both inlined, we'll try to join them. We can't inline them fully if the sum
        // of their lengths is greater than `INLINE_SIZE`, so we have to just return the original
        // pair.

        match (self.0, other.0) {
            // "sa" for "self array", "sr" for "self range", etc.
            (
                BsKind::Ref { backing_array: sa, range: sr },
                BsKind::Ref { backing_array: oa, range: or },
            ) if Arc::ptr_eq(&sa, &oa) && sr.end == or.start => {
                // We can join the arc-backed slices because they point to the same allocation and
                // their ranges touch.
                Ok(ByteSlice(BsKind::Ref {
                    backing_array: sa,
                    range: sr.start..or.end,
                }))
            }
            (
                BsKind::Inline(mut s_vec),
                BsKind::Inline(o_vec),
            ) if s_vec.len() + o_vec.len() <= INLINE_SIZE => {
                // We can join the slices because we know there'll be room for them:
                s_vec.extend_from_slice(&o_vec);
                Ok(ByteSlice(BsKind::Inline(s_vec)))
            }
            // Otherwise, we couldn't join the two byte slices
            (s, o) => Err((ByteSlice(s), ByteSlice(o))),
        }
    }
}

impl Deref for ByteSlice {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        match &self.0 {
            BsKind::Ref {
                backing_array,
                range,
            } => &backing_array[range.clone()],
            BsKind::Inline(vec) => vec.as_ref(),
        }
    }
}
