//! Wrapper module for [`Line`] and [`LineRange`]

use super::{Cache, Encoding};
use crate::text::objects::ByteTree;
use crate::text::ranged::{IndexedRangeSlice, Ranged};
use std::ops::Range;
use std::sync::{Arc, Mutex};

/// A range of bytes, corresponding to a number of lines
pub(super) struct LineRange {
    /// The number of lines contained within the range of bytes represented here
    num_lines: usize,

    /// Whether this range of lines ends with a trailing newline. Joining two `LineRange`s is
    /// guaranteed to succeed if the first doesn't end with a newline.
    ///
    /// The final line in a file will also not end in a trailing newline, which we will not join
    /// with.
    ends_in_newline: bool,

    /// A reference to various cached information about the file, from `TextTree.cache`
    ///
    /// We need access to this cache in order to implement a few different operations, notably
    /// `RangeSlice::split_at` and `RangeSlice::index`.
    cache: Arc<Mutex<Cache>>,
}

/// The "goal" maximum number of bytes that we'll contain in a [`LineRange`]
///
/// An individual `LineRange` *may* contain more, though that will typically be a result of a
/// single, extremely long line. There are a couple other cases, though.
const SPLIT_BYTE_SIZE: usize = 1 << 16; // 1 << 16 = 65536

/// Information about a particular line of the text
///
/// All of the non-trivial values are lazily calculated and externally cached, so that they can be
/// retrieved later if necessary.
pub struct Line {
    // The range of bytes corresponding to this line of the text, including the newline
    byte_range: Range<usize>,

    // Cached information about the particular line, or nothing if the value hasn't been
    // calculated
    info_cache: Arc<Mutex<Cache>>,
    // TODO- more fields, including index into the global cache.
}

/// The maximum number of lines we'll store at a time in a [`LineRange`]
const MAX_LINES: usize = 32;

/// The maximum number of bytes we'll store in a contiguous section in a [`LineRange`]
const MAX_LINE_BYTES: usize = 1 << 10;

/// Constructs the `LineRange`s stored in a `TextTree`, for use at initialization
///
/// This function is *really* only intended to be called in `TextTree::new`, so the cache is
/// assumed to be empty.
pub(super) fn make_ranged<Enc: Encoding>(
    bytes: ByteTree,
    enc: &Enc,
    cache: &Arc<Mutex<Cache>>,
) -> Ranged<LineRange> {
    todo!()
}

impl IndexedRangeSlice for LineRange {
    // The accumulator for a `LineRange` represents the number of lines contained within the range
    type Accumulator = usize;

    fn accumulated(&self, base_idx: usize, idx: usize) -> usize {
        todo!()
    }

    fn index_of_accumulated(&self, base_idx: usize, acc: Self::Accumulator) -> usize {
        todo!()
    }

    type Value = Line;

    fn index(&self, idx: usize) -> Line {
        todo!()
    }

    fn split_at(&mut self, base: usize, idx: usize) -> Self {
        todo!()
    }

    fn try_join(self, _self_size: usize, other: Self) -> Result<Self, (Self, Self)> {
        todo!()
    }
}
