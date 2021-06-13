//! The interface for the shared cache inside `TextTree`
//!
//! This essentially just uses the `SizedLruCache` exposed by the sibling `lru` module, but
//! provides a nice API around it.

use super::{CharResult, SizedLruCache};
use crate::text::objects::ByteTree;
use std::ops::Range;

pub struct Cache {
    // If we need to access the actual text of the object multiple times, we store it here. The
    // cache is invalidated on each call to `sync`
    snapshot: Option<ByteTree>,

    // Information about various pieces of the file, depending on the size of the
    sized_cache: SizedLruCache<EntryPos, Entry>,
}

enum Entry {
    Summary {
        line_size: usize,
    },
    // `byte_range` corresponds to the range of bytes *within* the line
    // `widths` gives the *displayed width* of each character, in columns. The vector will be empty
    // if all of the characters have a displayed width of 1 (or if there aren't any characters in
    // `chars`).
    LineSegment {
        byte_range: Range<usize>,
        chars: Vec<CharResult>,
        widths: Vec<u8>,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct EntryPos {
    // The index of the line for this entry
    line_idx: usize,
    // The byte position in the line at which this entry starts. Equal to `None` if
    // `Entry::Summary`, or `Some(byte_range.start)` for `Entry::LineSegment`.
    byte_in_line: Option<usize>,
}

// Maximum cost allowed for a single cache. This really is just set to an arbitrary value; tuning
// it should only really matter for large files -- that's something that can be done later. We just
// need it to be *something* for the time being.
const MAX_CACHE_COST: u64 = 1 << 15; // 1 << 15 = 32768 (2^16)

impl Cache {
    /// Creates a new, empty cache with the default maximum cost
    pub(super) fn new() -> Self {
        Cache {
            snapshot: None,
            sized_cache: SizedLruCache::new(MAX_CACHE_COST),
        }
    }
}

impl Entry {
    /// Returns the cost associated with this entry
    fn cost(&self) -> u64 {
        match self {
            Entry::Summary { .. } => 1,
            // The cost for a line segment is just a rough estimate. It *could* be more or less in
            // terms of actual memory usage, but it's probably *around* this amount.
            Entry::LineSegment {
                byte_range,
                chars,
                widths,
            } => (byte_range.len() + 8 * chars.len() + widths.len()) as u64,
        }
    }
}
