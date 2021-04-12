//! Management of individual text objects, using shared references to immutable backing arrays

use std::ops::Range;
use std::sync::Arc;
use tokio::sync::RwLock;

use crate::init::LazyInit;
use crate::macros::{id, make_extension};

static SLICES: LazyInit<RwLock<Vec<Arc<[u8]>>>> = LazyInit::new();

make_extension! {
    path: text,
    aliases: ["Text"],
    exports: [],
    init: {
        SLICES.initialize_with(RwLock::new(Vec::new()));
    }
}

const MAX_SLICE_SICE: usize = 1_usize << 20;

id! {
    pub struct SliceId in [Arc<[u8]>];
}

struct TextSlice {
    range: Range<usize>,
    id: SliceId,
    arc: Arc<[u8]>,
}

impl TextSlice {
    /// Constructs a new `TextSlice` from the provided identifier
    pub async fn from_id(id: SliceId, range: Range<usize>) -> Option<TextSlice> {
        let guard = SLICES.read().await;
        todo!()
    }

    /// Allocates a new `TextSlice`, based on the
    pub async fn alloc_new(bytes: Box<[u8]>) -> TextSlice {
        let mut guard = SLICES.read().await;
        todo!()
    }

    /// An internal method for getting the full slice of bytes that the value represents
    pub fn get(&self) -> &[u8] {
        &self.arc[self.range.clone()]
    }

    /// Retrieves the unique identifier corresponding to the `TextSlice`
    pub fn id(&self) -> SliceId {
        self.id
    }
}

/// Gets the slice of text with the given byte range, provided it is valid
async fn slice_values(id: usize, range: (usize, usize)) -> Result<Vec<u8>, String> {
    if range.0 > range.1 {
        return Err(format!("invalid range: {:?}", range));
    }

    let r = range.0..range.1;

    let guard = SLICES.read().await;
    let arc = guard
        .get(id)
        .ok_or_else(|| format!("no `TextSlice` with id {}", id))?
        .clone();
    drop(guard);

    arc.get(r)
        .ok_or_else(|| {
            format!(
                "range end {} out of range for length {}",
                range.1,
                arc.len()
            )
        })
        .map(|slice| slice.to_owned())
}
