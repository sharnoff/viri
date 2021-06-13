//! Wrapper module for [`ByteTree`]

use std::io::{self, Read};
use std::marker::Unpin;
use std::ops::Range;
use tokio::io::AsyncRead;

use super::{ByteSlice, Ranged};

/// The low-level, byte-wise representation of a text object
///
/// This is extracted out separately in order for multiple higher-level text objects to reference
/// the same shared allocations. An individual `ByteTree` doesn't have the synchronization required
/// to handle this sharing -- it only manages the low-level operations.
///
/// For higher-level sharing of `ByteTree`s, refer to the [`SharedByteTree`] object.
///
/// [`SharedByteTree`]: super::SharedByteTree
///
/// ## Performance characteristics
///
// @req "`Ranged` is splay tree" v0
///
/// `ByteTree` is represented internally as a splay tree, with `ByteSlice`s as nodes, and each one
/// tagged with its relative index in the text. Because of this, we have `O(log(k))` amortized
/// replacement and indexing, for `k` slices. Retrieving a range of bytes may be up to `O(k)`, just
/// because it could require accessing each node in the tree, though typically it will also be
/// cheap.
///
// TODO-ALG: See this comment.
/// Currently, we have no way of moving from multiple inlined slices into a larger heap-allocated
/// one. This may be added in the future in order to improve locality of reference on files that
/// have been heavily-modified. The overall effect of the current design is that `k` tends to be
/// proportional to the number of edits that have been made to the file.
#[derive(Clone)]
pub struct ByteTree {
    bytes: Ranged<ByteSlice>,
}

impl ByteTree {
    //////////////////////////////////////////
    // ByteTree construction -- all methods //
    //////////////////////////////////////////

    /// Creates an empty `ByteTree`
    ///
    /// This is typically reserved only for creating a new text object. Other methods are provided
    /// for constructing from other sources, e.g. [`from_io`]/[`from_io_stream`].
    ///
    /// [`from_io`]: Self::from_io
    /// [`from_io_stream`]: Self::from_io_stream
    pub fn empty() -> Self {
        let init = ByteSlice::new(&[]);

        ByteTree {
            bytes: Ranged::new(init, 0),
        }
    }

    /// Reads a new `ByteTree` from the provided reader
    ///
    /// Typically, [`from_io_stream`] should be used instead - but this method is provided
    /// nonetheless.
    ///
    /// [`from_io_stream`]: Self::from_io_stream
    ///
    /// ## Errors
    ///
    /// This function only returns an error if the reader being called returns one. Otherwise, it
    /// successfully returns the new `ByteTree`.
    pub fn from_io(mut reader: impl Read) -> io::Result<Self> {
        let mut buf: Vec<u8> = Vec::new();

        reader.read_to_end(&mut buf)?;

        Ok(Self::from_single_array(buf.into_boxed_slice()))
    }

    /// Reads a new `ByteTree` from the provided asynchronous reader
    ///
    /// This function is typically preferred over [`from_io`] (the synchronous counterpart to this
    /// function), but both are provided nonetheless.
    ///
    /// [`from_io`]: Self::from_io
    ///
    /// ## Errors
    ///
    /// This function only returns an error if the reader being called returns one. Otherwise, it
    /// successfully returns the new `ByteTree`.
    pub async fn from_io_stream(mut reader: impl AsyncRead + Unpin) -> io::Result<Self> {
        // `Vec<u8>` implements `AsyncWrite`, so we can pull all of the bytes by copying into it:
        let mut buf: Vec<u8> = Vec::new();

        tokio::io::copy(&mut reader, &mut buf).await?;

        Ok(Self::from_single_array(buf.into_boxed_slice()))
    }

    /// (*Internal*) Constructs the `ByteTree` from a single backing array
    fn from_single_array(array: Box<[u8]>) -> Self {
        let len = array.len();

        let slice = ByteSlice::from_owned(array);

        ByteTree {
            bytes: Ranged::new(slice, len),
        }
    }

    //////////////////////////
    // Other public methods //
    //////////////////////////

    /// Returns the total length of the text represented by the `ByteTree`, in bytes
    pub fn len(&self) -> usize {
        self.bytes.size()
    }
}

impl crate::text::diff::ByteReplace for ByteTree {
    fn length(&self) -> usize {
        self.len()
    }

    fn is_eq(&mut self, start_idx: usize, bytes: &[u8]) -> bool {
        // We can assume that `start_idx + bytes.len() < self.length()` -- the trait requires it.
        // If we panic, that's the caller's fault.
        let range = self.bytes.clone_range(start_idx..start_idx + bytes.len());

        let mut idx = 0;
        for (slice, _) in range.iter() {
            let len = slice.len();
            if &slice as &[u8] != &bytes[idx..idx + len] {
                return false;
            }

            idx += len;
        }

        true
    }

    fn replace(&mut self, replace: Range<usize>, with: &[u8]) {
        let slice = ByteSlice::new(with);
        let values = Ranged::new(slice, with.len());

        self.bytes.replace(replace, values);
    }
}
