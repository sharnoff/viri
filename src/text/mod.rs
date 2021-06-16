//! General processing of text
//!
//! This module exports a few key types.
// TODO-DOC: explain the relation between Textual, Text + Cursor, Paired as implementation,
// low-level *Pos, and implementation in TextTree

use std::ops::Range;

mod cursor;
mod diff;
pub mod grouped_history;
mod history_core;
mod max_vec;
pub mod objects;
pub mod ranged;

pub use cursor::{Cursor, SingleCursor};
pub use diff::Diff;
pub use grouped_history::GroupedHistory;
pub use max_vec::MaxVec;

/// Wrapper type for byte positions within a text object
///
/// Many of the functions in the [`text`](self) module use this wrapper type as a way of
/// disambiguating when it could be unclear (e.g. character position vs. byte position). In
/// general, we use byte positions anyways, but it's often helpful to make this explicit. For
/// example:
/// ```no_run
/// # fn complicated_function() -> usize { 0_usize }
/// let pos: usize = complicated_function();
///
/// // Using `BytePos` makes it unambiguous that we're referring to the byte position.
/// let new_cursor = Cursor::new_single(BytePos(pos));
/// ```
///
/// For the less-used character positioning, see [`CharPos`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BytePos(pub usize);

/// Wrapper type for character positions within a text object
///
/// For general information on why this sort of newtype is useful, refer to the explanation for
/// [`BytePos`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CharPos(pub usize);

/// A trait for string-like objects
///
/// This helps to encapsulate many of the same available methods we might have on a `String`, but
/// in a way that allows us to abstract over the concrete data type storing the data.
///
/// In practice, this is more like a `Vec<u8>` with additional ergonomics to support reading
/// individual characters. Please note that there's absolutely no guarantees that the text is UTF-8
/// encoded, though it usually will be. Other file encodings are not *yet* implemented, but room
/// has been explicitly made for them.
// @req "only utf8 supported but plans for more" v0
pub trait Text {
    /// Returns the full length of the `Text`, in bytes
    fn len(&self) -> usize;

    /// Fills the buffer with the contents of the `Text`, starting at the given index
    ///
    /// ## Panics
    ///
    /// If `start_idx + buf.len()` is greater than `self.len()`, this method should panic.
    fn fill_range(&self, start_idx: usize, buf: &mut [u8]);

    /// Replaces the given byte range with the provided slice of bytes
    fn replace_byte_range(&mut self, range: Range<usize>, with: &[u8]);
}

// TODO-DOC ~ string-like things, paired with a cursor over them. Particularly note that cursors
// must be updated when text changes.
pub trait Textual<Pos>: Text {
    /// Produces a reference to the [`Cursor`] paired with the text
    ///
    /// This trait provides that the value of the cursor does not change outside of any changes
    /// made by [`cursor_mut`], or by changes to the underlying [`Text`].
    ///
    /// [`cursor_mut`]: Self::cursor_mut
    fn cursor(&self) -> &Cursor<Pos>;

    /// Produces a mutable reference to the [`Cursor`] paired with the text
    ///
    /// This trait provides that the value of the cursor can only change through access given by
    /// this method or as a result of changes to the underlying [`Text`].
    fn cursor_mut(&mut self) -> &mut Cursor<Pos>;
}

/// Wraps a [`Text`] with a [`Cursor`] so that it may satisfy the [`Textual`] trait
///
/// This type can essentially be thought of as a concrete type satisfying the interface specified
/// by [`Textual`]. While it typically isn't required that this type be used directly, it does
/// provide a simple way of wrapping any [`Text`] to implement [`Textual`] in the simplest way.
pub struct Paired<T: Text, Pos> {
    text: T,
    cursor: Cursor<Pos>,
}

impl<T: Text, Pos> Text for Paired<T, Pos> {
    fn len(&self) -> usize {
        self.text.len()
    }

    fn fill_range(&self, start_idx: usize, buf: &mut [u8]) {
        self.text.fill_range(start_idx, buf)
    }

    fn replace_byte_range(&mut self, range: Range<usize>, with: &[u8]) {
        self.text.replace_byte_range(range, with)
    }
}

impl<T: Text, Pos> Textual<Pos> for Paired<T, Pos> {
    fn cursor(&self) -> &Cursor<Pos> {
        &self.cursor
    }

    fn cursor_mut(&mut self) -> &mut Cursor<Pos> {
        &mut self.cursor
    }
}
