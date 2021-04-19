//! General processing of text
//!
//! This module exports a few key types.
// TODO-DOC: explain the relation between Textual, Text + Cursor, Paired as implementation,
// low-level Pos

mod cursor;
mod diff;
pub mod history;
mod history_core;

pub use cursor::{Cursor, Pos};
pub use diff::{Diff, MaxVec};

// TODO-FEATURE
pub trait Text {}

// TODO-DOC ~ string-like things, paired with a cursor over them. Particularly note that cursors
// must be updated when text changes.
pub trait Textual: Text {
    /// Produces a reference to the [`Cursor`] paired with the text
    ///
    /// This trait provides that the value of the cursor does not change outside of any changes
    /// made by [`cursor_mut`](Self::cursor_mut), or by changes to the underlying [`Text`].
    fn cursor(&self) -> &Cursor;

    /// Produces a mutable reference to the [`Cursor`] paired with the text
    ///
    /// This trait provides that the value of the cursor can only change through access given by
    /// this method or as a result of changes to the underlying [`Text`].
    fn cursor_mut(&mut self) -> &mut Cursor;
}

/// Wraps a [`Text`] with a [`Cursor`] so that it may satisfy the [`Textual`] trait
///
/// This type can essentially be thought of as a concrete type satisfying the interface specified
/// by [`Textual`]. While it typically isn't required that this type be used directly, it does
/// provide a simple way of wrapping any [`Text`] to implement [`Textual`] in the simplest way.
pub struct Paired<T: Text> {
    text: T,
    cursor: Cursor,
}

impl<T: Text> Text for Paired<T> {}

impl<T: Text> Textual for Paired<T> {
    fn cursor(&self) -> &Cursor {
        &self.cursor
    }

    fn cursor_mut(&mut self) -> &mut Cursor {
        &mut self.cursor
    }
}
