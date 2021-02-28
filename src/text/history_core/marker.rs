//! (*Internal*) Marker types and traits on them
//!
//! There's essentially two groups defined here: [`Undo`]/[`Redo`], and [`Lower`]/[`Upper`]. The
//! first is abstracted over with the [`Operation`] trait, and the second with [`Direction`].
//!
//! Broadly speaking, `Operation`s are closer to the user-facing code than `Direction`s, the latter
//! of which is only really used as a sort of helper abstraction.

use super::{BytesRef, Edit, EditId, Edits};
use std::ops::{Deref, DerefMut};

/// The "undo" [`Operation`]
pub struct Undo;

/// The "redo" [`Operation`]
pub struct Redo;

pub(super) trait Operation<Time: Ord> {
    // Whether the operation is the "undo" operation. True for Undo, false for Redo.
    const IS_UNDO: bool;
    // Whether the operation should end with the edit as applied. False for Undo, true for Redo.
    const GOAL_IS_APPLIED: bool;

    // The other operation
    type Inverse: Operation<Time>;

    // A wrapper around `Time` that allows specifying the direction in which we care about
    // time. This is a little complex, and is best defined by its implmentation: undoing reverses
    // the ordering, whereas redoing keeps it.
    //
    // The main reason for this is because the description of the algorithm defined below in
    // `EditHistory::required_changes` is in terms of undoing, so we don't change the ordering
    // of undo.
    type Ord: Ord;

    // Conversion functions for creating an `Ord` from a time
    fn ord(time: Time) -> Self::Ord;

    // The "child" edits in the direction of requirement for this application. Undoing requires
    // later edits to be absent, so it returns `edit.after`. Redoing requires earlier edits to
    // be present, so it returns `edit.before`.
    fn requires<R>(edit: &Edit<Time, R>) -> &[(isize, EditId)];

    // The opposite direction of `requires`
    fn required_by<R>(edit: &Edit<Time, R>) -> &[(isize, EditId)];
}

#[rustfmt::skip]
impl<Time: Ord> Operation<Time> for Undo {
    const IS_UNDO: bool = true;
    const GOAL_IS_APPLIED: bool = false;

    type Inverse = Redo;

    type Ord = std::cmp::Reverse<Time>;

    fn ord(time: Time) -> Self::Ord { std::cmp::Reverse(time) }

    fn requires<R>(edit: &Edit<Time, R>) -> &[(isize, EditId)] {
        &edit.after
    }

    fn required_by<R>(edit: &Edit<Time, R>) -> &[(isize, EditId)] {
        &edit.before
    }
}

#[rustfmt::skip]
impl<Time: Ord> Operation<Time> for Redo {
    const IS_UNDO: bool = false;
    const GOAL_IS_APPLIED: bool = true;

    type Inverse = Undo;

    type Ord = Time;

    fn ord(time: Time) -> Self::Ord { time }

    fn requires<R>(edit: &Edit<Time, R>) -> &[(isize, EditId)] {
        &edit.before
    }

    fn required_by<R>(edit: &Edit<Time, R>) -> &[(isize, EditId)] {
        &edit.after
    }
}

pub struct Lower;
pub struct Upper;

/// The direction of a search; either lower than a value or above it
pub(super) trait Direction<Time, R: BytesRef> {
    // The opposite direction
    type Opposite;

    fn furthest(edit: &Edit<Time, R>) -> Option<EditId>;

    // Returns whether `new` is closer to the edit than `old`, under the assumption that they
    // are both to this direction of
    fn is_closer(old: &Edit<Time, R>, new: &Edit<Time, R>) -> bool;

    fn allow(base: &Edit<Time, R>, new: &Edit<Time, R>) -> bool;
}

impl<Time, R: BytesRef> Direction<Time, R> for Lower {
    type Opposite = Upper;

    fn furthest(edit: &Edit<Time, R>) -> Option<EditId> {
        edit.after.first().map(|&(_offset, id)| id)
    }

    fn is_closer(old: &Edit<Time, R>, new: &Edit<Time, R>) -> bool {
        new.diff.diff_idx > old.diff.diff_idx
    }

    fn allow(base: &Edit<Time, R>, new: &Edit<Time, R>) -> bool {
        new.diff.diff_idx + new.diff.old.len() < base.diff.diff_idx
    }
}

impl<Time, R: BytesRef> Direction<Time, R> for Upper {
    type Opposite = Lower;

    fn furthest(edit: &Edit<Time, R>) -> Option<EditId> {
        edit.after.last().map(|&(_offset, id)| id)
    }

    fn is_closer(old: &Edit<Time, R>, new: &Edit<Time, R>) -> bool {
        new.diff.diff_idx < old.diff.diff_idx
    }

    fn allow(base: &Edit<Time, R>, new: &Edit<Time, R>) -> bool {
        new.diff.diff_idx + new.diff.old.len() > base.diff.diff_idx + base.diff.old.len()
    }
}

/// An abstraction over mutable or immutable references to an [`Edits<Time, R>`](Edits)
///
/// This works in conjunction with the [`Recover`] trait to allow temporary borrows of single with
/// re-borrowing
pub(super) trait EditsRef<Time, R>: Sized {
    /// The wrapper around an edit to an individual reference; either [`SingleEditRef`] or
    /// [`SingleEditMut`]
    ///
    /// This is created with the `get` method, dereferences to an actual edit, and can be
    /// un-borrowed with `edit.recover()`
    type Edit: Deref<Target = Edit<Time, R>> + Recover<Self>;

    /// Gets a recoverable reference to a single edit, given by the [`EditId`]
    fn get_edit(self, id: EditId) -> Self::Edit;
}

/// `std::convert::Into` with a different name
///
/// This trait exists for [`EditsRef`]; it allows ergonomic-ish use of borrowing an edit before
/// "recovering" the base structure when we release the borrow.
pub(super) trait Recover<T> {
    /// Convert the edit-like value into the [`EditsRef`] it originally borrowed
    fn recover(self) -> T;
}

impl<'a, Time, R> EditsRef<Time, R> for &'a Edits<Time, R> {
    type Edit = SingleEditRef<'a, Time, R>;

    fn get_edit(self, id: EditId) -> Self::Edit {
        // Check that the edit is valid
        Edits::get(self, "", id);
        SingleEditRef { edits: self, id }
    }
}

impl<'a, Time, R> EditsRef<Time, R> for &'a mut Edits<Time, R> {
    type Edit = SingleEditMut<'a, Time, R>;

    fn get_edit(self, id: EditId) -> Self::Edit {
        // Check that the edit is valid
        Edits::get(self, "", id);
        SingleEditMut { edits: self, id }
    }
}

/// An immutable edit reference, implementing [`Recover<&EditsRef>`](EditsRef)
pub(super) struct SingleEditRef<'a, Time, R> {
    edits: &'a Edits<Time, R>,
    id: EditId,
}

impl<'a, Time, R> Recover<&'a Edits<Time, R>> for SingleEditRef<'a, Time, R> {
    fn recover(self) -> &'a Edits<Time, R> {
        self.edits
    }
}

impl<Time, R> Deref for SingleEditRef<'_, Time, R> {
    type Target = Edit<Time, R>;

    fn deref(&self) -> &Self::Target {
        Edits::get(self.edits, "", self.id)
    }
}

/// A mutable edit reference, implementing [`Recover<&mut EditsRef>`](EditsRef)
pub(super) struct SingleEditMut<'a, Time, R> {
    edits: &'a mut Edits<Time, R>,
    id: EditId,
}

impl<'a, Time, R> Recover<&'a mut Edits<Time, R>> for SingleEditMut<'a, Time, R> {
    fn recover(self) -> &'a mut Edits<Time, R> {
        self.edits
    }
}

impl<Time, R> Deref for SingleEditMut<'_, Time, R> {
    type Target = Edit<Time, R>;

    fn deref(&self) -> &Self::Target {
        Edits::get(self.edits, "", self.id)
    }
}

impl<Time, R> DerefMut for SingleEditMut<'_, Time, R> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Edits::get_mut(self.edits, "", self.id)
    }
}
