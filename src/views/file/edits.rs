//! Utilities for handling the processing of individual edits in a `FileView`
//!
//! This should primarily be a sub-module of 'views::file::handle', but for the sake of simplifing
//! the module hierarchy, it is not.
//!
//! The primary construct here is undoing, which is currently fairly simple: there is a single,
//! global list of the edit history (note: distinct from diff history). When new changes are made
//! from a point back in the history, all changes that had previously occured after that are
//! discarded.

// TODO: This is the idea for a new, local/global based undo system
//
// //! ## Overview
// //!
// //! **Terminology**: The fundamental unit here that we'll describe is the *edit*. Edits and diffs
// //! may not map 1-1 (i.e. a single edit may be composed of multiple diffs), but that will be
// //! discussed further down. (see: ["Edits vs diffs"](#edits-vs-diffs))
// //!
// //! The undo system is complex in a way that is orthagonal to the type of tree-based undo systems
// //! that might be seen in other, similar editors. Here, edits made by different handles (i.e.
// //! different buffers) are treated differently.
// //!
// //! The goal of this edit system is to allow sets of edits to occur independently between Views. A
// //! user should be able to make changes at different points in a file in different views and undo
// //! them separately. The rest of this documentation describes precisely how this system works.
// //!
// //! ## Edits: Local and Global
// //!
// //! Because we allow edits to be reversed in a single view, we need a way of distinguishing between
// //! reversing the most recent edit in the current view versus the most recent global edit to a
// //! file. As such, there are two types of edits: local and global.
// //!
// //! ## Epochs
// //!
// //! Sets of edits are split into epochs to segment them into different groups. This is because
// //! there are fundamentally two cases when a file is being edited: Either the file is open in a
// //! single View (and therefore there's one handle) or the file is open in multiple Views at the
// //! same time (there's multiple handles). A single handle is the simple case, so we'll briefly
// //! describe that:
// //!
// //! When there's only a single handle attached to the file, all edits are considered global. It
// //! should be noted that - regardless of the number of current handles - all edits from previous
// //! epochs are *also* considered global.
// //!
// //! When there are multiple active handles, a new epoch is started only once the file is being
// //! edited from a *different* view than the original one at the time of the second handle joining.
// //! Epochs are not created on subsequent handles editing a file; they simply join into the current
// //! one. An epoch with multiple handles is called a "split" epoch.
// //!
// //! Spit epochs are composed of distinct "edit streams" for each handle. When a handle attempts to
// //! undo a *local* change, it will try to revert the most recent edit in its stream. This *may*
// //! fail under a number of circumstances.
//
// TODO before implementing: Detail precisely what these circumstances are
//
// //! The most recent global change can still be undone, independently of which handle is in focus.
// //! When the epoch ends, the streams are merged so that they all become part of the *global* edit
// //! history.
// //!
// //! Epochs end automatically when the number of handles decreases to one, and may be triggered by a
// //! user in the case of attempting to undo past the beginning of the epoch.
//
// TODO before implementing: Need to determine the semantics of manually triggering a new epoch
//
// //!
// //! ## Edits vs diffs
// //!
// //! In some cases, there may be multiple diffs coresponding to a single, cohesive "edit". In insert
// //! mode, for example, each individual character change should not constitute an edit; edits should
// //! instead be collections of a few changes at a time - even though they are still marked as
// //! individual diffs to the file's content.

use super::handle::HandleId;
use crate::text::Diff;

#[derive(Debug)]
pub(super) struct Edits {
    history: Vec<Edit>,

    // /// The last index in `history` for which the edit is currently applied. This may be equal to
    // /// `history.len()` if `current_edit` is applied.
    /// The first index in `history` for which the edits have not been applied. This will be equal
    /// to `history.len() + 1` if we are currently making a block edit - i.e.
    /// `current_edit.is_some()`
    ///
    /// Therefore when adding a new element back in history, we truncate `history` to exactly the
    /// length `place_in_history`.
    place_in_history: usize,

    /// The next edit id that will be given out
    next_id: EditId,

    /// When making a block edit, this gives the current edit being built
    current_edit: Option<Edit>,

    /// The depth of the current edit. This allows `start_edit_block` to be called when we are
    /// already making a change within a block
    edit_depth: usize,
}

#[derive(Debug)]
struct Edit {
    owner: EditOwner,
    id: EditId,
    diffs: Vec<Diff>,
}

/// The owner of an edit. This is primarily in place as future-proofing.
#[derive(Debug, PartialEq, Eq)]
pub enum EditOwner {
    /// A local edit
    Local(HandleId),

    /// A global edit might occur from things like running a formatter; this can be undone by the
    /// user.
    Global,

    /// A networked edit cannot be undone.
    Network,
}

/// A unique, increasing identifier for individual edits
#[derive(Copy, Clone, Debug)]
struct EditId(u64);

impl Edits {
    pub fn new() -> Self {
        Self {
            history: Vec::new(),
            place_in_history: 0,
            next_id: EditId(0),
            current_edit: None,
            edit_depth: 0,
        }
    }

    pub fn make_edit(&mut self, diff: Diff, owner: EditOwner) {
        match &mut self.current_edit {
            None => {
                let edit = Edit {
                    owner,
                    id: self.next_id.bump(),
                    diffs: vec![diff],
                };

                if self.edit_depth == 0 {
                    self.history.truncate(self.place_in_history);
                    self.history.push(edit);
                    self.place_in_history += 1;
                } else {
                    // We'll set the current edit that we're creating to be this one.
                    self.history.truncate(self.place_in_history);
                    self.current_edit = Some(edit);
                    self.place_in_history += 1;
                }
            }

            // Per the comment on the field, this indicates that the diffs given by `current_edit`
            // haven't been applied. We'll need to reset it
            Some(_) if self.place_in_history <= self.history.len() => {
                self.history.truncate(self.place_in_history);
                self.current_edit = None;

                // The rest of this block is pasted from above.
                // TODO: Refactor to not duplicate the code here.
                let edit = Edit {
                    owner,
                    id: self.next_id.bump(),
                    diffs: vec![diff],
                };

                if self.edit_depth == 0 {
                    self.history.truncate(self.place_in_history);
                    self.history.push(edit);
                    self.place_in_history += 1;
                } else {
                    // We'll set the current edit that we're creating to be this one.
                    self.history.truncate(self.place_in_history);
                    self.current_edit = Some(edit);
                }
            }

            Some(cur) if cur.owner == owner => {
                cur.diffs.push(diff);
            }

            // cur.owner != owner. We need to push that edit and start a new grouped edit
            Some(_) => {
                let edit = Edit {
                    owner,
                    id: self.next_id.bump(),
                    diffs: vec![diff],
                };

                self.history.push(self.current_edit.take().unwrap());
                self.current_edit = Some(edit);
                self.place_in_history += 1;
            }
        }
    }

    pub fn start_edit_block(&mut self) {
        self.edit_depth += 1;
        log::trace!("start: new edit depth: {:?}", self.edit_depth);
    }

    pub fn end_edit_block(&mut self) {
        self.edit_depth -= 1;
        log::trace!("end: new edit depth: {:?}", self.edit_depth);
        if self.edit_depth == 0 && self.current_edit.is_some() {
            self.history.push(self.current_edit.take().unwrap());
        }
    }

    /// Produces the set of diffs that - when executed in order - would correspond to undoing a
    /// single edit.
    ///
    /// This function by itself does not record the edit as being undone here; for that,
    /// `commit_undo` must be used.
    ///
    /// If there are no more edits that can be undone, this function will return `None`.
    pub fn get_undo(&self) -> Option<Vec<Diff>> {
        if self.place_in_history == 0 {
            return None;
        }

        let idx = self.place_in_history - 1;

        let diffs: &[Diff] = if idx == self.history.len() {
            // This is only true when `current_edit` is Some(_)
            &self.current_edit.as_ref().unwrap().diffs
        } else {
            &self.history[idx].diffs
        };

        Some(diffs.iter().rev().map(Diff::inverse).collect())
    }

    /// For use in combination with `get_undo`. This function will return `None` under the same
    /// conditions that `get_undo` will return `None`.
    pub fn commit_undo(&mut self) -> Option<()> {
        if self.place_in_history == 0 {
            return None;
        }

        self.place_in_history -= 1;
        Some(())
    }

    /// Like `get_undo`, but works in the opposite direction
    pub fn get_redo(&self) -> Option<&[Diff]> {
        let max_place = match self.current_edit.is_some() {
            true => self.history.len() + 1,
            false => self.history.len(),
        };

        // A safeguard to catch any logic errors so that we don't error later
        if self.place_in_history > max_place {
            panic!(
                "Internal error: Edits.place_in_history > max_place. Self: {:?}",
                self
            );
        }

        // Nothing more to redo
        if self.place_in_history == max_place {
            return None;
        }

        if self.place_in_history == self.history.len() {
            // From above, we know that `current_edit.is_some()`
            Some(&self.current_edit.as_ref().unwrap().diffs)
        } else {
            Some(&self.history[self.place_in_history].diffs)
        }
    }

    /// Like `commit_undo`, but for `get_redo`
    pub fn commit_redo(&mut self) -> Option<()> {
        let max_place = match self.current_edit.is_some() {
            true => self.history.len() + 1,
            false => self.history.len(),
        };

        if self.place_in_history == max_place {
            return None;
        }

        Some(())
    }
}

impl EditId {
    /// Increments this edit id, returning the old value
    fn bump(&mut self) -> EditId {
        let EditId(id) = *self;
        *self = EditId(id + 1);
        EditId(id)
    }
}
