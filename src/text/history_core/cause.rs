//! Wrapper module for [`CauseStack`]

use super::{marker::Operation, EditId};
use maplit::btreeset;
use std::collections::BTreeSet;

/// (*Internal*) A type alias for the stack of edits requesting one be present (or not)
///
/// This exists to solve a very particular problem. There's essentially two properties that we
/// would *really* like to have guaranteed by this system: that, for any edits `A` and `B`, the
/// operations:
///   1. `undo A; redo A` / `redo A; undo A`, and
///   2. `undo A; undo B; redo A; redo B`
/// are equivalent to the identity operationn - i.e. they result in the same initial state.
///
/// The way we do this is by keeping a "cause stack", which records the reasons why a particular
/// edit has been flipped to its current state. Alternating indexes of the stack indicate causes
/// for alternating states of the edit; even stack indexes give causes for being undone and odd
/// ones are for being redone. Correspondingly, the "height" of the stack gives the current state:
/// if the stack has even height, the edit is present; odd height means it is not.
///
/// The operations on a "cause stack" are then fairly simple. They're elaborated further in the
/// internal documentation within method bodies.
#[derive(Debug)]
pub(super) struct CauseStack {
    vec: Vec<CauseSet>,
}

/// The set of edits individually responsible for a particular edit state
type CauseSet = BTreeSet<EditId>;

impl CauseStack {
    /// Returns a new, empty `CauseStack`
    pub fn new() -> Self {
        CauseStack { vec: Vec::new() }
    }

    /// Returns whether the stack indicates the edit is present
    pub fn is_present(&self) -> bool {
        self.vec.len() % 2 == 0
    }

    /// Returns whether the stack is empty
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }

    /// Marks the stack as being changed by the parameterized operation, returning whether
    /// executing it resulted in a change - i.e. whether the edit is now in the opposite state.
    pub fn op<T: Ord, Op: Operation<T>>(&mut self, cause: EditId) -> bool {
        if Op::IS_UNDO {
            self.undo(cause)
        } else {
            self.redo(cause)
        }
    }

    /// Marks the stack as being undone by the given edit, returning whether that resulted in a
    /// change - i.e. whether the edit is now absent
    pub fn undo(&mut self, cause: EditId) -> bool {
        let is_present = self.is_present();
        match self.vec.last_mut() {
            None => {
                self.vec.push(btreeset! { cause });
                true
            }
            // If the edit is already undone, then we just add this to the set
            Some(s) if is_present => {
                s.insert(cause);
                false
            }
            // If the edit is present, either (a) remove this edit from the
            Some(s) => {
                if !s.remove(&cause) {
                    self.vec.push(btreeset! { cause });
                    true
                } else if s.is_empty() {
                    self.vec.pop();
                    true
                } else {
                    false
                }
            }
        }
    }

    /// Marks the stack as being redone by the given edit, returning whethe that resulted in a
    /// change - i.e. whether the edit is now present
    pub fn redo(&mut self, cause: EditId) -> bool {
        let is_present = self.is_present();
        let last = (self.vec)
            .last_mut()
            .expect("redo should have at least one stack element");

        match is_present {
            true => {
                last.insert(cause);
                false
            }
            false => {
                if !last.remove(&cause) {
                    self.vec.push(btreeset! { cause });
                    true
                } else if last.is_empty() {
                    self.vec.pop();
                    true
                } else {
                    false
                }
            }
        }
    }

    /// Removes the edit from the top of the stack, returning both (i) whether the edit was there,
    /// and (ii) whether the edit changed state
    ///
    /// This is used in the implementation of [`HistoryCore::do_op`](super::HistoryCore::do_op), in
    /// order to account for reverting the changes corresponding to an edit, when those changes
    /// depend on the edit.
    pub fn remove_if_top(&mut self, id: EditId) -> (bool, bool) {
        println!("remove_if_top! id = {:?}, self = {:?}", id, self);

        match self.vec.last_mut() {
            None => (false, false),
            Some(set) => {
                let removed = set.remove(&id);
                if removed && set.is_empty() {
                    self.vec.pop();
                    (true, true)
                } else {
                    (true, false)
                }
            }
        }
    }
}
