//! A "basic" wrapper around [`history_core`] that provides linear undo/redo
//!
//! This is a filler type for the time being, in order to allow basic editing functionality before
//! the full client-server architecture is written. The primary export of this module is the
//! [`History`] struct, which does what it says it does.

use super::diff::{BytesRef, Diff};
use super::history_core::{EditId, HistoryCore as CoreHistory};
use std::cmp::Ordering;

/// The time each edit is made, paired with an increasing counter to be independent of timing
#[derive(Clone)]
struct LinearTime<T> {
    counter: usize,
    time: T,
}

impl<T> PartialEq for LinearTime<T> {
    fn eq(&self, other: &Self) -> bool {
        self.counter == other.counter
    }
}

impl<T> Eq for LinearTime<T> {}

impl<T> PartialOrd for LinearTime<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for LinearTime<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.counter.cmp(&other.counter)
    }
}

/// A temporary type allowing basic linear undo/redo
pub struct History<R, Time> {
    core: CoreHistory<LinearTime<Time>, R>,
    /// A counter for the last unique "time" given to an edit. We store the actual time an edit was
    /// made alongside it, but this counter is what's used for ordering the edits instead.
    counter: usize,
    /// The linear stack of edits that can be undone
    edit_stack: Vec<EditId>,
    /// The current position in the stack, plus one
    stack_pos: usize,
}

impl<R: BytesRef, Time: Clone> History<R, Time> {
    /// Creates a new [`History`] with the specified length
    fn new(len: usize) -> Self {
        History {
            core: CoreHistory::new(len),
            counter: 0,
            edit_stack: Vec::new(),
            stack_pos: 0,
        }
    }

    /// Constructively adds a new edit, returning the resulting [`Diff`] and the [`EditId`] it is
    /// labelled with
    fn edit(&mut self, diff: Diff<R>, time: Time) -> (Diff<R>, EditId) {
        let t = LinearTime {
            counter: self.counter,
            time,
        };
        self.counter += 1;

        let mut res = (self.core)
            .edit(diff, t, &[])
            .expect("unable to edit linear history");
        self.edit_stack.truncate(self.stack_pos.saturating_sub(1));
        self.edit_stack.push(res.new_id);

        // TODO-ERROR: We could do some validation about the edits removed as a result of this one.
        // But currently we just don't care - it could be non-zero, but it won't include edits
        // still on the stack.

        assert_eq!(res.diffs.len(), 1);
        res.diffs.remove(0)
    }

    /// Undoes a single edit, returning the time it occured at, if there was one
    fn undo(&mut self) -> Option<(Diff<R>, EditId, &Time)> {
        let id = self.edit_stack[self.stack_pos.checked_sub(1)?];

        let mut res = self.core.undo(id);
        assert_eq!(res.undone.len(), 1);
        assert_eq!(res.diffs.len(), 1);

        self.stack_pos -= 1;

        let (diff, i) = res.diffs.remove(0);
        debug_assert_eq!(i, id);
        let time = &self.core.get_edit(id).time.time;
        Some((diff, id, time))
    }

    fn redo(&mut self) -> Option<(Diff<R>, EditId, &Time)> {
        let id = *self.edit_stack.get(self.stack_pos)?;

        let mut res = self.core.redo(id);
        assert_eq!(res.redone.len(), 1);
        assert_eq!(res.diffs.len(), 1);

        self.stack_pos += 1;

        let (diff, i) = res.diffs.remove(0);
        debug_assert_eq!(i, id);
        let time = &self.core.get_edit(id).time.time;
        Some((diff, id, time))
    }
}
