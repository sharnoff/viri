//! Wrapper module for [`GroupedHistory`]

use smallvec::SmallVec;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use super::diff::{BytesRef, Diff};
pub use super::history_core::{Edit, EditId, EditResult, HistoryCore, RedoResult, UndoResult};

/// Edit history with edit groups for block undo/redo
///
/// This is essentially the same as what's provided by [`HistoryCore`], but allows us to group
/// multiple smaller edits into larger, "conceptual" edits. We disallow directly undoing/redoing
/// edits that are part of a larger group, but they can still be individually toggled if, e.g. a
/// dependent edit is undone.
///
/// The API is not too different from [`HistoryCore`], with small changes to accomodate the
/// addition of edit groups.
pub struct GroupedHistory<Time, R> {
    core: HistoryCore<Time, R>,

    groups: HashMap<GroupId, GroupInfo>,
    id_to_group: HashMap<EditId, GroupId>,
    next_group_id: u64,
}

/// A unique identifier corresponding to groups of edits
///
/// Typically, not all edits will require a `GroupId`. While it's probably not an issue if used
/// generously, creating more groups than necessary *will* add unecessary cost to operations.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GroupId(u64);

/// (*Internal*) All of the information we store about a particular group
struct GroupInfo {
    members: HashSet<EditId>,
    // The number of the edits in the group that have been undone
    n_undone: usize,
}

impl<Time: Clone + Ord, R: BytesRef> GroupedHistory<Time, R> {
    /// Creates a new, blank `GroupedHistory` for a text object with the given length
    pub fn new(len: usize) -> Self {
        GroupedHistory {
            core: HistoryCore::new(len),
            groups: HashMap::new(),
            id_to_group: HashMap::new(),
            next_group_id: 0,
        }
    }

    /// Produces a new `GroupId`
    ///
    /// This is essentially cost-free until an edit is added for the group.
    pub fn new_group(&mut self) -> GroupId {
        let g = GroupId(self.next_group_id);
        self.next_group_id += 1;
        g
    }

    /// Returns whether the given group cannot take more edits
    ///
    /// Groups can become "fixed" when an edit in the group becomes undone, due to one of its
    /// transitive dependencies being undone. The best action to take in this case is to just
    /// create a new group -- when used correctly, attempting to add to a fixed group should be
    /// very rare.
    ///
    /// Any attempt to add an edit to the group while this method returns true will panic.
    pub fn group_is_fixed(&self, group: GroupId) -> bool {
        let group = match self.groups.get(&group) {
            None => return false,
            Some(info) => info,
        };

        // A group is not fixed as long as nothing has been undone
        group.n_undone == 0
    }

    /// Adds a new edit to the history, removing any conflicting, currently-unapplied edits
    ///
    /// This method is essentially identical to [`HistoryCore::edit`] -- it's actually just a thin
    /// wrapper around it. Please refer to that method's documentation for more info.
    ///
    /// ## Panics
    ///
    /// If this edit is intended as part of a group, *and* that group is fixed (see:
    /// [`group_is_fixed`]), then this method will panic. Otherwise, there are no restrictions on
    /// how late an edit can be added to a group.
    ///
    /// [`group_is_fixed`]: Self::group_is_fixed
    pub fn edit(&mut self, diff: Diff<R>, group: Option<GroupId>, time: Time) -> EditResult<R> {
        if matches!(group, Some(g) if self.group_is_fixed(g)) {
            panic!("edit group is already fixed; cannot make edit")
        }

        // We don't need to fix the current members of the group, because we already know they're
        // all present.
        //
        // We should have gotten `Ok(_)` because there's nothing in the fixed set. This might
        // change at a later point, but that's currently the case.
        let res = self.core.edit(diff, time, []).unwrap();

        // Add the new edit id to the appropriate group
        if let Some(g) = group {
            self.id_to_group.insert(res.new_id, g);
            self.groups
                .entry(g)
                .or_insert(GroupInfo {
                    members: HashSet::new(),
                    n_undone: 0,
                })
                .members
                .insert(res.new_id);
        }

        // Stop tracking any edits that were removed as a consequence of this edit
        for e_id in res.removed.iter() {
            if let Some(g_id) = self.id_to_group.remove(e_id) {
                let mut group = match self.groups.entry(g_id) {
                    Entry::Occupied(g) => g,
                    Entry::Vacant(_) => unreachable!(),
                };

                let g = group.get_mut();

                g.members.remove(&e_id);
                // Removed edits are always undone, so we have to decrement `n_undone`
                g.n_undone -= 1;

                // If there's nothing
                if g.members.is_empty() {
                    group.remove();
                }
            }
        }

        res
    }

    /// Undoes the edit and the rest of its group if it is present, otherwise indicating that they
    /// should *stay* undone
    ///
    /// This is roughly equivalent to the [`try_undo`] method on [`HistoryCore`], only with soft
    /// failure encompassed into the [`UndoResult`]. What we mean by this is that -- instead of
    /// returning `Option<_>` to indicate that a *particular* edit couldn't be undone -- we return
    /// an `UndoResult` with no undone edits to indicate that *no* edit could be undone.
    ///
    /// Everything else about the meaning of the [`UndoResult`] is kept the same. For more
    /// information, refer to the documentation in the original [`undo`] method.
    ///
    /// ## Panics
    ///
    /// This method may panic if the [`EditId`] is invalid, e.g. if it has been removed.
    ///
    /// [`try_undo`]: HistoryCore::try_undo
    /// [`undo`]: HistoryCore::undo
    pub fn undo(&mut self, id: EditId) -> UndoResult<R> {
        // The default `UndoResult`. We have it here so that we can `unwrap_or(default)` later.
        let default = UndoResult {
            diffs: SmallVec::new(),
            undone: SmallVec::new(),
        };

        let res = match self.id_to_group.get(&id) {
            None => {
                // If this edit isn't part of a group, we don't have to do anything extra (yet)
                self.core.try_undo(id).unwrap_or(default)
            }
            Some(g_id) => {
                let group = &self.groups[g_id];

                // TODO-RFC#2229
                let core = &mut self.core;
                group
                    .members
                    .iter()
                    .filter_map(|e_id| core.try_undo(*e_id))
                    .reduce(|mut x, y| {
                        x.diffs.extend(y.diffs);
                        x.undone.extend(y.undone);
                        x
                    })
                    .unwrap_or(default)
            }
        };

        // For each edit that was undone as a result of this, record in its group that it was
        // undone.
        //
        // TODO-PERF: Could optimize this by storing the group across iterations, because we'll
        // often have many edits from the same group in a row. There's something similar in
        // `Self::redo` as well.
        for e_id in res.undone.iter() {
            if let Some(g_id) = self.id_to_group.get(e_id) {
                let g = self.groups.get_mut(g_id).unwrap();
                g.n_undone += 1;
                debug_assert!(g.n_undone <= g.members.len());
            }
        }

        res
    }

    /// Redoes the edit and the rest of its group if it's not present, otherwise indicating that
    /// they should *stay* present
    ///
    /// This is equivalent to the [`try_redo`] method on [`HistoryCore`] -- hence why we return an
    /// `Option<_>`. Information about usage of the `RedoResult` can be found in the original
    /// [`redo`] method.
    ///
    /// ## Panics
    ///
    /// This method may panic if the [`EditId`] is invalid, e.g. if it has been removed.
    ///
    /// [`try_redo`]: HistoryCore::try_redo
    /// [`redo`]: HistoryCore::redo
    pub fn redo(&mut self, id: EditId) -> RedoResult<R> {
        // The body of this function is largely copied from `Self::undo`. There's more comments
        // there, if you're curious.

        let default = RedoResult {
            diffs: SmallVec::new(),
            redone: SmallVec::new(),
        };

        let res = match self.id_to_group.get(&id) {
            None => self.core.try_redo(id).unwrap_or(default),
            Some(g_id) => {
                let group = &self.groups[g_id];

                // TODO-RFC#2229
                let core = &mut self.core;
                group
                    .members
                    .iter()
                    .filter_map(|e_id| core.try_redo(*e_id))
                    .reduce(|mut x, y| {
                        x.diffs.extend(y.diffs);
                        x.redone.extend(y.redone);
                        x
                    })
                    .unwrap_or(default)
            }
        };

        // TODO-PERF: See note in `Self::undo`.
        for e_id in res.redone.iter() {
            if let Some(g_id) = self.id_to_group.get(e_id) {
                // Don't need the debug assertion here; we get underflow checking for free.
                self.groups.get_mut(g_id).unwrap().n_undone -= 1;
            }
        }

        res
    }

    /// Drops all of the edits corresponding to the given `EditId`s, returning the edits themselves
    ///
    /// This method is nearly identical to the one on [`HistoryCore`] by the same name. For more
    /// information (including panic conditions), please refer to [`HistoryCore::drop_edits`].
    ///
    /// The only distinction here is that we additionally return the [`GroupId`] of each removed
    /// edit, if it was part of a group.
    pub fn drop_edits(&mut self, ids: &[EditId]) -> Vec<(EditId, Option<GroupId>, Edit<Time, R>)> {
        // First: remove all of the edits from the internal history. This way, we panic quickly if
        // something's wrong
        let edits = self.core.drop_edits(ids);

        // Remove the edit from `id_to_group`, and the group itself, if it was the last member
        edits
            .into_iter()
            .map(|(e_id, edit)| {
                let g_id = self.id_to_group.remove(&e_id);

                if let Some(g_id) = g_id {
                    let mut group = match self.groups.entry(g_id) {
                        Entry::Occupied(e) => e,
                        Entry::Vacant(_) => panic!("unexpected missing group for id"),
                    };

                    let g = group.get_mut();
                    g.members.remove(&e_id);
                    // All dropped edits are required to be undone
                    g.n_undone -= 1;

                    if g.members.is_empty() {
                        group.remove();
                    }
                }

                (e_id, g_id, edit)
            })
            .collect()
    }
}
