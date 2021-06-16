//! Wrapper module for [`SharedByteTree`]

use super::{ByteSlice, ByteTree};
use crate::text::diff::Diff;
use crate::text::grouped_history::{GroupId, GroupedHistory};
use crate::text::history_core::{EditId, EditResult, RedoResult, UndoResult};
use std::collections::{HashMap, VecDeque};
use std::ops::Range;
use std::sync::{Arc, Mutex};
use tokio::sync::Notify;

/// A shared handle on a single [`ByteTree`], with history tracking and update notifications
///
/// This is the root text object for *all* pieces of text that have shared modification in any way.
/// A single `SharedByteTree` roughly corresponds to an `Arc<ByteTree>`, with various operations
/// treated *as if* they are atomic. The edit history of the object is also provided by an internal
/// [`GroupedHistory`].
///
/// Duplicating handles is provided by the implementation of [`Clone`].
///
/// ## General usage patterns
///
/// This type essentially provides two mechanisms for handling updates to the text object, and
/// they're intended to be used together. The first is the [`sync`] method, which returns all
/// of the changes that have been made since the last call to `sync`. The second is the [`updated`]
/// method, which blocks until there has been an un-synced change made to the text object.
///
/// Typically, usage will involve some kind event loop, selecting over updates to the object or
/// some other kind of desired action.
///
/// [`sync`]: Self::sync
/// [`updated`]: Self::updated
pub struct SharedByteTree<Time, Tag> {
    tree_ref: Arc<TreeRef<Time, Tag>>,
    synced_to: ChangeId,
}

/// (*Internal*) A unique identifier for every single [`Diff`] applied to the text object
///
/// This is used to index into the `changes` field of [`Manager`] -- more information is given in
/// the documentation there.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ChangeId(u64);

/// The result of a single successful change made to the [`SharedByteTree`] object, by any of the
/// [`edit`], [`undo`], or [`redo`] methods
///
/// Values of this type are primarily exposed through the [`sync`] method.
///
/// This type has a couple convenience methods. For example, [`diffs`] returns a reference to the
/// actual changes to the text object corresponding to this conceptual change.
///
/// [`sync`]: SharedByteTree::sync
/// [`edit`]: SharedByteTree::edit
/// [`undo`]: SharedByteTree::undo
/// [`redo`]: SharedByteTree::redo
/// [`diffs`]: Self::diffs
#[derive(Clone)]
pub enum Change {
    Edit(EditResult<ByteSlice>),
    Undo(UndoResult<ByteSlice>),
    Redo(RedoResult<ByteSlice>),
}

/// (*Internal*) Helper struct for sharing a reference-count between `notify` and `manager`
///
/// This essentially just exists so that we don't need to have separate values in `SharedByteTree`
/// for `Arc<Notify>` and `Arc<Mutex<Manager>>`.
struct TreeRef<Time, Tag> {
    notify: Notify,

    // We're using an `std::Mutex` because we're never actually holding the lock. It also allows us
    // to provide an implementation of `Clone` for `SharedByteTree`.
    manager: Mutex<Manager<Time, Tag>>,
}

/// (*Internal*) Wrapper around the text object for organizing sharing
///
/// This is the actual object that's at the shared core of a [`SharedByteTree`]. It tracks the
/// changes that haven't been seen yet by each listener, alongside the full edit history of the
/// file.
struct Manager<Time, Tag> {
    /// The actual content of the file
    bytes: ByteTree,

    /// The changes made to the text object that haven't yet been viewed by one or more listeners.
    ///
    /// Each element is a tuple (count, ...), where `count` gives the number of listeners that have
    /// the change as the first one they haven't viewed. The vector is empty when all listeners are
    /// up-to-date.
    changes: VecDeque<(usize, Change, Tag)>,

    /// The `ChangeId` of the first item in `changes`. If `changes` is empty, this gives the ID of
    /// the next change that will occur.
    last_unviewed: ChangeId,

    /// The number of up-to-date listeners. When adding an entry to `changes`, we set the count to
    /// this number
    up_to_date_listeners: usize,

    /// The full history of the object
    history: GroupedHistory<Time, ByteSlice>,

    /// The tags for each edit
    //
    // TODO-PERF: This could actually be integrated into the `Time` parameter for the history, in
    // which case we wouldn't need to store it separately.
    tags: HashMap<EditId, Tag>,
}

impl Change {
    /// Returns the slice of [`Diff`]s applied to the text object as a result of this change
    pub fn diffs(&self) -> &[(Diff<ByteSlice>, EditId)] {
        match self {
            Self::Edit(e_res) => &e_res.diffs,
            Self::Undo(u_res) => &u_res.diffs,
            Self::Redo(r_res) => &r_res.diffs,
        }
    }
}

impl<Time, Tag> Clone for SharedByteTree<Time, Tag> {
    fn clone(&self) -> Self {
        // When cloning, we have to update our entry in `changes`, if applicable.
        let mut mgr = self.tree_ref.manager.lock().unwrap();

        if mgr.all_listeners_are_up_to_date() {
            // If we're up-to-date, just increment the number of up-to-date listeners:
            mgr.up_to_date_listeners += 1;
        } else {
            // Otherwise, we need to increment the appropriate value in `mgr.changes`
            let idx = mgr.change_idx(self.synced_to);
            mgr.changes[idx].0 += 1;
        }

        SharedByteTree {
            tree_ref: Arc::clone(&self.tree_ref),
            synced_to: self.synced_to,
        }
    }
}

impl<Time, Tag> Drop for SharedByteTree<Time, Tag> {
    fn drop(&mut self) {
        // Because we're inside of a `Drop` implementation, we really don't want to panic. If the
        // Mutex has been poisoned, there isn't anything we can really do, beyond letting our `Arc`
        // drop to decrease the refcount.
        if let Ok(mut guard) = self.tree_ref.manager.lock() {
            // Assuming everything's fine, we want to remove our count from whatever change we
            // havne't yet seen yet is
            guard.mark_change_viewed(self.synced_to);
        }
    }
}

impl<Time: Clone + Ord, Tag: Clone> SharedByteTree<Time, Tag> {
    /// Constructs a new `SharedByteTree` with the given initial bytes
    pub fn new(bytes: ByteTree) -> Self {
        let len = bytes.len();

        let tree_ref = TreeRef {
            notify: Notify::new(),
            manager: Mutex::new(Manager {
                bytes,
                changes: VecDeque::new(),
                // Even though there haven't yet been any changes, we need *something* to go here.
                // It's easier to just say that change 0 is a "phantom" change that never existed,
                // than it is to make this an Option<ChangeId>.
                last_unviewed: ChangeId(1),
                up_to_date_listeners: 1,
                history: GroupedHistory::new(len),
                tags: HashMap::new(),
            }),
        };

        SharedByteTree {
            tree_ref: Arc::new(tree_ref),
            synced_to: ChangeId(0),
        }
    }

    /// Syncs the `SharedByteTree` with any updates that have happened, returning the list of
    /// changes
    ///
    /// After calling this method, it *will* be assumed that this particular handle does not need
    /// access to those changes, so they must be appropriately processed.
    ///
    /// Each returned change is represented by a tuple, consisting of:
    /// * The [`EditId`] corresponding to the particular change, whether it was due to the edit
    ///   being applied in the first place or undone;
    /// * The content of the change, in the form of a [`Diff`]; and
    /// * The "tag" associated with the change, as it was supplied to the [`edit`] method
    ///
    /// [`edit`]: Self::edit
    pub fn sync(&mut self) -> Vec<(Change, Tag)> {
        let (changes, synced_to) = self.tree_ref.manager.lock().unwrap().sync(self.synced_to);
        self.synced_to = synced_to;

        changes
    }

    /// Blocks until an update has been made to the text object
    ///
    /// If an update has already been made since the last call to [`sync`], this method returns
    /// immediately. Because of this, dropping the future will not miss out on any signals.
    ///
    /// [`sync`]: Self::sync
    pub async fn updated(&self) {
        let mgr_guard = self.tree_ref.manager.lock().unwrap();

        // If we're already not up-to-date, immediately return. Otherwise, we'll wait for something
        // to happen
        if self.synced_to != mgr_guard.last_change() {
            return;
        }

        // We have to acquire the future *before* dropping the lock, because `notify_waiters` will
        // only wake up threads that currently hold a future. If we were to drop the mutex first
        // and then do this, it would be possible for a notification to occur *before* we start
        // waiting for one.
        let fut = self.tree_ref.notify.notified();
        drop(mgr_guard);

        fut.await
    }

    /// Makes an edit to the underlying text object, returning `Err(())` if this handle is too far
    /// out-of-date
    ///
    /// This method makes a best-effort attempt to account for any edits that may have occured
    /// between the last call to [`sync`] and calling this method. It's fundamentally not possible
    /// for all circumstances, unfortunately, so we reject edits that conflict with something that
    /// happened in-between.
    ///
    /// The `get_time` function provides a way to determine the current time, only after acquiring
    /// the internal lock. This should help limit any accidentally racy behavior here.
    ///
    /// ## Errors
    ///
    /// This method can return `Err(())` in two cases, either (a) if there has been a newer change
    /// than what the handle has last synced to, that *also* conflicts with this edit, or (b) if
    /// the edit group has already been fixed. In either case, the edit should be discarded (or
    /// carefully modified by a call to [`sync`]) and the `GroupId` changed, if it had one.
    ///
    /// ## Panics
    ///
    /// Panics if the [`Diff`] did not agree with the state of the text object at the time of the
    /// last call to [`sync`].
    ///
    /// ## Additional notes
    ///
    /// An interesting interaction to remember here is that the [`updated`] method will return if
    /// *any* change is made -- including from this handle. Because of this, `edit` and
    /// `undo`/`redo` are treated as fallible, standalone requests. Instead of returning the
    /// [`EditResult`] directly, processing changes in case of success must be done by calls to
    /// [`sync`] instead.
    //
    // @def "SharedByteTree::edit docs" v0 -- update this on any documentation change.
    //
    ///
    /// [`updated`]: Self::updated
    /// [`sync`]: Self::sync
    pub fn edit(
        &mut self,
        mut diff: Diff<ByteSlice>,
        group: Option<GroupId>,
        get_time: impl FnOnce() -> Time,
        tag: Tag,
    ) -> Result<(), ()> {
        // Subtle point:
        //
        // We might want to worry about accidentally overwriting a change (e.g. undo) that happened
        // after the last change this handle is synced to. That should already be covered for
        // because we'll reject any edit that has a range that conflicts with a more recent change,
        // and that sort of undo would, already.

        let mut mgr_guard = self.tree_ref.manager.lock().unwrap();

        // There's a small amount of pre-processing of the `Diff` we need to do. For every change
        // that occured after `self.synced_to`, we should shift `diff.diff_idx` by the appropriate
        // amount. If any later change covers the same range of bytes, we can't make the edit.

        if self.synced_to != mgr_guard.last_change() {
            let first_unseen = mgr_guard.change_idx(self.synced_to) + 1;

            let all_diffs = mgr_guard
                .changes
                .range(first_unseen..)
                .map(|(_, c, _)| c.diffs())
                .flatten()
                .map(|(d, _)| d);

            for d in all_diffs {
                // If there's any overlap between the two ranges, we can't apply this edit; we're
                // done.
                if range_overlaps(d.old_range(), diff.old_range()) {
                    return Err(());
                }

                // Otherwise, if `d` occurs earlier in the text before `diff`, shift `diff` by the
                // appropriate amount
                if d.diff_idx < diff.diff_idx {
                    // We can't use += because we the old range might be bigger
                    diff.diff_idx = diff.diff_idx + d.new_range().len() - d.old_range().len();
                }
            }
        }

        // Preprocessing done, we can actually make the edit now
        //
        // Just need to check that we're allowed to add to this group. `GroupedHistory::edit` will
        // panic if we don't check this.
        if matches!(group, Some(g) if mgr_guard.history.group_is_fixed(g)) {
            return Err(());
        }

        // Apply the diff & record the edit:
        diff.apply(&mut mgr_guard.bytes);
        let edit_result = mgr_guard.history.edit(diff, group, get_time());

        // Insert the tag into our storage, and remove any edits that were removed here.
        mgr_guard.tags.insert(edit_result.new_id, tag.clone());
        edit_result.removed.iter().for_each(|id| {
            mgr_guard.tags.remove(id);
        });
        mgr_guard.history.drop_edits(&edit_result.removed);

        // Record the change & notify any waiting tasks:
        mgr_guard.record_change(Change::Edit(edit_result), tag);
        self.tree_ref.notify.notify_waiters();

        Ok(())
    }

    /// Undoes the edit, alongside the rest of its group, if it has one
    ///
    /// This method is essentially just a more forgiving wrapper around [`GroupedHistory::undo`].
    /// If - at the last change this handle was synced to - the edit existed, this method will not
    /// panic. It will return `Err(())` only if the error has been removed, but this handle hasn't
    /// yet seen that information.
    ///
    /// Normally, this method will unblock any task waiting on [`updated`]. However, if undoing
    /// this edit does not cause any changes (i.e. it only indicates a request that the edit *stay*
    /// undone), then we will not wake tasks blocked on calls to [`updated`], and the change will
    /// not be given by calls to [`sync`].
    ///
    /// ## Panics
    ///
    /// This method panics if the `EditId` was invalid at the last call to [`sync`]. Proper
    /// handling of changes where edits are removed should avoid this entirely.
    ///
    /// ## Additional notes
    ///
    /// An interesting interaction to remember here is that the [`updated`] method will return if
    /// *any* change is made -- including from this handle. Because of this, `edit` and
    /// `undo`/`redo` are treated as fallible, standalone requests. Instead of returning the
    /// [`EditResult`] directly, processing changes in case of success must be done by calls to
    /// [`sync`] instead.
    ///
    /// [`updated`]: Self::updated
    /// [`sync`]: Self::sync
    pub fn undo(&mut self, id: EditId) -> Result<(), ()> {
        let mut mgr_guard = self.tree_ref.manager.lock().unwrap();
        if mgr_guard.edit_removed_after(id, self.synced_to) {
            return Err(());
        }

        let res = mgr_guard.history.undo(id);
        // Because we successfully undid the edit, we know that it's valid; we should have a tag
        // for it.
        let tag = mgr_guard.tags[&id].clone();

        // If there were actually changes, apply them, store them, and notify any task blocked on
        // `updated()`
        if !res.diffs.is_empty() {
            res.diffs
                .iter()
                .for_each(|(d, _)| d.apply(&mut mgr_guard.bytes));

            mgr_guard.record_change(Change::Undo(res), tag);
            self.tree_ref.notify.notify_waiters();
        }

        Ok(())
    }

    /// Redoes the edit, alongside the rest of its group, if it has one
    ///
    /// This method is essentially just a more forgiving wrapper around [`GroupedHistory::redo`].
    /// If - at the last change this handle was synced to - the edit existed, this method will not
    /// panic. It will return `Err(())` only if the error has been removed, but this handle hasn't
    /// yet seen that information.
    ///
    /// Normally, this method will unblock any task waiting on [`updated`]. However, if redoing
    /// this edit does not cause any changes (i.e. it only indicates a request that the edit *stay*
    /// redone), then we will not wake tasks blocked on calls to [`updated`], and the change will
    /// not be given by calls to [`sync`].
    ///
    /// ## Panics
    ///
    /// This method panics if the `EditId` was invalid at the last call to [`sync`]. Proper
    /// handling of changes where edits are removed should avoid this entirely.
    ///
    /// ## Additional notes
    ///
    /// An interesting interaction to remember here is that the [`updated`] method will return if
    /// *any* change is made -- including from this handle. Because of this, `edit` and
    /// `undo`/`redo` are treated as fallible, standalone requests. Instead of returning the
    /// [`EditResult`] directly, processing changes in case of success must be done by calls to
    /// [`sync`] instead.
    ///
    /// [`updated`]: Self::updated
    /// [`sync`]: Self::sync
    pub fn redo(&mut self, id: EditId) -> Result<(), ()> {
        let mut mgr_guard = self.tree_ref.manager.lock().unwrap();
        if mgr_guard.edit_removed_after(id, self.synced_to) {
            return Err(());
        }

        let res = mgr_guard.history.redo(id);
        // Because we successfully redid the edit, we know that it's valid; we should have a tag
        // for it.
        let tag = mgr_guard.tags[&id].clone();

        // If there were actually changes, apply them, store them, and notify any task blocked on
        // `updated()`
        if !res.diffs.is_empty() {
            res.diffs
                .iter()
                .for_each(|(d, _)| d.apply(&mut mgr_guard.bytes));

            mgr_guard.record_change(Change::Redo(res), tag);
            self.tree_ref.notify.notify_waiters();
        }

        Ok(())
    }

    /// Produces a new [`GroupId`] for use in calls to [`edit`]
    ///
    /// This is just a wrapper around [`GroupedHistory::new_group`], and so is essentially
    /// cost-free until an edit is actually added for the group.
    ///
    /// [`edit`]: Self::edit
    pub fn new_group(&mut self) -> GroupId {
        let mut mgr_guard = self.tree_ref.manager.lock().unwrap();
        mgr_guard.history.new_group()
    }

    /// Takes a snapshot of the text object, aligned with the state at the time of the last call to
    /// [`sync`]
    ///
    /// Calling this method while out of date will have cost `O(n)` in the number of changes that
    /// have not yet been processed. Typically this shouldn't be an issue, but... use this method
    /// at your own risk.
    ///
    /// A pattern used in [`TextTree`] is to cache snapshots between calls to [`sync`], so that the
    /// overall cost is minimized.
    ///
    /// [`sync`]: Self::sync
    /// [`TextTree`]: super::TextTree
    pub fn snapshot(&self) -> ByteTree {
        let mgr_guard = self.tree_ref.manager.lock().unwrap();
        let mut bytes = mgr_guard.bytes.clone();

        // Invert all recent changes that we haven't sycned yet:
        if self.synced_to != mgr_guard.last_change() {
            let idx = mgr_guard.change_idx(self.synced_to);

            mgr_guard
                .changes
                .range(idx..)
                .map(|(_, change, _)| change.diffs())
                .flatten()
                .map(|(d, _)| d)
                // Reverse the order of the diffs so that inverting the changes goes in the correct
                // order
                .rev()
                .for_each(|d| d.apply_inverted(&mut bytes));
        }

        bytes
    }

    /// Returns the size of the text object, according to the last time that this handle called
    /// [`sync`]
    ///
    /// This method will return the same value as `self.snapshot().len()`, but should be
    /// considerably faster.
    ///
    /// [`sync`]: Self::sync
    pub fn synced_size(&self) -> usize {
        let mgr_guard = self.tree_ref.manager.lock().unwrap();
        let mut current_size = mgr_guard.bytes.len();

        // Walk backwards through the diffs, dealing with all of the changes that occured
        if self.synced_to != mgr_guard.last_change() {
            let idx = mgr_guard.change_idx(self.synced_to);

            mgr_guard
                .changes
                .range(idx..)
                // Collect all of the diffs into a single iterator
                .map(|(_, change, _)| change.diffs())
                .flatten()
                .map(|(d, _)| d)
                // Go through the diffs in reverse
                .rev()
                .for_each(|d| current_size = current_size + d.old.len() - d.new.len());
        }

        current_size
    }
}

/// (*Internal*) Helper function for [`SharedByteTree::edit`]; not for general use
///
/// Returns whether there's any part of `target` that overlaps with `base`. The two sides are
/// distinct because there's some subtle edge cases that we handle here.
///
/// This function is specifically used to determine whether two [`Diff`s] overlap (i.e. if we can't
/// apply one with range `target` because of `base`). This is why there's some subtle edge cases,
/// and why it may not return results that are generally expected.
///
/// [`Diff`s]: Diff
///
/// ## Edge Cases
///
/// There's an argument to be made that -- unless `base` contains an index that `target` also
/// contains -- we should just figure out a solution. We could do that in most cases, but it's
/// likely that we would just be guessing, with only a 50% chance of guessing "correctly" (if there
/// is even a "correct" solution).
///
/// So, given that conflicts like this should be exceptionally rare anyways, we're maximally
/// pessimistic -- saying that ranges overlap when they don't *quite*. To be precise, we'll say
/// that these overlap if:
///
/// * `base` and `target` contain a shared value; or
/// * `base` borders `target` -- i.e. `target.end == base.start` or vice versa
///
/// We assume that `start <= end` for all of the ranges here, which is true when it's being called
/// from `SharedByteTree::edit`.
fn range_overlaps(base: Range<usize>, target: Range<usize>) -> bool {
    // This function is not optimal. It's not called often, and so we have the liberty of writing
    // it in a way that better expresses the intent.

    // Helper function to check whether `ra` contains either endpoint of `rb`
    fn contains_either(ra: &Range<usize>, rb: &Range<usize>) -> bool {
        ra.contains(&rb.start) || (!rb.is_empty() && ra.contains(&(rb.end - 1)))
    }

    let contains_shared_value = contains_either(&base, &target) || contains_either(&target, &base);
    let borders = base.start == target.end || base.end == target.start;

    contains_shared_value || borders
}

impl<Time, Tag> Manager<Time, Tag> {
    /// Returns true if all of the listeners are up to date
    fn all_listeners_are_up_to_date(&self) -> bool {
        self.changes.is_empty()
    }

    /// Returns the index in `self.changes` that the given `ChangeId` corresponds to
    ///
    /// ## Panics
    ///
    /// This method will panic if the `ChangeId` is outside the range of changes currently stored.
    fn change_idx(&self, change: ChangeId) -> usize {
        if self.changes.is_empty() {
            panic!("no changes to index");
        }

        let base_idx = self.last_unviewed.0;
        let changes_range = base_idx..base_idx + self.changes.len() as u64;

        if !changes_range.contains(&change.0) {
            panic!(
                "{:?} out of bounds of stored range {:?}",
                change, changes_range
            );
        }

        (change.0 - base_idx) as usize
    }

    /// Marks the given change as viewed by *a* viewer
    ///
    /// NOTE: This method *does not* increment `up_to_date_listeners`, and so -- if the number of
    /// listeners is constant -- that must be done after calling this.
    fn mark_change_viewed(&mut self, id: ChangeId) {
        let idx = self.change_idx(id);
        let count_ref = &mut self.changes[idx].0;
        *count_ref -= 1;

        // If we were the last viewer that hadn't seen this change, drop all the changes until we
        // find one that another viewer hasn't seen.
        if *count_ref == 0 && idx == 0 {
            // Remove elements of `self.changes` until we find something that hasn't been viewed
            while !self.changes.is_empty() && self.changes[0].0 == 0 {
                self.changes.pop_front();
                self.last_unviewed.0 += 1;
            }
        }
    }

    /// Returns the `ChangeId` of the most recent change made
    fn last_change(&self) -> ChangeId {
        // `last_unviewed` is always >= 1
        ChangeId(self.last_unviewed.0 - 1 + self.changes.len() as u64)
    }

    /// Returns true if -- because of any of the changes occuring after `change` -- the edit has
    /// been removed from the history
    ///
    /// Note that this does *not* imply that the edit currently exists; an `EditId` that was never
    /// valid will return `false` here.
    fn edit_removed_after(&self, id: EditId, change: ChangeId) -> bool {
        if self.last_change() == change {
            return false;
        }

        let idx = self.change_idx(change);
        self.changes.range(idx + 1..).any(|(_, c, _)| match c {
            Change::Edit(res) => res.removed.contains(&id),
            _ => false,
        })
    }

    /// Records the change: adds it to the list of changes and sets the number of listeners that
    /// haven't viewed it
    fn record_change(&mut self, change: Change, tag: Tag) {
        let unviewed = std::mem::take(&mut self.up_to_date_listeners);
        self.changes.push_back((unviewed, change, tag));
    }
}

impl<Time, Tag: Clone> Manager<Time, Tag> {
    fn sync(&mut self, last_seen: ChangeId) -> (Vec<(Change, Tag)>, ChangeId) {
        let last_change = self.last_change();

        // If we're already up-to-date, don't do anything.
        if last_seen == last_change {
            return (Vec::new(), last_seen);
        }

        // Collect all of the changes:
        let idx = self.change_idx(last_seen);
        let sync_list: Vec<_> = self
            .changes
            .range(idx..)
            .cloned()
            .map(|(_, change, tag)| (change, tag))
            .collect();

        self.mark_change_viewed(last_seen);
        self.up_to_date_listeners += 1;

        (sync_list, last_change)
    }
}
