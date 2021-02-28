//! Wrapper module for the [`EditHistory`] type
//!
//! In short, edit histories provide a method for managing clustered groups of [`Diff`]s on the
//! same text object, with support for undoing and redoing edits on the individual level. Further
//! information is provided in the [type's documentation](EditHistory).
//!
//! This is the most basic abstraction provided over sets of [`Diff`]s, with additional
//! functionality provided by building on top of this.

// Known problems:
//
//  1. In a multi-user editing scenario, it might be the case that someone undoes an edit and then
//     writes over it, before receiving information that the other user had built ontop of those
//     undone edits. By the time the undo'er gets that information, the edits will have already
//     been destroyed, and so it wouldn't be possible to sync.

use crate::text::diff::{BytesRef, Diff};
use smallvec::SmallVec;
use std::borrow::Borrow;
use std::collections::{BTreeSet, BinaryHeap, HashSet};
use std::hash::Hash;
use std::num::NonZeroUsize;

mod cause;
mod marker;
mod pos_map;
mod ranged;

#[cfg(test)]
mod tests;

use cause::CauseStack;
use marker::{EditsRef, Operation, Recover, Redo, Undo};
use pos_map::{PosMap, TrackBlame};
use ranged::{RangeSlice, Ranged};

/// (*Internal*) The individual record of the regions a particular edit is responsible for
/// affecting, as in [`EditHistory.blame`] or [`EditHistory.shadow`].
///
/// [`EditHistory.blame`]: EditHistory#structfield.blame
/// [`EditHistory.shadow`]: EditHistory#structfield.shadow
type Blame = Ranged<Option<BlameRange>>;

/// (*Internal*) The blame for a region of bytes, alongside the offset from the position of the
/// original edit
#[derive(Copy, Clone, Debug)]
struct BlameRange {
    /// The starting index, using the 2x+1 scheme. The left-hand side boundary of an edit is index
    /// zero, and the right-hand side boundary has index equal to 2 times the length, plus one.
    start_idx: usize,
    /// The edit responsible for the byte range
    id: EditId,
}

impl RangeSlice for BlameRange {
    fn split_at(&mut self, idx: usize) -> Self {
        BlameRange {
            start_idx: self.start_idx + idx,
            id: self.id,
        }
    }

    fn try_join(self, self_size: usize, other: Self) -> Result<Self, (Self, Self)> {
        // We only join if they're the same edit and the offset is continuous.
        //
        // In practice, we shouldn't really need to check that the offset is continuous, because -
        // if it's interrupted - that'll be a distinct region for the byte boundary. But it's worth
        // having here anyways in case my infallible logic is not so infallible.
        if self.id != other.id || self.start_idx + self_size != other.start_idx {
            return Err((self, other));
        }

        // Because we don't track the size, we can let the tree handle giving `self` all of the
        // range that belongs to `other`.
        Ok(self)
    }
}

/// The primary low-level history interface; a handler for edits on a single text object
///
/// The generic parameter `Time` is the particular *time-like* type used for ordering edits; `R` is
/// the representation of a byte slice used for [`Diff`]s, required to implement [`BytesRef`].
///
/// The interface for this type is currently (pending further use-cases) quite limited; an
/// `EditHistory` is created with the [`new`](Self::new) function and functionality is primarily
/// exposed through the [`edit`], [`undo`], [`redo`], and [`try_{undo,redo}`] methods.
///
/// The [module-level documentation] has more detailed information about usage of this type.
///
/// [`edit`]: Self::edit
/// [`undo`]: Self::undo
/// [`edit`]: Self::redo
/// [`try_{undo,redo}`]: Self::try_undo
/// [module-level documentation]: self
pub struct EditHistory<Time, R> {
    /// The full list of edits, indexed by their `EditId`s
    ///
    /// Values of `None` indicate an edit that has been discarded. The minimum index of these
    /// yet-to-be-recycled edits is given by [`self.last_unused`], if there are any.
    ///
    /// [`self.last_unused`]: #structfield.last_unused
    edits: Edits<Time, R>,

    /// The last unused index of an edit, kept for recycling previous edits
    last_unused: Option<usize>,

    /// Which edit is responsible for each byte of the text. Instead of using an effective size
    /// equal to the length of the text object, we *also* track the the edits responsible for
    /// setting the value adjacent to bytes as well - we use a total size of twice the length of
    /// the text object, plus one.
    ///
    /// The edit responsible for writing the byte value at an individual index can be found at
    /// `blame[2*i + 1]`, whereas the blame for writing its neighbor to the left can be found at
    /// `blame[2*i]` and to the right as `blame[2*i + 2]`.
    ///
    /// There is always at least one value in `blame`, and `blame.len() == 1` if the text object is
    /// empty. If that's the case, `blame[0]` gives the edit responsible for the edit that emptied
    /// it, if there was one.
    blame: Blame,

    /// Like [`self.blame`](#structfield.blame) but travelling in the opposite direction
    ///
    /// This is a little bit tricky; it essentially records the regions that an above,
    /// currently-undone edit *would* affect, if it were re-applied. We say that an edit "shadows"
    /// a particular byte position if it's the *first* unapplied edit that would be able to affect
    /// that particular byte.
    ///
    /// The relationship with `blame` is more simple: for any undone edit in
    /// `self.bottommost_unapplied` (i.e. it can be immediately redone), applying that edit will
    /// copy over its region in `shadow` to `blame`. Its region in `shadow` is then replaced by the
    /// previously-stored value for the edits above it.
    shadow: Blame,

    /// The set of all **applied** edits `e` for which no edits dependent on `e` are applied -- i.e
    /// nothing in `e.after` is applied.
    ///
    /// This, along with the corresponding `bottommost_unapplied`, are stored so that we can
    /// minimize the number of edit positions we need to update whenever a change (one of: new
    /// edit, undo, redo) is made; only edits that could be undone or redone without any other
    /// edits changing are the ones whose positions we need to update.
    //
    // TODO-ALG: This could *probably* be made more efficient; we can use something similar in
    // spirit to `Ranged` in order to reduce the number of updates we need to do when there's a
    // change being made. Realistically, there probably isn't a whole lot of gain to be made there;
    topmost_applied: BTreeSet<EditId>,

    /// The set of all **unapplied* edits with all their dependencies applied. Essentially the
    /// inverse of `topmost_applied`.
    bottommost_unapplied: BTreeSet<EditId>,

    /// An incrementing counter to assign each edit a unique value for verification of [`EditId`]s
    count: UniqueEditId,
}

/// (*Internal*) The edits stored in an [`EditHistory`]
///
/// This is extracted out so that we can provide the [`get`](Self::get) and
/// [`get_mut`](Self::get_mut) methods without requiring a full borrow on the `EditHistory` itself.
struct Edits<Time, R> {
    /// The internal list of edits
    ls: Vec<Option<Edit<Time, R>>>,
}

/// A unique identifier corresponding to a single [`Edit`]
///
/// It should be noted that `EditId`s are only unique for the lifetime of an edit; after an
/// edit is discarded (a side-effect that may occur from calls to [`EditHistory::edit`]), the
/// corresponding `EditId` *will* be re-used.
//
// A note for the curious:
//
// Due to the `validation_id` field, `EditId`s ARE - strictly speaking - unique when building with
// debug assertions. However, the indexes they correspond to are not. This is used for extra
// validation when indexing, in order to ensure that old `EditId`s are never used.
//
/// [`Edit`]s are not exposed publicly, but typically represent a [`Diff`] paired with an
/// ordered abstraction of time. For more information about [`Edit`]s, refer to the
/// [module-level documentation](self).
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EditId {
    /// The index in the [`EditHistory`]'s list of edits that this points to
    idx: usize,

    /// The unique identifier given to the corresponding edit; used for checking that this `EditId`
    /// isn't stale (i.e. the old edit at the same index hasn't been removed)
    validation_id: UniqueEditId,
}

/// A unique value given to each [`Edit`]; a component of each [`EditId`]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct UniqueEditId {
    /// This value is a `NonZeroUsize` because it allows `Option<EditId>` to be significantly
    /// smaller
    id: NonZeroUsize,
}

impl UniqueEditId {
    /// (*Internal*) Increments the `UniqueEditId`
    fn increment(&mut self) {
        self.id = NonZeroUsize::new(self.id.get() + 1).unwrap()
    }
}

/// A [`Diff`] paired with the time it occured
///
/// These are visible only in documentation; there isn't a way to produce an `Edit` outside of this
/// module, but the descriptions available here may provide some additional insight not given by the
/// [module-level documentation](self).
///
/// An `Edit` can be returned from an [`EditHistory`] by the [`get_edit`](EditHistory::get_edit) or
/// [`drop_edits`](EditHistory::drop_edits) methods. This struct is primarily provided so that - if
/// edits are at some point discarded, their pieces may be retreived later.
pub struct Edit<Time, R> {
    /// A unique id given to this edit alone; used for ensuring that [`EditId`]s pointing to the
    /// index containing this value aren't stale.
    validation_id: UniqueEditId,

    /// Whether the edit has been "removed" from the graph. If it's still here, it hasn't been
    /// "purged" yet -- edits are allowed to remain stored in case the associated `Diff` might need
    /// to be used
    is_removed: bool,

    /// The [`Diff`] for this particular edit. There's a couple things to note here about the
    /// position of the diff (`diff.diff_idx`).
    ///
    /// The position of the diff is almost never correct. The *only* conditions under which it's
    /// guaranteed to be correct are if it has no unapplied dependencies and all its dependent
    /// edits are unapplied (i.e. when it's in `EditHistory.topmost_applied` or
    /// `.bottommost_unapplied`).
    diff: Diff<R>,

    time: Time,

    /// The stack of edits requesting this edit be present (or not)
    cause_stack: CauseStack,

    /// The set of immediately prior disjoint edits having an overlapping affected region. Paired
    /// with each edit is the offset from this `diff_idx` that it would occur at if all edits in
    /// `before` were present. These are sorted by the indexes of the affected ranges, meaning that
    /// they are also sorted by the offset.
    ///
    /// All edits `e` in `before` contain the [id](EditId) of this edit in `e.after`.
    before: Vec<(isize, EditId)>,

    /// The set of immediately following disjoint edits having an overlapping affected region.
    /// Paired with each edit is the offset from this `diff_idx` that it *would* occur at, if no
    /// other edits in `after` were applied.
    ///
    /// While this might seem to be a problem if, say `after[1].before` contains `after[0]`, that
    /// cannot actually occur; for `after[0]` to be included in `after[1].before`, the edits would
    /// not be disjoint.
    ///
    /// Like `before`, the edits here are sorted by the offset from this one.
    ///
    /// All edits `e` in `after` contain the [id](EditId) of this edit in `e.before`.
    after: Vec<(isize, EditId)>,

    /// The previous region of `EditHistory.blame` that this edit was constructed on top of
    ///
    /// The size of the blame region is equal to `2 * self.old.len() + 1`
    previous_blame: Blame,

    /// Like `previous_blame`, but for `EditHistory.shadow`. This field is only `Some(...)` if the
    /// edit has been undone at some point
    ///
    /// Similarly to `previous_blame`, the size of the region is equal to `2 * self.new.len() + 1`
    /// (Note! `shadow` uses `new`; `blame` uses `old`)
    previous_shadow: Option<Blame>,
}

/// The result of adding an [`Edit`] to the [`EditHistory`]
///
/// For more information, see [`EditHistory::edit`] - the only method that returns this type.
pub struct EditResult<R> {
    /// The id of the new `Edit`, if the edit was successful
    ///
    /// If [`EditHistory::edit`] was passed `override_newer = Yes`, then this will never be `None`.
    /// If `override_newer = No`, this value equalling `None` indicates that applying the edit
    /// failed.
    ///
    /// In short, if you pass `override_newer = Yes`, this is safe to unwrap.
    new_id: EditId,

    /// The diff(s) that occured as a result of applying the edit. This is often, but not always,
    /// the original diff passed in.
    ///
    /// The [`Diff`]s should be applied in order, without modification to any of them
    diffs: SmallVec<[Diff<R>; 1]>,

    /// The edits that were removed as a result of the edit. Edits within the `fixed` are not
    /// removed.
    ///
    /// When provided here, the edits are not yet de-allocated. They can be accessed externally
    /// with the [`get_edit`](EditHistory::get_edit) method, and fully dropped with the
    /// [`drop_edits`](EditHistory::drop_edits) method.
    removed: Vec<EditId>,
}

/// The result of undoing an edit within an [`EditHistory`]
///
/// This type is essentially the same as [`RedoResult`], but made distinct as part of an effort to
/// guard against accidental incorrect usage.
///
/// This contains both the required change to the text object and the set of other edits that may
/// have been undone as well. It is the responsibility of the caller to record that these edits were
/// undone - or separately check with [`EditHistory::is_present`] before calls to
/// [`undo`](EditHistory::undo).
pub struct UndoResult<R> {
    /// The change(s) required to the text object to account for this action
    ///
    /// The [`Diff`]s should be applied in order, without modification to any of them
    pub diffs: SmallVec<[Diff<R>; 1]>,

    /// The complete list of edits that were un-applied as a direct result of undoing this edit,
    /// *including this one*.
    pub undone: SmallVec<[EditId; 1]>,
}

/// The result of redoing an edit within an [`EditHistory`]
///
/// This type is essentially the same as [`UndoResult`], but made distinct as part of an effort to
/// guard against accidental incorrect usage.
///
/// This contains both the required change to the text object and the set of other edits that may
/// have been redone as well. It is the responsibility of the caller to record that these edits were
/// redone - or separately check with [`EditHistory::is_present`] before calls to
/// [`redo`](EditHistory::redo).
pub struct RedoResult<R> {
    /// The change(s) required to the text object to account for this action, in order
    ///
    /// The [`Diff`]s should be applied in order, without modification to any of them
    pub diffs: SmallVec<[Diff<R>; 1]>,

    /// The complete list of edits that were re-applied as a direct result of reapplying this edit,
    /// *including this one*.
    pub redone: SmallVec<[EditId; 1]>,
}

///////////////////////////////
// Internal, convenience API //
///////////////////////////////

impl<Time, R> Edits<Time, R> {
    /// (*Internal*) Retrieves an immutable reference to the corresponding edit, panicking if the
    /// [`EditId`] is invalid
    ///
    /// The prefix string provided is prepended to any panic message generated; it may simply be
    /// `""`.
    #[rustfmt::skip]
    fn get(&self, err_prefix: &str, id: EditId) -> &Edit<Time, R> {
        let edit = self.ls.get(id.idx)
            .expect(&format!("{}{}", err_prefix, "invalid `EditId`: index out of bounds"))
            .as_ref()
            .expect(&format!("{}{}", err_prefix, "edit has already been destroyed"));

        assert!(
            id.validation_id == edit.validation_id,
            "{}{}",
            err_prefix,
            "invalid `EditId`: edit has already been destroyed"
        );

        edit
    }

    /// (*Internal*) Retrieves a mutable reference to the corresponding edit, panicking if the
    /// [`EditId`] is invalid
    ///
    /// The prefix string provided is prepended to any panic message generated; it may simply be
    /// `""`.
    #[rustfmt::skip]
    fn get_mut(&mut self, err_prefix: &str, id: EditId) -> &mut Edit<Time, R> {
        let edit = self.ls.get_mut(id.idx)
            .expect(&format!("{}{}", err_prefix, "invalid `EditId`: index out of bounds"))
            .as_mut()
            .expect(&format!("{}{}", err_prefix, "edit has already been destroyed"));

        assert!(
            id.validation_id == edit.validation_id,
            "{}{}",
            err_prefix,
            "invalid `EditId`: edit has already been destroyed"
        );

        edit
    }
}

////////////////
// Public API //
////////////////

/// An abstraction over immutable, unordered collections of [`EditId`]s, with access to an
/// [`EditHistory`]
///
/// There are standalone implementations provided for the standard library's set types: both
/// [`BTreeSet`] and [`HashSet`]. The trait primarily exists so that the set of "fixed" edits used
/// in [`EditHistory::edit`] does not need to be stored separately, and that the API need not be
/// dependent on particular outside data structures being used.
///
/// There is also an implementation provided for zero-length arrays, allowing them to serve as the
/// empty set.
pub trait EditSet<Time, R> {
    /// Returns whether set contains the provided value
    fn contains(&self, history: &EditHistory<R, Time>, edit: EditId) -> bool;
}

impl<Time, R> EditSet<Time, R> for BTreeSet<EditId> {
    fn contains(&self, _history: &EditHistory<R, Time>, edit: EditId) -> bool {
        BTreeSet::contains(self, &edit)
    }
}

impl<Time, R> EditSet<Time, R> for HashSet<EditId> {
    fn contains(&self, _history: &EditHistory<R, Time>, edit: EditId) -> bool {
        HashSet::contains(self, &edit)
    }
}

impl<Time, R> EditSet<Time, R> for [EditId; 0] {
    fn contains(&self, _history: &EditHistory<R, Time>, _edit: EditId) -> bool {
        false
    }
}

impl<'a, Time, R, S> EditSet<Time, R> for &'a S
where
    S: EditSet<Time, R>,
{
    fn contains(&self, history: &EditHistory<R, Time>, edit: EditId) -> bool {
        S::contains(*self, history, edit)
    }
}

impl<Time: Clone + Ord, R: BytesRef> EditHistory<Time, R> {
    /// Creates a new, blank `EditHistory` for a text object with the given length
    pub fn new(len: usize) -> Self {
        EditHistory {
            edits: Edits { ls: Vec::new() },
            last_unused: None,
            blame: Ranged::new(None, 2 * len + 1),
            shadow: Ranged::new(None, 2 * len + 1),
            topmost_applied: BTreeSet::new(),
            bottommost_unapplied: BTreeSet::new(),
            count: UniqueEditId {
                id: NonZeroUsize::new(1).unwrap(),
            },
        }
    }

    /// Returns the total length of the text object this represents
    pub fn len(&self) -> usize {
        self.blame.size() / 2
    }

    /// Returns a reference to the edit associated with the provided `EditId`
    ///
    /// ## Panics
    ///
    /// This method will panic on any invalid `EditId`: always for edits that have since been
    /// dropped (with [`drop_edits`](Self::drop_edits)), and sometimes for edits corresponding to a
    /// different [`EditHistory`].
    pub fn get_edit(&self, id: EditId) -> &Edit<Time, R> {
        self.edits.get("", id)
    }

    /// Prints the graph, using the provided function to map [`EditId`]s to a displayed name
    ///
    /// This is only really used within the `tests` submodule.
    #[cfg(test)]
    pub fn print_graph<'a>(&self, display: impl 'a + Fn(EditId) -> &'a str) {
        println!("---- Print Graph ----");
        println!("--- Blame ---");
        let blame_strs: Vec<_> = (self.blame)
            .iter()
            .map(|(b, range)| {
                format!(
                    "({} × {})",
                    range.len(),
                    b.map(|b| display(b.id)).unwrap_or("—")
                )
            })
            .collect();
        let mut blame_str = format!("[{}", blame_strs[0]);
        blame_strs[1..].iter().for_each(|s| {
            blame_str.push_str(", ");
            blame_str.push_str(&s);
        });
        blame_str.push(']');

        println!("{}", blame_str);

        println!("------ Graph ------");
        let iter = (self.edits.ls)
            .iter()
            .enumerate()
            .filter_map(|(i, e)| Some((i, e.as_ref()?)));
        for (idx, edit) in iter {
            let base_id = EditId {
                idx,
                validation_id: edit.validation_id,
            };
            let before: Vec<_> = edit.before.iter().map(|&(_, id)| display(id)).collect();
            let after: Vec<_> = edit.after.iter().map(|&(_, id)| display(id)).collect();
            println!(
                "{:?}: before = {:?}, after = {:?}",
                display(base_id),
                before,
                after
            )
        }
        println!("-------- End --------");
    }

    /// Drops all of edits corresponding to the given `EditId`s, returning the edits themselves
    ///
    /// The edits must no longer be in use - i.e. indicated as removed by a call to
    /// [`self.edit(..)`](Self::edit). The returned list has each edit paired with its ID.
    ///
    /// ## Panics
    ///
    /// This method panics if any of the `EditId`s are invalid (i.e. if `get_edit` would panic), or
    /// if the edits are still in use. This method cannot be used to remove undone edits.
    ///
    /// There are also certain, internal invariants that may cause this method to panic if
    /// violated. Those cannot be avoided, except by submitting bug reports :)
    pub fn drop_edits(&mut self, ids: &[EditId]) -> Vec<(EditId, Edit<Time, R>)> {
        let min_idx = ids.iter().map(|id| id.idx).min();
        self.last_unused = self.last_unused.min(min_idx);

        let edits = ids
            .into_iter()
            .map(|&id| {
                // Check that the edit is still there:
                if !self.get_edit(id).is_removed {
                    panic!(
                        "cannot remove edit with {:?}: edit has not been removed",
                        id
                    );
                }

                (id, self.edits.ls[id.idx].take().unwrap())
            })
            .collect();

        // FIXME: We still need to remove all of the `EditId`s here from cause stacks. It'll look
        // something like this:
        //
        //     let id_set = ids.iter().cloned().collect();
        //     self.edits
        //         .do_foreach_affected_mut::<Undo, _, _>(&self.topmost_applied, |_, edit| {
        //             let did_remove = edit.cause_stack.remove_all(&id_set);
        //             did_remove
        //         });
        //     self.edits
        //         .do_foreach_affected_mut::<Redo, _, _>(&self.bottommost_unapplied, |_, edit| {
        //             let did_remove = edit.cause_stack.remove_all(&id_set);
        //             did_remove
        //         });
        //
        // That depends a bit on the exact semantics of how we'd like to expose this. I don't know
        // whether we can just "simply remove" them from the stack without changing it. It might be
        // that it just so happens to be the case, but that would take a fair amount of effort to
        // sufficiently prove.

        edits
    }

    /// Adds a new edit to the history, removing any conflicting, currently-unapplied edits
    ///
    /// The [module-level documentation](self) is required pre-reading for understanding this
    /// method.
    ///
    /// `EditHistory::edit` works as you'd expect for normal cases; it's only the corner cases that
    /// add complexity to this method. As such, it is vitally important that you understand the
    /// precise behavior here before using it.
    ///
    /// ## Semantics
    ///
    /// To explain the semantics guaranteed by this method, we'll start with the general
    /// description of what happens internally.
    //
    // TODO-DOC. There's a couple specific examples that should be represented here to describe
    // corner cases.
    //  1. Committing a new edit on a cluster that's partially-undone: it destroys the previous
    //     newer edits.
    //  2. Committing a new edit that's older than the most-recent edit: it *might* destroy
    //     previous newer edits. It's linear in the number of edits it needs to go through.
    //  3. Multiple edits can occur at the same time, but we DON'T allow conficting edits to occur
    //     at the same time.
    pub fn edit(
        &mut self,
        mut diff: Diff<R>,
        time: Time,
        // The set of edits we aren't allowed to touch when we add ours
        fixed: impl EditSet<R, Time>,
        // Note: returns error if applying would remove an edit in `fixed`
    ) -> Result<EditResult<R>, ()> {
        // Adding an edit is not *too* difficult. There's essentially (n) different things we need
        // to check & do:
        //
        //  1. For all edits `e` with `e.time > time`, emulate applying the edits in order,
        //     shifting the position of this one by the required amount. (TODO-ALG: we could do
        //     this in batches to mean we only need to do this once for a set of out-of-date edits)
        //     If there's any edit that conflicts with this one and has a later timestamp, we'll
        //     either (i) return that we failed to add the new edit, if it's in `fixed`, or (ii)
        //     we'll mark it for removal.
        //  2. Mark all edits in `self.shadow` directly above this diff for removal
        //  3. With the corrected position, calculate `this.before` based on the edits present in
        //     `self.blame`.
        //  4. Apply the edit! Set `self.blame` appropriately, add it to `topmost_applied`, and
        //     remove its dependencies from `topmost_applied`.
        //
        // We'll go through these in order.

        // Step 1:
        //
        // This is the most tricky step.
        //
        // In order to find all currently-applied edits with `e.time > time`, we'll search
        // backwards from every value in `self.topmost_applied`. Because it's so complicated, we're
        // basically going to cheat: we'll use an auxiliary data structure to do most of the hard
        // work for us.
        //
        // Our magic data structure essentially serves as a map of usize -> Option<usize>, giving
        // us the "new" position corresponding to any old one. Once we've processed all of the
        // edits with `e.time > time`, it'll also tell us which edits conflict with the one we want
        // to add. Assuming that those aren't fixed (i.e. in `fixed`), we remove them and then get
        // the final, true position of the edit we're adding.
        //
        // To do this, we need to traverse the graph. Note that typically - because this graph
        // traversal only includes edits with `e.time > time` - it will typically only visit leaf
        // nodes; it's rarely the case that old edits are added after the fact.
        //
        // The implementation for constructing the `PosMap` is in `make_pos_map`; it doesn't have
        // much worth talking about though - it just uses `do_foreach_affected_ref`.

        let mut pos_map = self.make_pos_map(&time, TrackBlame::Yes);

        // If there's edits that we need to remove, we'll do that. Afterwards, we'll reconstruct
        // the mapping and get the position again.
        let init_diff_range = diff.diff_idx..diff.diff_idx + diff.old.len();
        let conflicts = pos_map.conflicts_from(init_diff_range);

        let mut resulting_diffs = SmallVec::new();

        if !conflicts.is_empty() {
            // First pass: we'll check if we're able to remove newer edits that are *currently*
            // applied. Before
            let mut can_do_edit = true;
            self.edits
                .do_foreach_affected_ref::<Undo, _, _>(conflicts.as_slice(), |id, _| {
                    if fixed.contains(self, id) {
                        can_do_edit = false;
                    }

                    can_do_edit
                });

            // We can't do the edit if we have conflicts we can't touch
            if !can_do_edit {
                return Err(());
            }

            // If there's no conflicts (yet), we'll undo these edits. It's possible in theory that
            // we need then redo these, but (1) that should be fine, albeit a bit expensive, and
            // (2) it should be very rare in practice.
            for &id in &conflicts {
                if let Some(res) = self.try_undo(id) {
                    resulting_diffs.extend(res.diffs);
                }
            }

            // Remake `pos_map`, after having removed these edits:
            pos_map = self.make_pos_map(&time, TrackBlame::No);
        }

        // Edits that we had to undo to get rid of these conflicts, but we're not sure if we can
        // commit to them; there may yet be other edits that prevent us from making the one we
        // want. We'll redo all of these if we need to.
        let tentative_undo = conflicts.as_slice();

        // Step 2 (somewhat): Also add regions from `self.shadow`
        diff.diff_idx = pos_map.map_index(diff.diff_idx);
        let blame_range = 2 * diff.diff_idx..2 * (diff.diff_idx + diff.old.len()) + 1;
        let shadow_conflicts: Vec<_> = (self.shadow)
            .clone_range(blame_range.clone())
            .iter()
            .filter_map(|(&b, _)| Some(b?.id))
            .collect();

        let mut removed_edits = Vec::new();

        // We then need to check if we're allowed to remove the shadow conflicts as well. At least
        // some of these will have been in the original `pos_map`, if there were conflicts there.
        // That's a rare enough case that it's not worth dealing with.
        if !shadow_conflicts.is_empty() {
            // This is just as above, for the `pos_map` conflicts
            let mut can_do_edit = true;
            self.edits.do_foreach_affected_ref::<Undo, _, _>(
                shadow_conflicts.as_slice(),
                |id, _| {
                    if fixed.contains(self, id) {
                        can_do_edit = false;
                    }

                    removed_edits.push(id);
                    can_do_edit
                },
            );

            // If we couldn't do the edit, we can't just return as we did in the `pos_map` case. We
            // have to undo the edits we just did as well.
            if !can_do_edit {
                for &id in tentative_undo {
                    self.try_redo(id);
                }
                return Err(());
            }

            // Otherwise, we can go ahead and mark these all for removal. We need to remove each
            // edit from its dependencies, so that it won't get accidentally included in the graph
            // again. We also need to tag it as removed.
            for &id in &removed_edits {
                // First: tag the edit as removed
                let edit = self.edits.get_mut("", id);
                edit.is_removed = true;

                // Second: remove the edit from its dependencies. Technically, this could be more
                // efficient if we don't clone here. It's probably fine.
                let deps = edit.before.clone();
                for (offset, dep_id) in deps {
                    let dep = self.edits.get_mut("", dep_id);
                    let remove_idx = dep
                        .after
                        .binary_search_by_key(&-offset, |&(o, _)| o)
                        .expect(
                            "edit does not have self at equal offset in edit from `self.before`",
                        );
                    debug_assert!(dep.after[remove_idx].1 == id);
                    dep.after.remove(remove_idx);
                }

                // Third: remove this edit from `self.bottommost_unapplied`, if it's there.
                self.bottommost_unapplied.remove(&id);
            }
        }

        // Step 3:
        //
        // We're generating the values of `edit.before` here. While directly taking the values from
        // `self.blame` *does* produce valid values (subject to a couple restrictions), we can do
        // better: only take the edits that aren't reachable by anything else in `before`. At
        // first, it might seem like this requires some kind of graph traversal - but we can
        // actually exploit the time-based orderings of edits to do this in a single pass.

        let mut before = Vec::new();
        #[cfg(debug_assertions)]
        let mut before_set = BTreeSet::new();

        let blame_range = 2 * diff.diff_idx..2 * (diff.diff_idx + diff.old.len()) + 1;

        // The boolean here stores whether this value had time greater than the one before it (or
        // if there was a gap with the one before)
        let mut last_values: Option<(bool, &Time, (isize, EditId))> = None;
        for (blame, mut range) in self.blame.clone_range(blame_range.clone()).iter() {
            // We need to shift the ranges because they start from zero in the cloned sub-range of
            // `blame`
            range.start += blame_range.start;
            range.end += blame_range.end;

            let (last, b) = match (last_values, blame) {
                (Some((true, _, (o, id))), None) => {
                    before.push((o, id));
                    debug_assert!(before_set.insert(id));
                    last_values = None;
                    continue;
                }
                (_, None) => {
                    last_values = None;
                    continue;
                }
                (last, Some(b)) => (last, b),
            };

            let offset = (range.start / 2 - diff.diff_idx) as isize - (b.start_idx / 2) as isize;
            let time = &self.edits.get("", b.id).time;

            let is_gt = match last {
                None => true,
                Some((true, last_t, (o, id))) if last_t > time => {
                    before.push((o, id));
                    debug_assert!(before_set.insert(id));
                    false
                }
                Some((_, last_t, _)) => {
                    assert!(last_t < time);
                    true
                }
            };

            last_values = Some((is_gt, time, (offset, b.id)));
        }
        if let Some((true, _, pair)) = last_values {
            before.push(pair);
        }

        before.sort_by_key(|(o, _)| *o);

        let validation_id = self.count;
        self.count.increment();
        let idx = (self.last_unused)
            .map(|idx| {
                self.last_unused =
                    (idx + 1..self.edits.ls.len()).find(|&i| self.edits.ls[i].is_none());
                idx
            })
            .unwrap_or_else(|| {
                self.edits.ls.push(None);
                self.edits.ls.len() - 1
            });

        let new_id = EditId { idx, validation_id };

        // Step 4:
        //
        // It's time to actually apply the edit now!
        //
        // Set `self.blame`:
        let blame = BlameRange {
            start_idx: 0,
            id: new_id,
        };

        let previous_blame = self.blame.replace(
            blame_range,
            Ranged::new(Some(blame), 2 * diff.new.len() + 1),
        );

        // Calculate the final `Diff`:
        resulting_diffs.push(diff.clone());

        // Remove everything in `edit.before` from `self.topmost_applied`, add the new edit. Also
        // add the new edit to all `e.after` for `e` in `before`.
        for (offset, id) in &before {
            // The edit isn't always in `topmost_applied`, but we have to remove it if it was
            self.topmost_applied.remove(id);
            let b_edit = self.edits.get_mut("", *id);

            // Add the new edit to `b_edit.after`:
            let idx = b_edit
                .after
                .binary_search_by_key(&-offset, |&(o, _)| o)
                .unwrap_or_else(|i| i);
            b_edit.after.insert(idx, (-offset, new_id));
        }

        self.topmost_applied.insert(new_id);

        let edit = Edit {
            validation_id,
            is_removed: false,
            diff,
            time,
            cause_stack: CauseStack::new(),
            before,
            after: Vec::new(),
            previous_blame,
            previous_shadow: None,
        };

        debug_assert!(self.edits.ls[idx].is_none());

        self.edits.ls[idx] = Some(edit);

        Ok(EditResult {
            new_id,
            diffs: resulting_diffs,
            removed: removed_edits,
        })
    }

    /// Undoes the edit if it is present, otherwise indicating that it should *stay* undone
    ///
    /// This serves as a way of indicating that an edit should be intentionally excluded,
    /// preventing it from being reapplied if one of its dependencies is reapplied.
    pub fn try_undo(&mut self, id: EditId) -> Option<UndoResult<R>> {
        self.try_op::<Undo>(id).map(Into::into)
    }

    /// Undoes the given edit, along with any other dependent edits that are currently applied
    ///
    /// The returned [`UndoResult`] contains both the [`Diff`] to apply to the text object and the
    /// list of additionally undone edits. This is somewhat complex, so it bears explanation:
    ///
    /// When we're undoing an "old" edit (i.e. one where newer edits are also applied), there's a
    /// chance that some newer edits rely on its result. If we were to only undo the target edit,
    /// the state of the text object wouldn't be well defined, so we need to *also* undo all of the
    /// edits that rely on this one. For more information about the edit system as a whole, please
    /// refer to the [module-level documentation](self).
    ///
    /// ## Panics
    ///
    /// This method will panic if the specified edit has already been undone. The list of edits
    /// that are additionally undone here is returned as part of the [`UndoResult`]; this list
    /// *must* be processed.
    ///
    /// Whether an edit has already been undone can be checked with [`EditHistory::is_present`].
    /// For a fallible version of this edit, see [`try_undo`](Self::try_undo).
    pub fn undo(&mut self, id: EditId) -> UndoResult<R> {
        self.do_op::<Undo>(id).into()
    }

    /// Redos the edit if it's not present, otherwise indicating that it should stay present
    ///
    /// This serves as a way of indicating that an edit should be intentionally included,
    /// preventing it from being undone if one of its dependencies is also undone.
    pub fn try_redo(&mut self, id: EditId) -> Option<RedoResult<R>> {
        self.try_op::<Redo>(id).map(Into::into)
    }

    /// Redoes the given edit, along with any other edits it depends on that are currently
    /// unapplied
    ///
    /// The returned [`RedoResult`] contains both the [`Diff`] to apply to the text object and the
    /// list of additionally redone edits. For more information, please refer to [`undo`] (which is
    /// exactly the same as this method, but in reverse) or the [module-level documentation].
    ///
    /// ## Panics
    ///
    /// Like [`undo`], this method will panic if the provided edit is already applied. The list of
    /// edits that are redone here is returned as part of the [`RedoResult`]; this list *must* be
    /// processed.
    ///
    /// Whether an edit has already been redone can be checked with [`EditHistory::is_present`].
    /// For a fallible version of this method, see [`try_redo`](Self::try_redo).
    ///
    /// [`undo`]: Self::undo
    /// [module-level documentation]: self
    pub fn redo(&mut self, id: EditId) -> RedoResult<R> {
        self.do_op::<Redo>(id).into()
    }
}

/////////////////////////////////////
// Internal implementation details //
/////////////////////////////////////

/// (*Internal*) The result of an operation, from [`EditHistory::do_op`] or [`EditHistory::try_op`]
///
/// This only exists temporarily, before it is converted to an [`UndoResult`] or [`RedoResult`],
/// which is provided the implementations of [`Into`].
struct OpResult<R> {
    /// The change required to the text object because of the operation
    diffs: SmallVec<[Diff<R>; 1]>,

    /// The complete list of edits that were changed as a result of performing the operation,
    /// including the one requested
    affected_edits: SmallVec<[EditId; 1]>,
}

impl<R> Into<RedoResult<R>> for OpResult<R> {
    fn into(self) -> RedoResult<R> {
        RedoResult {
            diffs: self.diffs,
            redone: self.affected_edits,
        }
    }
}

impl<R> Into<UndoResult<R>> for OpResult<R> {
    fn into(self) -> UndoResult<R> {
        UndoResult {
            diffs: self.diffs,
            undone: self.affected_edits,
        }
    }
}

impl<Time: Clone + Ord, R: BytesRef> EditHistory<Time, R> {
    fn make_pos_map(&self, time: &Time, track_blame: TrackBlame) -> PosMap<Time, R> {
        let mut pos_map = PosMap::new(self.len(), track_blame);

        self.edits
            .do_foreach_affected_ref::<Redo, _, _>(&self.topmost_applied, |id, edit| {
                if &edit.time < time {
                    return false;
                } else if &edit.time == time {
                    panic!("Attempted to add edit with `time` equal to another");
                }

                pos_map.simulate_undo(id, edit);
                true
            });

        pos_map
    }

    /// (*Internal*) Performs the full undo or redo operation for a given edit, assuming that it is
    /// not currently in the desired state
    ///
    /// The generic parameter `Op` serves to allow us to - at compile time - abstract over whether
    /// we're undoing or redoing. This method provides the implementation for the
    /// [`undo`](Self::undo) and [`redo`](Self::redo) methods.
    ///
    /// This method will panic if the edit is already in the requested state. For the fallible
    /// version, see [`try_op`](Self::try_op).
    fn do_op<Op: Operation<Time>>(&mut self, id: EditId) -> OpResult<R> {
        // Performing a single operation is a fairly simple procedure. We essentially do it in two
        // parts:
        //  1. Collect all of the edits that need to change
        //  2. Perform the individual operation on each edit in turn, collecting the full `Diff`
        //     that results from the procedure.
        //
        // While we're performing the individual operations, it's not necessarily the case that the
        // graph will stay in a valid state.

        // Step 1: Collect all of the edits that need to change.
        //
        // The `do_foreach_affected_*` helper methods give us edits ordered by time in the opposite
        // direction that we need to perform the operations. So: we'll go through each edit,
        // modifying the cause stacks. For any edit that indicates it should change because of this
        // operation, we push onto a FIFO queue so that edits are accounted for *after* their
        // dependencies.
        let mut queue = SmallVec::new();

        // TODO-ALG: This currently has the possibility of taking linear time in the depth of the
        // edit graph; that's not great. What this means in practice is that normal undo behavior
        // for a linear number of edits takes quadratically-many cause stack updates. One way we
        // could possibly improve this is by grouping regions of the graph together, where we allow
        // cause to be - in some sense - built into the graph itself.
        //
        // This kind of optimization, while probably *somewhat* useful, doesn't provide enough of
        // an impact to be done soon, though it definitely SHOULD be done eventually.
        // (Written Feb.  2021)
        self.edits
            .do_foreach_affected_mut::<Op, _, _>(&[id], |e_id, edit| {
                // If we're looking at the dependencies of a redo, and we get far enough down a
                // graph to the point where the cause stacks are empty, we don't need to register
                // ourselves.
                //
                // This is to stop a full graph traversal in cases where we've already undone
                // everything we need to.
                if edit.cause_stack.is_empty() && !Op::IS_UNDO {
                    return false;
                }

                if edit.cause_stack.op::<Time, Op>(id) {
                    queue.push(e_id);
                }
                true
            });

        // We then need to check all of the edits that were most-recently changed because of a
        // previous operation on this one.
        let mut backwards_queue = SmallVec::new();
        self.edits
            .do_foreach_affected_mut::<Op::Inverse, _, _>(&[id], |e_id, edit| {
                // Don't do the base edit twice:
                if e_id == id {
                    return true;
                }

                // We can safely remove from the top here because we know that the edit stack is
                // in-line with the base edit
                let (had_edit, changed) = edit.cause_stack.remove_if_top(id);
                if changed {
                    backwards_queue.push(e_id);
                }
                had_edit
            });

        println!("backwards_queue: {:?}", backwards_queue);

        backwards_queue.reverse();
        backwards_queue.extend(queue);
        queue = backwards_queue;

        // Step 2:
        // Do all of the operations :)
        let mut diffs = SmallVec::new();
        for &id in queue.iter().rev() {
            let edit = self.edits.get("", id);
            match Op::IS_UNDO {
                true => diffs.push(edit.diff.clone().invert()),
                false => diffs.push(edit.diff.clone()),
            }

            self.update_single_op::<Op>(id);
        }

        OpResult {
            diffs,
            affected_edits: queue,
        }
    }

    /// (*Internal*) Attempts to undo or redo the given edit, if it is needed. Otherwise marks the
    /// edit as explicitly in its state
    ///
    /// Like [`do_op`](Self::do_op), this serves as the shared, abstract implementation of
    /// [`try_undo`](Self::try_undo) and [`try_redo`](Self::try_redo).
    fn try_op<Op: Operation<Time>>(&mut self, id: EditId) -> Option<OpResult<R>> {
        let edit = self.edits.get("", id);

        // If the edit isn't in the desired state, do full operation, as required.
        if edit.is_applied() != Op::GOAL_IS_APPLIED {
            return Some(self.do_op::<Op>(id));
        }

        // Otherwise, we don't have much to do - just mark everything that this edit depends on
        self.edits
            .do_foreach_affected_mut::<Op, _, _>(&[id], |_, edit| {
                let did_change = edit.cause_stack.op::<Time, Op>(id);
                debug_assert!(!did_change);
                true
            });

        None
    }

    /// Updates the state of the graph to reflect performing the operation on the given edit
    ///
    /// This method doesn't update any edit-local values (`diff`, `cause_stack`, etc.)
    fn update_single_op<Op: Operation<Time>>(&mut self, id: EditId) {
        // There's a few structures in the `EditHistory` that need updating whenever we perform an
        // operation, namely: `blame`, `topmost_applied`, and `bottommost_unapplied`.
        //
        // The essential change to `blame` is that we're either setting a range to equal this
        // `EditId`, or we're restoring the previous blame that was below us. For redoing, we set
        // `blame`; for undoing we restore it.
        //
        // `topmost_applied` and `bottommost_unapplied` are fairly simple; we remove the edit from
        // the correct one of these, then check if any of the edits dependent on it can be added.
        // Because all of the edits in those sets must have valid diff positions, we also shift
        // those if needed.

        let edit = self.edits.get_mut("`EditHistory` internal error: ", id);
        let edit_idx = edit.diff.diff_idx;

        // Here, "old" and "new" refer to before & after this method is called; while the values
        // are taken from `edit.diff.{old,new}`, they'll be swapped if we're undoing.
        let (old_size, new_size) = match Op::IS_UNDO {
            true => (edit.diff.new.len(), edit.diff.old.len()),
            false => (edit.diff.old.len(), edit.diff.new.len()),
        };

        let old_blame_range = 2 * edit_idx..2 * (edit_idx + old_size) + 1;
        let new_blame_size = 2 * new_size + 1;

        ///////////////////////////////////
        // Part 1: Modify blame & shadow //
        ///////////////////////////////////

        if Op::IS_UNDO {
            // Undo!

            let new_shadow = Ranged::new(Some(BlameRange { start_idx: 0, id }), new_blame_size);

            debug_assert!(edit.previous_shadow.is_none());
            edit.previous_shadow = Some(self.shadow.replace(old_blame_range.clone(), new_shadow));
            let _ = (self.blame).replace(old_blame_range, edit.previous_blame.clone());
        } else {
            // Redo!
            //
            // We *could* double-check that the blame is the same, but that's a lot of extra work
            // when we don't need to use the value for anything else.

            let new_blame = Ranged::new(Some(BlameRange { start_idx: 0, id }), new_blame_size);
            let _ = self.blame.replace(old_blame_range.clone(), new_blame);

            let restored_shadow = (edit.previous_shadow)
                .take()
                .expect("`EditHistory` internal error: redo edit without previous shadow");
            self.shadow.replace(old_blame_range, restored_shadow);
        }

        /////////////////////////////////////////////////////////////////
        // Part 2: Update `topmost_applied` and `bottommost_unapplied` //
        /////////////////////////////////////////////////////////////////

        // TODO-PERF: We could actually hold the reference here, as a raw pointer; when we go to
        // use this later, we aren't modifying `edit.before` or `edit.after`. That requires a bit
        // of unsafe though, so it's only necessary if this turns out to be a performance
        // bottleneck (unlikely).
        let edit_required_by = Op::required_by(&edit).to_owned();
        let (this_shift_from, this_shift_into) = match Op::IS_UNDO {
            true => (&mut self.bottommost_unapplied, &mut self.topmost_applied),
            false => (&mut self.topmost_applied, &mut self.bottommost_unapplied),
        };

        this_shift_from.remove(&id);
        this_shift_into.insert(id);

        for (_, e_id) in &edit_required_by {
            this_shift_from.insert(*e_id);
        }
        for (_, e_id) in Op::requires(&edit) {
            this_shift_into.remove(e_id);
        }

        // Shift everything in topmost_applied and bottommost_unapplied:
        for &id in (self.topmost_applied.iter()).chain(self.bottommost_unapplied.iter()) {
            let edit = self.edits.get_mut("`EditHistory` internal error: ", id);
            let pos = &mut edit.diff.diff_idx;
            if *pos < (edit_idx + old_size) {
                *pos += new_size;
                *pos -= old_size;
            }
        }

        // After shifting everything, we need to go back and reset the positions of the edits
        // that are (because of changing this one) newly in `topmost_applied` or
        // `bottommost_unapplied`:

        for (offset, id) in edit_required_by {
            let mut edit = self.edits.get_mut("`EditHistory` internal error: ", id);
            edit.diff.diff_idx = (edit_idx as isize + offset) as usize;
        }
    }
}

impl<Time: Clone + Ord, R> Edits<Time, R> {
    /// (*Internal*) An immutable specialization of [`do_foreach_affected_internal`]
    fn do_foreach_affected_ref<'a, Op, Iter, Func>(&self, ids: Iter, mut func: Func)
    where
        Op: Operation<Time>,
        Iter: IntoIterator<Item = &'a EditId>,
        Func: FnMut(EditId, &Edit<Time, R>) -> bool,
    {
        Self::do_foreach_affected_internal::<Op, _, Iter, _>(self, ids, |id, edit| {
            (func(id, &edit), edit)
        })
    }

    /// (*Internal*) A mutable specialization of [`do_foreach_affected_internal`]
    fn do_foreach_affected_mut<'a, Op, Iter, Func>(&mut self, ids: Iter, mut func: Func)
    where
        Op: Operation<Time>,
        Iter: IntoIterator<Item = &'a EditId>,
        Func: FnMut(EditId, &mut Edit<Time, R>) -> bool,
    {
        Self::do_foreach_affected_internal::<Op, _, Iter, _>(self, ids, |id, mut edit| {
            let keep_going = func(id, &mut edit);
            (keep_going, edit)
        })
    }

    /// (*Internal*) Calls a function once for each edit in `ids` and their dependencies for the
    /// operation
    ///
    /// This is a bit abstract; consider the case of undoing a single edit -- we have other edits
    /// that come after the starting one that may need to be undone as well. If that's the case,
    /// this method will call `func` for each edit in `ids[0].after` and all of the edits in their
    /// dependencies, both directly and indirectly. Edits are provided to `func` in order of
    /// distance in time from `id`, starting with those close in time.
    ///
    /// `func` will not be called with the same edit twice. If `func` returns `false` for an edit,
    /// its dependencies for the operation will not have `func` called with them -- mostly; an edit
    /// is only not added if *all* of the edits that depend on it return false.
    //
    // Well dang. We'd really like to be able to use `impl IntoIterator` or `impl FnMut(...)` here
    // to make the signature shorter. But becuase we *need* to supply `Op` explicitly whenever this
    // method is called, and because rustc doesn't allow you to make generic parameters explicit
    // when there's `impl Trait` syntax, we can't do that.
    fn do_foreach_affected_internal<'a, Op, Ref, Iter, Func>(
        mut this: Ref,
        ids: Iter,
        mut func: Func,
    ) where
        Ref: EditsRef<Time, R>,
        Op: Operation<Time>,
        Iter: IntoIterator<Item = &'a EditId>,
        Func: FnMut(EditId, Ref::Edit) -> (bool, Ref::Edit),
    {
        use std::cmp::Ordering;

        // The standard library's `BinaryHeap` is a max heap. We therefore require an ordering that
        // places the maximum away from the direction of dependencies -- i.e. reversed for undo and
        // the normal ordering for redo, because the direction of dependencies is forward in time
        // for undoing and backwards in time for redoing.
        let mut queue = BinaryHeap::new();

        // The queue is filled with `Entry`s; each edit paired with the time at which it occured.
        // The implementation of `Ord` is such that only the time is taken into account.
        struct Entry<Time: Ord> {
            time: Time,
            id: EditId,
        }

        impl<Time: Ord> PartialEq for Entry<Time> {
            fn eq(&self, other: &Self) -> bool {
                self.time == other.time
            }
        }

        impl<Time: Ord> Eq for Entry<Time> {}

        impl<Time: Ord> Ord for Entry<Time> {
            fn cmp(&self, other: &Self) -> Ordering {
                self.time.cmp(&other.time)
            }
        }

        impl<Time: Ord> PartialOrd for Entry<Time> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        for id in ids.into_iter().map(|i| *i.borrow()) {
            let e = this.get_edit(id);
            let time = e.time.clone();
            this = e.recover();

            queue.push(Entry {
                id,
                time: Op::ord(time),
            });
        }

        let mut previous_id = None;
        while let Some(entry) = queue.pop() {
            if Some(entry.id) == previous_id {
                continue;
            }

            let edit = this.get_edit(entry.id);

            // While we have access to the edit directly, we'll add the necessary elements to the
            // queue. We have to collect these before adding them to the queue in order to avoid
            // borrowing conflicts on `self.edits`
            let next_ids: SmallVec<[_; 2]> =
                Op::requires(&edit).iter().map(|&(_, id)| id).collect();

            // And then call the function as required
            let (recurse, edit_returned) = func(entry.id, edit);
            previous_id = Some(entry.id);

            this = edit_returned.recover();

            if recurse {
                // Now that we don't need this iteration's `edit` anymore, we can go ahead and add
                // its dependencies to the queue.
                //
                // We'd really like to be able to use `queue.extend(...)`, but that unfortunately
                // ends up with unworkable borrow-checker side effects from the mapping closure.
                queue.reserve(next_ids.len());
                for id in next_ids {
                    let e = this.get_edit(id);
                    let time = Op::ord(e.time.clone());
                    this = e.recover();

                    queue.push(Entry { time, id });
                }
            }
        }
    }
}

impl<Time: Clone + Ord, R: BytesRef> Edit<Time, R> {
    /// Returns whether the edit is currently applied to the text object
    fn is_applied(&self) -> bool {
        self.cause_stack.is_present()
    }
}
