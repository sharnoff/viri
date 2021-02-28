//! Wrapper module for the [`PosMap`] type, a specialized data structure used to implement
//! [`EditHistory::edit`]
//!
//! [`EditHistory::edit`]: super::EditHistory::edit

use super::ranged::{Constant, IndexedRangeSlice, Ranged};
use super::{BytesRef, Edit, EditId};
use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::ops::Range;

// `Translation` is defined lower down in this module.
use Translation::{Edited, Shifted};

/// A specialized data structure used to implement [`EditHistory::edit`]
///
/// There's a very specific problem that this is designed to solve: When we're adding an "old"
/// edit, we can't immediately determine where it should go. We're given its position from *when it
/// was made*, but that may have shifted since. In order to figure out what its current position
/// *should* be, we can pretend to undo all of the newer edits, purely tracking their positions.
pub(super) struct PosMap<Time, R> {
    /// The representation of how to map an "old" position to a new one, sectioned by how each
    /// range of indexes is mapped
    map: Ranged<Translation>,

    /// All of the edits for which no edit they depend upon has had its "simulated undo", paired
    /// with their position in the text object
    ///
    /// We essentially require all positions to be updated for each undo we simulate, just like how
    /// the `EditHistory` does for any operation.
    bottommost_undone: BTreeMap<EditId, usize>,

    /// If it's desired, store the blame
    blame: Option<Ranged<Constant<Option<EditId>>>>,

    /// Ensure that a `PosMap` can't be shared between `EditHistory`s - or at least not for ones
    /// with different types
    marker: PhantomData<(Time, R)>,
}

/// A helper type to represent the way old values are mapped to newer ones
///
/// For any index in the "old" values, either (a) it has been overwritten or (b) it has been
/// shifted by some amount, but not overwritten. Ranges with the first case are represented by the
/// `Edited` variant, with the second case done by `Shifted`. Indexes that have been edited don't
/// have an equivalent "new" index, so they cannot be mapped to a new value.
///
/// `Edited` ranges additionally carry the mapping that was previously above them, so that - if
/// need be - they can be inverted. If two `Edited` ranges have the same `EditId`, they are
/// guaranteed to have the same previous mapping, provided that no edit is processed twice.
#[rustfmt::skip]
#[derive(Clone)]
enum Translation {
    Edited { id: EditId },
    Shifted { new: usize },
}

impl IndexedRangeSlice for Translation {
    type Value = Option<usize>;

    fn index(&self, idx: usize) -> Option<usize> {
        match self {
            Edited { .. } => None,
            Shifted { new } => Some(new + idx),
        }
    }

    fn split_at(&mut self, idx: usize) -> Self {
        match self {
            Shifted { new } => Shifted { new: *new + idx },
            Edited { .. } => self.clone(),
        }
    }

    fn try_join(self, self_size: usize, other: Self) -> Result<Self, (Self, Self)> {
        match (&self, &other) {
            (Shifted { new: s }, Shifted { new: o }) if s + self_size == *o => Ok(self),
            (Edited { id: s, .. }, Edited { id: o, .. }) if s == o => Ok(self),
            _ => Err((self, other)),
        }
    }
}

/// Boolean flag for whether a `PosMap` should store "blame" information
pub enum TrackBlame {
    Yes,
    No,
}

impl<Time: Ord, R: BytesRef> PosMap<Time, R> {
    /// Creates a new `PosMap` with the specified *current size* of the text object
    ///
    /// `do_blame` indicates whether the map should store blame information. `TrackBlame::Yes` is
    /// required to call [`PosMap::conflicts_from`] later.
    pub fn new(current_size: usize, do_blame: TrackBlame) -> Self {
        PosMap {
            bottommost_undone: BTreeMap::new(),
            map: Ranged::new(Shifted { new: 0 }, current_size),
            blame: match do_blame {
                TrackBlame::Yes => Some(Ranged::new(Constant(None), 2 * current_size + 1)),
                TrackBlame::No => None,
            },
            marker: PhantomData,
        }
    }

    /// Adds the edit to the set of ranges we take into account, incorporating the position offset
    /// we'd expect if it were about to be undone
    ///
    /// The position of the edit need not be correct; it is not used.
    pub fn simulate_undo(&mut self, id: EditId, edit: &Edit<Time, R>) {
        let start_idx = edit
            .after
            .iter()
            .filter_map(|&(o, id)| {
                self.bottommost_undone
                    .get(&id)
                    .map(|pos| (*pos as isize - o) as usize)
            })
            .next()
            // If there aren't any edits in `edit.after` that are in `bottommost_undone`, this edit
            // must be applied without anything dependent on it applied; it's at the top, so the
            // index doesn't change.
            .unwrap_or(edit.diff.diff_idx);

        // We're replacing `new` with `old` because we're simulating an 'undo'.
        let range = start_idx..start_idx + edit.diff.new.len();

        self.bottommost_undone.insert(id, start_idx);
        edit.after
            .iter()
            .for_each(|(_, id)| drop(self.bottommost_undone.remove(id)));

        self.bottommost_undone.values_mut().for_each(|p| {
            if *p > range.start {
                debug_assert!(*p >= range.end);
                *p = *p + edit.diff.old.len() - edit.diff.new.len();
            }
        });

        self.map.replace(
            range.clone(),
            Ranged::new(Edited { id }, edit.diff.old.len()),
        );

        // If we're tracking the blame, do that
        if let Some(b) = self.blame.as_mut() {
            let blame_range = 2 * range.start..2 * range.end + 1;
            let old_blame = b.replace(
                blame_range,
                Ranged::new(Constant(Some(id)), 2 * edit.diff.old.len() + 1),
            );
            assert!({
                let mut iter = old_blame.iter();
                iter.next();
                iter.next().is_none()
            });
        }
    }

    /// Returns the list of edits that build upon an element of the provided range
    ///
    /// This is equivalent to the list of edits that would *directly* conflict if we were to add a
    /// new edit affecting `old_range`. Please note that this means only the edits at the "bottom"
    /// of the graph will be returned; edits reachable by another will not.
    ///
    /// This method is only available if this `PosMap` was constructed with [`TrackBlame::Yes`].
    ///
    /// ## Panics
    ///
    /// This method will panic if `old_range` is not contained within the size of the "old" text
    /// object. It will also panic if this `PosMap` was not constructed with [`TrackBlame::Yes`].
    pub fn conflicts_from(&mut self, old_range: Range<usize>) -> Vec<EditId> {
        let blame = match self.blame.as_mut() {
            None => panic!("cannot call `PosMap::conflicts_from`: value not tracking blame"),
            Some(b) => b,
        };

        let blame_range = 2 * old_range.start..2 * old_range.end + 1;
        // TODO-RFC#2229
        let bottommost_undone = &self.bottommost_undone;

        blame
            .clone_range(blame_range)
            .iter()
            .filter_map(|(Constant(opt), _)| *opt)
            .filter(|id| bottommost_undone.contains_key(id))
            .collect()
    }

    /// Maps the given index, assuming there aren't any edits that would conflict
    /// with it
    ///
    /// ## Panics
    ///
    /// This method will panic if there are any edits that would conflict with the index - for a
    /// loose definition of "conflict". All cases where this might panic would have
    /// `self.conflicts_from(idx..idx)` return a non-empty list.
    pub fn map_index(&mut self, idx: usize) -> usize {
        self.map.index(idx).expect("index has conflicting edits")
    }
}
