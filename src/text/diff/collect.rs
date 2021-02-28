// NOTE: This module is currently not used. It is bug-ridden, but will be necessary at some point
// to merge multiple edits into one. It needs lots and lots of tests.
//
//! Wrapper module for the [`Collect`] type, which allows collecting multiple adjacent [`Diff`]s
//! into a single one.

use super::{BytesRef, Diff};
use std::ops::Range;

/// (*Internal*) A helper struct for collecting many adjacent [`Diff`]s into a single, larger
/// [`Diff`]
///
/// This exists primarily as a helper type for operations on [`EditHistory`], but could
/// theoretically be applied elsewhere. Typical usage starts with [`Collect::new`], adds multiple
/// edits with [`add_edit`], and finishes with [`into_single`].
///
/// [`EditHistory`]: super::EditHistory
/// [`add_edit`]: Self::add_edit
/// [`into_single`]: Self::add_single
//
// If you're looking for a deeper understanding, there's a detailed description inside the
// `add_diff` method about how this works.
pub struct Collect {
    start_is_set: bool,
    start_idx: usize,

    old: Vec<u8>,
    new: Vec<u8>,

    regions: Vec<DiffRegion>,
}

struct DiffRegion {
    old_range: Range<usize>,
    new_range: Range<usize>,
}

impl Collect {
    /// Instantiates the `Collect` object
    pub fn new() -> Self {
        println!("new `Collect`");
        Collect {
            start_is_set: false,
            start_idx: 0,
            old: vec![],
            new: vec![],
            regions: vec![],
        }
    }

    /// Adds a `Diff` to the set, treating it as inverted if the const parameter indicates as such
    ///
    /// This method will panic if the `Diff` provided conflicts with the current output that we
    /// already have.
    //
    // If you're wanting to look at the internals of this function, know that  it's ~450 lines
    // long. There's *many* comments, but it is a hefty beast. Get a glass of water and some
    // snacks, because you'll be here a while.
    pub fn add_diff<const INVERTED: bool, R: BytesRef>(&mut self, diff: &Diff<R>) {
        // Ensure everything's initialized nicely
        if !self.start_is_set {
            self.start_idx = diff.diff_idx;
        }

        // There's a particular illustration that I find helpful to understanding what's going on
        // here.
        //
        // You can think of a `Collect` object as having two layers of regions: those for the `new`
        // values and those for `old`. We could draw some example as:
        //
        //     new:  |-----|     |-----|      |-----|
        //     old:  |---|     |---------|      |---|
        //
        // This example has 3 distinct regions. We can then draw adding a diff to this as piling
        // *on top* of the existing layers. It needs to be done this way because it's primarily
        // being applied to the `new` values, not the old ones.
        //
        // A diff that partially intersects with the second region might look like:
        //
        //          new (diff):       |--|
        //          old (diff):     |-----|
        //     new:  |-----|     |-----|      |-----|
        //     old:  |---|     |---------|      |---|
        //
        // The key thing to note here is the overhang on the right side of "old (diff)". Because
        // that region hasn't been modified yet (i.e. there isn't a range in `new` covering it), it
        // *must* have values from `old`. So we know that the last few values of this particular
        // diff actually correspond to what the values of `old` should be:
        //
        //          new (diff):       |--|
        //          old (diff):     |-----|
        //     new:  |-----|     |-----|   \  |-----|
        //     old:  |---|     |---------|++|   |---|
        //
        // (My apologies for the poor drawing. The plus characters are meant to symbolize the part
        // of `old` that has values filled in from this.)
        //
        // There's an invariant here that's not immediately obvious, and so should be briefly
        // discussed: the gaps between regions are guaranteed to be equal. To rephrase, all
        // adjacent regions r1 and r2 have the same distance between them for `r1,r2.new` and
        // `r1,r2.old`.
        //
        // Determining exactly why this must be true is left more as an exercise for the reader.
        // The only additional piece of information you should need is that inserting a diff at
        // some index `idx` will use `idx` for `new`, but will shift it for `old` by the sum of the
        // changes from earlier regions.
        //
        // For example, given a set of regions like:
        //
        //     new:  |--|
        //     old:  |----|
        //
        // Adding a diff past the end of the first region that has equal-sized `old` and `new`
        // components will look like:
        //
        //     new:  |--|       |----|
        //     old:  |----|       |----|
        //
        // Because we shift it to account for the earlier reduction in size from `old` to `new`.
        //
        //
        // --- THE ALGORITHM ---
        //
        // With all of this information in hand, it now becomes abundantly clear how to add a diff
        // here. So, broadly speaking, we split the work into two parts.
        //
        // -- Part 1 --
        //
        // In the first part, we check for parts of `diff.old` (or: `diff.new` if it's inverted)
        // that aren't covered by any range in `new`. These can then be traced down provide the
        // correct values for a section of `old`.
        //
        // The sections of `diff.old` that *are* covered by one of the ranges in `new` can be used
        // to verify accuracy.
        //
        // -- Part 2 --
        //
        // After writing the values of `old`, all that's *really* left is to write the values to
        // `new`. This is actually exceptionally simple because we don't need to adjust the indexes
        // at all.
        //
        // We also change the set of ranges as necessary: if the diff didn't overlap with any, then
        // we need to insert a new one. If it overlaps with one or more, we can merge those
        // together with the range covered by the diff.
        //
        // With that all out of the way, we'll start with...
        //
        //
        // Part 1:
        //
        // We'll go through each distinct range in `diff.old`, where distinct ranges are defined by
        // whether they overlap a range in `new`, setting the values of `self.old` where possible,
        // and checking with the values of `new` for those that overlap.
        //
        // To give an illustration of distinct ranges, we'll show a sample of `self.new` with
        // `diff.old` above it:
        //
        //    (diff) old: |xxx++++++xxxxxxx++|
        //    (self) new:     |----|       |----|
        //
        // The two types of regions are labeled with 'x's and '+'s. The ones labeled with 'x's are
        // what we call an "overhanging range", and those are used to set the values of `self.old`.
        // Each new region of 'x's or '+'s is a "distinct range".
        //
        // -- Actually getting to it --
        //
        // First off, we need to handle possible inversion of the diff.
        let (old, new) = match INVERTED {
            true => (&diff.new, &diff.old),
            false => (&diff.old, &diff.new),
        };

        // Then, we'll start going over all of the distinct ranges. This requires finding the first
        // region with a starting index <= that of the diff. It's possible there won't be one, in
        // which case the index will be `None`.
        //
        // We'll also use this varible for looping over distinct ranges
        let mut current_region_idx = (self.regions)
            .binary_search_by_key(&diff.diff_idx, |r| r.new_range.start)
            .map(Some)
            // On failure, we get the index we *could insert a region at*. This means that the
            // region below the diff will be equal to `i - 1`. Again, if there isn't one here, we
            // use `None`.
            .unwrap_or_else(|i| i.checked_sub(1));

        // (we'll do a sneaky save for later sorta deal)
        let starting_pre_region_idx = current_region_idx;

        // A value to track whether the current distinct range we're going through is inside or
        // after `current_region`
        let mut is_after_region = match current_region_idx {
            None => true,
            Some(i) => diff.diff_idx >= self.regions[i].new_range.end,
        };

        // The length of `old` that we've gone through.
        let mut covered_len = 0;

        // The actual loop over individual "distinct ranges"
        while covered_len < old.len() {
            // At the top of the loop, we'll 'quickly' handle the case of not being after any
            // region.
            let reg_idx = match current_region_idx {
                Some(i) => i,
                // If we're before any stored regions, `current_region_idx` is `None`. We'll go
                // through as much as we can. This can only be `None` on the first iteration.
                None => {
                    let first_region_start = self
                        .regions
                        .first()
                        .map(|r| r.new_range.start)
                        .unwrap_or(usize::MAX);

                    let len = (diff.diff_idx + old.len()).min(first_region_start) - diff.diff_idx;

                    self.set_old(diff.diff_idx, &old[..len]);
                    covered_len += len;

                    // Setting this to 1 might be out of bounds, but - if it is - we will have
                    // already consumed all of `old`, so we won't run into that.
                    current_region_idx = Some(1);
                    is_after_region = false;
                    continue;
                }
            };

            // The "normal" case continues:
            //
            // There's a large difference between the cases of being within a region or after
            // it, so we'll split by those.
            if is_after_region {
                // You'll notice that this appears similar to the `None` case for
                // `current_region_idx` above - it's because it *is* similar.
                let next_region_start = self
                    .regions
                    .get(reg_idx + 1)
                    .map(|r| r.new_range.start)
                    .unwrap_or(usize::MAX);

                let end_idx = (diff.diff_idx + old.len()).min(next_region_start);
                let len = end_idx - (diff.diff_idx + covered_len);

                // Because there are regions before us, we need to account for the shift in indexes
                // from new to old:
                let start_idx_in_new = diff.diff_idx + covered_len;
                let start_idx_in_old = self.regions[reg_idx].old_idx_from_new(start_idx_in_new);

                // And then we continue as usual
                self.set_old(start_idx_in_old, &old[covered_len..covered_len + len]);
                covered_len += len;
                current_region_idx = Some(reg_idx + 1);
                is_after_region = false;
            } else {
                // Inside a region!
                // This case is actually much nicer.
                //
                // If we're inside a region, the upper bound on the length is produced from
                // `region.new_range.end` (instead of the next region), and we ALSO don't need to
                // set the values of `old` (that's already been done!)
                //
                // The only actual piece of work we need to do here is to double-check that this
                // particular range of `old` matches what we already have.

                let end_idx = (diff.diff_idx + old.len()).min(self.regions[reg_idx].new_range.end);
                let start_idx = diff.diff_idx + covered_len;

                // Produce the two ranges for `self.new` and the diff
                let range_in_new = Range {
                    start: start_idx - self.start_idx,
                    end: end_idx - self.start_idx,
                };

                let range_in_diff = Range {
                    start: start_idx - diff.diff_idx,
                    end: end_idx - diff.diff_idx,
                };

                // We don't want to use assert_eq here because it panics with the debug print of
                // the arguments. If this happens on *really* big slices, that would be an
                // additional issue that we don't want to deal with.
                assert!(self.new[range_in_new] == old[range_in_diff]);

                covered_len += end_idx - start_idx;
                is_after_region = true;
            }
        }

        // Part 2:
        //
        // As indicated above, all we need to do is write the values to `new` and upate the ranges.
        // Let's do it:
        //
        // First of all, we'll make sure that `new` contains the space we need for `old` to exist.
        // We'll then replace the region afterwards.
        let diff_range = diff.diff_idx..diff.diff_idx + old.len();
        Self::ensure_contains_range(self.start_idx, &mut self.new, diff_range);

        // Now we'll actually apply the diff:
        //
        // If the size of the array is decreasing, we can avoid reallocating again by shifting the
        // portion of `new` after the diff to the left.
        if let Some(rm) = old.len().checked_sub(new.len()) {
            let idx = diff.diff_idx - self.start_idx;

            // Shift everything left by `rm`
            if rm != 0 {
                self.new[idx..].rotate_left(rm);
            }

            self.new.truncate(self.new.len() - rm);
            self.new[idx..idx + new.len()].copy_from_slice(new);
        } else {
            // Otherwise, we need to extend the vector:
            let ext = new.len() - old.len();
            self.new.reserve(ext);

            let idx = diff.diff_idx - self.start_idx;

            // We'll then extend the length of the vector, shift the tail to the right, and write
            // the new values in the middle:
            unsafe { self.new.set_len(self.new.len() + ext) }
            self.new[idx + old.len()..].rotate_right(ext);
            self.new[idx..idx + new.len()].copy_from_slice(new);
        }

        // After applying the diff, we need to shift (and combine) the ranges involved. This isn't
        // *too* bad, but there's a lot of fiddling about with indexes here.
        //
        // One of the tricks we're using for our index fiddling is tracking whether a region's
        // index is "inclusive" -- i.e. whether the region associated with that index touches the
        // diff or not. This is relevant because there's essentially two types of bounds we can
        // have:
        //
        //    Inclusive:
        //       (diff)         |----|
        //       (self)      |----|
        //
        //    Exclusive:
        //       (diff)              |----|
        //       (self)      |----|
        //
        // The other complication is that exclusive bounds also might not exist. So an exclusive
        // upper bound of `i` indicates that the region `i - 1` is either contained with the diff
        // or less than it. This is essentially equivalent to the exclusive upper bound on slicing
        // with ranges.
        //
        // Conversely, we treat the *addition* as already having been performed for exclusive lower
        // bounds, because we can't represent -1 as an unsigned integer. So an exclusive lower
        // bound of `i` indicates that the region at `i` itself is either contained within the diff
        // or greater than it. The region `i - 1` is then guaranteed to be less than the diff, if
        // it exists.
        //
        // To make things easier, we actually then also treat regular lower bounds like this: an
        // inclusive lower bound of `i` means that the region `i - 1` contains within it the lower
        // bound of the diff.
        //
        //
        // Anyways, with all that out of the way, we'll get on with the wacky index stuff.
        let (start_region, start_inclusive) = match starting_pre_region_idx {
            None => match self.regions.as_slice() {
                [] => (0, false),
                [reg, ..] => (1, diff.diff_idx <= reg.new_range.end),
            },
            Some(i) => (i + 1, diff.diff_idx <= self.regions[i].new_range.end),
        };

        // The value of `start_shift_idx` is non-trivial. The reason it exists is described in
        // depth below, in the section "SHIFTING REGIONS".
        let (end_region, end_inclusive, start_shift_idx) = self
            .regions
            .binary_search_by_key(&(diff.diff_idx + old.len()), |r| r.new_range.start)
            .map(|i| {
                // If we get an exact result, we know that
                //
                //   self.ranges[i].new_range.start == diff.diff_idx + old.len()
                //
                // so the diff *just barely* touches the range. Because we're including things like
                // this in the ranges we collapse, the index must be included. This is also the
                // special case that `start_shift_idx` exists for. More info (much further) below.
                (i, true, i)
            })
            .unwrap_or_else(|i| {
                // binary_search returns `Err(idx)` if we could insert a region starting at the end
                // of the diff at this index, and the region set would remain ordered. This means
                // that - if regions[i] exists - it'll have a start *after* the end of this diff.
                //
                // There are two cases here: either (a) `regions[i]` exists and contains the end of
                // the diff, or (b) it doesn't. If (a) is true, we should return `(i, true, ..)`,
                // but if (b) is true, we should return `(i + 1, false, ..)`.
                match self.regions.get(i) {
                    // If the region exists, we know that it starts before the diff ends. We're
                    // concerned about whether it ends before the diff starts.
                    Some(r) if r.new_range.start <= diff.diff_idx + old.len() => (i, true, i + 1),
                    // As above, anything else means it doesn't contain the diff
                    _ => (i + 1, false, i + 1),
                }
            });

        // -- SHIFTING REGIONS --
        //
        // Given these indexes, we'll delay collapsing the range into one until *after* we adjust
        // all of the positions.
        //
        // The reason we need to adjust the positions first is in the case of a region just
        // bordering the end of the diff. For example:
        //
        //    new (diff):           |--|
        //    old (diff):           |-----|
        //           new:  |-----|        |-----|
        //           old:  |---|            |---|
        //
        // The region at index 1 is not *strictly* included within the diff, but because it's
        // bordering the diff, we need to collapse it into our larger range.
        //
        // But it's also clear to see that it will be shifted to the left by applying the diff.
        // This is the only case like this, but it's crucial we account for it - which we have done
        // by keeping `start_shift_idx` from above.
        for region in &mut self.regions[start_shift_idx..] {
            match old.len() <= new.len() {
                true => {
                    let inc = new.len() - old.len();
                    region.new_range.start += inc;
                    region.new_range.end += inc;
                }
                false => {
                    let dec = old.len() - new.len();
                    region.new_range.start -= dec;
                    region.new_range.end -= dec;
                }
            }
        }

        // And then we produce the final region. This is also unfortunately complex.
        //
        // We're eventually initializing it as:
        //
        //   DiffRegion {
        //       old_range: old_start..old_end,
        //       new_range: new_start..new_end,
        //   }
        //
        let (old_start, new_start) = if start_inclusive {
            // We subtract 1 here because that's what's specified above.
            let r = &self.regions[start_region - 1];
            (r.old_range.start, r.new_range.start)
        } else {
            // We need to determine the corresponding "old" index for the start of the diff:
            let old_start = match starting_pre_region_idx {
                None => diff.diff_idx,
                Some(i) => self.regions[i].old_idx_from_new(diff.diff_idx),
            };

            (old_start, diff.diff_idx)
        };

        let (old_end, new_end) = if end_inclusive {
            let r = &self.regions[end_region];
            (r.old_range.end, r.new_range.end)
        } else {
            let new_end = diff.diff_idx + old.len();

            // We - once again - need to determine the corresponding "old" index for the start of
            // the diff.
            let old_end = match end_region.checked_sub(1) {
                None => new_end,
                Some(i) => self.regions[i].old_idx_from_new(new_end),
            };

            (old_end, new_end)
        };

        let new_region = DiffRegion {
            old_range: old_start..old_end,
            new_range: new_start..new_end,
        };

        // And finally, replacing the existing regions with the new one. We can use the same
        // "rotate them around and replace" trick as from before, when we were applying the diff.
        //
        // First, we need to find the actual range of regions being replaced. Both the start and
        // end require some slight modification.
        let replace_start = match start_inclusive {
            false => start_region + 1,
            true => start_region,
        };

        let replace_end = match end_inclusive {
            false => end_region,
            true => end_region + 1,
        };

        // Replacing is then pretty simple:
        if replace_start >= replace_end {
            self.regions.insert(replace_start, new_region);
        } else {
            let replace = replace_start..replace_end;

            // replace_start < replace_end, so we can do our rotate-trucate trick from before
            if replace.len() > 1 {
                let new_len = self.regions.len() - replace.len();

                self.regions[replace.start + 1..].rotate_left(replace.len() - 1);
                self.regions.truncate(new_len);
            }

            self.regions[replace_start] = new_region;
        }

        // And then we're done! Finally! You can be done with trying to understand this hellhole of
        // a function that took half a day to write.
    }

    /// Converts the set of `Diff`s into a single one, panicking if there were uncovered regions in
    /// the `Diff`s
    pub fn into_single<R: BytesRef>(self) -> Diff<R> {
        assert_eq!(self.regions.len(), 1);

        Diff {
            diff_idx: self.start_idx,
            old: self.old.into_boxed_slice().into(),
            new: self.new.into_boxed_slice().into(),
        }
    }
}

////////////////////////////////////////////////////////////
// Internal helper methods                                //
////////////////////////////////////////////////////////////

impl Collect {
    // A helper function for `set_old` and `add_diff`. The method of extension does not guarantee
    // anything about the values outside the range of the original vector after performing this
    // operation.
    fn ensure_contains_range(vec_start: usize, vec: &mut Vec<u8>, range: Range<usize>) {
        let extend_left = vec_start.checked_sub(range.start).unwrap_or(0);
        let extend_right = range.end.checked_sub(range.start + vec.len()).unwrap_or(0);

        if extend_left == 0 && extend_right == 0 {
            return;
        }

        // If there's the existing capacity for it, we'll perform this operation in place to avoid
        // reallocating.
        //
        // TODO-ALG: Is this generally more efficient than just reallocating? If it isn't, we
        // should just remove this step. At time of writing, this is implemented because the author
        // believes that avoiding new allocations is a good idea - especially considering that these
        // diffs will often be small.
        let required_cap = vec.len() + extend_left + extend_right;
        if vec.capacity() >= required_cap {
            // If the capacity is enough, we'll do a couple things. Essentially:
            //   1. set length higher and shift everything right by `extend_left`, then
            //   2. set length to `required_cap`.

            if extend_left != 0 {
                // SAFETY: Any byte is valid u8, so uninitialized memory is safe to use (albeit
                // possibly garbage). We know that the capacity is at least what's required because
                // of above.
                unsafe { vec.set_len(vec.len() + extend_left) }
                // Shift everything to the right:
                vec.rotate_right(extend_left);
            }

            // SAFETY: Same as above. We don't need to rotate because it's at the end.
            unsafe { vec.set_len(required_cap) }
            return;
        }

        // Otherwise, we create a new vector and copy everything in
        let mut new_vec = Vec::with_capacity(required_cap);
        // SAFETY: Any byte is a valid u8, so uninitialized memory is safe to use; we'll just have
        // garbage there if there's ever a logic error.
        unsafe { new_vec.set_len(required_cap) }

        // Copy everything in:
        new_vec[extend_left..required_cap - extend_right].copy_from_slice(&vec);
        // And continue on our merry way
        *vec = new_vec;
    }

    // Sets the values in `self.old` according to the starting index, stretching `self.old` as
    // required.
    fn set_old(&mut self, start_idx: usize, bytes: &[u8]) {
        self.start_idx =
            Self::set_offset_vec_range(self.start_idx, &mut self.old, start_idx, bytes);

        let end_idx = start_idx + bytes.len();
        Self::ensure_contains_range(self.start_idx, &mut self.old, start_idx..end_idx);

        self.start_idx = self.start_idx.min(start_idx);

        let range_in_vec = Range {
            start: start_idx - self.start_idx,
            end: end_idx - self.start_idx,
        };

        self.old[range_in_vec].copy_from_slice(bytes);
    }

    // Exactly the same as `set_old`, but for `self.new`
    fn set_new(&mut self, start_idx: usize, bytes: &[u8]) {
        self.start_idx =
            Self::set_offset_vec_range(self.start_idx, &mut self.new, start_idx, bytes);
    }

    // Shared internals of `set_{old,new}`.
    fn set_offset_vec_range(
        mut start_idx: usize,
        vec: &mut Vec<u8>,
        bytes_start: usize,
        bytes: &[u8],
    ) -> usize {
        let bytes_end = bytes_start + bytes.len();
        Self::ensure_contains_range(start_idx, vec, bytes_start..bytes_end);

        start_idx = start_idx.min(bytes_start);

        let range_in_vec = Range {
            start: bytes_start - start_idx,
            end: bytes_end - start_idx,
        };

        vec[range_in_vec].copy_from_slice(bytes);

        // Return the (maybe) new start_idx
        start_idx
    }
}

impl DiffRegion {
    // Converts an index in `new` to one in `old`, based on the new-to-old shift from this
    // `DiffRegion`
    fn old_idx_from_new(&self, idx: usize) -> usize {
        idx + self.new_range.end - self.old_range.end
    }
}
