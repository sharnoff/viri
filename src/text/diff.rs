//! A module for specifying byte-wise text differences

use std::cmp::Ordering as CmpOrdering;
use std::fmt::{self, Display, Formatter};
use std::ops::Range;
use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use lazy_static::lazy_static;

/// The number of bytes on either side of a diff to include as verification
pub const CTX_LEN: usize = 16;

/// A single change to a source set of bytes
///
/// This is inspired by Google's [diff-match-patch] library and its specification of a format very
/// similar to [Unidiff].
///
/// All of the fields are made public so that more specialized [`apply`] implementations may be
/// written.
///
/// [diff-match-patch]: https://github.com/google/diff-match-patch/wiki/Unidiff
/// [Unidiff]: https://en.wikipedia.org/wiki/Diff#Unified_format
/// [`apply`]: #method.apply
#[derive(Debug, Clone)]
pub struct Diff {
    /// Additional context about the region immediately preceeding the location of the change,
    /// provided for verification
    ///
    /// This records the previous CTX_LEN bytes, if available. If the diff is less than that many
    /// bytes out from the start of the file, the list will be shortened to that number. E.g. for
    /// an edit at the start of the file, `pre_context.len()` will be zero. For one taking place
    /// after 10 bytes, this value will be 10, etc.
    pub pre_context: Vec<u8>,

    /// Additional context about the region immediately following the location of the change,
    /// provided for verification
    ///
    /// This is nearly exactly the same as `pre_context`, but works in the opposite direction; it
    /// gives the bytes following the change instead.
    pub post_context: Vec<u8>,

    /// The index in the set of bytes to make the change
    pub diff_idx: usize,

    /// The original values being replaced
    ///
    /// This is provided so that diffs can be reversed
    pub old: Vec<u8>,

    /// The new values replacing `old` at `diff_idx`.
    pub new: Vec<u8>,
}

/// An enumerated error type for representing failure to apply a `Diff`
#[derive(Debug, Clone)]
pub enum Error {
    StartIndexOutOfBounds { idx: usize, len: usize },
    EndIndexOutOfBounds { idx: usize, len: usize },
    MismatchPreContext,
    MismatchPostContext,
    InvalidState,
    // The only valid error
    IncompatibleUpdate,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Error::*;

        match self {
            StartIndexOutOfBounds { idx, len } => write!(
                f,
                "Error: starting index {} out of bounds for len {}",
                idx, len
            ),
            EndIndexOutOfBounds { idx, len } => write!(
                f,
                "Error: ending index {} out of bounds for len {}",
                idx, len
            ),
            MismatchPreContext => write!(f, "Error: mismatched pre-context"),
            MismatchPostContext => write!(f, "Error: mismatched post-context"),
            InvalidState => write!(f, "Error: invalid diff state"),
            IncompatibleUpdate => write!(f, "incompatible diff update"),
        }
    }
}

impl Diff {
    /// Applies the diff to the target set of bytes, returning an [`Error`] on failure
    ///
    /// This is mostly provided as a default implementation; most use cases will require some other
    /// context in order to reduce the cost of yielding the entire vector to this method.
    ///
    /// For more information on failure cases, refer to the documentation for `Error`.
    ///
    /// [`Error`]: enum.Error.html
    pub fn apply(&self, target: &mut Vec<u8>) -> Result<(), Error> {
        // Validating all of the indices
        let len = target.len();
        let end = self.diff_idx + self.old.len();

        if self.diff_idx > len {
            return Err(Error::StartIndexOutOfBounds {
                idx: self.diff_idx,
                len,
            });
        } else if end > len {
            return Err(Error::EndIndexOutOfBounds {
                idx: self.diff_idx + self.old.len(),
                len,
            });
        } else if self.pre_context.len() > self.diff_idx {
            log::error!("Diff::apply, line {}: invalid state {:?}", line!(), self);
            return Err(Error::InvalidState);
        } else if end + self.post_context.len() > len {
            return Err(Error::MismatchPostContext);
        }

        // Now we can index safely without fear of panics
        // We'll first check that both of the contexts are correct

        if self.pre_context.len() != self.diff_idx.min(CTX_LEN) {
            log::error!("Diff::apply, line {}: invalid state {:?}", line!(), self);
            return Err(Error::InvalidState);
        } else if self.post_context.len() != (len - end).min(CTX_LEN) {
            return Err(Error::MismatchPostContext);
        }

        let pre_range = Range {
            start: self.diff_idx - self.pre_context.len(),
            end: self.diff_idx,
        };
        if &self.pre_context[..] != &target[pre_range] {
            return Err(Error::MismatchPreContext);
        }

        let post_range = end..end + self.post_context.len();
        if &self.post_context[..] != &target[post_range] {
            return Err(Error::MismatchPostContext);
        }

        // And now we've finally verified it
        //
        // The actual application is simple.
        //
        // We could improve this with unsafe code or perhaps without using an additional heap
        // allocation every single time, but the reality of the situation is that this doesn't
        // really matter - the actual diff application process is unlikely to be a bottleneck at
        // any point.
        let mut new_values = Vec::with_capacity(len + self.new.len() - self.old.len());
        new_values.extend_from_slice(&target[..self.diff_idx]);
        new_values.extend_from_slice(&self.new);
        new_values.extend_from_slice(&target[end..]);

        *target = new_values;

        Ok(())
    }

    /// Updates another diff to be compatible with the changes from the first
    ///
    /// This will return an error if the updated diff is not compatible with the first. There are
    /// *many* comments inside this function to explain case.
    #[rustfmt::skip]
    pub fn update(&self, _other: &mut Diff) -> Result<(), Error> {
        todo!()
        /*
        Currently, this is disabled until this is formalized.

        // There are a few cases to consider here:
        // 1. `other` is before `self`
        //   1a. Without overlap in contexts
        //   1b. *With* overlap in contexts
        // 2. `other` is after `self`
        //   2a. Without overlap in contexts
        //   2b. *With* overlap in contexts
        // and finally:
        // 3. `other` and `self` overlap at both ends
        //   3a. `other` and `self` are both inserts...
        //
        // The last subcategory is the most difficult to handle, and even the best case (3a) is not
        // perfect - do we prefer `other` to go before or after?

        // Basic indexing cases we want to handle beforehand
        if self.pre_context.len() > self.diff_idx {
            log::error!("Diff::update, line {}: invalid state {:?}", line!(), self);
            return Err(Error::InvalidState);
        } else if other.pre_context.len() > other.diff_idx {
            log::error!("Diff::update, line {}: invalid state {:?}", line!(), other);
            return Err(Error::InvalidState);
        }

        // We first check for a complete miss before (1):
        let other_end = other.diff_idx + other.old.len();
        if other_end + other.post_context.len() < self.diff_idx {
            // Case 1
            // 1a is fairly simple, and is just done outright. 1b is not nearly as simple.
            
            if other_end + other.post_context.len() < self.diff_idx - self.pre_context.len() {
                // Case 1a
                //
                // There aren't any additional checks we can do here, and we actually don't need to
                // update `other` at all; it's completely unaffected
                return Ok(());
            }

            // Case 1b
            //
            // For this case, we also check that the contexts match. There's a couple annoying edge
            // cases here...
            //
            // For example: Suppose `self` and `other` act in turn on an array of length 4, where
            // `self` appends (diff_idx = 4), and `other` prepends (`diff_idx = 0`). In both cases,
            // the length of the contexts will be limited because they exist at the boundary.
            //
            // We'll go through each of them in turn. We'll use '*' to represent the location of
            // `other.diff_idx`, and '&' to represent 'self.diff_idx'.
            // Additionally, '-' will represent the post-context of `other`, and `|` will represent
            // the pre-context of `self`. We'll use '+' to represent the intersection of the two.

            // I: Overflowing overlap
            //   ||^++++&    <- RHS is at the edge
            //     ^++++&--  <- LHS is at the edge
            //   ||^++++&--  <- both sides
            // The above cases are the only *valid* ones possible. We get the first variant when
            // `other` is within CTX_LEN of the end, and we get the second when `self` is within
            // `CTX_LEN` of 0. The third case occurs when both of these are true. In all three of
            // these, the region between self and other is smaller than CTX_LEN (and this only
            // occurs in any of these three).
            //
            // BUT FIRST! it is worth noting that the overflow can be entirely captured inside
            // `old` in either of these cases without going over to the outer contexts. Also:
            // `other` should not be expected to include the changes made *due to `self`*.
            if self.diff_idx - other_end < CTX_LEN {
                // Whether we have case 1
                let overflow_left = {
                    // We can't directly examine from the length of the byte sequence (we don't
                    // have access to it!). We know that `self.post_context` will be empty if it's
                    // at the end, so we can use that instead.
                    self.post_context.is_empty()
                };

                // Whether we have case 2
                let overflow_right = other.diff_idx == 0;

                // Catch a potential error - we need this for index assumptions later
                if overflow_right && !other.pre_context.is_empty() {
                    log::error!("Diff::update, line {}: invalid state: {:?}", line!(), other);
                    return Err(Error::InvalidState);
                }

                todo!()
                // ^ Have a look at the comment describing this section.
            }

            // II: Partial overlap
            //   ^---+++|||&
            // For this to be the case, the lengths of the contexts must be less than what would be
            // required to reach the other values. There's an additional validity check to be made
            // here: If they aren't long enough to reach each other, they should be the maximum
            // length. -- In fact, if one of them is too short, the other one should be as well! So
            // we can just take the minimum of the two! (Because we already tried case I)
            //
            // Fortunately, this actually just ends up as the `else` clause from case I:
            /* if self.diff_idx - other_end
                >= min(self.pre_context.len(), other.post_context.len()).min(CTX_LEN) */
            if self.pre_context.len() != CTX_LEN {
                // This is probably a mistake, so we'll log it
                log::error!("Diff::update, line {}: invalid state: {:?}", line!(), self);
                return Err(Error::InvalidState);
            } else if self.post_context.len() != CTX_LEN {
                // This *might* just be incompatibility due to something else. We'll return one
                // of the simpler errors
                return Err(Error::MismatchPostContext);
            }

            // At this point, the indices are valid, so we can just compare and return.
            let overlap_start_idx = self.diff_idx - CTX_LEN;
            let overlap_size = 2*CTX_LEN - (self.diff_idx - other_end);
            //  ^^^^^^^^^^^^ Guaranteed to be <= CTX_LEN because of the condition assumed by
            //  getting to this block
            
            let other_range = (overlap_start_idx - other_end) .. CTX_LEN;
            let self_range = 0 .. overlap_size;

            if &self.pre_context[self_range] != &other.post_context[other_range] {
                // There isn't really a proper error we could return here, but this will
                // suffice.
                return Err(Error::MismatchPostContext);
            }

            // If that was fine, we're done! This one is *still* compatible
            return Ok(());
        }
        */
    }

    /// Takes as input a byte index and produces a new one, after considering the diff
    ///
    /// This essentially determines where the new index would be after applying the diff. There are
    /// a couple of specifics detailed further inside the method definition.
    pub fn shift_idx(&self, idx: usize) -> usize {
        // This operation should be fairly simple - there are a few things to look out for, though.
        // There are basically three cases:
        //  1. idx is before self;
        //  2. idx is after self; and
        //  3. idx is inside self
        // The first two are trivial to handle; we'll get those out of the way right now:

        // Note that if idx = self.diff_idx, we'll default to keeping the index where it is
        if idx <= self.diff_idx {
            return idx;
        } else if idx >= self.diff_idx + self.old.len() {
            // To be sure this condition isn't off by one, imagine the following:
            // diff_idx = 0; old.len() = 3; idx = 3.
            //
            //     old.len
            //  ╒═════╩═════╕
            //  | 0 | 1 | 2 | 3 | ...
            //    ↑           ↑
            // diff_idx      idx
            //
            // From this, it's clear that if idx was 2, it *would* be affected by the change, but
            // because it's 3, it isn't (and 4 wouldn't, either). So idx *may* be equal to
            // `diff_idx + old.len()`.
            return idx + self.new.len() - self.old.len();
        }

        // Now we're at case 3 - where the index is inside the change. There isn't really a *right*
        // answer here. To make things easy for ourselves, we'll stick to something simple: we'll
        // just put the index at the end of the changed region.

        self.diff_idx + self.new.len() - self.old.len()
    }

    /// Returns the inverse diff corresponding to this one
    ///
    /// The inverse diff can be thought of as the diff that undoes the given diff.
    pub fn inverse(&self) -> Self {
        Self {
            old: self.new.clone(),
            new: self.old.clone(),
            ..self.clone()
        }
    }

    /// Returns whether the diff is structurally valid - i.e. whether it *could* actually exist
    ///
    /// This is actually very simple, and is therefore limited in scope. It checks the lengths of
    /// both contexts (that they are ≤ [`CTX_LEN`]) and that `diff_idx >= pre_context.len()`.
    ///
    /// [`CTX_LEN`]: const.CTX_LEN.html
    pub fn is_valid(&self) -> bool {
        self.pre_context.len() <= CTX_LEN.min(self.diff_idx) && self.post_context.len() <= CTX_LEN
    }
}

/// A wrapper around `SystemTime` to provide more accurate time differences
///
/// This is mostly a best-effort improvement at the moment. In the future, clock recalibration
/// could be agreed over a connection. This value uses an epoch-based system to ensure that `Time`
/// values can be compared monotonically, even though `SystemTime`s cannot.
///
/// Equality of `Time`s is provided; this simply holds the case that the same *value* can be
/// checked for equality. Separately-generated `Time`s will never be equal.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Time {
    sys_time: SystemTime,
    epoch: usize,
}

lazy_static! {
    static ref LAST_TIME: Arc<Mutex<Time>> = Arc::new(Mutex::new(Time {
        sys_time: SystemTime::now(),
        epoch: 0
    }));
}

impl Time {
    fn now() -> Self {
        let mut guard = LAST_TIME.lock().unwrap();

        // We get the time *after* locking so that we don't have clock races with the following
        // comparison
        let now = SystemTime::now();

        let epoch = if guard.sys_time <= now {
            guard.epoch + 1
        } else {
            guard.epoch
        };

        let this = Time {
            sys_time: now,
            epoch,
        };

        *guard = this;
        this
    }
}

impl PartialOrd for Time {
    fn partial_cmp(&self, other: &Time) -> Option<CmpOrdering> {
        Some(self.cmp(other))
    }
}

impl Ord for Time {
    fn cmp(&self, other: &Time) -> CmpOrdering {
        if self.epoch != other.epoch {
            self.epoch.cmp(&other.epoch)
        } else {
            self.sys_time.cmp(&other.sys_time)
        }
    }
}
