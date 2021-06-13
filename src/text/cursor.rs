//! Wrapper module for the [`Cursor`] and [`SingleCursor`] types
//!
//! This is a private module, so most of the documentation is provided on types here. The
//! [`Cursor`] type is just a newtype over the internal enum that we use.

use std::mem;

/// One or more cursors in a text object, given by its byte position as a single point or a range
///
/// `Cursor`s handle a range of possible behaviors, including combinations of point-wise/selection
/// and single/multi-cursor. In general, some methods are only available on certain cursor states
/// (e.g. `as_single` panics if the cursor isn't single), and others will work in any state. These
/// methods are marked as such.
///
/// ## Multi-cursor leaders
///
/// A problem that exists when using multi-cursors is the challenge of knowing which cursor to
/// display on-screen. If the space spanned by them is too large, how do you choose which cursor to
/// focus on?
///
/// The solution we're using here is to assign a single cursor as the "leader". For a single
/// cursor, it's just that cursor, but it exists as a stable cursor for multi-cursors as well. The
/// current leader can be cycled around with the [`incr_leader`] and [`decr_leader`] methods, and
/// individual cursors can be removed with [`remove_leader`].
///
/// Having a single, stable cursor designated as the leader allows for displaying multiple cursors
/// in a way that stays smooth but allows the flexibility of exploring the progress of each cursor
/// without restarting.
///
/// [`incr_leader`]: Self::incr_leader
/// [`decr_leader`]: Self::decr_leader
/// [`remove_leader`]: Self::remove_leader
#[derive(Debug, Clone)]
pub struct Cursor<Pos>(Kind<Pos>);

#[derive(Debug, Clone)]
enum Kind<Pos> {
    Single(SingleCursor<Pos>),
    // The "leader" of a group of cursors allows us to choose a consistent cursor to focus on. It
    // can be cycled through with the `incr_leader` and `decr_leader` methods.
    Multi {
        cs: Vec<SingleCursor<Pos>>,
        leader: usize,
    },
}

/// An individual cursor, either as a point or range of bytes
///
/// This type exists because the [`Cursor`] type also allows multiple cursors, whereas this does
/// not. It can be extracted by the [`Cursor::as_single`] method, and is exposed to allow direct,
/// checked access to the internals.
#[derive(Debug, Copy, Clone)]
pub enum SingleCursor<Pos> {
    /// A cursor at a singular byte position in the text
    ///
    /// This is the "standard" way of viewing a cursor.
    Point(Pos),

    /// A cursor that exists as a selection over a range of bytes. In a typical GUI textbox, this
    /// might be made by `shift+<arrow key>`.
    ///
    /// In order to allow the actual position of the cursor to be independent of the start and
    /// ending bytes of the selection, we have a seperate `cursor_point` field that's required to
    /// be between `start` and `end`. The [`as_point`] method returns this value.
    ///
    /// [`as_point`]: Self::as_point
    Selection {
        // We can't really use a Range<Pos> here because Range doesn't implement copy,
        // unfortunately -- it'd mean that `SingleCursor` never implements copy.
        start: Pos,
        end: Pos,
        cursor_point: Pos,
    },
}

impl<Pos> Cursor<Pos> {
    /// Creates a new, single-point [`Cursor`] at the given byte position in the text
    pub fn new_single(pos: Pos) -> Cursor<Pos> {
        Cursor(Kind::Single(SingleCursor::Point(pos)))
    }

    /// Returns the number of individual cursors that this object holds
    ///
    /// The result of this function can guarantee some others as well; `num_cursors() == 1` means
    /// that `is_single()` is true, and `num_cursors() > 1` means that `is_multi()` is true.
    ///
    /// There will always be at least one cursor.
    pub fn num_cursors(&self) -> usize {
        match &self.0 {
            Kind::Single(_) => 1,
            Kind::Multi { cs, .. } => {
                debug_assert_ne!(cs.len(), 0);
                cs.len()
            }
        }
    }

    /// Returns true if this cursor object corresponds to a single internal cursor
    ///
    /// This method must return `true` to use methods marked "Only for single cursors" without
    /// panicking.
    pub fn is_single(&self) -> bool {
        self.num_cursors() == 1
    }

    /// Returns true if this cursor object corresponds to multiple internal cursors
    ///
    /// This method must return `true` to use methods marked "Only for multi-cursors" without
    /// panicking.
    pub fn is_multi(&self) -> bool {
        self.num_cursors() > 1
    }

    /// *[Only for single cursors]* Returns the inner, single cursor
    ///
    /// For an alternative that works on multi-cursors, see the [`leader`](Self::leader) method.
    ///
    /// ## Panics
    ///
    /// This method will panic if `is_single` is false.
    pub fn as_single(&self) -> &SingleCursor<Pos> {
        match &self.0 {
            Kind::Single(s) => s,
            // The panic message here isn't *perfect*. We don't actually expose a `::Multi` for
            // `Cursor`, so technically it isn't correct. But I can't immediately think of better
            // phrasing here.
            //
            // If you have a better idea, feel free to submit it. There's a similar panic message
            // below in `remove_leader`
            Kind::Multi { .. } => panic!("called `as_single` on `Cursor::Multi`"),
        }
    }

    /// Returns the "leader" of the set of cursors, or just the single cursor if there's only one
    ///
    /// For more information about "leaders", refer to the type-level documentation.
    pub fn leader(&self) -> &SingleCursor<Pos> {
        match &self.0 {
            Kind::Single(s) => s,
            Kind::Multi { cs, leader } => &cs[*leader],
        }
    }

    /// Adds the specified cursor, ensuring that there are multiple cursors represented here
    ///
    /// After this method, `as_multi` is guaranteed to return true.
    pub fn add_cursor(&mut self, cursor: SingleCursor<Pos>) {
        match &mut self.0 {
            Kind::Single(_) => {
                // We can't get the data out of `Single` yet, because it maybe doesn't implement
                // `Copy`. We'll temporarily replace it first.
                #[rustfmt::skip]
                let filler = Kind::Multi { cs: Vec::new(), leader: 0 };
                let s = match mem::replace(&mut self.0, filler) {
                    Kind::Single(s) => s,
                    _ => unreachable!(),
                };

                self.0 = Kind::Multi {
                    cs: vec![s, cursor],
                    leader: 1,
                }
            }
            // We always add directly after the leader:
            Kind::Multi { cs, leader } => {
                *leader += 1;
                cs.insert(*leader, cursor);
            }
        }
    }

    /// Increments the leader, setting the next cursor as the leader if there are multiple
    ///
    /// If there is only one cursor, this method will not change the state of that cursor. Multiple
    /// cursors exist in a cycle, so moving to the next leader will always succeed (and will
    /// eventually repeat leaders).
    pub fn incr_leader(&mut self) {
        match &mut self.0 {
            Kind::Single(_) => (),
            Kind::Multi { cs, leader } => *leader = (*leader + 1) % cs.len(),
        }
    }

    /// Decrements the leader, setting the previous cursor as the leader if there are multiple
    ///
    /// If there is only one cursor, this method will not change the state of that cursor. Multiple
    /// cursors exist in a cycle, so moving to the previous leader will always succeed (and will
    /// eventually repeat leaders).
    pub fn decr_leader(&mut self) {
        match &mut self.0 {
            Kind::Single(_) => (),
            Kind::Multi { cs, leader } => *leader = leader.checked_sub(1).unwrap_or(cs.len()),
        }
    }

    /// *[Only for multi-cursors]* Removes the current "leader" cursor
    ///
    /// Please note that, if there are only two cursors left, this method will revert the cursor
    /// back to a "single" internal cursor. Methods that rely strictly on more than one cursor
    /// (like this one) may after calling this.
    ///
    /// ## Panics
    ///
    /// This method will panic if `is_multi` is false.
    pub fn remove_leader(&mut self) {
        match &mut self.0 {
            Kind::Single(_) => panic!("called `remove_leader` on `Cursor::Single`"),
            Kind::Multi { cs, leader } => {
                cs.remove(*leader);
                // leader -= 1 (mod cs.len)
                *leader = leader.checked_sub(1).unwrap_or(cs.len() - 1);

                if cs.len() == 1 {
                    // Single(cs[0])
                    self.0 = Kind::Single(cs.remove(0));
                }
            }
        }
    }

    // TODO-FEATURE: How do we allow modifying cursors?
}

impl<Pos: Clone> SingleCursor<Pos> {
    /// Returns the singular point for the cursor within the text
    ///
    /// For `Selection` variants, this returns the `cursor_point` field.
    pub fn as_point(&self) -> Pos {
        match self {
            SingleCursor::Point(p) => p.clone(),
            SingleCursor::Selection { cursor_point, .. } => cursor_point.clone(),
        }
    }
}
