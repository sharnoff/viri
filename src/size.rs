//! Wrapper module around [`TermSize`] and [`TermPos`]

use std::num::NonZeroU16;
use std::ops::{Add, AddAssign};

/// The size of a region of the terminal
///
/// The standard method for constructing a `TermSize` is through the [`new`] method. Only where a
/// pair of values has already been given should the [`from_pair`] method be used.
///
/// The reason we don't provide an implementation of `From<(u16, u16)>` is that it's unclear at a
/// glance which of the two values gives the width and which gives the height - the implementation
/// would necessarily ascribe additional meaning to the tuple beyond its simple structure. This is
/// why the [`from_pair`] method is intentionally more hassle than [`new`].
///
/// [`new`]: Self::new
/// [`from_pair`]: Self::from_pair
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct TermSize {
    pub width: NonZeroU16,
    pub height: NonZeroU16,
}

impl TermSize {
    /// Creates a new `TermSize` from the width and the height, panicking if either value is zero
    ///
    /// Even though this function may be very similar to [`TermSize::from_pair`], it is preferable
    /// to use this, as the meaning of the arguments is explicit in their name.
    ///
    /// For a fallible version of this function, see [`TermSize::try_new`].
    pub fn new(width: u16, height: u16) -> TermSize {
        match TermSize::try_new(width, height) {
            Some(ts) => ts,
            None => panic!(
                "cannot construct `TermSize`, width-height pair {:?} has a zero value",
                (width, height)
            ),
        }
    }

    /// Attempt to construct a `TermSize`, returning `None` if either input is zero
    ///
    /// For an infallible version of this function, see [`TermSize::new`].
    ///
    /// ## Example
    ///
    /// ```
    /// assert_eq!(TermSize::try_new(0, 10), None);
    /// assert_eq!(TermSize::try_new(10, 0), None);
    /// assert_eq!(TermSize::try_new(10, 10), Some(TermSize::new(10, 10)));
    /// ```
    pub fn try_new(width: u16, height: u16) -> Option<TermSize> {
        Some(TermSize {
            width: NonZeroU16::new(width)?,
            height: NonZeroU16::new(height)?,
        })
    }

    /// Produces a new `TermSize` from a pair of values
    ///
    /// This is in accordance with the output from crossterm: the first value gives the width and
    /// the second gives the height.
    ///
    /// Wherever it is reasonable to create the pair of values separately, [`TermSize::new`] or
    /// [`TermSize::try_new`] should be used instead as the names of their arguments provides
    /// additional context.
    ///
    /// This function will panic if either of the provided values are equal to zero.
    pub fn from_pair((width, height): (u16, u16)) -> TermSize {
        TermSize::new(width, height)
    }

    /// Returns the width
    ///
    /// This method is provided so that users need not directly interface with the inner
    /// `NonZeroU16`.
    pub fn width(&self) -> u16 {
        self.width.get()
    }

    /// Returns the height
    ///
    /// This method is provided so that users need not directly interface with the inner
    /// `NonZeroU16`.
    pub fn height(&self) -> u16 {
        self.height.get()
    }
}

/// A single position in the terminal
///
/// Row and column values start at zero. Two `TermPos`s may be joined by the provided
/// implementation of [`Add`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct TermPos {
    pub row: u16,
    pub col: u16,
}

impl Add for TermPos {
    type Output = Self;

    fn add(mut self, other: TermPos) -> TermPos {
        self += other;
        self
    }
}

impl AddAssign for TermPos {
    fn add_assign(&mut self, other: TermPos) {
        self.row += other.row;
        self.col += other.col;
    }
}
