//! A wrapper module for the [`Painter`] type
//!
//! This is a private module, mostly made for code organization.

use crate::{TermPos, TermSize};
use ansi_term::Style;
use std::fmt::{self, Debug, Formatter};
use std::marker::PhantomData;
use std::num::NonZeroU16;

use super::*;

/// A handle on the paint buffer
pub struct Painter<'a> {
    base_ptr: *mut Buffer,
    offset: TermPos,
    size: TermSize,
    marker: PhantomData<&'a ()>,
}

/// A region of a [`Painter`] to extract; used only for the [`split`] method
///
/// This type exists only to be an argument to [`Painter::split`], and so all relevant
/// documentation can be found there.
///
/// [`split`]: Painter::split
#[derive(Debug, Copy, Clone)]
pub enum Extract {
    Top(u16),
    Bottom(u16),
    Left(u16),
    Right(u16),
}

impl<'a> Painter<'a> {
    /// Creates a new `Painter` with access to the entire of the buffer
    pub(super) fn from_buf(buf: &mut Buffer) -> Self {
        Painter {
            base_ptr: buf as *mut _,
            offset: TermPos { row: 0, col: 0 },
            size: buf.size,
            marker: PhantomData,
        }
    }

    /// Returns the size of the painter
    pub fn size(&self) -> TermSize {
        self.size
    }

    /// A shorthand for `self.size().width()`
    pub fn width(&self) -> u16 {
        self.size.width()
    }

    /// A shorthand for `self.size().height()`
    pub fn height(&self) -> u16 {
        self.size.height()
    }

    /// Attempts to split the painter into two distinct regions
    ///
    /// If there is room in the current size of the painter, the extraction mode will remove the
    /// specified amount of space along the given dimension. The returned `Painter` will give
    /// exactly that region, and the source `Painter` will be modified to exclude the extracted
    /// region.
    ///
    /// If there is not enough space in the size of the painter to extract the requested amount,
    /// this method will return `Err` and no changes will be
    ///
    /// ## Examples
    ///
    /// This is perhaps a bit complex, and so a visual example should help demystify it.
    ///
    /// Suppose we have a painter with size `width = 19, height = 7`:
    /// ```ignore
    /// let mut painter: Painter = /* given to us :) */;
    /// ```
    /// Which we can represent as a blank canvas (note: including the borders):
    /// ```text
    /// +------------------+
    /// |                  |
    /// |                  |
    /// |                  |
    /// |                  |
    /// |                  |
    /// +------------------+
    /// ```
    /// Then, if we extract a piece of this painter into `lhs`:
    /// ```no_run
    /// # let mut painter: Painter = unimplemented!();
    /// let lhs = painter.split(Extract::Left(7));
    /// ```
    /// We then have the following regions within the original:
    /// ```text
    /// +-----++-----------+
    /// |     ||           |
    /// |     ||           |
    /// | lhs ||  painter  |
    /// |     ||           |
    /// |     ||           |
    /// +-----++-----------+
    /// ```
    /// Note that `painter` is modified so that it no longer includes the left-hand side region
    /// that was extracted into `lhs`.
    ///
    /// The same behavior is present, regardless of direction; the name of the extracted area
    /// always gives the side of the original region on which the new `Painter` is produced.
    ///
    /// ## Panics
    ///
    /// This function will panic if the inner value to extract has size zero.
    //
    // SAFETY:
    // While this function doesn't make use of any unsafe, it's a key part of the interface to
    // `Painter`, and - if incorrect - would introduce safety concerns.
    // The safety of this function on the inability to produce overlapping `Painter`s. Tests at the
    // bottom of this file help to ensure that this never happens, in addition to debug assertions
    // that are present before returning here.
    pub fn split(&mut self, mode: Extract) -> Result<Self, ()> {
        // We only implement `split` for two directions, because their opposites can be done simply
        // by swapping.

        match mode {
            Extract::Right(amount) => {
                let mut new = self.split(Extract::Left(amount))?;
                std::mem::swap(&mut new, self);
                Ok(new)
            }
            Extract::Left(amount) => {
                let amount = match NonZeroU16::new(amount) {
                    Some(a) => a,
                    None => panic!("`Painter::split` given zero quantity"),
                };

                // get the amount of space remaining (as a NonZeroU16) after subtracting the
                // requested amount from the width
                let remaining = (self.size.width())
                    .checked_sub(amount.get())
                    .and_then(NonZeroU16::new)
                    .map(Ok)
                    .unwrap_or(Err(()))?;

                // The size of the new painter will have our height, but width equal to the
                // requested amount:
                let new_size = TermSize {
                    width: amount,
                    height: self.size.height,
                };

                // We need to update our own:
                self.size.width = remaining;

                // The new position will be the same as ours, but we need to offset our own:
                let new_pos = self.offset;
                self.offset.col += amount.get();

                let new_painter = Painter {
                    base_ptr: self.base_ptr,
                    offset: new_pos,
                    size: new_size,
                    // Directly copy the marker so there's no funny business with lifetimes
                    marker: self.marker,
                };

                debug_assert!(
                    !self.overlaps(&new_painter),
                    "overlap after removing {} from left. new self: {:?}, returned: {:?}",
                    amount,
                    (self.size, self.offset),
                    (new_painter.size, new_painter.offset),
                );

                Ok(new_painter)
            }

            Extract::Bottom(amount) => {
                let mut new = self.split(Extract::Top(amount))?;
                std::mem::swap(&mut new, self);
                Ok(new)
            }
            Extract::Top(amount) => {
                // The logic here is largely identical to what's present above, for extracting a
                // region on the left. Refer there for commentary.

                let amount = match NonZeroU16::new(amount) {
                    Some(a) => a,
                    None => panic!("`Painter::split` given zero quantity"),
                };

                let remaining = (self.size.height())
                    .checked_sub(amount.get())
                    .and_then(NonZeroU16::new)
                    .map(Ok)
                    .unwrap_or(Err(()))?;

                let new_size = TermSize {
                    height: amount,
                    width: self.size.width,
                };

                self.size.height = remaining;

                let new_pos = self.offset;
                self.offset.row += amount.get();

                let new_painter = Painter {
                    base_ptr: self.base_ptr,
                    offset: new_pos,
                    size: new_size,
                    marker: self.marker,
                };

                debug_assert!(!self.overlaps(&new_painter));

                Ok(new_painter)
            }
        }
    }

    /// Paints the styled content at a given region
    ///
    /// The position should be within the `Painter`'s allocated region, and will panic if this is
    /// not the case.
    pub fn paint_at(&mut self, mut pos: TermPos, content: StyledContent<impl IntoSymbols>) {
        for StyledString { style, content } in content.segments {
            if !self.size.contains(pos) {
                return;
            }

            for sym in content.into_symbols() {
                self.paint_symbol(pos, sym, style);
            }

            pos.col += 1;
        }
    }

    /// Clears the entire contents of the painter
    ///
    /// This is one of the few "core" methods. Unless you're doing something advanced, it's
    /// probably a good idea to use `clear_all` before redrawing, and so this seemingly-simple
    /// method is used in many different places.
    pub fn clear_all(&mut self) {
        let top_left = TermPos { row: 0, col: 0 };
        let bottom_right = TermPos {
            row: self.size.height(),
            col: self.size.width(),
        };

        // SAFETY: We know that the corners are within the required bounds because we have just
        // constructed them to be exactly equal to the bounds
        unsafe { self.clear_rect_internal(top_left, bottom_right) }
    }

    /// Clears all of the cells in the given rectangular region
    ///
    /// Please note: The top-left position is inclusive, and the bottom-right is **exclusive**.
    /// This is a subtle detail that should help with cleaner code, but must be remembered.
    ///
    /// This function will panic if the `top_left` is not above and to the left of `bottom_right`
    /// (i.e. if it isn't the case that both of its coordinates are less than `bottom_right`). It
    /// will also panic if any of the corners of the rectangle aren't within the region of the
    /// painter.
    pub fn clear_rect(&mut self, top_left: TermPos, bottom_right: TermPos) {
        if bottom_right.col > self.size.width() || bottom_right.row > self.size.height() {
            panic!(
                "bottom-right corner {:?} is outside the bounds of size {:?}",
                bottom_right, self.size
            );
        }

        let row_diff = match bottom_right.row.checked_sub(top_left.row) {
            Some(d) => d,
            None => panic!(
                "top-left corner {:?} is not above bottom-right corner {:?}",
                top_left, bottom_right
            ),
        };

        let col_diff = match bottom_right.col.checked_sub(top_left.col) {
            Some(d) => d,
            None => panic!(
                "top-left corner {:?} is not left of bottom-right corner {:?}",
                top_left, bottom_right
            ),
        };

        if row_diff == 0 || col_diff == 0 {
            return;
        }

        // And then, once we've validated everything... go and actually do it!
        unsafe { self.clear_rect_internal(top_left, bottom_right) }
    }

    /// An internal-only function for clearing a rectangle, without the checks from [`clear_rect`]
    ///
    /// This method has all of the same requirements as [`clear_rect`], but it does not check them.
    /// The unsafety is purely from needing these requirements to be satisfied.
    ///
    /// [`clear_rect`]: Self::clear_rect
    unsafe fn clear_rect_internal(&mut self, top_left: TermPos, bottom_right: TermPos) {
        for row in top_left.row..bottom_right.row {
            for col in top_left.col..bottom_right.col {
                let pos = TermPos { row, col };

                // SAFETY: Assume we're in `clear_rect`.
                //
                // We've already verified that the the upper bound for this position
                // (bottom_right) is within the bounds of the size. That's the only additional
                // requirement to ensure that we don't do any wacky indexing.
                let cell = unsafe { Buffer::index(self.base_ptr, self.offset + pos, self.marker) };
                cell.update(None, Style::default());
            }
        }
    }

    /// Paints a single [`Symbol`] to a location within the painter's local region
    ///
    /// This may be desired in cases where the region being painted is not horzontal (e.g. when
    /// painting a vertical dividing line between views).
    ///
    /// If the position is not contained within the `Painter`, this function will panic.
    pub fn paint_symbol(&mut self, pos: TermPos, symbol: Symbol, style: Style) {
        if !self.size.contains(pos) {
            panic!(
                "{:?} is not contained within `Painter` of size {:?}",
                pos, self.size
            );
        }

        // SAFETY: This function requires that the position not be aliased.
        let cell = unsafe { Buffer::index(self.base_ptr, self.offset + pos, self.marker) };
        cell.update(Some(symbol), style);
    }

    /// Checks whether the regions given to the two painters overlap
    ///
    /// This is used both in debug assertions for [`split`](Self::split) and within unit tests. It
    /// is expected that no two painters referencing the same underlying buffer should return true.
    fn overlaps(&self, other: &Painter) -> bool {
        // There's an overlap precisely when any one of the corners of a given painter is inside
        // another. There isn't a need for this to be overly efficient; this function isn't used
        // outside of testing and debug assertions.

        fn corners(this: &Painter) -> [TermPos; 4] {
            [
                this.offset,
                this.offset.add_row(this.size.height() - 1),
                this.offset.add_col(this.size.width() - 1),
                this.offset
                    .add_row(this.size.height() - 1)
                    .add_col(this.size.width() - 1),
            ]
        }

        corners(self)
            .iter()
            .any(|&pos| other.size.contains_with_offset(other.offset, pos))
            || corners(other)
                .iter()
                .any(|&pos| self.size.contains_with_offset(self.offset, pos))
    }
}

impl Debug for Painter<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("Painter")
            .field("base_ptr", &format!("{:#x}", self.base_ptr as usize))
            .field("offset", &self.offset)
            .field("size", &self.size)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // A helper function to produce a fake global painter
    //
    // Please note that the created painter has a null pointer as its reference, and so any
    // function that relies on the underlying buffer will segfault.
    fn fake_painter(size: TermSize, offset: TermPos) -> Painter<'static> {
        Painter {
            base_ptr: std::ptr::null_mut(),
            offset,
            size,
            marker: PhantomData,
        }
    }

    // Ensure that the `overlaps` method is correct
    #[test]
    #[rustfmt::skip]
    fn check_overlaps() {
        // All (u16, u16) pairs are (width, height)
        static CASES: &[(((u16, u16), (u16, u16)), ((u16, u16), (u16, u16)), bool)] = &[
            // All of p2 inside p1:
            (((10, 10), (5, 5)), ((4, 4), (8, 8)), true),
            // All of p2 outside p1:
            (((5, 5), (3, 2)), ((4, 4), (8, 8)), false),
            // p2 equal to p1:
            (((4, 8), (3, 7)), ((4, 8), (3, 7)), true),

            // The next set have p2 bordering (but not overlapping) on each of:
            // BOTTOM:
            (((5, 5), (3, 2)), ((4, 4), (4, 7)), false),
            // RIGHT:
            (((5, 5), (2, 3)), ((4, 4), (7, 4)), false),
            
            // And then bordering (with an overlap of 1) on each of:
            // BOTTOM:
            (((5, 5), (3, 2)), ((4, 4), (4, 6)), true),
            // RIGHt:
            (((5, 5), (2, 3)), ((4, 4), (6, 4)), true),

            // And then each individual corner of p2 inside of p1:
            // Bottom left:
            (((5, 5), (3, 2)), ((4, 4), (6, 6)), true),
            // Bottom right:
            (((5, 5), (3, 3)), ((4, 4), (6, 1)), true),
            // Upper left/upper right are checked by the inverse (i.e. p2 `overlaps` p1)
        ];

        for ((s1, o1), (s2, o2), overlaps) in CASES.into_iter().cloned() {
            let s1 = TermSize::from_pair(s1);
            let s2 = TermSize::from_pair(s2);

            let o1 = TermPos {
                col: o1.0,
                row: o1.1,
            };

            let o2 = TermPos {
                col: o2.0,
                row: o2.1,
            };

            let p1 = fake_painter(s1, o1);
            let p2 = fake_painter(s2, o2);

            assert_eq!(p1.overlaps(&p2), overlaps);
            assert_eq!(p2.overlaps(&p1), overlaps);
        }
    }

    // Ensure that overlapping painters cannot be created from splitting
    #[test]
    fn no_overlap() {
        let mut base = Buffer::new(TermSize::new(100, 100));
        let mut painter = base.painter();

        let mut big_left = painter.split(Extract::Left(65)).unwrap();
        let big_right = painter;

        assert!(!big_left.overlaps(&big_right));

        let mut upper_left = big_left.split(Extract::Top(45)).unwrap();
        let lower_left = big_left;

        assert!(!upper_left.overlaps(&lower_left));
        assert!(!upper_left.overlaps(&big_right));
        assert!(!lower_left.overlaps(&big_right));

        let mut upper_inner_left = upper_left.split(Extract::Right(20)).unwrap();
        let upper_outer_left = upper_left;

        assert!(!upper_inner_left.overlaps(&upper_outer_left));
        assert!(!upper_inner_left.overlaps(&lower_left));
        assert!(!upper_inner_left.overlaps(&big_right));
        assert!(!upper_outer_left.overlaps(&lower_left));
        assert!(!upper_outer_left.overlaps(&big_right));

        let inner_upper_inner_left = upper_inner_left.split(Extract::Bottom(10)).unwrap();
        let outer_upper_inner_left = upper_inner_left;

        assert!(!inner_upper_inner_left.overlaps(&outer_upper_inner_left));
        assert!(!inner_upper_inner_left.overlaps(&upper_outer_left));
        assert!(!inner_upper_inner_left.overlaps(&lower_left));
        assert!(!inner_upper_inner_left.overlaps(&big_right));
        assert!(!outer_upper_inner_left.overlaps(&upper_outer_left));
        assert!(!outer_upper_inner_left.overlaps(&lower_left));
        assert!(!outer_upper_inner_left.overlaps(&big_right));
    }

    #[test]
    #[should_panic]
    fn zero_left() {
        let mut painter = fake_painter(TermSize::new(10, 10), TermPos { col: 0, row: 0 });
        let _ = painter.split(Extract::Left(0));
    }

    #[test]
    #[should_panic]
    fn zero_right() {
        let mut painter = fake_painter(TermSize::new(10, 10), TermPos { col: 0, row: 0 });
        let _ = painter.split(Extract::Right(0));
    }

    #[test]
    #[should_panic]
    fn zero_top() {
        let mut painter = fake_painter(TermSize::new(10, 10), TermPos { col: 0, row: 0 });
        let _ = painter.split(Extract::Top(0));
    }

    #[test]
    #[should_panic]
    fn zero_bottom() {
        let mut painter = fake_painter(TermSize::new(10, 10), TermPos { col: 0, row: 0 });
        let _ = painter.split(Extract::Left(0));
    }
}
