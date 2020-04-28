//! Defines `ViewBuffer`, a base `View` that can be extended by others
//!
//! Additionally provided are the modules `normal_mode` and `insert_mode`, which define generic
//! handlers for typical normal and insert modes.

use std::convert::TryInto;
use std::mem;
use std::num::NonZeroUsize;
use std::ops::{Range, RangeInclusive};
use std::sync::Mutex;

use crate::config::prelude::*;
use crate::mode::{CharPredicate, CursorStyle, DeleteKind, Direction, Movement, ScrollKind};
use crate::prelude::*;
use crate::runtime::{Painter, TermCoord, TermSize};
use crate::text::{ContentProvider, Diff, Line};

use super::{OutputSignal, RefreshKind, View};

/// A basic `View` with utilities for extending it
///
/// The term "view buffer" comes from the standard meaning in vi-style editors, where a buffer is a
/// single window into a file (or something else).
#[derive(Debug)]
pub struct ViewBuffer<P: ContentProvider> {
    /// The type providing the content of the buffer
    ///
    /// This is made available through various methds on the type
    provider: P,

    /// The size of the view
    size: TermSize,

    /// The position of the top-left corner of the view within the screen. We cache this, even
    /// though we don't need to in order to avoid redrawing all the time
    pos: Option<TermCoord>,

    /// The position of the cursor *within* the view
    cursor: TermCoord,

    /// The line displayed as the top row, starting from 0
    top_row: usize,

    /// The column displayed as the left-most column, starting from 0
    left_col: usize,

    /// Whether the cursor is allowed to be one index past the end of the line
    ///
    /// This is typically `true` for insert mode and `false` for normal mode. This does not affect
    /// lines with width equal to zero.
    allow_cursor_after: bool,

    /// The column that the cursor *would like* to be at
    ///
    /// This is used to allow cursor movements to operate in a similar way to Vim. This value will
    /// be equal to `usize::MAX` if the cursor has been moved to the end of the line.
    virtual_col: usize,

    /// Whether the view needs refreshing - and if so, what kind
    needs_refresh: Option<RefreshKind>,
}

impl<P: ContentProvider> View for ViewBuffer<P> {
    fn refresh(&mut self, painter: &Painter) {
        log::trace!("Refreshing!");

        // If we don't need to redraw, just return
        if self.needs_refresh.is_none() && self.pos == Some(painter.abs_pos()) {
            return;
        }

        let width = self.size.width as usize;

        let display_range = std::ops::Range {
            start: self.left_col,
            end: self.left_col + width,
        };

        let content = self.provider.content();
        let lines: Vec<_> = content.iter(self.top_row..).collect();

        let iter = lines.iter().map(move |l| {
            let (line, Range { mut start, mut end }) = l.display_segment(display_range.clone());

            // Shift the start/end points to where they actually are on the display:
            start -= display_range.start;
            end -= display_range.start;

            ((start as u16..end as u16), line)
        });

        painter.print_lines(iter);

        self.pos = Some(painter.abs_pos());
        self.needs_refresh = None;
    }

    fn refresh_cursor(&self, painter: &Painter) {
        painter.set_cursor(self.cursor);
    }

    fn resize(&mut self, size: TermSize) -> Vec<OutputSignal> {
        if size == self.size {
            Vec::new()
        } else {
            self.size = size;
            self.cursor.col = self.cursor.col.min(size.width - 1);
            self.cursor.row = self.cursor.row.min(size.height - 1);

            self.needs_refresh = Some(RefreshKind::Full);
            vec![OutputSignal::NeedsRefresh(RefreshKind::Full)]
        }
    }
}

impl<P: ContentProvider> ViewBuffer<P> {
    /// Creates a new `ViewBuffer` with the given content source
    pub fn new(size: TermSize, provider: P) -> Self {
        Self {
            provider,
            size,
            pos: None,
            cursor: (0, 0).into(),
            top_row: 0,
            left_col: 0,
            allow_cursor_after: false,
            virtual_col: 0,
            needs_refresh: None,
        }
    }

    /// Gives immutable access to the content provider for this buffer
    pub fn provider(&self) -> &P {
        &self.provider
    }

    /// Gives mutable access to the content provider for this buffer
    pub fn provider_mut(&mut self) -> &mut P {
        &mut self.provider
    }

    /// Sets the current cursor style
    pub fn set_cursor_style(&mut self, style: CursorStyle) {
        self.set_allow_after(style.allow_after);
    }

    /// Returns the on-screen position of the cursor *within the buffer*
    pub fn cursor_pos(&self) -> TermCoord {
        self.cursor
    }

    /// Returns the on-screen size of the buffer
    pub fn size(&self) -> TermSize {
        self.size
    }

    /// Returns the *logical* column of the cursor in the content
    ///
    /// This is distinct from the on-screen position of the cursor, which can be obtained by the
    /// [`cursor_pos`] method.
    ///
    /// [`cursor_pos`]: #method.cursor_pos
    pub fn current_col(&self) -> usize {
        self.left_col + self.cursor.col as usize
    }

    /// Returns the *logical* row of the cursor in the content
    ///
    /// This is distinct from the on-screen position of the cursor, which can be obtained by the
    /// [`cursor_pos`] method.
    ///
    /// [`cursor_pos`]: #method.cursor_pos
    pub fn current_row(&self) -> usize {
        self.top_row + self.cursor.row as usize
    }

    /// Returns the total number of lines in the buffer
    pub fn num_lines(&self) -> usize {
        let content = self.provider.content();
        content.num_lines()
    }

    /// Returns whether the buffer currently allows cursors to move one index beyond the end of the
    /// line.
    ///
    /// For more information, see the `allow_cursor_after` field.
    pub fn allows_after(&self) -> bool {
        self.allow_cursor_after
    }

    /// Shifts all relevant context by the diffs, in order. Currently this will simply move the
    /// cursor according to the diffs. A return of `None` indicates that there is no refreshing
    /// necessary.
    ///
    /// This function *must* be called after applying a set of diffs to the content, and not
    /// before. If this is not upheld, this (or other functions) will panic.
    ///
    /// Planned improvements: This function shouldn't move the view if the
    pub fn refresh_diffs(&mut self, diffs: &[Diff]) -> Option<RefreshKind> {
        if diffs.is_empty() {
            return None;
        }

        // Keeping `content` in scope for the majority of the function ensures that it'll be
        // locked.
        let content = self.provider.content();

        // Shift the cursor index by the amount given by all of the diffs
        let mut cursor_byte_idx = content.byte_index(self.current_row(), self.current_col());
        for d in diffs {
            cursor_byte_idx = d.shift_idx(cursor_byte_idx);
        }

        // Generate new cursor index. We unwrap here because the diffs should already be applied to
        // the content. If they aren't this is a hard error.
        let (new_row, new_char) = content.line_pair_from_byte(cursor_byte_idx);

        let line = content.line(new_row);
        let mut new_col = line.width_idx_from_char(new_char);

        if new_col != 0 && new_col == line.width() && !self.allow_cursor_after {
            new_col -= 1;
        }

        drop(line);
        drop(content);

        self.virtual_col = new_col;
        self.move_cursor_row_unchecked(new_row);
        self.try_move_virtual_cursor();

        // Currently, we aren't tracking where the actually occur, so we'll just do a full refresh.
        // In the future, we could do smart things like choosing to not change the display if the
        // diff doesn't affect what's on-screen
        self.needs_refresh = self.needs_refresh.max(Some(RefreshKind::Full));
        Some(RefreshKind::Full)
    }

    /// Moves the cursor by the given movement, repeating `amount` times
    pub fn move_cursor(&mut self, movement: Movement, amount: usize) -> Option<RefreshKind> {
        let (new_row, new_virt_col) = self.simulate_movement(movement, amount, true)?;
        self.virtual_col = new_virt_col;

        let refresh = self
            .move_cursor_row_unchecked(new_row)
            .max(self.try_move_virtual_cursor());
        self.needs_refresh = self.needs_refresh.max(refresh);
        refresh
    }

    /// Scrolls the buffer by `amount` lines/columns in the direction given
    pub fn scroll(&mut self, kind: ScrollKind, amount: usize) -> Option<RefreshKind> {
        if amount == 0 {
            return None;
        }

        self.provider_mut().lock();

        // `new_row` and `new_col` give the top-left corner of the displayed region
        let (mut new_row, mut new_col) = self.simulate_scroll(kind, amount);
        let (old_row, old_col) = (self.top_row, self.left_col);

        new_row = new_row.min(self.num_lines() - 1);

        let mut changed = false;

        if new_row != old_row {
            changed = true;

            // Drag the cursor to the new row
            self.top_row = new_row;
            if new_row < old_row {
                let max_row = self.size.height - 1;

                self.cursor.row = (self
                    .cursor
                    .row
                    .saturating_add((old_row - new_row).try_into().unwrap_or(std::u16::MAX)))
                .min(max_row);
            } else {
                // old_row < new_row
                self.cursor.row = self
                    .cursor
                    .row
                    .saturating_sub((new_row - old_row).try_into().unwrap_or(std::u16::MAX));
            }
        }

        let max_line_col = match self.allows_after() {
            true => self.current_line().width(),
            false => self.current_line().width().saturating_sub(1),
        };
        new_col = new_col.min(max_line_col);

        if new_col != old_col {
            changed = true;

            // drag the cursor to the new column
            self.left_col = new_col;
            if new_col < old_col {
                let max_col = (max_line_col - new_col).try_into().unwrap_or(std::u16::MAX);

                self.cursor.col = (self
                    .cursor
                    .col
                    .saturating_add((old_col - new_col).try_into().unwrap_or(std::u16::MAX)))
                .min(max_col);
            } else {
                // old_row < new_row
                self.cursor.col = self
                    .cursor
                    .col
                    .saturating_sub((new_col - old_col).try_into().unwrap_or(std::u16::MAX));
            }
        }

        self.provider_mut().unlock();

        if !changed {
            return None;
        }

        // calculate the new cursor position - scrolling will drag it along

        self.top_row = new_row;
        self.left_col = new_col;

        self.needs_refresh = self.needs_refresh.max(Some(RefreshKind::Full));
        Some(RefreshKind::Full)
    }

    /// Inserts the given string at the current position of the cursor
    pub fn insert(&mut self, s: &str) -> Option<RefreshKind> {
        self.provider.lock();

        let row = self.current_row();
        let col = self.current_col();
        let diff = {
            // ^ What the heck, NLL?
            // This should work but doesn't...
            let content = self.provider.content_mut();
            let byte_idx = content.byte_index(row, col);
            content.insert_at_byte(byte_idx, s)
        };
        self.provider.apply_diff(diff).unwrap();

        // And now we double-check that our cursor is still allowed to be there
        // It could be the case that the string contained a newline
        //
        // TODO: It might be more correct to go to the next line - imagine pasting a newline...
        // This should be done via the shifted byte index from the diff.
        let mut width = self.provider.line(row).width();

        if !self.allow_cursor_after {
            width = width.saturating_sub(1);
        }

        if col > width {
            self.virtual_col = width;
            self.try_move_virtual_cursor();
            self.virtual_col = self.current_col();
        }

        self.provider.unlock();

        self.needs_refresh = Some(RefreshKind::Full);
        Some(RefreshKind::Full)
    }

    pub fn delete(&mut self, kind: DeleteKind) -> Option<RefreshKind> {
        let refresh = match kind {
            DeleteKind::ByMovement {
                movement,
                amount,
                from_inclusive,
                to_inclusive,
            } => self.delete_movement(movement, amount, from_inclusive, to_inclusive),
            DeleteKind::ByLines { movement, amount } => {
                let row = self.current_row();
                let (new_row, _) = self.simulate_movement(movement, amount, true)?;
                let range = match row < new_row {
                    true => row..=new_row,
                    false => new_row..=row,
                };

                self.delete_lines(range)
            }
            DeleteKind::CurrentLine { amount } if amount != 0 => {
                let row = self.current_row();
                let max_row = (row + amount - 1).min(self.num_lines() - 1);
                self.delete_lines(row..=max_row)
            }
            _ => None,
        };

        self.needs_refresh = self.needs_refresh.max(refresh);
        refresh
    }

    // Doesn't set `self.needs_refresh` -- this is left to `delete`
    fn delete_movement(
        &mut self,
        movement: Movement,
        amount: usize,
        from_inclusive: bool,
        to_inclusive: bool,
    ) -> Option<RefreshKind> {
        self.provider.lock();

        let cur_row = self.current_row();
        let cur_char = self
            .current_line()
            .char_idx_from_width(self.current_col())
            .0;

        // temporarily enable `allow_cursor_after` so that we can do proper deletion
        let old_allow_after = mem::replace(&mut self.allow_cursor_after, true);

        let (new_row, new_char) = self.simulate_movement(movement, amount, true)?;

        // re-enable whetever `allow_cursor_after` we had before
        self.allow_cursor_after = old_allow_after;

        if (new_row, new_char) == (cur_row, cur_char) {
            return None;
        }

        let (fwd, mut lo_row, mut lo_char, mut hi_row, mut hi_char) =
            match (cur_row, cur_char) < (new_row, new_char) {
                true => (true, cur_row, cur_char, new_row, new_char),
                false => (false, new_row, new_char, cur_row, cur_char),
            };

        // Handle `{to,from}_inclusive`
        if fwd && !from_inclusive || !fwd && !to_inclusive {
            // attmept to add to lo_char
            if self.provider.line(lo_row).num_chars() == lo_char {
                if self.num_lines() == lo_row + 1 {
                    return None;
                }

                lo_char = 0;
                lo_row += 1;
            } else {
                lo_char += 1;
            }
        }

        if fwd && to_inclusive || !fwd && from_inclusive {
            // attempt to add to hi_char
            if self.provider.line(hi_row).num_chars() == hi_char {
                if hi_row == self.num_lines() {
                    // do nothing
                } else {
                    hi_char = 0;
                    hi_row += 1;
                }
            } else {
                hi_char += 1;
            }
        }

        // Convert the two pairs into byte indices
        let content = self.provider.content();

        let lo_col = content.line(lo_row).width_idx_from_char(lo_char);
        let hi_col = content.line(hi_row).width_idx_from_char(hi_char);
        let lo_byte_idx = content.byte_index(lo_row, lo_col);
        let hi_byte_idx = content.byte_index(hi_row, hi_col);

        // Record the current position of the cursor
        let cur_byte_idx = content.byte_index(cur_row, self.current_col());

        let diff = content.delete_byte_range(lo_byte_idx..hi_byte_idx);
        drop(content);

        // apply the diff to the content and the old cursor index
        let new_cursor_idx = diff.shift_idx(cur_byte_idx);
        self.provider.apply_diff(diff).unwrap();

        let content = self.provider.content();

        // get the new position of the cursor
        let (cur_row, cur_char) = content.line_pair_from_byte(new_cursor_idx);

        let cur_col = content.line(cur_row).width_idx_from_char(cur_char);

        drop(content);
        self.provider.unlock();

        // and move the cursor into place
        self.virtual_col = cur_col;

        self.move_cursor_row_unchecked(new_row);
        self.try_move_virtual_cursor();
        Some(RefreshKind::Full)
    }

    // Doesn't set `self.needs_refresh` -- this is left to `delete`
    fn delete_lines(&mut self, line_range: RangeInclusive<usize>) -> Option<RefreshKind> {
        if line_range.start() > line_range.end() {
            // if line_range.is_empty() { // <- Unstable feature `range_is_empty`
            return None;
        }

        self.provider.lock();
        let content = self.provider.content();

        let start_byte = content.byte_index(*line_range.start(), 0);
        let end_byte = if *line_range.end() != content.num_lines() {
            content.byte_index(line_range.end() + 1, 0)
        } else {
            content.total_bytes()
        };

        let old_row = self.current_row();

        let diff = content.delete_byte_range(start_byte..end_byte);
        drop(content);

        self.provider.apply_diff(diff).unwrap();

        let content = self.provider.content();

        let new_row = {
            if old_row <= *line_range.start() {
                old_row.min(content.num_lines())
            } else {
                // We add one here because the range is inclusive
                old_row.saturating_sub(line_range.end() - line_range.start() + 1)
            }
        };

        drop(content);
        self.provider.unlock();

        self.move_cursor_row_unchecked(new_row);
        self.try_move_virtual_cursor();
        Some(RefreshKind::Full)
    }

    // Doesn't set `self.needs_refresh` -- this is left to `delete`
    fn set_allow_after(&mut self, allow: bool) -> Option<RefreshKind> {
        self.allow_cursor_after = allow;

        if !allow && self.current_col() != 0 && self.current_col() == self.current_line().width() {
            let refresh = self.try_move_virtual_cursor();
            self.needs_refresh = self.needs_refresh.max(refresh);
            refresh
        } else {
            None
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Internal ViewBuffer helper methods                                                             //
////////////////////////////////////////////////////////////////////////////////////////////////////

// MOVEMENT SIMULATION
//
// The following `impl` block provides *only* movement simulation functions
//
// Each function is named `sim_move_*`, where the '*' is replaced by some description of the
// movement.
//
// There is a common notion of "weak failure", which is described in detail in the comment above
// `simulate_movement` - the only function called from outside this impl block.
impl<P: ContentProvider> ViewBuffer<P> {
    /// Simulates the movement, returning what the cursor's updated position would be, if the
    /// movement was able to be executed
    ///
    /// The returned tuple (if present) give, in order, the new row and new virtual column for the
    /// cursor. This *does* take `allow_cursor_after` into account.
    ///
    /// `weak_fail` has a specific function: if the movement is able to be executed for some
    /// non-zero amount less than what was given, `weak_fail` indicates whether that partial
    /// movement should be returned in favor of a complete fail with `None`.
    ///
    /// This is used in muliple places, but primarily serves as a way to reduce the amount of
    /// repetition in various types of cursor movements and deletion patterns.
    #[rustfmt::skip]
    pub fn simulate_movement(
        &self,
        movement: Movement,
        amount: usize,
        weak_fail: bool,
    ) -> Option<(usize, usize)> {
        log::trace!("simulating movement: {:?}, weak_fail: {:?}", movement, weak_fail);

        use crate::mode::{
            HorizMove::{Const, LineBoundary, UntilFst, UntilSnd},
            Movement::{Down, Left, Right, Up, LeftCross, RightCross},
        };

        let amount = match NonZeroUsize::new(amount) {
            Some(a) => a,
            None => return Some((self.current_row(), self.current_col())),
        };

        let res = match movement {
            Up => self.sim_move_up(amount, weak_fail),
            Down => self.sim_move_down(amount, weak_fail),

            Left(LineBoundary) | LeftCross(LineBoundary) => self.sim_move_bol(),
            Right(LineBoundary) | RightCross(LineBoundary) => self.sim_move_eol(),

            Left(Const) => self.sim_move_left(amount, weak_fail),
            LeftCross(Const) => self.sim_move_left_cross(amount, weak_fail),

            Left(UntilFst(pred)) => self.sim_move_left_pred(pred, amount, true),
            Left(UntilSnd(pred)) => self.sim_move_left_pred(pred, amount, false),
            LeftCross(UntilFst(pred)) => self.sim_move_left_pred_cross(pred, amount, true),
            LeftCross(UntilSnd(pred)) => self.sim_move_left_pred_cross(pred, amount, false),

            Right(Const) => self.sim_move_right(amount, weak_fail),
            Right(UntilFst(pred)) => self.sim_move_right_pred(pred, amount, true),
            Right(UntilSnd(pred)) => self.sim_move_right_pred(pred, amount, false),

            RightCross(Const) => self.sim_move_right_cross(amount, weak_fail),
            RightCross(UntilFst(pred)) => self.sim_move_right_pred_cross(pred, amount, true),
            RightCross(UntilSnd(pred)) => self.sim_move_right_pred_cross(pred, amount, false),

            _ => todo!(),
        };

        log::trace!("New position: {:?}", res);
        res
    }

    fn sim_move_up(&self, amount: NonZeroUsize, weak_fail: bool) -> Option<(usize, usize)> {
        let row = self.current_row();
        let new_line = match row.checked_sub(amount.get()) {
            Some(line_idx) => line_idx,
            None if weak_fail && row != 0 => 0,
            None => return None,
        };

        Some((new_line, self.virtual_col))
    }

    fn sim_move_down(&self, amount: NonZeroUsize, weak_fail: bool) -> Option<(usize, usize)> {
        let lines_until_last = self.provider.num_lines() - self.current_row() - 1;

        let new_lines_until_last = match lines_until_last.checked_sub(amount.get()) {
            Some(line) => line,
            None if weak_fail && lines_until_last != 0 => 0,
            None => return None,
        };

        let new_line = self.provider.num_lines() - new_lines_until_last - 1;

        Some((new_line, self.virtual_col))
    }

    // Simulates a movement to the beginning of the line
    fn sim_move_bol(&self) -> Option<(usize, usize)> {
        Some((self.current_row(), 0))
    }

    // Simulates a movement to the end of the line
    fn sim_move_eol(&self) -> Option<(usize, usize)> {
        Some((self.current_row(), std::usize::MAX))
    }

    fn sim_move_left(&self, amount: NonZeroUsize, weak_fail: bool) -> Option<(usize, usize)> {
        let line = self.current_line();

        let current_char = line.char_idx_from_width(self.current_col()).0;
        let new_char = match current_char.checked_sub(amount.get()) {
            Some(c) => c,
            None if weak_fail && self.current_col() != 0 => 0,
            None => return None,
        };

        Some((self.current_row(), line.width_idx_from_char(new_char)))
    }

    fn sim_move_right(&self, amount: NonZeroUsize, weak_fail: bool) -> Option<(usize, usize)> {
        let allows_after = self.allows_after();
        let line = self.current_line();

        let max_char = match allows_after {
            false => line.num_chars().saturating_sub(1),
            true => line.num_chars(),
        };

        let current_char = line.char_idx_from_width(self.current_col()).0;
        let diff_from_max = max_char - current_char;
        let new_diff = match diff_from_max.checked_sub(amount.get()) {
            Some(d) => d,
            None if weak_fail && diff_from_max != 0 => 0,
            None => return None,
        };

        let new_char = max_char - new_diff;

        Some((self.current_row(), line.width_idx_from_char(new_char)))
    }

    fn sim_move_left_cross(&self, amount: NonZeroUsize, weak_fail: bool) -> Option<(usize, usize)> {
        let line = self.current_line();
        let mut amount = amount.get();

        // start from the current line
        let cur_char_idx = line.char_idx_from_width(self.current_col()).0;
        if let Some(char_idx) = cur_char_idx.checked_sub(amount) {
            return Some((self.current_row(), line.width_idx_from_char(char_idx)));
        }

        // We add one to factor in the newline
        amount -= cur_char_idx + 1;

        // We need more, so we'll keep going to previous lines
        let mut line_idx_plus_one = self.current_row();
        while line_idx_plus_one > 0 {
            let line_idx = line_idx_plus_one - 1;
            let line = self.provider.line(line_idx);

            let num_chars = match self.allows_after() {
                true => line.num_chars(),
                false => line.num_chars().saturating_sub(1),
            };

            if let Some(char_idx) = num_chars.checked_sub(amount) {
                return Some((line_idx, line.width_idx_from_char(char_idx)));
            }

            // We add one to factor in the newline
            amount -= num_chars + 1;
            line_idx_plus_one -= 1;
        }

        // We ran out of space. If we're allowing weak failure, we'll just return the leftmost
        // position (0,0) and if we aren't, we'll properly fail to move
        match weak_fail {
            true => Some((0, 0)),
            false => None,
        }
    }

    fn sim_move_right_cross(
        &self,
        amount: NonZeroUsize,
        weak_fail: bool,
    ) -> Option<(usize, usize)> {
        let line = self.current_line();
        let mut amount = amount.get();

        // start from the current line
        let max_char = match self.allows_after() {
            true => line.num_chars(),
            false => line.num_chars().saturating_sub(1),
        };

        let cur_char = line.char_idx_from_width(self.current_col()).0;
        let rem_chars = max_char - cur_char;
        if let Some(new_rem) = rem_chars.checked_sub(amount) {
            let new_char = max_char - new_rem;
            return Some((self.current_row(), line.width_idx_from_char(new_char)));
        }

        // We add one to factor in the newline
        amount -= rem_chars + 1;

        let mut line_idx = self.current_row() + 1;
        while line_idx < self.num_lines() {
            let line = self.provider.line(line_idx);

            let max_char = match self.allows_after() {
                true => line.num_chars(),
                false => line.num_chars().saturating_sub(1),
            };

            if let Some(new_rem) = max_char.checked_sub(amount) {
                let new_char = max_char - new_rem;
                return Some((line_idx, line.width_idx_from_char(new_char)));
            }

            // We add one to factor in the newline
            amount -= max_char + 1;
            line_idx += 1;
        }

        // We ran out of space. If we're allowing weak failure, we'll just return the rightmost
        // position, and if we aren't we'll properly fail to move
        match weak_fail {
            false => None,
            true => {
                let final_line = self.provider.line(line_idx - 1);
                let final_char = match self.allows_after() {
                    true => line.num_chars(),
                    false => line.num_chars().saturating_sub(1),
                };

                Some((line_idx - 1, final_line.width_idx_from_char(final_char)))
            }
        }
    }

    fn sim_move_left_pred(
        &self,
        pred: CharPredicate,
        original_amount: NonZeroUsize,
        shift_back: bool,
    ) -> Option<(usize, usize)> {
        let line = self.current_line();
        if line.num_chars() == 0 {
            return None;
        }

        let mut amount = original_amount.get();
        let f: fn(Option<char>, Option<char>) -> bool = pred.into();

        let mut chars = line.chars_from_width(..=self.current_col()).rev();
        if shift_back {
            chars.next()?;
        }

        // p is the previous character
        let mut p = chars.next()?.1;
        for (i, c) in chars {
            if f(p, c) {
                amount -= 1;
                if amount == 0 {
                    let char_idx = match shift_back {
                        true => i + 1,
                        false => i,
                    };

                    return Some((self.current_row(), line.width_idx_from_char(char_idx)));
                }
            }

            p = c;
        }

        // handle the beginning of the line
        if shift_back && f(p, Some('\n')) {
            amount -= 1;
            if amount == 0 {
                let char_idx = match shift_back {
                    true => 1,
                    false => 0,
                };

                return Some((self.current_row(), line.width_idx_from_char(char_idx)));
            }
        }

        // if we've gotten this far, we still haven't found anything so we'll return `None`
        None
    }

    fn sim_move_right_pred(
        &self,
        pred: CharPredicate,
        original_amount: NonZeroUsize,
        shift_back: bool,
    ) -> Option<(usize, usize)> {
        let line = self.current_line();
        if line.num_chars() == 0 {
            return None;
        }

        let mut amount = original_amount.get();
        let f: fn(Option<char>, Option<char>) -> bool = pred.into();

        let mut chars = line.chars_from_width(self.current_col()..);
        if shift_back {
            chars.next()?;
        }

        // p is the previous character
        let mut p = chars.next()?.1;
        for (i, c) in chars {
            if f(c, p) {
                amount -= 1;
                if amount == 0 {
                    let char_idx = match shift_back {
                        true => i - 1,
                        false => i,
                    };

                    return Some((self.current_row(), line.width_idx_from_char(char_idx)));
                }
            }

            p = c;
        }

        // handle the end of the line
        if shift_back && f(p, Some('\n')) {
            amount -= 1;
            if amount == 0 {
                let mut char_idx = line.num_chars();
                if shift_back || !self.allows_after() {
                    char_idx = char_idx.saturating_sub(1);
                }

                return Some((self.current_row(), line.width_idx_from_char(char_idx)));
            }
        }

        // if we've gotten this far, we still haven't found anything so we'll return `None`
        None
    }

    fn sim_move_left_pred_cross(
        &self,
        pred: CharPredicate,
        amount: NonZeroUsize,
        shift_back: bool,
    ) -> Option<(usize, usize)> {
        let mut amount = amount.get();

        let f: fn(Option<char>, Option<char>) -> bool = pred.into();

        // Gives the character one past the end - i.e. the upper bound in an exclusive range
        let end_char = |line_idx| {
            let line = self.provider.line(line_idx);
            if line.num_chars() == 0 {
                return 0;
            }

            if line_idx != self.current_row() {
                match self.allows_after() {
                    true => line.num_chars() + 1,
                    false => line.num_chars(),
                }
            } else {
                let mut char_idx = line.char_idx_from_width(self.current_col()).0;
                if !shift_back {
                    char_idx += 1;
                }
                char_idx
            }
        };

        let mut previous_char: Option<Option<char>> = None;
        for line_idx in (0..=self.current_row()).rev() {
            let line = self.provider.line(line_idx);
            let chars = line.chars(..end_char(line_idx)).rev();
            for (char_idx, c) in chars {
                if let Some(p) = previous_char {
                    match f(p, c) {
                        false => (),
                        true if amount != 1 => amount -= 1,
                        true /* if amount == 1 */ => {
                            // We want to return the proper location, so there's a bit of logic
                            // needed to handle shifting back
                            let (line_idx, char_idx) = match (shift_back, char_idx) {
                                (false, i) => (line_idx, i),
                                (true, i) if i + 1 < end_char(line_idx) => (line_idx, i + 1),
                                (true, _) => (line_idx + 1, 0),
                            };

                            return Some((
                                line_idx,
                                self.provider.line(line_idx).width_idx_from_char(char_idx),
                            ));
                        }
                    }
                }

                previous_char = Some(c);
            }

            if let (Some(p), true) = (previous_char, line_idx != 0 || shift_back) {
                match f(p, Some('\n')) {
                    true if amount == 1 => {
                        return Some((line_idx, 0));
                    }
                    true => amount -= 1,
                    false => (),
                }
            }

            previous_char = Some(Some('\n'));
        }

        None
    }

    fn sim_move_right_pred_cross(
        &self,
        pred: CharPredicate,
        amount: NonZeroUsize,
        shift_back: bool,
    ) -> Option<(usize, usize)> {
        let mut amount = amount.get();
        let f: fn(Option<char>, Option<char>) -> bool = pred.into();

        let start_char = |line_idx| {
            if line_idx != self.current_row() {
                return 0;
            }

            let idx = self
                .current_line()
                .char_idx_from_width(self.current_col())
                .0;
            match shift_back {
                true => idx + 1,
                false => idx,
            }
        };

        let mut previous_char: Option<Option<char>> = None;
        for line_idx in self.current_row()..self.num_lines() {
            let line = self.provider.line(line_idx);
            let chars = line.chars(start_char(line_idx)..);
            // ^ NOTE, FIXME: This probably breaks on empty lines :(
            for (char_idx, c) in chars {
                if let Some(p) = previous_char {
                    match f(p, c) {
                        true if amount == 1 => {
                            // We want to return the proper location - there's a bit of convoluted
                            // logic to handle that though, because we need to deal with shifting.
                            //
                            // Shifting is okay when we're not at the end of the line (i != 0), but
                            // if we're shifting to the previous line, things get more complicated.
                            let (line_idx, char_idx) = match (shift_back, char_idx) {
                                (false, i) => (line_idx, i),
                                (true, i) if i != 0 => (line_idx, i - 1),

                                // Shifting to the previous line - a bit more complex behavior that
                                // we need to handle
                                (true, _) => {
                                    let prev_line = self.provider.line(line_idx - 1);
                                    let char_idx = match self.allows_after() {
                                        true => prev_line.num_chars(),
                                        false => prev_line.num_chars().saturating_sub(1),
                                    };

                                    (line_idx - 1, char_idx)
                                }
                            };

                            return Some((
                                line_idx,
                                self.provider.line(line_idx).width_idx_from_char(char_idx),
                            ));
                        }
                        true => amount -= 1,
                        false => (),
                    }
                }

                previous_char = Some(c);
            }

            if let (Some(p), true) = (previous_char, line_idx != self.num_lines() || shift_back) {
                match f(p, Some('\n')) {
                    true if amount == 1 => {
                        let char_idx = match self.allows_after() {
                            true => line.num_chars(),
                            false => line.num_chars().saturating_sub(1),
                        };

                        return Some((line_idx, line.width_idx_from_char(char_idx)));
                    }
                    true => amount -= 1,
                    _ => (),
                }
            }

            previous_char = Some(Some('\n'));
        }

        None
    }
}

// SCROLL SIMULATION
//
// This is much the same as the "movement simulation" block above.
//
// The main function, `simulate_scroll` returns a `(usize, usize)`, which signifies the new values
// of `top_row` and `left_col`, respectively. `simulate_scroll` is the only function that should be
// called from this block.
//
// All other functions return `(Option<usize>, Option<usize>)`, which signifies the same thing as
// above, except `None` indicates no change.
//
// NOTE: `simulate_scroll` does not perform bounds checks on the values it returns; these are done
// by the caller, `ViewBuffer::scroll`.
impl<P: ContentProvider> ViewBuffer<P> {
    // Description given by the comment on the surrounding impl block
    fn simulate_scroll(&self, kind: ScrollKind, amount: usize) -> (usize, usize) {
        use Direction::{Down, Left, Right, Up};
        use ScrollKind::{ByDirection, DownPage, UpPage, VerticalCenter};

        let (row, col) = match kind {
            ByDirection(Up) => self.sim_scroll_up(amount),
            ByDirection(Down) => self.sim_scroll_down(amount),
            ByDirection(Left) => self.sim_scroll_left(amount),
            ByDirection(Right) => self.sim_scroll_right(amount),

            // We ignore `amount` here because repeated scrolling to the center wouldn't mean
            // anything.
            VerticalCenter => self.sim_scroll_vertical_center(),
            DownPage(frac) => self.sim_scroll_down_page(frac, amount),
            UpPage(frac) => self.sim_scroll_up_page(frac, amount),
        };

        (row.unwrap_or(self.top_row), col.unwrap_or(self.left_col))
    }

    fn sim_scroll_up(&self, amount: usize) -> (Option<usize>, Option<usize>) {
        (Some(self.top_row.saturating_sub(amount)), None)
    }

    fn sim_scroll_down(&self, amount: usize) -> (Option<usize>, Option<usize>) {
        (Some(self.top_row + amount), None)
    }

    fn sim_scroll_left(&self, amount: usize) -> (Option<usize>, Option<usize>) {
        (None, Some(self.left_col.saturating_sub(amount)))
    }

    fn sim_scroll_right(&self, amount: usize) -> (Option<usize>, Option<usize>) {
        (None, Some(self.left_col + amount))
    }

    fn sim_scroll_vertical_center(&self) -> (Option<usize>, Option<usize>) {
        let center = (self.size.height / 2) as usize;
        let current = self.cursor.row as usize;

        let new_row = if current > center {
            // Cursor below middle
            self.top_row + (current - center)
        } else {
            // Cursor above middle
            self.top_row.saturating_sub(center - current)
        };

        (Some(new_row), None)
    }

    fn sim_scroll_down_page(&self, mut frac: f64, amount: usize) -> (Option<usize>, Option<usize>) {
        if frac.is_nan() {
            panic!(
                "Invalid float {:?} given to `ViewBuffer::sim_scroll_down_page`",
                frac
            );
        }

        // The bounds on the floating-point value before casting it to a `usize`.
        // We need to do this because it is currently undefined behavior to cast a float outside of
        // the range supported by the `usize`.
        //
        // Relevant issue: https://github.com/rust-lang/rust/issues/10184
        const MAX_FLOAT: f64 = std::usize::MAX as f64;
        const MIN_FLOAT: f64 = 0.0;

        frac *= amount as f64;
        frac *= self.size.height as f64;
        frac = frac.max(MIN_FLOAT).min(MAX_FLOAT);

        // `frac` can't be NaN because we've already checked for that above and it won't have been
        // produced by the operations above.

        let n_lines = frac as usize;
        self.sim_scroll_down(n_lines)
    }

    fn sim_scroll_up_page(&self, mut frac: f64, amount: usize) -> (Option<usize>, Option<usize>) {
        if frac.is_nan() {
            panic!(
                "Invalid float {:?} given to `ViewBuffer::sim_scroll_up_page`",
                frac
            );
        }

        // The bounds on the floating-point value before casting it to a `usize`.
        // We need to do this because it is currently undefined behavior to cast a float outside of
        // the range supported by the `usize`
        //
        // Relevant issue: https://github.com/rust-lang/rust/issues/10184
        const MAX_FLOAT: f64 = std::usize::MAX as f64;
        const MIN_FLOAT: f64 = 0.0;

        frac *= amount as f64;
        frac *= self.size.height as f64;
        frac = frac.max(MIN_FLOAT).min(MAX_FLOAT);

        // `frac` can't be NaN because we've already checked for that above and it won't have been
        // produced by the operations above.

        let n_lines = frac as usize;
        self.sim_scroll_up(n_lines)
    }
}

// All of the private / internal methods for the ViewBuffer
impl<P: ContentProvider> ViewBuffer<P> {
    /// Returns the current line the cursor is on
    fn current_line<'a>(&'a self) -> Line<P::Deref<'a>> {
        self.provider.line(self.current_row())
    }

    /// Moves the cursor to the specified column, adjusting horizontal scrolling as needed
    ///
    /// This function does not check that the column is within the current line, nor does it check
    /// that it is at the boundary of a character (as some may be wide). Hence it should be used
    /// with caution
    ///
    /// Additionally, while this function *returns* `RefreshKind`, it does not set
    /// `self.needs_refresh` like other similar functions. This is left to the caller.
    #[rustfmt::skip]
    fn move_cursor_column_unchecked(&mut self, col: usize) -> Option<RefreshKind> {
        let cursor_col = self.cursor.col as usize;
        let current_col = self.current_col(); // self.left_col + cursor_col

        if current_col == col {
            return None;
        }

        let screen_width = self.size.width as usize;
        // The subtraction is okay because self.cursor.col is guaranteed to be < screen_width
        let screen_right = screen_width - cursor_col - 1;

        let refresh_kind = if current_col < col {
            // Moving to the right...
            //
            // If the cursor will still be on-screen (col - current_col ≤ screen_right), just do
            // that. Otherwise, we need to scroll first. How we scroll is controlled by
            // `FileConfig.center_scroll_right_edge` - if true, we'll scroll so that the cursor can
            // be centered. If not, we'll only scroll enough so that it's at the last column.
            if col - current_col <= screen_right {
                // We'll still be on-screen
                self.cursor.col += (col - current_col) as u16;
                RefreshKind::Cursor
            } else {
                // We do need to scroll...
                // This centers the screen horizontally given that we're moving to the right
                let new_cursor_col = screen_width / 2;
                self.left_col = col - new_cursor_col;
                self.cursor.col = new_cursor_col as u16;
                RefreshKind::Full
            }
        } else /* current_col > col */ { // <- this gets reformatted with rustfmt
            // Moving to the left...
            //
            // This is *essentially* the same as moving to the right, but if we want to center the
            // screen, we need to perform the additional check to confirm that we are actually able
            // to.
            if current_col - col <= cursor_col {
                // We'll still be on-screen
                self.cursor.col -= (current_col - col) as u16;
                RefreshKind::Cursor
            } else {
                // We do need to scroll
                let mid = screen_width / 2;
                let new_left_col = col.saturating_sub(mid);
                //                     ^^^^^^^^^^^^^^
                //       We use a saturating sub to guard against trying to center the
                //       screen too far to the left
                self.left_col = new_left_col;
                self.cursor.col = (col - new_left_col) as u16;
                RefreshKind::Full
            }
        };

        Some(refresh_kind)
    }

    /// Moves the cursor to the specified row, adjusting vertical scrolling as needed
    ///
    /// This function does not check that the cursor will be within the new line, nor does it check
    /// that it will be at the boundary of a character (as some may be wide). Hence it should be
    /// used with caution.
    ///
    /// Additionally, while this function *returns* `RefreshKind`, it does not set
    /// `self.needs_refresh` like other similar functions. This is left to the caller.
    #[rustfmt::skip]
    fn move_cursor_row_unchecked(&mut self, row: usize) -> Option<RefreshKind> {
        let current_row = self.current_row();
        let cursor_row = self.cursor.row as usize;

        if row == current_row {
            None
        } else if row > current_row {
            let diff = row - current_row;
            let height = self.size.height as usize;

            // If we can remain on the screen we'll just move the cursor down to that row
            if diff < height - cursor_row {
                self.cursor.row += diff as u16;
                Some(RefreshKind::Cursor)
            } else {
                // Otherwise, we need to scroll - we'll do this by setting the top
                // currently-displayed row
                self.top_row = current_row + diff - (height - 1) as usize;
                self.cursor.row = self.size.height - 1;
                Some(RefreshKind::Full)
            }

        } else /* row < current_row */ { // <- this gets reformatted with rustfmt
            let diff = current_row - row;

            // If we can remain on the screen, we'll just move the cursor up to that row
            if diff <= cursor_row {
                self.cursor.row -= diff as u16;
                Some(RefreshKind::Cursor)
            } else {
                // Otherwise, we need to scroll - we'll do this by setting the top
                // currently-displayed row
                self.top_row = current_row - diff;
                self.cursor.row = 0;
                Some(RefreshKind::Full)
            }
        }
    }

    /// Attempts to move the cursor as close as possible to the column given by `self.virtual_col`
    ///
    /// Note that this method does not set `self.needs_refresh`. This is left to the caller.
    fn try_move_virtual_cursor(&mut self) -> Option<RefreshKind> {
        let line = self.current_line();

        // If line we're on is blank, move the cursor somewhere reasonable
        if line.width() == 0 {
            drop(line);

            // This needs to be a special case because we usually move to 'column - 1', which
            // obviously isn't an option here.
            return self.move_cursor_column_unchecked(0);
        }

        let line_width = line.width();
        //  ^^^^^^^^^^
        // We need to put this here to avoid the 2-phase borrow conflict that would result from
        // calling `self.move_cursor_column_unchecked(line.width())`
        if self.virtual_col >= line_width && self.allow_cursor_after {
            drop(line);
            return self.move_cursor_column_unchecked(line_width);
        } else if self.virtual_col >= line_width {
            drop(line);
            return self.move_cursor_column_unchecked(line_width - 1);
        }

        // We now need to find the nearest character boundary to move to
        let (round_down, _round_up) = line.align_width(self.virtual_col);
        drop(line);

        // For simplicity, we always round down
        return self.move_cursor_column_unchecked(round_down);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Config stuff                                                                                   //
////////////////////////////////////////////////////////////////////////////////////////////////////

const DEFAULT_TABSTOP: usize = 4;

#[derive(Debug, Serialize, Deserialize)]
pub struct Builder {
    tabstop: Option<usize>,
}

static_config! {
    static GLOBAL;
    @Builder = Builder;
    pub struct Config {
        pub tabstop: usize = DEFAULT_TABSTOP,
    }

    impl ConfigPart {
        fn update(this: &mut Self, builder: Builder) {
            if let Some(t) = builder.tabstop {
                this.tabstop = t;
            }
        }
    }
}

impl XFrom<Builder> for Config {
    fn xfrom(builder: Builder) -> Self {
        Self {
            tabstop: builder.tabstop.unwrap_or(DEFAULT_TABSTOP),
        }
    }
}
