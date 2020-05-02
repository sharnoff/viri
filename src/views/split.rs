//! Definitions of horizontal and vertical splits
//!
//! Horizontal splits are those that preserve the width of the [`View`]s, stacking them vertically.
//! Vertical splits are the opposite: placing them side by side, preserving the height.
//!
//! The two types corresponding to these are [`Horiz`] and [`Vert`], respectively. Their
//! implementations are very similar, but are extracted into separate types in order to allow for
//! simplified code.
//!
//! ## Visualizing layouts
//!
//! Creating a horizontal split can be visualized as the following change:
//! ```text
//! Before:                 After:
//! ╔═══════════════════╗  ╔═══════════════════╗
//! ║                   ║  ║       Upper       ║
//! ║                   ║  ║                   ║
//! ║     Main View     ║  ╠═══════════════════╣
//! ║                   ║  ║       Lower       ║
//! ║                   ║  ║                   ║
//! ╚═══════════════════╝  ╚═══════════════════╝
//! ```
//!
//! Whereas creating a vertical split can be visualized as:
//! ```text
//! Before:                 After:
//! ╔═══════════════════╗  ╔═════════╦═════════╗
//! ║                   ║  ║         ║         ║
//! ║                   ║  ║         ║         ║
//! ║     Main View     ║  ║  Left   ║  Right  ║
//! ║                   ║  ║         ║         ║
//! ║                   ║  ║         ║         ║
//! ╚═══════════════════╝  ╚═════════╩═════════╝
//! ```
//!
//! [`View`]: ../trait.View.html
//! [`Horiz`]: struct.Horiz.html
//! [`Vert`]: struct.Vert.html

use super::{ConcreteView, OutputSignal, RefreshKind, SignalHandler, View};
use crate::container::Signal;
use crate::mode::Direction;
use crate::runtime::{Painter, TermSize};
use crossterm::style::Colorize;
use std::convert::TryFrom;
use std::iter;

/// A horizontally-split container of two (or more) [`View`]s
///
/// For the difference between horizontal and vertical splits, please refer to the
/// [module-level documentation].
///
/// [`View`]: ../trait.View.html
/// [module-level documentation]: index.html
pub struct Horiz {
    /// The total size of the `View`
    size: TermSize,

    /// The index in `inner_views` of the view that is currently selected.
    selected_idx: usize,

    /// The set of internal `View`s and the number of rows that each takes up on the screen. Lower
    /// indices correspond to `View`s displayed higher on the screen. To take the module-level
    /// documentation as an example, we would have the following indices:
    /// ```text
    /// ╔══════════════════╗
    /// ║  inner_views[0]  ║
    /// ║                  ║
    /// ╠══════════════════╣
    /// ║  inner_views[1]  ║
    /// ║                  ║
    /// ╚══════════════════╝
    /// ```
    /// It should be noted that this number of rows does not include the bottom bars inserted
    /// between `View`s (and at the very bottom as well, if `include_bottom_bar` is true).
    inner_views: Vec<(u16, Box<dyn ConcreteView>)>,

    /// Whether a custom bottom bar is included within the region of the screen allocated to this
    /// `View`
    // TODO: Describe in more detail.
    include_bottom_bar: bool,
}

////////////////////////////////////////////////////////////////////////////////
// Publicly-exposed API/methods - `Horiz`                                     //
////////////////////////////////////////////////////////////////////////////////

impl Horiz {
    pub fn construct(views: Vec<Box<dyn ConcreteView>>) -> Self {
        Self {
            // It's easier to do it this way, than to handle passing sizes through
            //
            // We'll just resize on the first refresh
            size: (1, 1).into(),
            selected_idx: 0,
            // Again, just passing it a random value
            inner_views: views.into_iter().map(|v| (10, v)).collect(),
            // Another one of the "easier to just resize" scenarios
            include_bottom_bar: true,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Trait implementations - `Horiz`                                            //
////////////////////////////////////////////////////////////////////////////////

impl View for Horiz {
    fn refresh(&mut self, painter: &Painter) {
        if painter.distinct_bottom_bar() == self.include_bottom_bar || painter.size() != self.size {
            // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
            // This is an interesting case - `distinct_bottom_bar` from a painter implies that
            // there's something else handling the bottom bar already, so we don't need to. Thus we
            // want exactly one of `painter.distinct_bottom_bar()` and `self.include_bottom_bar` to
            // be true.
            self.include_bottom_bar = !painter.distinct_bottom_bar();
            self.size = painter.size();
            self.resize();
        }

        // Sometimes there won't be enough room to actually display all of the inner views. In this
        // case, we'll just display a warning message
        if !self.can_display() {
            const CANNOT_DISPLAY: &'static str =
                "View too small; please resize or close inner views";
            let range = 0..CANNOT_DISPLAY.len().min(painter.size().width as usize);
            // ^ FIXME: This must also include the end padding, which it currently does not.
            // For more information, see the documentation for `Painter::print_single`.

            painter.print_single(0, 0, CANNOT_DISPLAY[range].red().on_white().to_string());
            return;
        }

        // We'll go through each inner view, going from the top down, refreshing (in order) their
        // main content, then their bottom bars
        //
        // `top_row` will store the top row of the painter for whatever `View` we're currently
        // refreshing.
        let mut top_row = 0_u16;
        let num_inner = self.inner_views.len();
        for (i, &mut (n_rows, ref mut view)) in self.inner_views.iter_mut().enumerate() {
            let draw_bottom = (i != num_inner - 1) || self.include_bottom_bar;

            // This is safe to unwrap because we already know that it's within the bounds of the
            // painter
            let inner_painter = painter.slice_vertically(top_row..top_row + n_rows).unwrap();
            view.refresh(&inner_painter);

            top_row += n_rows;

            if draw_bottom {
                let text = view
                    .construct_bottom_text(self.size.width)
                    .black()
                    .on_white()
                    .to_string();
                painter.print_single(top_row, 0, text);
                top_row += 1;
            }
        }
    }

    fn refresh_cursor(&self, painter: &Painter) {
        if let Some(p) = self.inner_painter(self.selected_idx, painter) {
            self.inner_views[self.selected_idx].1.refresh_cursor(&p);
        }
    }

    fn bottom_left_text(&mut self) -> Option<(String, usize)> {
        // If we're handling our own bottom text bar, we won't need to display anything here
        if self.include_bottom_bar {
            return None;
        }

        // Otherwise, we'll just return the value passed by the `View` on the bottom.
        self.inner_views.last_mut().unwrap().1.bottom_left_text()
    }

    fn bottom_right_text(&mut self) -> Option<(String, usize)> {
        // Much the same as `bottom_left_text`:
        // If we're handling our own bottom text bar, we won't need to display anything here
        if self.include_bottom_bar {
            return None;
        }

        // Otherwise, we'll just return the value passed by the `View` on the bottom.
        self.inner_views.last_mut().unwrap().1.bottom_right_text()
    }

    fn prefer_bottom_left(&self) -> bool {
        false
    }
}

impl ConcreteView for Horiz {}

impl SignalHandler for Horiz {
    fn try_handle(&mut self, signal: Signal) -> Option<Vec<OutputSignal>> {
        let current_focus = &mut self.inner_views[self.selected_idx].1;
        let output_signals = current_focus.try_handle(signal)?;
        Some(self.handle_signals(output_signals))
    }
}

////////////////////////////////////////////////////////////////////////////////
// Helper methods - `Horiz`                                                   //
////////////////////////////////////////////////////////////////////////////////

impl Horiz {
    fn inner_painter<'a, 'b: 'a>(
        &self,
        inner_idx: usize,
        painter: &'b Painter<'a>,
    ) -> Option<Painter<'b>> {
        let idx = u16::try_from(inner_idx).unwrap_or(u16::MAX);
        let rows_offset =
            idx.saturating_add(self.inner_views[..inner_idx].iter().map(|(r, _)| r).sum());
        let height = self.inner_views[inner_idx].0;
        let new_painter = painter.slice_vertically(rows_offset..rows_offset + height)?;

        match self.include_bottom_bar {
            true => Some(new_painter.with_distinct_bottom_bar()),
            false => Some(new_painter),
        }
    }

    /// Returns the current height of the `View` as given by the sum of the heights of inner views
    /// (plus bottom bars). This need not fit within a `u16`.
    fn current_sum_height(&self) -> usize {
        // The total size is made up of two components: the bottom bars between the views and the
        // actual size of each view itself. The addition below is between these two components in
        // that order.
        //
        // We subtract 1 from the length to account for the fact that the bottom bar for the
        // bottom-most view might not be included in the size; it may be handled by something else.
        let total_height = (self.inner_views.len() - 1)
            + self
                .inner_views
                .iter()
                .map(|&(s, _)| s as usize)
                .sum::<usize>();

        match self.include_bottom_bar {
            false => total_height,
            true => total_height + 1,
        }
    }

    /// Resizes the horizontal split, only adjusting the number of rows taken up by the inner
    /// `Views`. No additional refreshing is performed; that is left to the caller (which is nearly
    /// always `refresh`).
    fn resize(&mut self) {
        // If we can't fit anything, simply return
        let min_height = match self.include_bottom_bar {
            true => 2 * self.inner_views.len(),
            false => 2 * self.inner_views.len() - 1,
        };

        if min_height > self.size.height as usize {
            return;
        }

        let size_total = self.current_sum_height();

        // Convert each inner view's height (plus the bottom bar, if there) into the portion of the
        // screen that it takes up.
        //
        // We'll then use the new size (via `self.size.height`) and calculate the new values for
        // each view's size.
        let include_bar = |this: &Horiz, inner_idx: usize| {
            inner_idx < this.inner_views.len() - 1 || this.include_bottom_bar
        };

        // The ratios in the screen
        let ratios = self.inner_views.iter().enumerate().map(|(i, &(h, _))| {
            let height = match include_bar(self, i) {
                true => h + 1,
                false => h,
            };

            (i, height as f64)
        });

        // the scaling ratio to apply
        let scale = self.size.height as f64 / size_total as f64;

        let min_height = |this, inner_idx| match include_bar(this, inner_idx) {
            true => 2,
            false => 1,
        };

        // Produce the new heights. We round down so that the last line can *always* pick up the
        // slack - if we didn't this would not be guaranteed.
        let mut running_total_height = 0_u16;
        let new_heights = ratios
            .map(|(i, r)| {
                let mut h = ((r * scale) as u16).max(min_height(self, i));
                running_total_height += h;
                if include_bar(self, i) {
                    h -= 1;
                }

                (i, h)
            })
            .collect::<Vec<_>>();

        for (i, h) in new_heights.into_iter() {
            self.inner_views[i].0 = h;
        }

        let diff = self.size.height - running_total_height;
        self.inner_views.last_mut().unwrap().0 += diff;
    }

    /// Returns whether the inner contents of the split can actually be displayed. This may be
    /// false if `self.size` cannot accomodate even a single line from each inner view.
    fn can_display(&self) -> bool {
        match u16::try_from(self.current_sum_height()) {
            Err(_) => false,
            // We would put `<=` here, but that would be overly defensive because it should always be
            // the case that either `total_size = self.size.height` or `total_size > self.size.height`.
            // Simply placing `==` here allows us to catch bugs as soon as they occur instead of causing
            // graphical issues.
            Ok(s) => s == self.size.height,
        }
    }

    // uses `self.selected_idx`
    fn handle_signals(&mut self, signals: Vec<OutputSignal>) -> Vec<OutputSignal> {
        let mut outputs = Vec::new();
        let mut sigs_iter = signals.into_iter();
        while let Some(s) = sigs_iter.next() {
            let (early_exit, sigs) = self.handle_output_signal(s);
            outputs.extend(sigs);
            if early_exit {
                outputs.extend(sigs_iter);
                return outputs;
            }
        }

        outputs
    }

    /// Returns the output signals and whether the caller should exit early - this will occur in
    /// cases where we are replacing *this* `View` -- output signals should not be handled any
    /// further.
    fn handle_output_signal(&mut self, signal: OutputSignal) -> (bool, Vec<OutputSignal>) {
        use Direction::{Down, Left, Right, Up};
        use OutputSignal::{
            ClearBottomBar, Close, LeaveBottomBar, NeedsRefresh, NoSuchCmd, Open, Replace,
            SaveBottomBar, SetBottomBar, ShiftFocus, WaitingForMore,
        };
        use RefreshKind::{Full, Inner};

        fn to_signal(refresh: Option<RefreshKind>) -> Vec<OutputSignal> {
            refresh.map(|r| vec![NeedsRefresh(r)]).unwrap_or(Vec::new())
        }

        match signal {
            SaveBottomBar
            | SetBottomBar { .. }
            | LeaveBottomBar
            | ClearBottomBar
            | NoSuchCmd
            | WaitingForMore => (false, vec![signal]),
            NeedsRefresh(_) => (false, vec![NeedsRefresh(Inner)]),
            Replace(new_view) => {
                self.inner_views[self.selected_idx].1 = new_view;
                (false, Vec::new())
            }
            Close if self.inner_views.len() == 2 => {
                self.inner_views.remove(self.selected_idx);
                (true, vec![Replace(self.inner_views.pop().unwrap().1)])
            }
            // inner_views.len() > 2
            Close => {
                self.inner_views.remove(self.selected_idx);
                self.selected_idx = self.selected_idx.min(self.inner_views.len() - 1);
                (false, vec![NeedsRefresh(Full)])
            }
            ShiftFocus(d, n) => match d {
                Up if n <= self.selected_idx => {
                    self.selected_idx -= n;
                    (
                        false,
                        to_signal(self.inner_views[self.selected_idx].1.focus()),
                    )
                }
                Down if self.selected_idx + n < self.inner_views.len() => {
                    self.selected_idx += n;
                    (
                        false,
                        to_signal(self.inner_views[self.selected_idx].1.focus()),
                    )
                }
                Up => (false, vec![ShiftFocus(Up, n - self.selected_idx)]),
                Down => (
                    false,
                    vec![ShiftFocus(
                        Up,
                        n - (self.inner_views.len() - self.selected_idx - 1),
                    )],
                ),
                Left | Right => (false, vec![ShiftFocus(d, n)]),
            },
            Open(d, v) => match d {
                Up => {
                    // TODO: Instead of assigning some random value here (20), we should actually
                    // do some proper resizing to produce the most ideal shifting
                    self.inner_views.insert(self.selected_idx, (20, v));
                    (false, vec![NeedsRefresh(Full)])
                }
                Down => {
                    // TODO: See above
                    self.inner_views.insert(self.selected_idx + 1, (20, v));
                    (false, vec![NeedsRefresh(Full)])
                }
                Left | Right => (false, vec![Open(d, v)]),
            },
        }
    }
}

/// A vertically-split container of two (or more) [`View`]s
///
/// For the difference between horizontal and vertical splits, please refer to the
/// [module-level documentation].
///
/// [`View`]: ../trait.View.html
/// [module-level documentation]: index.html
pub struct Vert {
    /// The total size of the `View`
    size: TermSize,

    /// The index in `inner_views` of the view that is currently selected.
    selected_idx: usize,

    /// The set of internal `View`s and the number of columns that each takes up on the screen.
    /// Lower indices correspond to `View`s displayed further left on the screen. To take the
    /// module-level documentation as an example, we would have the following indices:
    /// ```text
    /// ╔══════════╦══════════╗
    /// ║          ║          ║
    /// ║          ║          ║
    /// ║ inner[0] ║ inner[1] ║
    /// ║          ║          ║
    /// ║          ║          ║
    /// ╚══════════╩══════════╝
    /// ```
    /// It should be noted that this number of columns does not include the vertical bars inserted
    /// between views.
    inner_views: Vec<(u16, Box<dyn ConcreteView>)>,

    /// Whether a custom bottom bar is included within the region of the screen allocated to this
    /// `View`
    // TODO: Describe in more detail.
    include_bottom_bar: bool,
}

////////////////////////////////////////////////////////////////////////////////
// Publicly-exposed API/methods - `Vert`                                      //
////////////////////////////////////////////////////////////////////////////////

impl Vert {
    pub fn construct(views: Vec<Box<dyn ConcreteView>>) -> Self {
        Self {
            // It's easier to do it this way, than to handle passing sizes through
            //
            // We'll just resize on the first refresh
            size: (1, 1).into(),
            selected_idx: 0,
            // Again, just passing it a random value
            inner_views: views.into_iter().map(|v| (10, v)).collect(),
            // Another one of the "easier to just resize" scenarios
            include_bottom_bar: true,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Trait implementations - `Vert`                                             //
////////////////////////////////////////////////////////////////////////////////

impl View for Vert {
    fn refresh(&mut self, painter: &Painter) {
        // This function is largely duplicated from `Horiz`. Each item is explained in detail
        // there; for more information please refer to `Horiz::refresh`.

        if painter.distinct_bottom_bar() == self.include_bottom_bar {
            self.include_bottom_bar = !painter.distinct_bottom_bar();
        }

        if painter.size() != self.size {
            self.size = painter.size();
            self.resize();
        }

        if !self.can_display() {
            const CANNOT_DISPLAY: &'static str =
                "View too small; please resize or close inner views";
            let range = 0..CANNOT_DISPLAY.len().min(painter.size().width as usize);
            painter.print_single(0, 0, CANNOT_DISPLAY[range].red().on_white().to_string());
            return;
        }

        let mut left_col = 0_u16;
        let num_inner = self.inner_views.len();
        for (i, &mut (n_cols, ref mut view)) in self.inner_views.iter_mut().enumerate() {
            // This is safe to unwrap because we already know that it's within the bounds of the
            // painter
            let inner_painter = painter
                .slice_horizontally(left_col..left_col + n_cols)
                .unwrap();
            view.refresh(&inner_painter);

            left_col += n_cols;

            if i != num_inner - 1 {
                // get the single column that we want to display
                let col_painter = painter.slice_horizontally(left_col..left_col + 1).unwrap();
                let iter = iter::repeat('|').map(|c| (0..1, c.black().on_white().to_string()));
                col_painter.print_lines(iter);
                left_col += 1;
            }
        }

        if self.include_bottom_bar {
            let text = self
                .construct_bottom_text(self.size.width)
                .black()
                .on_white()
                .to_string();
            painter.print_single(self.size.height - 1, 0, text);
        }
    }

    fn refresh_cursor(&self, painter: &Painter) {
        // Get the inner painter corresponding to that index
        let idx = u16::try_from(self.selected_idx).unwrap_or(u16::MAX);
        let cols_offset = idx.saturating_add(
            self.inner_views[..self.selected_idx]
                .iter()
                .map(|(r, _)| r)
                .sum(),
        );
        let width = self.inner_views[self.selected_idx].0;

        let inner_painter = match painter.slice_horizontally(cols_offset..cols_offset + width) {
            Some(p) => p,
            None => return,
        };

        let inner_painter = match self.include_bottom_bar {
            true => match inner_painter.trim_bot(1) {
                Some(p) => p,
                None => return,
            },
            false => inner_painter,
        };

        self.inner_views[self.selected_idx]
            .1
            .refresh_cursor(&inner_painter)
    }

    fn bottom_left_text(&mut self) -> Option<(String, usize)> {
        None
    }

    fn bottom_right_text(&mut self) -> Option<(String, usize)> {
        None
    }

    fn prefer_bottom_left(&self) -> bool {
        false
    }

    fn construct_bottom_text(&mut self, width: u16) -> String {
        if width != self.size.width {
            self.size.width = width;
            self.resize();
        }

        let &mut (w, ref mut v) = &mut self.inner_views[0];
        let mut text = v.construct_bottom_text(w).black().on_white().to_string();

        for &mut (width, ref mut view) in self.inner_views.iter_mut() {
            text += &" ".black().on_white().to_string();
            text += &view
                .construct_bottom_text(width)
                .black()
                .on_white()
                .to_string();
        }

        text
    }
}

impl ConcreteView for Vert {}

impl SignalHandler for Vert {
    fn try_handle(&mut self, signal: Signal) -> Option<Vec<OutputSignal>> {
        let current_focus = &mut self.inner_views[self.selected_idx].1;
        let output_signals = current_focus.try_handle(signal)?;
        Some(self.handle_signals(output_signals))
    }
}

////////////////////////////////////////////////////////////////////////////////
// Helper methods - `Vert`                                                    //
////////////////////////////////////////////////////////////////////////////////

impl Vert {
    /// Returns the current width of the `View` as given by the sum of the widths of inner views
    /// (plus inner columns). This need not fit within a `u16`.
    fn current_sum_width(&self) -> usize {
        // This is largely replicated from `Horiz::current_sum_height`. For more comments, see that
        // function.
        (self.inner_views.len() - 1)
            + self
                .inner_views
                .iter()
                .map(|&(s, _)| s as usize)
                .sum::<usize>()
    }

    fn resize(&mut self) {
        // If we can't fit anything, simply return
        let min_width = 2 * self.inner_views.len() - 1;
        if min_width > self.size.height as usize {
            return;
        }

        let size_total = self.current_sum_width();

        let include_bar = |this: &Vert, inner_idx: usize| inner_idx < this.inner_views.len() - 1;

        // The ratios in the screen
        let ratios = self.inner_views.iter().enumerate().map(|(i, &(h, _))| {
            let width = match include_bar(self, i) {
                true => h + 1,
                false => h,
            };

            (i, width as f64)
        });

        // the scaling ratio to apply
        let scale = self.size.width as f64 / size_total as f64;

        let min_width = |this, inner_idx| match include_bar(this, inner_idx) {
            true => 2,
            false => 1,
        };

        // Produce the new heights. We round down so that the last line can *always* pick up the
        // slack - if we didn't this would not be guaranteed.
        let mut running_total_width = 0_u16;
        let new_widths = ratios
            .map(|(i, r)| {
                let mut w = ((r * scale) as u16).max(min_width(self, i));
                running_total_width += w;
                if include_bar(self, i) {
                    w -= 1;
                }

                (i, w)
            })
            .collect::<Vec<_>>();

        for (i, w) in new_widths.into_iter() {
            self.inner_views[i].0 = w;
        }

        let diff = self.size.width - running_total_width;
        self.inner_views.last_mut().unwrap().0 += diff;
    }

    /// Returns whether the inner contents of the split can actually be displayed. This may be
    /// false if `self.size` cannot accomodate even a single column from each inner view
    fn can_display(&self) -> bool {
        match u16::try_from(self.current_sum_width()) {
            Err(_) => false,
            // For an explanation of why this is `==` and not `<=`, see `Horiz::can_display`
            Ok(w) => w == self.size.width,
        }
    }

    // Copied exactly line-for-line from `Horiz::handle_singals`
    fn handle_signals(&mut self, signals: Vec<OutputSignal>) -> Vec<OutputSignal> {
        let mut outputs = Vec::new();
        let mut sigs_iter = signals.into_iter();
        while let Some(s) = sigs_iter.next() {
            let (early_exit, sigs) = self.handle_output_signal(s);
            outputs.extend(sigs);
            if early_exit {
                outputs.extend(sigs_iter);
                return outputs;
            }
        }

        outputs
    }

    /// Returns the output signals and whether the caller should exit early - this will occur in
    /// cases where we are replacing *this* `View` -- output signals should not be handled any
    /// further.
    fn handle_output_signal(&mut self, signal: OutputSignal) -> (bool, Vec<OutputSignal>) {
        // NOTE: This is copied nearly line-for-line from `Horiz::handle_output_signal`
        use Direction::{Down, Left, Right, Up};
        use OutputSignal::{
            ClearBottomBar, Close, LeaveBottomBar, NeedsRefresh, NoSuchCmd, Open, Replace,
            SaveBottomBar, SetBottomBar, ShiftFocus, WaitingForMore,
        };
        use RefreshKind::{Full, Inner};

        fn to_signal(refresh: Option<RefreshKind>) -> Vec<OutputSignal> {
            refresh.map(|r| vec![NeedsRefresh(r)]).unwrap_or(Vec::new())
        }

        match signal {
            SaveBottomBar
            | SetBottomBar { .. }
            | LeaveBottomBar
            | ClearBottomBar
            | NoSuchCmd
            | WaitingForMore => (false, vec![signal]),
            NeedsRefresh(_) => (false, vec![NeedsRefresh(Inner)]),
            Replace(new_view) => {
                self.inner_views[self.selected_idx].1 = new_view;
                (false, Vec::new())
            }
            Close if self.inner_views.len() == 2 => {
                self.inner_views.remove(self.selected_idx);
                (true, vec![Replace(self.inner_views.pop().unwrap().1)])
            }
            // inner_views.len() > 2
            Close => {
                self.inner_views.remove(self.selected_idx);
                self.selected_idx = self.selected_idx.min(self.inner_views.len() - 1);
                (false, vec![NeedsRefresh(Full)])
            }
            ShiftFocus(d, n) => match d {
                Left if n <= self.selected_idx => {
                    self.selected_idx -= n;
                    (
                        false,
                        to_signal(self.inner_views[self.selected_idx].1.focus()),
                    )
                }
                Right if self.selected_idx + n < self.inner_views.len() => {
                    self.selected_idx += n;
                    (
                        false,
                        to_signal(self.inner_views[self.selected_idx].1.focus()),
                    )
                }
                Left => (false, vec![ShiftFocus(Up, n - self.selected_idx)]),
                Right => (
                    false,
                    vec![ShiftFocus(
                        Up,
                        n - (self.inner_views.len() - self.selected_idx - 1),
                    )],
                ),
                Up | Down => (false, vec![ShiftFocus(d, n)]),
            },
            Open(d, v) => match d {
                Left => {
                    // TODO: Instead of assigning some random value here (20), we should actually
                    // do some proper resizing to produce the most ideal shifting
                    self.inner_views.insert(self.selected_idx, (20, v));
                    (false, vec![NeedsRefresh(Full)])
                }
                Right => {
                    // TODO: See above
                    self.inner_views.insert(self.selected_idx + 1, (20, v));
                    (false, vec![NeedsRefresh(Full)])
                }
                Up | Down => (false, vec![Open(d, v)]),
            },
        }
    }
}
