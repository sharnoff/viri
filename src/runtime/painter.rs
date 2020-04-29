//! Defines the controls given by the runtime for writing to the screen

use std::convert::TryInto;
use std::io::{self, Write};
use std::ops::Range;

use crossterm::{cursor, style, ExecutableCommand, QueueableCommand};

use crate::runtime::{TermCoord, TermSize};
use crate::utils;

/// A handler for writing to the screen without requiring positional knowledge
#[derive(Debug)]
pub struct Painter<'a> {
    /// Gives the position of the top-left corner of the painting surface, relative to its parent
    ///
    /// If its parent does not exist, this is relative to the total screen of the terminal
    pos: TermCoord,

    /// Gives the size of the terminal that we have available
    size: TermSize,

    /// The parent painter, if it exists.
    parent: Option<&'a Painter<'a>>,
}

/// A logical display region in the terminal
///
/// This is used internally to handle printing
#[derive(Debug, Clone)]
struct Window {
    cols: Range<u16>,
    rows: Range<u16>,
}

impl<'a> Painter<'a> {
    /// Creates the root painter instance
    pub fn global(size: TermSize) -> Self {
        Self {
            pos: (0, 0).into(),
            size,
            parent: None,
        }
    }

    /// Returns the size of the painter
    pub fn size(&self) -> TermSize {
        self.size
    }

    /// Returns the absolute position of the painter on the screen
    pub fn abs_pos(&self) -> TermCoord {
        // TODO: Maybe this shouldn't be written recursively? It would be much cheaper to be
        // written as a loop.
        self.pos
            + self
                .parent
                .as_ref()
                .map(|p| p.abs_pos())
                .unwrap_or((0, 0).into())
    }

    /// A helper function mostly for use in [`Container::handle_view_output_exits`]
    ///
    /// This returns a new painter whose size has been decreased vertically trimming the bottom. If
    /// the painter is not tall enough, `None` will returned. I.e. `amount` must be strictly less
    /// than the current height.
    ///
    /// [`Container::handle_view_output_exits`]: ../container/struct.Container.html#handle_view_output_exits
    pub fn trim_bot<'b: 'a>(&'b self, amount: u16) -> Option<Painter<'b>> {
        if self.size.height <= amount {
            return None;
        }

        Some(Painter {
            pos: self.pos,
            size: TermSize {
                height: self.size.height - amount,
                width: self.size.width,
            },
            parent: Some(self),
        })
    }

    /// Returns a new painter whose size has been decreased horizontally by pushing the left side
    /// inwards
    ///
    /// This will shift the position of the painter rightwards by `amount` and decrease the
    /// horizontal size by `amount`. If the painter's window is too small to support this
    /// operation, it will return `None`.
    pub fn trim_left<'b: 'a>(&'b self, amount: u16) -> Option<Painter<'b>> {
        if self.size.width <= amount {
            return None;
        }

        let pos = TermCoord {
            col: self.pos.col + amount,
            ..self.pos
        };

        let size = TermSize {
            width: self.size.width - amount,
            ..self.size
        };

        Some(Painter {
            pos,
            size,
            parent: Some(self),
        })
    }

    /// Returns a new painter whose size has been decreased horizontally by pushing the right side
    /// inwards
    ///
    /// This will not shift the position of the painter, but will decrease the horizontal size by
    /// `amount`. If the painter's window is too small to support this operation, it will return
    /// `None`.
    pub fn trim_right_to<'b: 'a>(&'b self, amount: u16) -> Option<Painter<'b>> {
        if self.size.width <= amount {
            return None;
        }

        let size = TermSize {
            width: self.size.width - amount,
            ..self.size
        };

        Some(Painter {
            pos: self.pos,
            size,
            parent: Some(self),
        })
    }

    /// Prints the lines given, where they are expected to fill `line_range`
    ///
    /// Each item in the supplied iterator has the actual displayed range of the line, in addition
    /// to the string to print. This is assumed to be correct - if it isn't, things will not
    /// display correctly.
    pub fn print_lines<S: AsRef<str>>(&self, iter: impl Iterator<Item = (Range<u16>, S)>) {
        let window = Window {
            cols: 0..self.size.width,
            rows: 0..self.size.height,
        };

        self.print_lines_internal(iter, window);
    }

    pub fn set_cursor(&self, mut pos: TermCoord) {
        pos = self.pos + pos;
        match self.parent.as_ref() {
            Some(p) => p.set_cursor(pos),
            None => {
                io::stdout()
                    .execute(cursor::MoveTo(pos.col, pos.row))
                    .unwrap();
            }
        }
    }
}

impl<'a> Painter<'a> {
    fn print_lines_internal<I, S>(&self, iter: I, mut window: Window)
    where
        I: Iterator<Item = (Range<u16>, S)>,
        S: AsRef<str>,
    {
        let c = self.pos.col;
        let r = self.pos.row;

        let mut iter = iter.map(move |(r, s)| {
            let r = Range {
                start: r.start + c,
                end: r.end + c,
            };

            (r, s)
        });

        let cols = window.cols;
        let rows = window.rows;
        window = Window {
            cols: cols.start + c..cols.end + c,
            rows: rows.start + r..rows.end + r,
        };

        // If this isn't the top-level painter, we'll pass on the message to print to that one
        if let Some(p) = self.parent.as_ref() {
            let dyn_iter = &mut iter as &mut dyn Iterator<Item = (Range<u16>, S)>;
            p.print_lines_internal(dyn_iter, window);
            return;
        }

        // Actually print the lines now
        //
        // We'll use this iterator to keep track of things. If there's any left over after we're
        // done, we'll use this to clear the rest of the screen (if it needs it)
        let mut line_indexes = window.rows.start as usize..window.rows.end as usize;

        let mut stdout = io::stdout();
        for (i, (segment, line)) in (&mut line_indexes).zip(iter) {
            let i: u16 = i.try_into().unwrap();

            stdout
                .queue(cursor::MoveTo(window.cols.start, window.rows.start + i))
                .unwrap();

            // preprocess the list:

            let left_pad = (segment.start - window.cols.start) as usize;
            //  ^^^^^^^^ Uh oh... hopefully this won't get yanked
            let right_pad = (window.cols.end - segment.end) as usize;

            if left_pad > 0 {
                stdout
                    .queue(style::Print(utils::blank_str(left_pad as u16)))
                    .unwrap();
            }

            stdout.queue(style::Print(line.as_ref())).unwrap();

            if right_pad > 0 {
                stdout
                    .queue(style::Print(utils::blank_str(right_pad as u16)))
                    .unwrap();
            }
        }

        // If there's still lines left, we need to print them as blank
        for i in line_indexes {
            let i: u16 = i.try_into().unwrap();
            stdout
                .queue(cursor::MoveTo(window.cols.start, window.rows.start + i))
                .unwrap();
            stdout
                .queue(style::Print(utils::blank_str(window.cols.len() as u16)))
                .unwrap();
        }

        stdout.flush().unwrap();
    }
}
