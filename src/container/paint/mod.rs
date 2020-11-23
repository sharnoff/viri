//! Facilities for orchestrating drawing content to the screen
//!
//! The primary type exposed by this module is [`Painter`], which is passed around to anything that
//! may want to draw to the screen. This is handled internally by the [`Buffer`] it references,
//! which is what actually writes to STDOUT.
//!
//! A small collection of helper types and traits are also provided. Inside each cell of the buffer
//! is a [`Symbol`], which corresponds to a single unicode grapheme. These are primarily produced
//! by the implementations of the [`IntoSymbols`] trait. Additionally, painters may be [`split`] to
//! divide regions of the screen - the direction and amount are handled by the [`Extract`] type,
//! which exists solely for that purpose.
//!
//! [`split`]: Painter::split

use crate::{TermPos, TermSize};
use ansi_term::{ANSIStrings, Style};
use std::io::Write;
use std::marker::PhantomData;
use tokio::io::{self, AsyncWrite, AsyncWriteExt};

mod painter;
mod styled;
mod symbol;

pub use painter::{Extract, Painter};
pub use styled::{Styled, StyledContent, StyledString};
pub use symbol::{IntoSymbols, Symbol};

/// The full contents of the terminal as they are displayed
///
/// This is only used inside the parent module, but the facilities it provides through [`Painter`
pub(super) struct Buffer {
    size: TermSize,
    inner: Vec<Cell>,
}

/// A single, atomic displayed region in the terminal - typically a single character
#[derive(Clone, PartialEq)]
struct Cell {
    symbol: Option<Symbol>,
    style: Style,

    previous: Option<(Option<Symbol>, Style)>,
    // Whether the contents of the cell have changed from what was previously displayed
    changed: bool,
}

impl Buffer {
    /// Creates a new `Buffer` with the specified size
    pub fn new(size: TermSize) -> Buffer {
        let num_cells = size.width() as usize * size.height() as usize;
        let inner = vec![Cell::new(); num_cells];

        Buffer { size, inner }
    }

    /// Returns the size of the buffer
    pub fn size(&self) -> TermSize {
        self.size
    }

    /// Creates the global painter with access to the entire buffer
    ///
    /// For more information on using [`Painter`]s, please refer to the documentation there.
    pub fn painter(&mut self) -> Painter {
        Painter::from_buf(self)
    }

    /// Produces a reference to the cell given by the buffer and the position within it
    ///
    /// This function is only available internally for usage within [`Painter`], which stores a
    /// lifetime-bound `*mut Buffer` for shared mutable access.
    ///
    /// The passed marker is for an additional layer of safety around the lifetime of the reference.
    /// It's largely symbolic and perhaps unnecessary, but it doesn't actively hurt to have here.
    //
    // We take a `*mut Buffer` instead of `&'a mut Buffer` to avoid the need to construct full
    // references to the buffer inside the caller. They would then be aliased mutable references,
    // which is maybe not great.
    unsafe fn index<'a>(buf: *mut Buffer, pos: TermPos, _: PhantomData<&'a ()>) -> &'a mut Cell {
        let this = &mut *buf;

        // We need to convert everythig to `usize`s first because - even though the dimensions are
        // guaranteed to be within the maximum terminal size - their product might not be.
        let idx = (this.size.width.get() as usize) * (pos.row as usize) + (pos.col as usize);

        &mut this.inner[idx]
    }

    /// Writes the content of the buffer to the provided writer
    ///
    /// This is typically used with [`stdout()`], but may be given something else, for testing.
    ///
    /// If this function produces an error, no guarantees are made about the status of the writer
    /// afterwards.
    ///
    /// [`stdout()`]: io::stdout
    pub async fn draw(&mut self, mut writer: impl AsyncWrite + Unpin) -> io::Result<()> {
        // TODO-ALG:
        // This is incredibly naïve at the moment, and ignores most of the benefit of handling
        // writing from one central place. This should be updated to an intelligent algorithm
        // -- maybe have a look at what tui-rs does?

        // Store all of our output into a temporary buffer, so that we ensure it outputs quickly
        let mut buf: Vec<u8> = Vec::new();

        for row_idx in 0..self.size.height() as usize {
            let start = row_idx * (self.size.width() as usize);
            let end = start + (self.size.width() as usize);

            Buffer::draw_line(&mut buf, row_idx, &self.inner[start..end]);
        }

        writer.write(&buf).await?;
        writer.flush().await?;

        Ok(())
    }

    fn draw_line(buf: &mut impl Write, row_idx: usize, cells: &[Cell]) {
        use crossterm::cursor::MoveTo;

        let prefix = MoveTo(0, row_idx as u16);

        let ansi_strings = (cells.iter())
            .map(|cell| match cell.symbol.as_ref() {
                Some(s) => cell.style.paint(s.as_str()),
                None => cell.style.paint(" "),
            })
            .collect::<Vec<_>>();

        write!(buf, "{}{}", prefix, ANSIStrings(&ansi_strings)).unwrap();
    }
}

impl Cell {
    /// Initializes a blank `Cell`
    fn new() -> Self {
        Cell {
            symbol: None,
            style: Style::default(),
            previous: None,

            // We always want to start with indicating that `changed` is true, just to ensure that
            // we get a clean reset when the terminal is divided differently.
            changed: true,
        }
    }

    /// Updates the `Cell` with the new value
    fn update(&mut self, symbol: Option<Symbol>, style: Style) {
        use std::mem::replace;

        // If nothing's changed from before, we don't need to do anything
        if let Some((old_symbol, old_style)) = self.previous.as_ref() {
            if &symbol == old_symbol && &style == old_style {
                return;
            }
        }

        let old_symbol = replace(&mut self.symbol, symbol);
        let old_style = replace(&mut self.style, style);

        // If the preious symbol and style were the ones last printed, we'll store them as such
        if !self.changed {
            self.previous = Some((old_symbol, old_style));
        }

        self.changed = true;
    }
}
