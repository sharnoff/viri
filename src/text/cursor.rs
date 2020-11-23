//! Wrapper module for the [`Cursor`] type
//!
//! This is a private module, so most of the documentation is provided on types here. The
//! [`Cursor`] type is just a newtype over the internal enum that we use.

// TODO-DOC
#[derive(Debug, Clone)]
pub struct Cursor(Kind);

#[derive(Debug, Clone)]
enum Kind {
    Single(Selection),
    Multi(Vec<Selection>),
}

#[derive(Debug, Copy, Clone)]
enum Selection {
    Point(Pos),
    Range(Pos, Pos),
}

#[derive(Debug, Copy, Clone)]
pub struct Pos {
    pub byte: usize,
    pub row: usize,
    pub col: usize,
}

impl Cursor {
    /// Creates a new, single-point [`Cursor`] at the start of the text
    pub fn new_single() -> Cursor {
        Cursor(Kind::Single(Selection::Point(Pos {
            byte: 0,
            row: 0,
            col: 0,
        })))
    }
}
