//! A supermodule of the various cursor modes, along with necessary types and abstractions
//!
//! This module is best defined by a discussion about what a "mode" actually is. For the purposes
//! of this module, a mode is an interface: a set of ways in which
// FIXME: Document

use crate::event::KeyEvent;
use crate::prelude::*;

pub mod handler;
pub mod insert;
pub mod normal;

#[macro_use]
mod macros;

pub use handler::Handler;

// This macro is provided in './macros.rs' - Doc comments for the produced types are also given
// there
modes! {
    #[derive(Debug, Copy, Clone, Serialize, Deserialize)]
    pub enum ModeKind = ...;

    #[derive(Copy, Clone, Debug)]
    pub struct ModeSet = ...;
    pub enum Modes<T> {
        Normal/normal: normal::Mode<T>,
        Insert/insert: insert::Mode<T>,
    }
}

/// A general trait for abstracting over modes
///
/// For more information on what is meant by a "mode", refer to the [module-level documentation].
///
/// [module-level documentation]: index.html
pub trait Mode<T>: Default + XInto<Modes<T>> {
    const NAME: Option<&'static str>;

    // FIXME: Documentation
    fn try_handle(&mut self, key: KeyEvent) -> Result<Vec<Cmd<T>>, Error>;
    fn cursor_style(&self) -> CursorStyle;
    fn expecting_input(&self) -> bool;
}

/// The possible types of instructions that `Mode`s may give
///
/// Most of the documentation is provided in the individual types referenced in the variants.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Cmd<T> {
    /// A cursor movement, given by the type of movement and a number of repetitions
    Cursor(Movement, usize),

    /// A scrolling movement, given by the type of scrolling and number of repetitions
    Scroll(ScrollKind, usize),

    /// An insertion of the given string at the current cursor position
    Insert(String),

    /// A deletion
    Delete(DeleteKind),

    /// A request to undo the last 'n' changes
    Undo(usize),

    /// A request to redo the 'n' most recently undone changes
    Redo(usize),

    /// A request to start a new "edit block" - a set of applied diffs that are treated as a single
    /// contiguous edit.
    StartEditBlock,

    /// A request to end the edit block
    EndEditBlock,

    /// A request to exit the current mode, returning to whatever the previous mode was
    ExitMode,

    /// Represents a request to change from the current mode the given one. This serves as the
    /// logical 'push' to `ExitMode`'s 'pop'; `EnterMode` is explicitly a request to push the
    /// following mode to the top of some sort of stack, so that it may return via `ExitMode` to
    /// the current one.
    EnterMode(ModeKind),

    /// Represents a request to change from the current mode to the given one *without* adding
    /// anything to the stack of modes.
    ChangeMode(ModeKind),

    /// Any other command that might be provided
    ///
    /// This is notably used in the case of [`views::Cmd`], which defines a type alias for
    /// `Cmd<views::MetaCmd<T>>`.
    ///
    /// [`views::Cmd`]: ../views/type.Cmd.html
    Other(T),
}

impl<S: XInto<T>, T> XFrom<Cmd<S>> for Cmd<T> {
    #[rustfmt::skip]
    fn xfrom(cmd: Cmd<S>) -> Self {
        use Cmd::{ChangeMode, Cursor, Delete, EnterMode, ExitMode, Insert, Other, Scroll, Undo, Redo, StartEditBlock, EndEditBlock};

        match cmd {
            Cursor(m, n) => Cursor(m, n),
            Scroll(d, n) => Scroll(d, n),
            Insert(s) => Insert(s),
            Delete(kind) => Delete(kind),
            StartEditBlock => StartEditBlock,
            EndEditBlock => EndEditBlock,
            ExitMode => ExitMode,
            EnterMode(kind) => EnterMode(kind),
            ChangeMode(kind) => ChangeMode(kind),
            Undo(n) => Undo(n),
            Redo(n) => Redo(n),
            Other(s) => Other(s.xinto()),
        }
    }
}

/// The set of errors allowed as a result of [`Mode::try_handle`] or from [`Handler::handle`]. The
/// only error related to [`Handler`] is from a mode change being denied.
///
/// [`Mode::try_handle`]: trait.Mode.html#tymethod.try_handle
/// [`Handler::handle`]: struct.Handler.html#method.handle
/// [`Handler`]: struct.Handler.html
#[derive(Debug, Clone)]
pub enum Error {
    /// Signals that the mode is unable to produce a command given the current input, but may be
    /// able to if given more.
    NeedsMore,

    /// Represents a failure to parse the sequence of input; the mode was unable to produce a
    /// command from the given input
    NoSuchCommand,

    /// Represents a value that is actually an error, and should be reported to the user in some
    /// fashion. This may be due to a variety of circumstances, either due to the user's actions or
    /// internal state.
    ///
    /// For simplicity, this string must consist entirely of ascii characters.
    Failure { msg: String },

    /// Represents an attempt to switch to a mode that was denied
    IllegalMode(ModeKind),
}

/// The current information about cursor styling
///
/// This type is currently limited, but will be expanded in the future as support for other
/// Vim-inspired modes is added. The fields will always be kept public.
#[derive(Copy, Clone, Debug)]
pub struct CursorStyle {
    /// Whether the cursor should be allowed immediately beyond the end of the line
    ///
    /// This is best described with images. Suppose we have the following line of text, with the
    /// cursor at the marked position:
    /// ```text
    /// """
    /// So long, and thanks for all the fish
    /// """                                 ^
    ///                                  cursor
    /// ```
    /// Note that there is no trailing whitespace in the line; the cursor is *after* the final 'h'
    /// character. Setting `allow_after` to true signifies that this is allowed; setting it to
    /// false would limit the cursor to the following rightmost position:
    /// ```text
    /// """
    /// So long, and thanks for all the fish
    /// """                                ^
    ///                                 cursor
    /// ```
    /// where the cursor occupies the same space as the letter 'h'.
    pub allow_after: bool,
}

/// The ways in which regions of text may be deleted
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum DeleteKind {
    /// A deletion where the deleted region is directly between the cursor's current position and
    /// the new position specified by the movement.
    ///
    /// Some of the fields here should be self-explanatory.
    ByMovement {
        movement: Movement,
        amount: usize,

        /// Whether to include the starting point (the current cursor position) in the deleted range
        from_inclusive: bool,
        /// Whether to include the ending point (the new cursor position) in the deleted range
        to_inclusive: bool,
    },

    /// A deletion where the deleted region covers the entirety of all lines between (inclusive) the
    /// cursor's current position and the new position specified by the movement.
    ByLines { movement: Movement, amount: usize },

    /// Deletes the entirety of the current line and the next `amount - 1` lines as well.
    CurrentLine { amount: usize },
}

/// Represents a logical direction on the screen
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum Direction {
    Up,
    Down,
    Left,
    Right,
}

/// Types of cursor movements
///
/// In addition to being used for movement, these are also used as a component of commands that may
/// be thought of as "compound commands". This is used, for example, in [`DeleteKind`].
///
/// [`DeleteKind`]: enum.DeleteKind.html
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum Movement {
    /// A constant movement up by one line
    Up,

    /// A constant movement down by one line
    Down,

    /// Represents a movement to the left within the current line
    Left(HorizMove),

    /// Represents a movement to the right within the current line
    Right(HorizMove),

    /// Represents a movement to the left that may cross lines
    LeftCross(HorizMove),

    /// Represents a movement to the right that may cross lines
    RightCross(HorizMove),
}

/// The types of scrolling actions that are available
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum ScrollKind {
    /// A scrolling movement that is given simply by its direction
    ByDirection(Direction),

    /// A scrolling movement that shifts so the cursor is in the middle of the screen. This should
    /// fail weakly - i.e. if it is not possible, the scrolling action taken should get as lose as
    /// possible to the desired outcome.
    VerticalCenter,

    /// A scrolling movement to move down by the given fraction of a page. Values given here should
    /// be between zero and one - any handlers need not fail nicely if given values outside that
    /// range.
    DownPage(f64),

    /// A scrolling movement to move up by the given fraction of a page. Values given here should
    /// be between zero and one - any handlers need not fail nicely if given values outside that
    /// range.
    UpPage(f64),
}

/// Represents a horizontal movement, regardless of direction or whether it is bounded to a single
/// line
///
/// The only noteworthy feature of this type is the distinction between `UntilFst` and `UntilSnd`.
/// Because [`CharPredicate`]s match on pairs of values, there are two possibilities for the
/// meaning of a movement to the first match of a predicate: either the first or second character
/// in the pair. `UntilFst` simply represents a movement to the first of the two values, while
/// `UntilSnd` represents a movement to the second.
///
/// But because character predicates additionally do not distinguish between directions, the
/// meaning of "first" is ambiguous. When a predicate matches on the pair `(a, b)`, `UntilFst`
/// symbolizes a movement to `a` whereas `UntilSnd` symbolizes a movement to `b`. More information
/// as to the ordering of `a` and `b` is provided in the documentation of [`CharPredicate`]. Simply
/// put, `b` will be the character that is further in the direction of movement.
///
/// [`CharPredicate`]: enum.CharPredicate.html
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum HorizMove {
    /// A constant movement of one character, left or right
    Const,

    /// A movement to the line boundary. If the movement is to the left, this symbolizes a movement
    /// to the beginning of the line. If it is to the right, it symbolizes a movement to the end of
    /// the line.
    LineBoundary,

    /// A movement to a character matching the given `char`
    ToChar(char),

    /// Described above
    UntilFst(CharPredicate),

    /// Described above
    UntilSnd(CharPredicate),
}

/// Indicates a movement until a particular predicate is matched on the surrounding characters
///
/// Character predicates based around matching on sequential pairs of characters. This is done
/// without any regard for direction, so that the same predicates may take different meanings
/// depending on the direction of movement.
///
/// The intended usage of character predicates is to use the implementation of
/// `Into<fn(Option<char>, Option<char>) -> bool>` that is provided in order to access the
/// predicate as a proper function.
///
/// ## Semantics
///
/// The corresponding functions produced by converting a value of type `CharPredicate` have the
/// signature `fn(Option<Char>, Option<char>) -> bool`. Both arguments use `None` as a method of
/// encoding invalid characters; because they cannot be used stably between different encodings,
/// it is necessary to make them opaque objects.
///
/// The first of the two characters in the pair corresponds to the "older" of the two: When moving
/// in a given direction, the second character corresponds to the character in the pair that is
/// further along in the direction of movement. The second character from one iteration will
/// typically be used as the first character in the next.
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum CharPredicate {
    /// Matches at the start of a word: a non-word character followed by a word character OR
    /// whitespace followed by a non-word character
    WordStart,

    /// Matches at the end of a word: a word character followed by a non-word character OR a
    /// non-word character followed by whitespace
    WordEnd,

    /// Matches on whitespace followed by any valid, non-whitespace character
    BigWordStart,

    /// Matches on any valid, non-whitespace character followed by whitespace
    BigWordEnd,
}

impl From<CharPredicate> for fn(Option<char>, Option<char>) -> bool {
    fn from(pred: CharPredicate) -> Self {
        use CharPredicate::{BigWordEnd, BigWordStart, WordEnd, WordStart};

        // All of the functions referenced here are defined following the end of this block.
        return match pred {
            WordEnd => word_end,
            WordStart => word_start,
            BigWordEnd => big_word_end,
            BigWordStart => big_word_start,
        };

        // `word` and `whitespace` are used as a couple primitive building blocks
        fn word(c: Option<char>) -> bool {
            match c {
                Some(c) => c.is_alphanumeric() || c == '_',
                None => false,
            }
        }
        fn whitespace(c: Option<char>) -> bool {
            match c {
                None | Some(' ') | Some('\t') | Some('\n') => true,
                _ => false,
            }
        }

        // The specification of these functions can be found in the type-level documentation

        fn word_end(fst: Option<char>, snd: Option<char>) -> bool {
            (word(fst) && !word(snd)) || (!whitespace(fst) && whitespace(snd))
        }

        fn word_start(fst: Option<char>, snd: Option<char>) -> bool {
            (!word(fst) && word(snd)) || (whitespace(fst) && !whitespace(snd))
        }

        fn big_word_end(fst: Option<char>, snd: Option<char>) -> bool {
            !whitespace(fst) && whitespace(snd)
        }

        fn big_word_start(fst: Option<char>, snd: Option<char>) -> bool {
            whitespace(fst) && !whitespace(snd)
        }
    }
}
