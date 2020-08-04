//! A supermodule of the various cursor modes, along with necessary types and abstractions
//!
//! This module is best defined by a discussion about what a "mode" actually is. For the purposes
//! of this module, a mode is an abstract interface: a set of ways in which key-events may be turned
//! into actions, where the set of possible actions is represented by [`Cmd`]s. This corresponds to
//! the [`try_handle`] method on the [`Mode`] trait.
//!
//! The set of available modes is intentionally limited (See: [Adding new modes]) so that other
//! simplifications can be made. These happen in places that would be difficult to handle
//! otherwise, like configuration.
//!
//! ## Adding new modes
//!
//! Adding modes must be done internally (not through config files), but there thankfully shouldn't
//! be many existing files in need of editing. There are essentially two stages to this process:
//! adding in the definition of and the support for the new mode, and actually integrating it.
//! Integration may take a variety of forms, from editing config files to changing the source of
//! individual [`View`]s.
// TODO: Note: Config files are currently half-baked; this is not actually available.
// TODO: Explain how to add configs (or reference the config module)
//!
//! The only *required* change to existing files, is adding a single line in 'src/mode/mod.rs',
//! where this documentation is defined. That line is marked with `@ADD-MODE`, and is part of a
//! (relatively) large macro expansion. As such, there are only three items that must be provided -
//! to explain them, we'll look at the entry for "normal" mode.
//!
//! The line looks something like this:
//! ```rust
//! modes! {
//!     // -- snip --
//!     pub enum Modes<T, Conf> {
//!         Normal/normal: normal::Mode<T, Conf>,
//!         // -- snip --
//!     }
//!
//!     // -- snip --
//! }
//! ```
//!
//! The line has three parts: the "proper name" of the mode (`Normal`), the sub-module it resides
//! in (`normal`), and the actual mode *type* relative to the current scope (`normal::Mode<T>`). It
//! is customary to name the public type implementing [`Mode`] as `Mode` itself in the sub-module.
//! This allows imports like:
//! ```
//! use mode::normal::Mode;
//! ```
//! instead of `use mode::normal::NormalMode` or `use mode::NormalMode`.
//!
//! The proper name of the mode is used as the name of the coresponding variants of [`Modes`] and
//! [`ModeKind`], and is produced by the `modes` macro (internal).
//!
//! [`Cmd`]: enum.Cmd.html
//! [`try_handle`]: trait.Mode.html#tymethod.try_handle
//! [`Mode`]: trait.Mode.html
//! [Adding new modes]: #adding-new-modes
//! [`View`]: ../view/trait.View.html
//! [`Modes`]: enum.Modes.html
//! [`ModeKind`]: enum.ModeKind.html

use crate::config::ConfigPart;
use crate::event::KeyEvent;
use crate::utils::{XFrom, XInto};
use serde::{Deserialize, Serialize};

#[macro_use]
mod macros;
pub mod config;
pub mod handler;

pub use handler::Handler;

// This macro is provided in 'macros.rs'. Many methods are provided there as well.
modes! {
    /// A stand-in type for any of the available modes defined in this module
    ///
    /// This is used as a concrete representation so that that we can statically define the list of
    /// available modes, instead of validating whether a mode *exists* at runtime. It should be
    /// noted that this system is not perfect; attempts to transition to modes that are not allowed
    /// can happen (see: [`ModeSet`]).
    // Note: This type is broken down in a fairly simple way. On each line below, we have three
    // items to look at. Taking the first line as an example:
    //   Normal/normal: normal::Mode<T>,
    //    ^^^^   ^^^^    ^^^^^^^^^^^^^
    // `Normal` gives the name of the variant in `Modes` and in `ModeKind` - in `ModeKind` the
    // variant is empty, but here it is a single-element tuple containing `normal::Mode<T>`, the
    // type given by the last item.
    //
    // The middle item, `normal`, gives the corresponding field name in `ModeSet`, as well as the
    // name of the module to import.
    pub enum Modes<T, Conf> {
        Normal/normal: normal::Mode<T, Conf>,
        Insert/insert: insert::Mode<T, Conf>,
        // @ADD-MODE -- Add your new mode here! For more info, see the module-level documentation
    }

    /// An enumeration over the different types of available modes.
    ///
    /// This type implements `XInto<Modes<T>>` for any `T` (see: [`XInto`]) so that it may be
    /// easily converted. (Note: this is subject to change - it may be reverted simply to `Into`,
    /// as the extra flexibility provided by `XInto` is not currently needed.)
    #[derive(Debug, Copy, Clone, Serialize, Deserialize)]
    // An explanation of the type produced is in a line-comment above `Modes` ^
    pub enum ModeKind = ...;

    /// A marker type to indicate which modes may be transitioned to by a handler
    ///
    /// This is primarily used by the [`Handler`] type, but is defined as part of a monolithic
    /// macro, so it is defined here.
    ///
    /// It is unfortunate that errors from attempting to transition between modes occur at runtime,
    /// but there is not any other (practical) way to ensure this.
    ///
    /// [`Handler`]: handler/struct.Handler.html
    #[derive(Copy, Clone, Debug)]
    // An explanation of the type produced is in a line-comment above `Modes` ^
    pub struct ModeSet = ...;
}

/// A general trait for abstracting over modes
///
/// For more information on what is meant by a "mode", refer to the [module-level documentation].
///
/// [module-level documentation]: index.html
pub trait Mode<Meta, Conf>: Default + XInto<Modes<Meta, Conf>>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<Meta> + ConfigPart,
{
    /// The name of the mode, if available. This string's length should be equal to its displayed
    /// width -- the simplest way to ensure this is the case is to compose it entirely of ASCII
    /// graphic characters.
    const NAME: Option<&'static str>;

    /// Attmepts to handle the key input, returning a list of commands to be executed if
    /// successful, or an explanation as to why it was unsuccessful (Note: [`Error`] is used to
    /// represent fairly routine items).
    ///
    /// [`Error`]: enum.Error.html
    fn try_handle(&mut self, key: KeyEvent) -> Result<Vec<Cmd<Meta>>, Error>;

    /// Returns the requested cursor styling. For more information, see [`CursorStyle`].
    ///
    /// [`CursorStyle`]: struct.CursorStyle.html
    fn cursor_style(&self) -> CursorStyle;

    /// Returns whether the mode is currently expecting input
    ///
    /// This should return true if - and only if - the mode is currently in the process of
    /// interpreting a sequence of inputs
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
    Scroll {
        kind: ScrollKind,
        amount: usize,
        /// Whether to keep the cursor at the same position on the screen while scrolling the text
        /// beneath it - if true, the cursor will also move with the scrolling.
        lock_cursor: bool,
    },

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
    fn xfrom(cmd: Cmd<S>) -> Self {
        use Cmd::{
            ChangeMode, Cursor, Delete, EndEditBlock, EnterMode, ExitMode, Insert, Other, Redo,
            Scroll, StartEditBlock, Undo,
        };

        match cmd {
            Cursor(m, n) => Cursor(m, n),
            Scroll {
                kind,
                amount,
                lock_cursor,
            } => Scroll {
                kind,
                amount,
                lock_cursor,
            },
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

/// The set of unsucessful return signals allowed as a result of [`Mode::try_handle`] or from
/// [`Handler::handle`].
///
/// It should be noted that some of the variants here are not errors in the traditional sense;
/// `NeedsMore` and `NoSuchCommand` are normal returns to indicate status and are used as such.
/// Conversely, `Failure` and `IllegalMode` are properly errors and should be reported to the user
/// as such.
///
/// The only error related to [`Handler`] is `IllegalMode`.
///
/// [`Mode::try_handle`]: trait.Mode.html#tymethod.try_handle
/// [`Handler::handle`]: struct.Handler.html#method.handle
/// [`Handler`]: handler/struct.Handler.html
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
    // TODO: Replace usage of this with `ByLines`
    CurrentLine { amount: usize },
}

/// A helper type to represent a logical direction on the screen
///
/// This is used in a variety of contexts, both within this module and outside it. It's used
/// immediately here in [`ScrollKind::ByDirection`], but is also present in
/// [`crate::views::OutputSignal`] where it serves a similar purpose.
///
/// [`ScrollKind::ByDirection`]: enum.ScrollKind.html#variant.ByDirection
/// [`crate::views::OutputSignal`]: ../views/enum.OutputSignal.html
/// [`Open`]: ../views/enum.OutputSignal.html#variant.Open
/// [`ShiftFocus`]: ../views/enum.OutputSignal.html#variant.ShiftFocus
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

    /// A movement to a certain line of text, given by its number (Note: starting from one)
    ///
    /// The given value here might be out of bounds. It is up to the user to determine how to
    /// handle this if it is the case. Additionally, there is no specification as to where on the
    /// line the movement is to - this may be chosen by the user as well.
    ToLine(usize),

    /// A movement to a certain portion down the screen, given by a value between 0 and 1.
    ScreenLine(f64),

    /// A movement to the top line of the file. Like `ToLine`, this may move to any point on the
    /// line.
    ToTop,

    /// A movement to the bottom line of the file. Like `ToLine`, this may move to any point on the
    /// line.
    ToBottom,

    /// A movement to the matching delimeter under the current cursor, wherever that may be
    ///
    /// This movement should fail (fully - ignoring any early failure mechanics) if there is not a
    /// recognized delimeter under the cursor, or if the delimeter is not matched.
    ///
    /// The set of available delimeters is left up to the implementor - this may differ by
    /// the language of the file (e.g. HTML might allow multi-character delimeters). Note: this is
    /// currently unimplemented, but is planned for the future.
    MatchingDelim,

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

    /// Matches exactly on a character as the second character in the pair
    ToChar(char),
}

impl CharPredicate {
    pub fn matches(&self, fst: Option<char>, snd: Option<char>) -> bool {
        use CharPredicate::{BigWordEnd, BigWordStart, ToChar, WordEnd, WordStart};

        // All of the functions referenced here are defined following the end of this block.
        return match self {
            WordEnd => word_end(fst, snd),
            WordStart => word_start(fst, snd),
            BigWordEnd => big_word_end(fst, snd),
            BigWordStart => big_word_start(fst, snd),
            &ToChar(c) => snd == Some(c),
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
