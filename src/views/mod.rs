//! This module defines the different types of things that you can do in the
//! editor - we refer to them as "Views".
//!
//! Customizing this may be most easily done through adding a Rust file to this
//! directory and including it as a sub-module. From there, you can add your
//! custom `View` into the `init` function below, which registers each
//! constructor with a unique name.
//!
//! For example:
//!
//! The startup view is given by the `create_view` function, which should return
//! a `View` given a set of command-line arguments.
//!
//! There is much more detail given in the file itself about the format of the
//! internal system and how to add your own types. Please refer there.

// Yup! Right here!
//
// For starters, Everything in this file is marked with headers, and their names
// only appear at those locations. They are as follows:
//   Header 0: Imports
//   Header 1: Initialization
//   Header 2: Type Definitions
// That should be all you need to get started!

// These are system-type imports - trait definitions, utilities, and things.
// They're here to allow everything else to function.
use serde::{Deserialize, Serialize};

use crate::container;
use crate::runtime::{Painter, TermSize};
// mod modes;

//-/////////////////////////////////////////////////////////////////////////-//
// Header 0: Imports                                                         //
//                                                                           //
// This is what you'd expect - it's where we put the 'use' statements for    //
// the various sub-modules used in this file.                                //
//                                                                           //
// Builtin ones are marked; change those with caution. Adding your own       //
// should be simple. If you you're importing something other than a sub-     //
// module, that should go at the top of the file, with the rest.             //
//                                                                           //
//-/////////////////////////////////////////////////////////////////////////-//

// Builtin modules:
mod buffer;
mod file;
mod modes;

// mod your_mod;

//-/////////////////////////////////////////////////////////////////////////-//
// Header 1: Initialization                                                  //
//                                                                           //
// This section defines the various functions that are used for setting up   //
// the various `View`s and the ability to switch between them.               //
//                                                                           //
// General overview (TODO)                                                   //
//                                                                           //
//-/////////////////////////////////////////////////////////////////////////-//

/// The macro expansion that generates an enum over the possible types of `View`s.
/// There's more information in that file itself - the macro is actually *very* simple.
#[macro_use]
mod macros;

viewkind! {
    pub enum ViewKind {
        File: file::FileView,
        // Foo: your_mod::Foo,
    }
}

// Defined in 'src/config.rs'. The real function signature isn't *quite* this.
/*
read_config! {
    pub fn read_config(cfg_str: &str) {
        struct {
            file: file::FileConfig,
        }
    }
}
*/

//-/////////////////////////////////////////////////////////////////////////-///
// Header 2: Type Definitions                                                 //
//                                                                            //
// If you're writing your own `View`, this section contains all of the        //
// things you could need to know. (Note that there is also documentation      //
// available on docs.rs as well.) It's unlikely, however, that you'll be      //
// doing something that actually warrants changing part of this section; it   //
// should have most - if not all - of the flexibility that you could be       //
// looking for.                                                               //
//                                                                            //
// As a general overview:                                                     //
//                                                                            //
// There are two traits that matter here: `View` and `ViewContainer`. When    //
// using multiple splits, there will be many of the first, existing in a tree //
// of `View`s conaining other `View`s. (This happens because splits are       //
// themselves just `View`s.)                                                  //
//     The second trait will only have one instance at a time; it serves as a //
// wrapper for the top-level `View` to handle the interactions between the    //
// editor's runtime and the tre of `View`s.                                   //
//                                                                            //
//-////////////////////////////////////////////////////////////////////////-///

/// The central trait for the equivalent of "buffers" or "splits" from other editors
pub trait View {
    /// Re-draws the `View`, using the provided painter to draw to the screen
    ///
    /// The painter handles drawing to the correct location on the screen.
    fn refresh(&mut self, painter: &Painter);

    /// Sets the position of the cursor through the painter
    fn refresh_cursor(&self, painter: &Painter);

    /// Gives the text to display at the bottom-left of the screen
    ///
    /// The second index in the tuple is the width in columns of the text. Note that this function
    /// is distinct from the bottom bar provided by the [`Container`]; that can be set with the
    /// appropriate [`OutputSignal`].
    ///
    /// If `None` is returned, the text that was previously there will not be changed. The default
    /// implementation simply does this.
    ///
    /// [`Container`]: ../container/struct.Container.html
    /// [`OutputSignal`]: enum.OutputSignal.html
    fn bottom_left_text(&mut self) -> Option<(String, usize)> {
        None
    }

    /// Gives the text to display at the bottom-right of the screen
    ///
    /// The second index in the tuple is the width in columns of the text.
    ///
    /// If `None` is returned, the text that was previously there will not be changed. The default
    /// implementation simply does this.
    fn bottom_right_text(&mut self) -> Option<(String, usize)> {
        None
    }

    /// Returns the `View`'s preference for the bottom-left vs. bottom-right text overwriting each
    /// other.
    ///
    /// If true, the bottom-left text will be given precedence when there is not enough room to fit
    /// the results from both [`bottom_left_text`] and [`bottom_right_text`]. The default
    /// implementation returns `true`, but this is not guaranteed to be stable and should be
    /// overwritten when implementing both `bottom_left_text` and `bottom_right_text`.
    ///
    /// [`bottom_left_text`]: #tymethod.bottom_left_text
    /// [`bottom_right_text`]: #tymethod.bottom_right_text
    fn prefer_bottom_left(&self) -> bool {
        false
    }

    /// Resizes the internal representation of the `View`
    ///
    /// Note that this method *should not* write to the display directly. It is merely to query the
    /// `View` about what changes will be required due to resizing.
    fn resize(&mut self, size: TermSize) -> OutputSignal;
}

/// `View`s that may be concretely instantiated
///
/// All [`View`]s implement this trait, with the exception of `ViewBuffer`, which cannot be used
/// directly.
pub trait ConcreteView: View + SignalHandler {
    /// Returns the `ViewKind` associated with the `View`
    fn kind(&self) -> ViewKind;
}

/// Helper for `ConcreteView`
///
/// Because `ConcreteView` is required elsewhere to be object-safe, this trait is defined to allow
/// instantiating views. It is used in the [`to_view`] method on `ViewKind`.
///
/// [`to_view`]: enum.ViewKind.html#method.to_view
pub trait ConstructedView: ConcreteView {
    /// Initializes the `View` with the given arguments and size
    ///
    /// Formalizing the arguments is currently a work in progress.
    // TODO: ^ see above
    fn init<S: AsRef<str>>(size: TermSize, args: &[S]) -> Self;
}

/// Types that can handle `Container` signals
///
/// This trait marks types that can receive the signals provided by the top-level [`Container`] and
/// produce the required view [`OutputSignal`].
///
/// [`Container`]: ../container/struct.Container.html
/// [`OutputSignal`]: enum.OutputSignal.html
pub trait SignalHandler {
    fn try_handle(&mut self, signal: container::Signal) -> OutputSignal;
}

/// The possible types of instructions that can be given to Views
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Cmd<E> {
    /// A cursor movement, given by the direction and an optional quantity
    ///
    /// If not given, the amount to move defaults to 1. If the cursor movement goes off-screen, the
    /// behavior will be determined by the configuration.
    Cursor(Movement, Option<usize>),

    /// A scroll movement, given by the direction and an optional quantity
    ///
    /// If not given, the amount to scroll defaults to 1.
    Scroll(Direction, Option<usize>),

    /// A request to close the *current view*
    TryClose(ExitKind),

    /*
    /// A request to exit the *entire* editor
    TryExit(ExitKind),
    */
    /// Any other commands that may be used, though not directly accounted for
    Extra(E),

    /// A set of commands to be executed in sequence
    Chain(Vec<Cmd<E>>),
}

// `None` defaults to HorizontalMove::Const(1)
#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum Movement {
    Up,
    Down,
    // Horizontal movement + whether it can cross lines
    Left(HorizontalMove, bool),
    Right(HorizontalMove, bool),
}

#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum HorizontalMove {
    // A constant movement of 1 to either the left or the right
    Const,
    LineBoundary,
    // `UntilFst` and `UntilSnd` are slightly different; given a match on the pair (a,b), the
    // second indicates that the movement should be all the way to `b`, whereas the first is only
    // to `a`.
    UntilFst(CharPredicate),
    UntilSnd(CharPredicate),
}

#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum CharPredicate {
    // Stops at the end of a word
    WordEnd,
    WordStart,
    BigWordEnd,
    BigWordStart,
}

/// Represents a logical direction on the screen
#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum Direction {
    Up,
    Down,
    Left,
    Right,
}

/// The ways in which we can change the contents of a buffer
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WriteKind {
    InsertAtCursor(String),
    // InsertBelow(String),
    // InsertAbove(String),
}

/// Distinct from `runtime::Signal` or a `container::Signal`, this communicates between a `View`
/// and its parent, eventually leading up to the host `Container`.
#[derive(Clone, Debug)]
pub enum OutputSignal {
    NeedsRefresh(RefreshKind),
    SaveBottomBar,
    SetBottomBar {
        prefix: Option<char>,
        value: String,
        width: usize,
        // The column to place the cursor there. If the cursor should not be in the bottom bar,
        // then this should be emulated with the `BottomTextUpdate` signal and an implementation of
        // `View::bottom_left_text`.
        //
        // Note that this column *does* include the prefix, and starts from 0.
        //
        // If this field is `None`, the input mode will not be changed
        cursor_col: Option<usize>,
    },
    LeaveBottomBar,
    ClearBottomBar,
    Close,
    NoSuchCmd,
    WaitingForMore,
    Nothing,
    Chain(Vec<Self>),
}

/// How much of a refresh needs to be done?
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RefreshKind {
    // Ranked in ascending order of magnitude.
    Cursor,
    BottomText,
    Inner,
    Full,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ExitKind {
    ReqSave,
    NoSave,
}

// TODO: Add warnings, etc here
#[derive(Clone, Debug)]
pub enum ExitSignal {
    Nothing,
}

#[derive(Copy, Clone, Debug)]
pub struct CursorStyle {
    pub allow_after: bool,
}

impl OutputSignal {
    pub fn is_nothing(&self) -> bool {
        match self {
            Self::Nothing => true,
            _ => false,
        }
    }

    pub fn waiting_for_more(&self) -> bool {
        match self {
            Self::WaitingForMore => true,
            Self::Chain(v) => v.iter().any(Self::waiting_for_more),
            _ => false,
        }
    }
}

impl<E> Cmd<E> {
    fn from<T: Into<E>>(cmd: Cmd<T>) -> Self {
        use Cmd::*;

        match cmd {
            Cursor(d, n) => Cursor(d, n),
            Scroll(d, n) => Scroll(d, n),
            TryClose(k) => TryClose(k),
            Extra(t) => Extra(t.into()),
            Chain(v) => Chain(v.into_iter().map(Self::from).collect()),
        }
    }

    fn into<T: From<E>>(self) -> Cmd<T> {
        Cmd::from(self)
    }
}

// `None` symbolizes an invalid character. Note that line breaks always give the character '\n'
impl From<CharPredicate> for fn(Option<char>, Option<char>) -> bool {
    fn from(pred: CharPredicate) -> Self {
        use CharPredicate::{BigWordEnd, BigWordStart, WordEnd, WordStart};

        return match pred {
            WordEnd => word_end,
            WordStart => word_start,
            BigWordEnd => big_word_end,
            BigWordStart => big_word_start,
        };

        // Returns true if the character is part of a word.
        // TODO: Allow this to be customized
        fn word(c: Option<char>) -> bool {
            match c {
                Some(c) => c.is_alphanumeric() || c == '_',
                None => false,
            }
        }

        fn whitespace(c: Option<char>) -> bool {
            match c {
                // TODO: When more whitespace is *actually* added, this should be updated
                None | Some(' ') | Some('\t') | Some('\n') => true,
                _ => false,
            }
        }

        // returns true iff fst is part of a word and snd is not
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
