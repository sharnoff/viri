//! Movement-related `KeyEvent` parsing for "normal" mode

use std::collections::HashMap;

use crate::config::prelude::*;
use crate::event::KeyEvent;
use crate::views::Movement;

use super::ParseResult::{Failed, Success};
use super::{ParseResult, ParseState, Priority};

/// The base parser for wrapping different types of movements
///
/// This parser by itself does not return a `Cmd`; it simply returns the movement so that whatever
/// is using may manipulate the movement as desired.
pub(super) enum Parser {
    Nothing,
}

impl Default for Parser {
    fn default() -> Self {
        Self::Nothing
    }
}

impl ParseState for Parser {
    type Output = Movement;

    fn add(&mut self, key: KeyEvent) -> ParseResult<Movement> {
        match self {
            Self::Nothing => (),
        }

        // Currently just simple things
        let cfg = Config::global();
        let (priority, movement) = match cfg.keys.get(&key) {
            Some(&(p, m)) => (p, m),
            None => {
                return Failed;
            }
        };

        // TODO: This should just return the movement, using a secondary wrapping "numerical"
        // parser to handle the rest
        Success(priority, movement)
    }

    fn max_priority(&self) -> Option<Priority> {
        match self {
            Self::Nothing => Config::global().keys.values().map(|(p, _)| *p).max(),
        }
    }
}

static_config! {
    static GLOBAL;
    pub struct Builder;
    pub struct Config {
        pub(super) keys: HashMap<KeyEvent, (Priority, Movement)> = default_keybindings(),
    }
}

#[rustfmt::skip]
fn default_keybindings() -> HashMap<KeyEvent, (Priority, Movement)> {
    use crate::views::CharPredicate::{BigWordEnd, BigWordStart, WordEnd, WordStart};
    use crate::views::HorizontalMove::{Const,LineBoundary, UntilFst, UntilSnd};
    use crate::views::Movement::{Down, Left, Right, Up};

    use super::Priority::Builtin;

    let keys = vec![
        // Directional movement
        (KeyEvent::none('k'), (Builtin, Up)),
        (KeyEvent::none('j'), (Builtin, Down)),
        (KeyEvent::none('h'), (Builtin, Left(Const, false))),
        (KeyEvent::none('l'), (Builtin, Right(Const, false))),

        // By words
        (KeyEvent::none('b'), (Builtin, Left(UntilFst(WordEnd), true))),
        (KeyEvent::none('B'), (Builtin, Left(UntilFst(BigWordEnd), true))),
        (KeyEvent::none('w'), (Builtin, Right(UntilSnd(WordStart), true))),
        (KeyEvent::none('W'), (Builtin, Right(UntilSnd(BigWordStart), true))),
        (KeyEvent::none('e'), (Builtin, Right(UntilFst(WordEnd), true))),
        (KeyEvent::none('E'), (Builtin, Right(UntilFst(BigWordEnd), true))),

        // Relative to the line beginning/end
        (KeyEvent::none('0'), (Builtin, Left(LineBoundary, true))),
        (KeyEvent::none('$'), (Builtin, Right(LineBoundary, true))),
    ];

    keys.into_iter().collect()
}
