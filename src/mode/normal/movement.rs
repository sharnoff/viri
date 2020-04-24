//! Movement-related `KeyEvent` parsing for "normal" mode

use std::collections::HashMap;

use crate::config::prelude::*;
use crate::event::KeyEvent;
use crate::mode::Movement;

use super::ParseResult::{Failed, Success};
use super::{ParseResult, ParseState, Priority};

/// The base parser for wrapping different types of movements
///
/// This parser by itself does not return a `Cmd`; it simply returns the movement so that whatever
/// is using may manipulate the movement as desired.
pub enum Parser {
    Nothing,
}

impl Parser {
    pub fn new() -> Self {
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
        pub keys: HashMap<KeyEvent, (Priority, Movement)> = default_keybindings(),
    }
}

#[rustfmt::skip]
fn default_keybindings() -> HashMap<KeyEvent, (Priority, Movement)> {
    use crate::mode::CharPredicate::{BigWordEnd, BigWordStart, WordEnd, WordStart};
    use crate::mode::HorizMove::{Const,LineBoundary, UntilFst, UntilSnd};
    use crate::mode::Movement::{Down, Left, Right, Up, LeftCross, RightCross};

    use super::Priority::Builtin;

    let keys = vec![
        // Directional movement
        (KeyEvent::none('k'), (Builtin, Up)),
        (KeyEvent::none('j'), (Builtin, Down)),
        (KeyEvent::none('h'), (Builtin, Left(Const))),
        (KeyEvent::none('l'), (Builtin, Right(Const))),

        // By words
        (KeyEvent::none('b'), (Builtin, LeftCross(UntilFst(WordEnd)))),
        (KeyEvent::none('B'), (Builtin, LeftCross(UntilFst(BigWordEnd)))),
        (KeyEvent::none('w'), (Builtin, RightCross(UntilSnd(WordStart)))),
        (KeyEvent::none('W'), (Builtin, RightCross(UntilSnd(BigWordStart)))),
        (KeyEvent::none('e'), (Builtin, RightCross(UntilFst(WordEnd)))),
        (KeyEvent::none('E'), (Builtin, RightCross(UntilFst(BigWordEnd)))),

        // Relative to the line beginning/end
        (KeyEvent::none('0'), (Builtin, LeftCross(LineBoundary))),
        (KeyEvent::none('$'), (Builtin, RightCross(LineBoundary))),
    ];

    keys.into_iter().collect()
}
