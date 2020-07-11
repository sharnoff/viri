//! Movement-related `KeyEvent` parsing for "normal" mode

use super::ParseResult::{Failed, NeedsMore, Success};
use super::{ParseResult, ParseState, Priority};
use crate::config::{Build, ConfigPart};
use crate::event::{KeyCode, KeyEvent, KeyModifiers};
use crate::mode::{CharPredicate, HorizMove, Movement};
use crate::utils::XFrom;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, MutexGuard};

/// The base parser for wrapping different types of movements
///
/// This parser by itself does not return a `Cmd`; it simply returns the movement so that whatever
/// is using may manipulate the movement as desired.
pub enum Parser {
    Nothing,
    /// This variant indicates that the parser is looking for the next character. The movement here
    /// must have a `HorizMove`
    Char(Priority, Movement),
}

impl Parser {
    pub fn new() -> Self {
        Self::Nothing
    }
}

impl ParseState for Parser {
    type Output = Movement;

    fn add(&mut self, key: KeyEvent) -> ParseResult<Movement> {
        use Movement::{Left, LeftCross, Right, RightCross};

        match self {
            Self::Nothing => (),
            Self::Char(priority, mv) => {
                let ch = match key.code {
                    KeyCode::Char(c) => c,
                    _ => return Failed,
                };

                // No control keys here
                if key.mods != KeyModifiers::NONE && key.mods != KeyModifiers::SHIFT {
                    return Failed;
                }

                let pred = CharPredicate::ToChar(ch);

                let f = match mv {
                    Left(_) => Left,
                    Right(_) => Right,
                    LeftCross(_) => LeftCross,
                    RightCross(_) => RightCross,
                    _ => unreachable!(),
                };

                let g = match mv {
                    Left(hz) | Right(hz) | LeftCross(hz) | RightCross(hz) => match hz {
                        HorizMove::UntilFst(_) => HorizMove::UntilFst,
                        HorizMove::UntilSnd(_) => HorizMove::UntilSnd,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };

                return Success(*priority, f(g(pred)));
            }
        }

        let cfg = Config::global();
        match cfg.keys.get(&key) {
            Some(&(p, Binding::RawMove(m))) => Success(p, m),
            Some(&(p, Binding::WaitForChar(m))) => {
                *self = Self::Char(p, m);
                NeedsMore
            }
            None => Failed,
        }
    }

    fn max_priority(&self) -> Option<Priority> {
        match self {
            Self::Nothing => Config::global().keys.values().map(|(p, _)| *p).max(),
            Self::Char(p, _) => Some(*p),
        }
    }
}

static_config! {
    static GLOBAL;
    pub struct Builder;
    pub struct Config {
        pub keys: HashMap<KeyEvent, (Priority, Binding)> = default_keybindings(),
    }
}

#[derive(Copy, Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum Binding {
    RawMove(Movement),
    WaitForChar(Movement),
}

#[rustfmt::skip]
fn default_keybindings() -> HashMap<KeyEvent, (Priority, Binding)> {
    use crate::mode::CharPredicate::{BigWordEnd, BigWordStart, WordEnd, WordStart, ToChar};
    use crate::mode::HorizMove::{Const,LineBoundary, UntilFst, UntilSnd};
    use crate::mode::Movement::{Down, Left, Right, Up, LeftCross, RightCross};
    use Binding::{RawMove, WaitForChar};

    use super::Priority::Builtin;

    let keys = vec![
        // Directional movement
        (KeyEvent::none('k'), (Builtin, RawMove(Up))),
        (KeyEvent::none('j'), (Builtin, RawMove(Down))),
        (KeyEvent::none('h'), (Builtin, RawMove(Left(Const)))),
        (KeyEvent::none('l'), (Builtin, RawMove(Right(Const)))),

        // By words
        (KeyEvent::none('b'), (Builtin, RawMove(LeftCross(UntilFst(WordEnd))))),
        (KeyEvent::shift('B'), (Builtin, RawMove(LeftCross(UntilFst(BigWordEnd))))),
        (KeyEvent::none('w'), (Builtin, RawMove(RightCross(UntilSnd(WordStart))))),
        (KeyEvent::shift('W'), (Builtin, RawMove(RightCross(UntilSnd(BigWordStart))))),
        (KeyEvent::none('e'), (Builtin, RawMove(RightCross(UntilFst(WordEnd))))),
        (KeyEvent::shift('E'), (Builtin, RawMove(RightCross(UntilFst(BigWordEnd))))),

        // Relative to the line beginning/end
        (KeyEvent::none('0'), (Builtin, RawMove(LeftCross(LineBoundary)))),
        (KeyEvent::none('$'), (Builtin, RawMove(RightCross(LineBoundary)))),

        // To a character
        (KeyEvent::none('f'), (Builtin, WaitForChar(Right(UntilSnd(ToChar(' ')))))),
        (KeyEvent::none('t'), (Builtin, WaitForChar(Right(UntilFst(ToChar(' ')))))),
        (KeyEvent::shift('F'), (Builtin, WaitForChar(Left(UntilSnd(ToChar(' ')))))),
        (KeyEvent::shift('T'), (Builtin, WaitForChar(Left(UntilFst(ToChar(' ')))))),
    ];

    keys.into_iter().collect()
}
