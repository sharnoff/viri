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

lazy_static::lazy_static! {
    static ref LAST_CHAR_MOVE: Mutex<Option<Movement>> = Mutex::new(None);
}

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

                let m = f(g(pred));
                *LAST_CHAR_MOVE.lock().unwrap() = Some(m);

                return Success(*priority, m);
            }
        }

        let cfg = Config::global();
        match cfg.keys.get(&key) {
            None => Failed,
            Some(&(p, Binding::RawMove(m))) => Success(p, m),
            Some(&(p, Binding::WaitForChar(m))) => {
                *self = Self::Char(p, m);
                NeedsMore
            }
            Some(&(p, Binding::RepeatToChar { fwd })) => {
                let last = match *LAST_CHAR_MOVE.lock().unwrap() {
                    Some(mv) => mv,
                    None => return Failed,
                };

                let f = match (last, fwd) {
                    (Left(_), true) | (Right(_), false) => Left,
                    (Right(_), true) | (Left(_), false) => Right,
                    (LeftCross(_), true) | (RightCross(_), false) => LeftCross,
                    (RightCross(_), true) | (LeftCross(_), false) => RightCross,
                    _ => unreachable!(),
                };

                let to_ch;
                let g = match last {
                    Left(hz) | Right(hz) | LeftCross(hz) | RightCross(hz) => match hz {
                        HorizMove::UntilFst(c) => {
                            to_ch = c;
                            HorizMove::UntilFst
                        }
                        HorizMove::UntilSnd(c) => {
                            to_ch = c;
                            HorizMove::UntilSnd
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };

                Success(p, f(g(to_ch)))
            }
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
    RepeatToChar { fwd: bool },
}

#[rustfmt::skip]
fn default_keybindings() -> HashMap<KeyEvent, (Priority, Binding)> {
    use crate::mode::CharPredicate::{BigWordEnd, BigWordStart, WordEnd, WordStart, ToChar};
    use crate::mode::HorizMove::{Const,LineBoundary, UntilFst, UntilSnd};
    use crate::mode::Movement::{
        Down, Left, Right, Up, LeftCross, RightCross, ToBottom, ToTop, MatchingDelim, ScreenLine
    };
    use Binding::{RawMove, WaitForChar, RepeatToChar};

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
        (KeyEvent::none(';'), (Builtin, RepeatToChar { fwd: true })),
        (KeyEvent::none(','), (Builtin, RepeatToChar { fwd: false })),

        // And by lines
        (KeyEvent::shift('G'), (Builtin, RawMove(ToBottom))),
        (KeyEvent::none('g'), (Builtin, RawMove(ToTop))),
        // ^ Note: This is temporary, as we'd much rather have 'gg' for this. We'll make this
        // change once some of the other multi-character movements are necessary (like 'gi', etc.)
        (KeyEvent::shift('H'), (Builtin, RawMove(ScreenLine(0.0)))),
        (KeyEvent::shift('M'), (Builtin, RawMove(ScreenLine(0.5)))),
        (KeyEvent::shift('L'), (Builtin, RawMove(ScreenLine(1.0)))),

        // Misc
        (KeyEvent::none('%'), (Builtin, RawMove(MatchingDelim))),
    ];

    keys.into_iter().collect()
}
