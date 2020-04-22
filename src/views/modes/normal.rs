// TODO: Module-level documentation

use std::fmt::{self, Debug, Formatter};

use serde::{Deserialize, Serialize};

use crate::config::prelude::*;
use crate::event::KeyEvent;
use crate::views::{Cmd, CursorStyle, Movement};

use super::{Mode, ModeResult};

pub struct NormalMode {
    parsers: Option<Parsers>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum NormalCmd {
    ExitMode,
    // The available modes are:
    // * "insert" => FileView
    ChangeMode(String),
}

impl Debug for NormalMode {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        enum OpaqueOption {
            Some,
            None,
        }

        impl Debug for OpaqueOption {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                match self {
                    Self::Some => f.write_str("Some(...)"),
                    Self::None => f.write_str("None"),
                }
            }
        }

        fn opaque<T>(opt: Option<T>) -> OpaqueOption {
            match opt {
                Some(_) => OpaqueOption::Some,
                None => OpaqueOption::None,
            }
        }

        f.debug_struct("NormalMode")
            .field("parsers", &opaque(self.parsers.as_ref()))
            .finish()
    }
}

impl Mode<NormalCmd> for NormalMode {
    fn try_handle(&mut self, key: KeyEvent) -> ModeResult<NormalCmd> {
        let parsers = match &mut self.parsers {
            Some(ps) => ps,
            None => {
                self.parsers = Some(Parsers::default());
                self.parsers.as_mut().unwrap()
            }
        };

        match parsers.add(key) {
            ParseResult::NeedsMore => ModeResult::NeedsMore,
            ParseResult::Success(_, cmd) => {
                self.parsers = None;
                ModeResult::Cmd(cmd)
            }
            ParseResult::Failed => {
                self.parsers = None;
                ModeResult::NoCommand
            }
        }
    }

    fn cursor_style(&self) -> CursorStyle {
        CursorStyle { allow_after: false }
    }
}

impl NormalMode {
    pub fn new() -> Self {
        Self { parsers: None }
    }

    pub fn currently_waiting(&self) -> bool {
        self.parsers.is_some()
    }
}

trait ParseState {
    type Output;

    fn add(&mut self, key: KeyEvent) -> ParseResult<Self::Output>;

    fn max_priority(&self) -> Option<Priority>;
}

#[derive(Clone)]
enum ParseResult<T> {
    Success(Priority, T),
    NeedsMore,
    Failed,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
enum Priority {
    Error,
    UserDefined,
    Builtin,
}

impl<T> ParseResult<T> {
    fn needs_more(&self) -> bool {
        match self {
            Self::NeedsMore => true,
            _ => false,
        }
    }
}

struct Parsers {
    inner: Vec<Box<dyn ParseState<Output = Cmd<NormalCmd>>>>,
}

impl Default for Parsers {
    fn default() -> Self {
        Self {
            inner: vec![Box::new(MovementParser::default())],
        }
    }
}

impl ParseState for Parsers {
    type Output = Cmd<NormalCmd>;

    fn add(&mut self, key: KeyEvent) -> ParseResult<Cmd<NormalCmd>> {
        // Set up a helper type
        enum SearchResult {
            Single(Priority, Cmd<NormalCmd>),
            Conflict(Priority),
            Nothing,
        }

        use SearchResult::*;

        impl SearchResult {
            fn priority(&self) -> Option<Priority> {
                match self {
                    Single(p, _) | Conflict(p) => Some(*p),
                    Nothing => None,
                }
            }
        }

        // The actual body of the function

        let mut found = Nothing;
        let mut max_possible: Option<Priority> = None;
        let mut next_set: Vec<Box<dyn ParseState<Output = Cmd<NormalCmd>>>> =
            Vec::with_capacity(self.inner.len());
        let mut needs_more = false;

        for mut parser in self.inner.drain(..) {
            match parser.add(key) {
                ParseResult::NeedsMore => {
                    needs_more = true;
                    max_possible = max_possible.max(parser.max_priority());
                }
                ParseResult::Failed => (),
                ParseResult::Success(priority, cmd) => match found {
                    Nothing => found = Single(priority, cmd),

                    Conflict(p) | Single(p, _) if p < priority => found = Single(priority, cmd),
                    Conflict(p) | Single(p, _) if p > priority => (),

                    // p == priority
                    Single(p, _) => found = Conflict(p),
                    Conflict(_) => (),
                },
            }
        }

        if max_possible.is_none() && found.priority().is_none() {
            return ParseResult::Failed;
        } else if max_possible >= found.priority() {
            // this is a weird case :(
            return ParseResult::Success(Priority::Error, todo!());
        }

        match found {
            Single(priority, cmd) => ParseResult::Success(priority, cmd),
            Conflict(_) => {
                return ParseResult::Success(Priority::Error, todo!());
            }
            Nothing => match needs_more {
                true => {
                    self.inner = next_set;
                    ParseResult::NeedsMore
                }
                false => ParseResult::Failed,
            },
        }
    }

    fn max_priority(&self) -> Option<Priority> {
        self.inner
            .iter()
            .map(|p| p.max_priority())
            .max()
            .unwrap_or(None)
    }
}

enum MovementParser {
    Simple(Priority, Movement),
    Nothing,
    Failed,
}

impl Default for MovementParser {
    fn default() -> Self {
        Self::Nothing
    }
}

impl ParseState for MovementParser {
    type Output = Cmd<NormalCmd>;

    fn add(&mut self, key: KeyEvent) -> ParseResult<Cmd<NormalCmd>> {
        match self {
            Self::Failed | Self::Simple(_, _) => {
                log::warn!("Warning: adding to MovementParser that has already finished.");
                ParseResult::Success(Priority::Error, todo!());
            }
            Self::Nothing => (),
        }

        let cfg = move_config::Config::global();
        let (priority, movement) = match cfg.keys.get(&key) {
            Some(&(p, m)) => (p, m),
            None => {
                *self = Self::Failed;
                return ParseResult::Failed;
            }
        };

        *self = Self::Simple(priority, movement);
        // TODO: This should just return the movement, using a secondary wrapping "numerical"
        // parser to handle the rest
        ParseResult::Success(priority, Cmd::Cursor(movement, None))
    }

    fn max_priority(&self) -> Option<Priority> {
        match self {
            Self::Simple(priority, _) => Some(*priority),
            Self::Failed => None,
            Self::Nothing => move_config::Config::global()
                .keys
                .values()
                .map(|(p, _)| *p)
                .max(),
        }
    }
}

mod move_config {
    use super::Priority;
    use crate::config::prelude::*;
    use crate::event::KeyEvent;
    use crate::views::Movement;
    use std::collections::HashMap;

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
}
