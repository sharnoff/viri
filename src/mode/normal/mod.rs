// TODO: Module-level documentation
pub mod combinators;
pub mod delete;
pub mod movement;

use std::fmt::{self, Debug, Formatter};

use serde::{Deserialize, Serialize};

use crate::config::prelude::*;
use crate::event::KeyEvent;
use crate::never::Never;
use crate::trie::Trie;

use super::{Cmd, CursorStyle, Error, Mode};

use combinators::{numerical, set, wrap};

/// The type responsible for handling inputs while in "normal" mode
pub struct NormalMode {
    /// The ongoing set of parsers that might be able to consume the next key input
    parsers: Option<combinators::Set<Cmd<Never>>>,
}

pub trait ParseState {
    type Output;

    fn add(&mut self, key: KeyEvent) -> ParseResult<Self::Output>;
    fn max_priority(&self) -> Option<Priority>;
}

#[derive(Clone)]
pub enum ParseResult<T> {
    Success(Priority, T),
    NeedsMore,
    Failed,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Priority {
    Error,
    UserDefined,
    Builtin,
}

impl NormalMode {
    pub fn new() -> Self {
        Self { parsers: None }
    }

    fn reset_parsers(&mut self) {
        let movement = wrap(numerical(movement::Parser::new()), |(n, m)| {
            Cmd::Cursor(m, n.unwrap_or(1))
        });

        self.parsers = Some(set(vec![
            Box::new(movement),
            Box::new(Misc::new()),
            Box::new(delete::Parser::new()),
        ]));
    }
}

impl Mode<Never> for NormalMode {
    fn try_handle(&mut self, key: KeyEvent) -> Result<Cmd<Never>, Error> {
        use combinators::SetResult::{FinishConflict, PartialConflict, Success};

        if self.parsers.is_none() {
            self.reset_parsers();
        }

        let parsers = self.parsers.as_mut().unwrap();

        match parsers.add(key) {
            ParseResult::NeedsMore => Err(Error::NeedsMore),
            ParseResult::Success(_, set_res) => match set_res {
                Success(cmd) => {
                    self.parsers = None;
                    Ok(cmd)
                }
                PartialConflict(_) => todo!(),
                FinishConflict => todo!(),
            },
            ParseResult::Failed => {
                self.parsers = None;
                Err(Error::NoSuchCommand)
            }
        }
    }

    fn cursor_style(&self) -> CursorStyle {
        CursorStyle { allow_after: false }
    }

    fn expecting_input(&self) -> bool {
        self.parsers.is_some()
    }
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

/// A parser for the miscellaneous singleton commands
#[derive(Default)]
struct Misc {
    stack: Vec<KeyEvent>,
}

impl Misc {
    fn new() -> Self {
        Self { stack: Vec::new() }
    }
}

impl ParseState for Misc {
    type Output = Cmd<Never>;

    fn add(&mut self, key: KeyEvent) -> ParseResult<Self::Output> {
        self.stack.push(key);

        let cfg = Config::global();
        let node = cfg.keys.find(&self.stack);

        match node {
            None => {
                self.stack.truncate(0);
                ParseResult::Failed
            }
            Some(n) if n.size() == 0 => {
                self.stack.truncate(0);
                ParseResult::Failed
            }
            Some(n) if n.size() == 1 => {
                self.stack.truncate(0);
                ParseResult::Success(Priority::Builtin, n.extract().clone())
            }
            // Some(n) if n.size > 1
            _ => ParseResult::NeedsMore,
        }
    }

    fn max_priority(&self) -> Option<Priority> {
        if Config::global().keys.find(&self.stack)?.size() == 0 {
            None
        } else {
            Some(Priority::Builtin)
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Config stuff                                                                                   //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Serialize, Deserialize)]
pub struct Builder {
    keys: Option<Vec<(Vec<KeyEvent>, Cmd<Never>)>>,
}

static_config! {
    static GLOBAL;
    @Builder = Builder;
    pub struct Config {
        pub keys: Trie<KeyEvent, Cmd<Never>> = default_keybindings(),
    }

    impl ConfigPart {
        fn update(this: &mut Self, builder: Builder) {
            if let Some(ks) = builder.keys {
                ks.into_iter().for_each(|(key,cmd)| drop(this.keys.insert(key, cmd)));
            }
        }
    }
}

impl From<Builder> for Config {
    fn from(builder: Builder) -> Self {
        Self {
            keys: builder
                .keys
                .map(|ks| Trie::from_iter(ks.into_iter()))
                .unwrap_or_else(default_keybindings),
        }
    }
}

#[rustfmt::skip]
fn default_keybindings() -> Trie<KeyEvent, Cmd<Never>> {
    use super::Cmd::{Chain, ChangeMode, Cursor, ExitMode};
    use super::HorizMove::{Const, LineBoundary};
    use super::ModeKind;
    use super::Movement::Right;
    use crate::event::{KeyCode::Esc, KeyModifiers as Mods};

    let keys = vec![
        // (mostly) meaningless for now - this will be available once colon "normal" mode will be
        // allowed to switch back to colon "insert" mode
        (vec![KeyEvent { code: Esc, mods: Mods::NONE }],
            ExitMode,
        ),

        // Switching to insert mode
        (vec![KeyEvent::none('i')],
            ChangeMode(ModeKind::Insert)),
        (vec![KeyEvent::none('a')],
            Chain(vec![
                ChangeMode(ModeKind::Insert),
                Cursor(Right(Const), 1)
            ])),
        (vec![KeyEvent::none('A')],
            Chain(vec![
                ChangeMode(ModeKind::Insert),
                Cursor(Right(LineBoundary), 1),
            ])),
    ];

    Trie::from_iter(keys.into_iter())
}
