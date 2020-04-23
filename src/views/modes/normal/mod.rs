// TODO: Module-level documentation
mod combinators;
mod delete;
mod movement;

use std::fmt::{self, Debug, Formatter};

use serde::{Deserialize, Serialize};

use crate::config::prelude::*;
use crate::event::KeyEvent;
use crate::trie::Trie;
use crate::views::{self, Cmd, CursorStyle, Movement};

use super::{Mode, ModeResult};

use combinators::{numerical, set, wrap};

/// The type responsible for handling inputs while in "normal" mode
pub struct NormalMode {
    /// The ongoing set of parsers that might be able to consume the next key input
    parsers: Option<combinators::Set<Cmd<NormalCmd>>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum NormalCmd {
    ExitMode,
    // The available modes are:
    // * "insert" => FileView
    ChangeMode(String),
    Delete(Movement, usize),
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

impl NormalMode {
    pub fn new() -> Self {
        Self { parsers: None }
    }

    pub fn currently_waiting(&self) -> bool {
        self.parsers.is_some()
    }

    fn reset_parsers(&mut self) {
        let movement = wrap(numerical(movement::Parser::default()), |(n, m)| {
            Cmd::Cursor(m, n)
        });

        let delete = wrap(
            numerical(delete::Parser::default()),
            |(n_outer, (n_inner, m))| {
                // FIXME: This could fail if the numbers are big enough - it *really* shoudn't do
                // that
                Cmd::Extra(NormalCmd::Delete(m, n_outer.unwrap_or(1) * n_inner))
            },
        );

        self.parsers = Some(set(vec![
            Box::new(movement),
            Box::new(Misc::default()),
            Box::new(delete),
        ]));
    }
}

impl Mode<NormalCmd> for NormalMode {
    fn try_handle(&mut self, key: KeyEvent) -> ModeResult<NormalCmd> {
        use combinators::SetResult::{FinishConflict, PartialConflict, Success};

        if self.parsers.is_none() {
            self.reset_parsers();
        }

        let parsers = self.parsers.as_mut().unwrap();

        match parsers.add(key) {
            ParseResult::NeedsMore => ModeResult::NeedsMore,
            ParseResult::Success(_, set_res) => match set_res {
                Success(cmd) => {
                    self.parsers = None;
                    ModeResult::Cmd(cmd)
                }
                PartialConflict(_) => todo!(),
                FinishConflict => todo!(),
            },
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

impl ParseState for Misc {
    type Output = Cmd<NormalCmd>;

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
    keys: Option<Vec<(Vec<KeyEvent>, Cmd<NormalCmd>)>>,
}

static_config! {
    static GLOBAL;
    @Builder = Builder;
    pub struct Config {
        pub keys: Trie<KeyEvent, Cmd<NormalCmd>> = default_keybindings(),
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
fn default_keybindings() -> Trie<KeyEvent, Cmd<NormalCmd>> {
    use crate::event::{KeyCode::Esc, KeyModifiers as Mods};
    use views::HorizontalMove::{Const, LineBoundary};
    use views::Movement::Right;

    let keys = vec![
        // (mostly) meaningless for now - this will be available once colon "normal" mode will be
        // allowed to switch back to colon "insert" mode
        (vec![KeyEvent { code: Esc, mods: Mods::NONE }], Cmd::Extra(NormalCmd::ExitMode)),

        // Switching to insert mode
        (vec![KeyEvent::none('i')], Cmd::Extra(NormalCmd::ChangeMode("insert".into()))),
        (vec![KeyEvent::none('a')], Cmd::Chain(vec![
                Cmd::Extra(NormalCmd::ChangeMode("insert".into())),
                Cmd::Cursor(Right(Const, false), None)
        ])),
        (vec![KeyEvent::none('A')], Cmd::Chain(vec![
                Cmd::Extra(NormalCmd::ChangeMode("insert".into())),
                Cmd::Cursor(Right(LineBoundary, false), None)
        ])),
    ];

    Trie::from_iter(keys.into_iter())
}
