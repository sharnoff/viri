// TODO: Module-level documentation

use serde::Deserialize;

use crate::config::prelude::*;
use crate::event::{KeyCode, KeyEvent, KeyModifiers};
use crate::trie::Trie;
use crate::views::{self, Cmd, CursorStyle, HorizontalMove, Movement};

use super::{Mode, ModeResult};

#[derive(Debug)]
pub struct InsertMode {
    key_stack: Vec<KeyEvent>,
}

#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum InsertCmd {
    InsertChar(char),
    Delete(Movement),
    ExitMode,
}

impl Mode<InsertCmd> for InsertMode {
    fn try_handle(&mut self, key: KeyEvent) -> ModeResult<InsertCmd> {
        self.key_stack.push(key);

        let cfg = Config::global();
        let node = cfg.keys.find(&self.key_stack);

        match node {
            None if !self.key_stack.is_empty() => {
                self.key_stack.truncate(0);
                return ModeResult::NoCommand;
            }
            Some(n) if n.size() == 1 => {
                return ModeResult::Cmd(n.extract().clone());
            }
            Some(n) if n.size() > 1 => {
                // ^ TODO: This isn't technically true... it could be possible to unwrap this
                // value, but we'd need something to disambiguate.
                return ModeResult::NeedsMore;
            }
            _ => (),
        }

        self.key_stack.truncate(0);

        // There weren't any commands that we could apply here, so we'll insert a character.
        // BUT! Only if the character has no modifiers. Other sorts of control flow (like line
        // breaks, deleting, etc. are provided by the commands)
        if key.mods == KeyModifiers::NONE {
            if let (KeyCode::Char(c), true) = (key.code, key.mods == KeyModifiers::NONE) {
                let insert = Cmd::Extra(InsertCmd::InsertChar(c));
                let shift = Cmd::Cursor(Movement::Right(HorizontalMove::Const, false), None);
                return ModeResult::Cmd(Cmd::Chain(vec![insert, shift]));
            }
        }

        ModeResult::NoCommand
    }

    fn cursor_style(&self) -> CursorStyle {
        CursorStyle { allow_after: true }
    }
}

impl InsertMode {
    pub fn new() -> Self {
        Self {
            key_stack: Vec::with_capacity(1),
        }
    }

    pub fn currently_waiting(&self) -> bool {
        !self.key_stack.is_empty()
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Builder {
    keys: Option<Vec<(Vec<KeyEvent>, Cmd<InsertCmd>)>>,
}

static_config! {
    static GLOBAL;
    @Builder = Builder;
    pub struct Config {
        pub keys: Trie<KeyEvent, Cmd<InsertCmd>> = default_keybindings(),
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
fn default_keybindings() -> Trie<KeyEvent, Cmd<InsertCmd>> {
    use crate::event::KeyCode::{Esc, Enter, Backspace, Delete};
    use crate::event::KeyModifiers as Mods;
    use views::HorizontalMove::{Const, UntilFst};
    use views::Movement::{Left, Right};
    use views::CharPredicate::WordEnd;

    let keys = vec![
        (vec![KeyEvent::ctrl('w')],
            Cmd::Extra(InsertCmd::Delete(Left(UntilFst(WordEnd), true)))),
        (vec![KeyEvent { code: Esc, mods: Mods::NONE }],
            Cmd::Chain(vec![
                Cmd::Cursor(Left(Const, false), Some(1)),
                Cmd::Extra(InsertCmd::ExitMode),
            ])),
        (vec![KeyEvent { code: Enter, mods: Mods::NONE }],
            Cmd::Chain(vec![
                Cmd::Extra(InsertCmd::InsertChar('\n')),
                Cmd::Cursor(Right(Const, true), Some(1)),
            ])),
        (vec![KeyEvent { code: Backspace, mods: Mods::NONE }],
                Cmd::Extra(InsertCmd::Delete(Left(Const, true)))),
        (vec![KeyEvent { code: Delete, mods: Mods::NONE }],
                Cmd::Extra(InsertCmd::Delete(Right(Const, true)))),
    ];

    Trie::from_iter(keys.into_iter())
}
