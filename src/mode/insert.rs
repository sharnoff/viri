// TODO: Module-level documentation

use serde::Deserialize;

use super::{Cmd, CursorStyle, Error, HorizMove, Mode, Movement};
use crate::config::prelude::*;
use crate::event::{KeyCode, KeyEvent, KeyModifiers};
use crate::never::Never;
use crate::trie::Trie;

#[derive(Debug)]
pub struct InsertMode {
    key_stack: Vec<KeyEvent>,
}

impl Mode<Never> for InsertMode {
    fn try_handle(&mut self, key: KeyEvent) -> Result<Cmd<Never>, Error> {
        self.key_stack.push(key);

        let cfg = Config::global();
        let node = cfg.keys.find(&self.key_stack);

        match node {
            None if self.key_stack.len() > 1 => {
                self.key_stack.truncate(0);
                return Err(Error::NoSuchCommand);
            }
            Some(n) if n.size() == 1 => {
                self.key_stack.truncate(0);
                return Ok(n.extract().clone());
            }
            Some(n) if n.size() > 1 => {
                // ^ TODO: This isn't technically true... it could be possible to unwrap this
                // value, but we'd need something to disambiguate.
                return Err(Error::NeedsMore);
            }
            _ => (),
        }

        self.key_stack.truncate(0);

        // There weren't any commands that we could apply here, so we'll insert a character.
        // BUT! Only if the character has no modifiers. Other sorts of control flow (like line
        // breaks, deleting, etc. are provided by the commands)
        if key.mods == KeyModifiers::NONE {
            if let (KeyCode::Char(c), true) = (key.code, key.mods == KeyModifiers::NONE) {
                let insert = Cmd::Insert(c.to_string());
                let shift = Cmd::Cursor(Movement::Right(HorizMove::Const), 1);
                return Ok(Cmd::Chain(vec![insert, shift]));
            }
        }

        Err(Error::NoSuchCommand)
    }

    fn cursor_style(&self) -> CursorStyle {
        CursorStyle { allow_after: true }
    }

    fn expecting_input(&self) -> bool {
        !self.key_stack.is_empty()
    }
}

impl InsertMode {
    pub fn new() -> Self {
        Self {
            key_stack: Vec::with_capacity(1),
        }
    }
}

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
    use super::CharPredicate::WordEnd;
    use super::Cmd::{Chain, Cursor, Delete, ExitMode, Insert};
    use super::DeleteKind::ByMovement;
    use super::HorizMove::{Const, UntilFst};
    use super::Movement::{Left, LeftCross, RightCross};
    use crate::event::KeyCode::{Backspace, Delete as Del, Enter, Esc};
    use crate::event::KeyModifiers as Mods;

    let keys = vec![
        (vec![KeyEvent::ctrl('w')],
            Delete(ByMovement {
                movement: LeftCross(UntilFst(WordEnd)),
                amount: 1,
                from_inclusive: false,
                to_inclusive: true,
            })),
        (vec![KeyEvent {
                code: Esc,
                mods: Mods::NONE,
            }],
            Chain(vec![
                Cursor(Left(Const), 1),
                ExitMode
            ])),
        (vec![KeyEvent {
                code: Enter,
                mods: Mods::NONE,
            }],
            Chain(vec![
                Insert('\n'.to_string()),
                Cursor(RightCross(Const), 1)
            ])),
        (vec![KeyEvent { code: Backspace, mods: Mods::NONE }],
            Delete(ByMovement {
                movement: LeftCross(Const),
                amount: 1,
                from_inclusive: false,
                to_inclusive: true,
            })),
        (vec![KeyEvent { code: Del, mods: Mods::NONE }],
            Delete(ByMovement {
                movement: RightCross(Const),
                amount: 1,
                from_inclusive: true,
                to_inclusive: false,
            })),
    ];

    Trie::from_iter(keys.into_iter())
}
