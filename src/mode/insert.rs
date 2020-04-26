// TODO: Module-level documentation

use crate::config::prelude::*;
use crate::prelude::*;
use std::marker::PhantomData;

use super::{Cmd, CursorStyle, Error, HorizMove, Movement};
use crate::event::{KeyCode, KeyEvent, KeyModifiers};
use crate::trie::Trie;

#[derive(Debug)]
pub struct Mode<T> {
    key_stack: Vec<KeyEvent>,
    _marker: PhantomData<T>,
}

impl<T> Default for Mode<T> {
    fn default() -> Self {
        Self {
            key_stack: Vec::new(),
            _marker: PhantomData,
        }
    }
}

impl<T> super::Mode<T> for Mode<T> {
    const NAME: Option<&'static str> = Some("-- INSERT --");

    fn try_handle(&mut self, key: KeyEvent) -> Result<Seq<Cmd<T>>, Error> {
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
                return Ok(n.extract().clone().xinto());
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
                return Ok(Many(vec![insert, shift]));
            }
        }

        Err(Error::NoSuchCommand)
    }

    fn cursor_style(&self) -> CursorStyle {
        CursorStyle { allow_after: true }
    }

    fn expecting_input(&self) -> bool {
        // We always return true because input mode is *always* expecting input
        true
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Builder {
    keys: Option<Vec<(Vec<KeyEvent>, Seq<Cmd<Never>>)>>,
}

static_config! {
    static GLOBAL;
    @Builder = Builder;
    pub struct Config {
        pub keys: Trie<KeyEvent, Seq<Cmd<Never>>> = default_keybindings(),
    }

    impl ConfigPart {
        fn update(this: &mut Self, builder: Builder) {
            if let Some(ks) = builder.keys {
                ks.into_iter().for_each(|(key,cmd)| drop(this.keys.insert(key, cmd)));
            }
        }
    }
}

impl XFrom<Builder> for Config {
    fn xfrom(builder: Builder) -> Self {
        Self {
            keys: builder
                .keys
                .map(|ks| Trie::from_iter(ks.into_iter()))
                .unwrap_or_else(default_keybindings),
        }
    }
}

#[rustfmt::skip]
fn default_keybindings() -> Trie<KeyEvent, Seq<Cmd<Never>>> {
    use super::CharPredicate::WordEnd;
    use super::Cmd::{Cursor, Delete, ExitMode, Insert};
    use super::DeleteKind::ByMovement;
    use super::HorizMove::{Const, UntilFst};
    use super::Movement::{Left, LeftCross, RightCross};
    use crate::event::KeyCode::{Backspace, Delete as Del, Enter, Esc};
    use crate::event::KeyModifiers as Mods;

    let keys = vec![
        (vec![KeyEvent::ctrl('w')],
            One(Delete(ByMovement {
                movement: LeftCross(UntilFst(WordEnd)),
                amount: 1,
                from_inclusive: false,
                to_inclusive: true,
            }))),
        (vec![KeyEvent { code: Esc, mods: Mods::NONE }],
            Many(vec![
                Cursor(Left(Const), 1),
                ExitMode
            ])),
        (vec![KeyEvent { code: Enter, mods: Mods::NONE }],
            Many(vec![
                Insert('\n'.to_string()),
                Cursor(RightCross(Const), 1)
            ])),
        (vec![KeyEvent { code: Backspace, mods: Mods::NONE }],
            One(Delete(ByMovement {
                movement: LeftCross(Const),
                amount: 1,
                from_inclusive: false,
                to_inclusive: true,
            }))),
        (vec![KeyEvent { code: Del, mods: Mods::NONE }],
            One(Delete(ByMovement {
                movement: RightCross(Const),
                amount: 1,
                from_inclusive: true,
                to_inclusive: false,
            }))),
    ];

    Trie::from_iter(keys.into_iter())
}
