// TODO: Module-level documentation

use serde::Deserialize;

use crate::config::prelude::*;
use crate::event::KeyEvent;
use crate::trie::Trie;
use crate::views::{self, Cmd, CursorStyle};

use super::{Mode, ModeResult};

#[derive(Debug)]
pub struct NormalMode {
    key_stack: Vec<KeyEvent>,
    // TODO: We'll need to keep track of numbers/movements/etc so can
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum NormalCmd {
    ExitMode,
    // The available modes are:
    // * "insert" => FileView
    ChangeMode(String),
}

impl Mode<NormalCmd> for NormalMode {
    fn try_handle(&mut self, key: KeyEvent) -> ModeResult<NormalCmd> {
        self.key_stack.push(key);

        let cfg = Config::global();
        let mut cmds_iter = cfg.keys.iter_all_prefix(&self.key_stack);

        match cmds_iter.len() {
            0 => {
                self.key_stack.truncate(0);
                ModeResult::NoCommand
            }
            1 => {
                let (_, cmd) = cmds_iter.next().unwrap();
                self.key_stack.truncate(0);
                ModeResult::Cmd(cmd.clone())
            }
            _ => ModeResult::NeedsMore,
        }
    }

    fn cursor_style(&self) -> CursorStyle {
        CursorStyle { allow_after: false }
    }
}

impl NormalMode {
    pub fn new() -> Self {
        Self {
            key_stack: Vec::with_capacity(1),
        }
    }

    pub fn currently_waiting(&self) -> bool {
        !self.key_stack.is_empty()
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
    use views::CharPredicate::{BigWordEnd, BigWordStart, WordEnd, WordStart};
    use views::HorizontalMove::{Const,LineBoundary, UntilFst, UntilSnd};
    use views::Movement::{Down, Left, Right, Up};

    let keys = vec![
        // (mostly) meaningless for now
        (vec![KeyEvent { code: Esc, mods: Mods::NONE }], Cmd::Extra(NormalCmd::ExitMode)),
        // Standard movmeent
        (vec![KeyEvent::none('k')], Cmd::Cursor(Up, None)),
        (vec![KeyEvent::none('j')], Cmd::Cursor(Down, None)),
        (vec![KeyEvent::none('h')], Cmd::Cursor(Left(Const, false), None)),
        (vec![KeyEvent::none('l')], Cmd::Cursor(Right(Const, false), None)),

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

        // More advanced movements - these map to (essentially) what they are in other editors
        (vec![KeyEvent::none('b')], Cmd::Cursor(Left(UntilFst(WordEnd), true), None)),
        (vec![KeyEvent::none('B')], Cmd::Cursor(Left(UntilFst(BigWordEnd), true), None)),
        (vec![KeyEvent::none('w')], Cmd::Cursor(Right(UntilSnd(WordStart), true), None)),
        (vec![KeyEvent::none('W')], Cmd::Cursor(Right(UntilSnd(BigWordStart), true), None)),
        (vec![KeyEvent::none('e')], Cmd::Cursor(Right(UntilFst(WordEnd), true), None)),
        (vec![KeyEvent::none('E')], Cmd::Cursor(Right(UntilFst(BigWordEnd), true), None)),
        (vec![KeyEvent::none('0')], Cmd::Cursor(Left(LineBoundary, true), None)),
        (vec![KeyEvent::none('$')], Cmd::Cursor(Right(LineBoundary, true), None)),

        // Switching to 'command mode' (not sure what this should really be called)
    ];

    Trie::from_iter(keys.into_iter())
}
