// TODO: Module-level documentation

use super::config;
use super::{Cmd, CursorStyle, Error, HorizMove, Movement};
use crate::config::{Build, ConfigPart, DerefChain, DerefMutChain};
use crate::event::{KeyCode, KeyEvent, KeyModifiers};
use crate::trie::Trie;
use crate::utils::{Never, XFrom, XInto};
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;
use std::ops::Deref;
use std::sync::{Arc, Mutex, MutexGuard};

#[derive(Debug)]
pub struct Mode<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
{
    key_stack: Vec<KeyEvent>,
    get_conf: fn() -> <config::ExtConfig<Conf> as ConfigPart>::Deref,
    _marker: PhantomData<T>,
}

impl<T, Conf> Default for Mode<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
{
    fn default() -> Self {
        Self {
            key_stack: Vec::new(),
            get_conf: <config::ExtConfig<Conf> as ConfigPart>::global,
            _marker: PhantomData,
        }
    }
}

impl<T, Conf> super::Mode<T, Conf> for Mode<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
    T: Clone,
    Conf: 'static,
{
    const NAME: Option<&'static str> = Some("-- INSERT --");

    fn try_handle(&mut self, key: KeyEvent) -> Result<Vec<Cmd<T>>, Error> {
        self.key_stack.push(key);

        // First get the most extended config, then recursively get its parent configs
        // The parent configurations are ordered from base -> extension, so we build a new Trie in
        // that order
        let ext_cfg = (self.get_conf)();
        let cfgs = config::get_all(Box::new(ext_cfg));
        let cfg = Trie::from_iter(cfgs.iter().map(|c| c.insert().keys()).flatten());

        // let cfg = Config::global();
        let node = cfg.find(&self.key_stack);

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
        if key.mods == KeyModifiers::NONE || key.mods == KeyModifiers::SHIFT {
            if let KeyCode::Char(c) = key.code {
                let insert = Cmd::Insert(c.to_string());
                let shift = Cmd::Cursor(Movement::Right(HorizMove::Const), 1);
                return Ok(vec![insert, shift]);
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

////////////////////////////////////////////////////////////////////////////////
// Base Config stuff                                                          //
////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Serialize, Deserialize)]
pub struct Builder {
    keys: Option<Vec<(Vec<KeyEvent>, Vec<Cmd<Never>>)>>,
}

static_config! {
    static GLOBAL;
    @Builder = Builder;
    pub struct Config {
        pub keys: Trie<KeyEvent, Vec<Cmd<Never>>> = default_keybindings(),
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
fn default_keybindings() -> Trie<KeyEvent, Vec<Cmd<Never>>> {
    use super::CharPredicate::WordEnd;
    use super::Cmd::{Cursor, Delete, ExitMode, Insert, EndEditBlock};
    use super::DeleteKind::ByMovement;
    use super::HorizMove::{Const, UntilFst};
    use super::Movement::{Left, LeftCross, RightCross};
    use crate::event::KeyCode::{Backspace, Delete as Del, Enter, Esc};
    use crate::event::KeyModifiers as Mods;

    let keys = vec![
        (vec![KeyEvent::ctrl('w')],
            vec![Delete(ByMovement {
                movement: LeftCross(UntilFst(WordEnd)),
                amount: 1,
                from_inclusive: false,
                to_inclusive: true,
            })]),
        (vec![KeyEvent { code: Esc, mods: Mods::NONE }],
            vec![
                EndEditBlock,
                Cursor(Left(Const), 1),
                ExitMode
            ]),
        (vec![KeyEvent { code: Enter, mods: Mods::NONE }],
            vec![
                Insert('\n'.to_string()),
                Cursor(RightCross(Const), 1)
            ]),
        (vec![KeyEvent { code: Backspace, mods: Mods::NONE }],
            vec![Delete(ByMovement {
                movement: LeftCross(Const),
                amount: 1,
                from_inclusive: false,
                to_inclusive: true,
            })]),
        (vec![KeyEvent { code: Del, mods: Mods::NONE }],
            vec![Delete(ByMovement {
                movement: RightCross(Const),
                amount: 1,
                from_inclusive: true,
                to_inclusive: false,
            })]),
    ];

    Trie::from_iter(keys.into_iter())
}

////////////////////////////////////////////////////////////////////////////////
// Config extensions                                                          //
////////////////////////////////////////////////////////////////////////////////

pub trait ExtendsCfg<T> {
    fn keys(&self) -> Vec<(Vec<KeyEvent>, Vec<Cmd<T>>)>;
}

impl<T: Clone> ExtendsCfg<T> for Config {
    fn keys(&self) -> Vec<(Vec<KeyEvent>, Vec<Cmd<T>>)> {
        self.keys
            .iter_all_prefix(&[])
            .map(|(keys, cmds)| (Vec::from(keys), cmds.clone().xinto()))
            .collect()
    }
}

impl<D, T> ExtendsCfg<T> for D
where
    D: Deref,
    D::Target: ExtendsCfg<T>,
{
    fn keys(&self) -> Vec<(Vec<KeyEvent>, Vec<Cmd<T>>)> {
        self.deref().keys()
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ExtBuilder<T> {
    pub keys: Option<Vec<(Vec<KeyEvent>, Vec<Cmd<T>>)>>,
}

#[derive(Debug)]
pub struct ExtConfig<T> {
    pub keys: Trie<KeyEvent, Vec<Cmd<T>>>,
}

impl<T> Default for ExtConfig<T> {
    fn default() -> Self {
        Self { keys: Trie::new() }
    }
}

impl<T> ConfigPart for ExtConfig<T>
where
    config::ExtConfig<T>: ConfigPart,
    T: Serialize + for<'a> Deserialize<'a>,
{
    type Deref = DerefChain<<config::ExtConfig<T> as ConfigPart>::Deref, Self>;
    type DerefMut = DerefMutChain<<config::ExtConfig<T> as ConfigPart>::DerefMut, Self>;

    fn global() -> Self::Deref {
        DerefChain {
            host: <config::ExtConfig<T> as ConfigPart>::global(),
            get: |ext| &ext.insert,
        }
    }

    fn global_mut() -> Self::DerefMut {
        DerefMutChain {
            host: <config::ExtConfig<T> as ConfigPart>::global_mut(),
            get: |ext| &ext.insert,
            get_mut: |ext| &mut ext.insert,
        }
    }

    fn update(&mut self, builder: Self::Builder) {
        todo!()
    }
}

impl<T> Build for ExtConfig<T>
where
    T: Serialize + for<'a> Deserialize<'a>,
{
    type Builder = ExtBuilder<T>;
}

impl<T> XFrom<ExtBuilder<T>> for ExtConfig<T> {
    fn xfrom(builder: ExtBuilder<T>) -> ExtConfig<T> {
        Self {
            keys: builder
                .keys
                .map(|ks| Trie::from_iter(ks.into_iter()))
                .unwrap_or_else(Trie::new),
        }
    }
}
