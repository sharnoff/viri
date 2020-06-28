// TODO: Module-level documentation

use super::{Cmd, CursorStyle, Error};
use crate::config::{Build, ConfigPart, DerefChain, DerefMutChain};
use crate::event::KeyEvent;
use crate::mode::config;
use crate::trie::Trie;
use crate::utils::{Never, OpaqueOption, XFrom, XInto};
use serde::{Deserialize, Serialize};
use std::fmt::{self, Debug, Formatter};
use std::marker::PhantomData;
use std::ops::Deref;
use std::sync::{Arc, Mutex, MutexGuard};

pub mod combinators;
pub mod delete;
pub mod movement;
pub mod scroll;

use combinators::{numerical, set, single, wrap};

/// The type responsible for handling inputs while in "normal" mode
pub struct Mode<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
{
    /// The ongoing set of parsers that might be able to consume the next key input
    parsers: Option<combinators::Set<Vec<Cmd<T>>>>,
    _marker: PhantomData<Conf>,
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

impl<T, Conf> Default for Mode<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
{
    fn default() -> Self {
        Self {
            parsers: None,
            _marker: PhantomData,
        }
    }
}

impl<T, Conf> Mode<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
    T: 'static + Clone,
    Conf: 'static,
{
    fn reset_parsers(&mut self) {
        let movement = wrap(numerical(movement::Parser::new()), |(n, m)| {
            vec![Cmd::Cursor(m, n.unwrap_or(1))]
        });

        let undo = wrap(
            numerical(single(KeyEvent::none('u'), Priority::Builtin)),
            |(n, _)| vec![Cmd::Undo(n.unwrap_or(1))],
        );

        let redo = wrap(
            numerical(single(KeyEvent::ctrl('r'), Priority::Builtin)),
            |(n, _)| vec![Cmd::Redo(n.unwrap_or(1))],
        );

        self.parsers = Some(set(vec![
            Box::new(movement),
            Box::new(scroll::Parser::new()),
            Box::new(delete::Parser::new()),
            Box::new(undo),
            Box::new(redo),
            Box::new(Misc::new()),
        ]));
    }
}

impl<T, Conf> super::Mode<T, Conf> for Mode<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
    T: 'static + Clone,
    Conf: 'static,
{
    const NAME: Option<&'static str> = Some("-- NORMAL --");

    fn try_handle(&mut self, key: KeyEvent) -> Result<Vec<Cmd<T>>, Error> {
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

impl<T, Conf> Debug for Mode<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("normal::Mode")
            .field("parsers", &OpaqueOption::from(&self.parsers))
            .finish()
    }
}

/// A parser for the miscellaneous singleton commands
struct Misc<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
{
    stack: Vec<KeyEvent>,
    get_conf: fn() -> <config::ExtConfig<Conf> as ConfigPart>::Deref,
    _marker: PhantomData<T>,
}

impl<T, Conf> Default for Misc<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
{
    fn default() -> Self {
        Self {
            stack: Vec::new(),
            get_conf: <config::ExtConfig<Conf> as ConfigPart>::global,
            _marker: PhantomData,
        }
    }
}

impl<T, Conf> Misc<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
{
    fn new() -> Self {
        Self::default()
    }
}

impl<T, Conf> ParseState for Misc<T, Conf>
where
    config::ExtConfig<Conf>: config::ExtendsCfg<T> + ConfigPart,
    T: Clone,
    Conf: 'static,
{
    type Output = Vec<Cmd<T>>;

    fn add(&mut self, key: KeyEvent) -> ParseResult<Self::Output> {
        self.stack.push(key);

        let ext_cfg = (self.get_conf)();
        let cfgs = config::get_all(Box::new(ext_cfg));
        let cfg = Trie::from_iter(cfgs.iter().map(|c| c.normal().keys()).flatten());

        let node = cfg.find(&self.stack);

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
                ParseResult::Success(Priority::Builtin, n.extract().to_vec())
            }
            // Some(n) if n.size > 1
            _ => ParseResult::NeedsMore,
        }
    }

    fn max_priority(&self) -> Option<Priority> {
        let cfgs = config::get_all(Box::new((self.get_conf)()));
        let cfg = Trie::from_iter(cfgs.iter().map(|c| c.normal().keys()).flatten());

        if cfg.find(&self.stack)?.size() == 0 {
            None
        } else {
            Some(Priority::Builtin)
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Base config stuff                                                                              //
////////////////////////////////////////////////////////////////////////////////////////////////////

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
    use super::Cmd::{EnterMode, Cursor, ExitMode, Insert, StartEditBlock};
    use super::HorizMove::{Const, LineBoundary};
    use super::ModeKind;
    use super::Movement::{Right, RightCross, Left};
    use crate::event::{KeyCode::Esc, KeyModifiers as Mods};

    let keys = vec![
        // (mostly) meaningless for now - this will be available once colon "normal" mode will be
        // allowed to switch back to colon "insert" mode
        (vec![KeyEvent { code: Esc, mods: Mods::NONE }],
            vec![ExitMode],
        ),

        // Switching to insert mode
        (vec![KeyEvent::none('i')],
            vec![
                StartEditBlock,
                EnterMode(ModeKind::Insert),
            ]),
        (vec![KeyEvent::none('a')],
            vec![
                StartEditBlock,
                EnterMode(ModeKind::Insert),
                Cursor(Right(Const), 1)
            ]),
        (vec![KeyEvent::none('A')],
            vec![
                StartEditBlock,
                EnterMode(ModeKind::Insert),
                Cursor(Right(LineBoundary), 1),
            ]),

        (vec![KeyEvent::none('o')],
            vec![
                StartEditBlock,
                EnterMode(ModeKind::Insert),
                Cursor(Right(LineBoundary), 1),
                Insert("\n".into()),
                Cursor(RightCross(Const), 1),
            ]),
        (vec![KeyEvent::none('O')],
            vec![
                StartEditBlock,
                EnterMode(ModeKind::Insert),
                Cursor(Left(LineBoundary), 1),
                Insert("\n".into()),
            ]),
    ];

    Trie::from_iter(keys.into_iter())
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Config extensions                                                                              //
////////////////////////////////////////////////////////////////////////////////////////////////////

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
            get: |ext| &ext.normal,
        }
    }

    fn global_mut() -> Self::DerefMut {
        DerefMutChain {
            host: <config::ExtConfig<T> as ConfigPart>::global_mut(),
            get: |ext| &ext.normal,
            get_mut: |ext| &mut ext.normal,
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
