//! This module defines the different types of things that you can do in the
//! editor - we refer to them as "Views".
//!
//! Customizing this may be most easily done through adding a Rust file to this
//! directory and including it as a sub-module. From there, you can add your
//! custom `View` into the `init` function below, which registers each
//! constructor with a unique name.
//!
//! For example:
//!
//! The startup view is given by the `create_view` function, which should return
//! a `View` given a set of command-line arguments.
//!
//! There is much more detail given in the file itself about the format of the
//! internal system and how to add your own types. Please refer there.

// Yup! Right here!
//
// For starters, Everything in this file is marked with headers, and their names
// only appear at those locations. They are as follows:
//   Header 0: Imports
//   Header 1: Initialization
//   Header 2: Type Definitions
// That should be all you need to get started!

// These are system-type imports - trait definitions, utilities, and things.
// They're here to allow everything else to function.

use crate::config::{Build, ConfigPart};
use crate::container;
use crate::event::KeyEvent;
use crate::mode::config::{dyn_extends_cfg, BaseConfig, ExtendsCfg};
use crate::mode::{self, insert, normal, Cmd, Direction};
use crate::runtime::{Painter, TermSize};
use crate::trie::Trie;
use crate::utils::{self, Never, XFrom, XInto};
use crossterm::style::Colorize;
use serde::{Deserialize, Serialize};
use std::fmt::{self, Debug, Formatter};
use std::rc::Rc;
use std::sync::{Arc, Mutex, MutexGuard};

//-/////////////////////////////////////////////////////////////////////////-//
// Header 0: Imports                                                         //
//                                                                           //
// This is what you'd expect - it's where we put the 'use' statements for    //
// the various sub-modules used in this file.                                //
//                                                                           //
// Builtin ones are marked; change those with caution. Adding your own       //
// should be simple. If you you're importing something other than a sub-     //
// module, that should go at the top of the file, with the rest.             //
//                                                                           //
//-/////////////////////////////////////////////////////////////////////////-//

// Builtin modules:
mod buffer;
mod file;
pub mod split;

// mod your_mod;

//-/////////////////////////////////////////////////////////////////////////-//
// Header 1: Initialization                                                  //
//                                                                           //
// This section defines the various functions that are used for setting up   //
// the various `View`s and the ability to switch between them. It            //
// additionally provides the `init` function that's called by `main` to do   //
// a little bit of setup.                                                    //
//                                                                           //
// General overview (TODO)                                                   //
//                                                                           //
//-/////////////////////////////////////////////////////////////////////////-//

/// The macro expansion that generates an enum over the possible types of `View`s.
/// There's more information in that file itself - the macro is actually *very* simple.
#[macro_use]
mod macros;

viewkind! {
    pub enum ViewKind {
        File: file::View,
        // Foo: your_mod::Foo,
    }
}

// Defined in 'src/config.rs'. The real function signature isn't *quite* this, but it's
// approximately the same.
read_config_fn! {
    pub static CONFIG_LOCATION: &'static str = "views";

    pub fn read_config(cfg_str: &str) {
        struct ViewsConfig {
            file: file::Config,
        }
    }
}

pub fn init() {
    buffer::init();
    file::init();
}

//-/////////////////////////////////////////////////////////////////////////-///
// Header 2: Type Definitions                                                 //
//                                                                            //
// If you're writing your own `View`, this section contains all of the        //
// things you could need to know. (Note that there is also documentation      //
// available on docs.rs as well.) It's unlikely, however, that you'll be      //
// doing something that actually warrants changing part of this section; it   //
// should have most - if not all - of the flexibility that you could be       //
// looking for.                                                               //
//                                                                            //
// As a general overview:                                                     //
//                                                                            //
// There are two traits that matter here: `View` and `ViewContainer`. When    //
// using multiple splits, there will be many of the first, existing in a tree //
// of `View`s conaining other `View`s. (This happens because splits are       //
// themselves just `View`s.)                                                  //
//     The second trait will only have one instance at a time; it serves as a //
// wrapper for the top-level `View` to handle the interactions between the    //
// editor's runtime and the tre of `View`s.                                   //
//                                                                            //
//-////////////////////////////////////////////////////////////////////////-///

/// The central trait for the equivalent of "buffers" or "splits" from other editors
pub trait View {
    /// Re-draws the `View`, using the provided painter to draw to the screen
    ///
    /// The painter handles drawing to the correct location on the screen. Note that the provided
    /// size of the painter may not equal the previous size; this must be accounted for.
    fn refresh(&mut self, painter: &Painter);

    /// Sets the position of the cursor through the painter
    fn refresh_cursor(&self, painter: &Painter);

    /// Records that the `View` has been put into focus, optionally returning the type of refresh
    /// needed, if any.
    fn focus(&mut self) -> Option<RefreshKind> {
        None
    }

    /// Gives the text to display at the bottom-left of the screen
    ///
    /// The second index in the tuple is the width in columns of the text. Note that this function
    /// is distinct from the bottom bar provided by the [`Container`]; that can be set with the
    /// appropriate [`OutputSignal`].
    ///
    /// If `None` is returned, the text that was previously there will not be changed. The default
    /// implementation simply does this.
    ///
    /// [`Container`]: ../container/struct.Container.html
    /// [`OutputSignal`]: enum.OutputSignal.html
    fn bottom_left_text(&mut self) -> Option<(String, usize)> {
        None
    }

    /// Gives the text to display at the bottom-right of the screen
    ///
    /// The second index in the tuple is the width in columns of the text.
    ///
    /// If `None` is returned, the text that was previously there will not be changed. The default
    /// implementation simply does this.
    fn bottom_right_text(&mut self) -> Option<(String, usize)> {
        None
    }

    /// Returns the `View`'s preference for the bottom-left vs. bottom-right text overwriting each
    /// other.
    ///
    /// If true, the bottom-left text will be given precedence when there is not enough room to fit
    /// the results from both [`bottom_left_text`] and [`bottom_right_text`]. The default
    /// implementation returns `true`, but this is not guaranteed to be stable and should be
    /// overwritten when implementing both `bottom_left_text` and `bottom_right_text`.
    ///
    /// [`bottom_left_text`]: #tymethod.bottom_left_text
    /// [`bottom_right_text`]: #tymethod.bottom_right_text
    fn prefer_bottom_left(&self) -> bool {
        false
    }

    /// Constructs what the totality of the text on the bottom bar should read, given the width.
    ///
    /// This function is sometimes used in place of `bottom_{left,right}_text`, but not always. The
    /// default implementation uses these two methods.
    fn construct_bottom_text(&mut self, width: u16) -> String {
        let left = self.bottom_left_text();
        let right = self.bottom_right_text();
        let prefer_left = self.prefer_bottom_left();

        let mut left_width = left.as_ref().map(|(_, w)| *w).unwrap_or(0);
        let mut right_width = right.as_ref().map(|(_, w)| *w).unwrap_or(0);

        let left_too_big = left_width > width as usize;
        let right_too_big = right_width > width as usize;

        // +1 so that we have space between them
        let combo_too_big = left_width + right_width + 1 > (width as usize);

        let do_left = left.is_some() && !left_too_big && (!combo_too_big || prefer_left);
        let do_right = right.is_some() && !right_too_big && (!combo_too_big || !prefer_left);

        if !do_left {
            left_width = 0
        };
        if !do_right {
            right_width = 0
        };

        let mut text = String::new();

        if do_left {
            text.push_str(left.unwrap().0.as_ref());
        }

        // Add spaces to cover the difference
        let difference = width - (left_width + right_width) as u16;
        let middle_str = utils::blank_str(difference);
        text.push_str(middle_str);

        if do_right {
            // ^ See: Benny Goodman and Peggy Lee
            text.push_str(right.unwrap().0.as_ref());
        }

        text
    }
}

/// `View`s that may be concretely instantiated
///
/// All [`View`]s implement this trait, with the exception of `ViewBuffer`, which cannot be used
/// directly.
pub trait ConcreteView: View + SignalHandler {}

/// Helper for `ConcreteView`
///
/// Because `ConcreteView` is required elsewhere to be object-safe, this trait is defined to allow
/// instantiating views. It is used in the [`to_view`] method on `ViewKind`.
///
/// [`to_view`]: enum.ViewKind.html#method.to_view
pub trait ConstructedView: ConcreteView {
    /// Initializes the `View` with the given arguments and size
    ///
    /// Formalizing the arguments is currently a work in progress.
    // TODO: ^ see above
    fn init<S: AsRef<str>>(size: TermSize, args: &[S]) -> Self;
}

/// Types that can handle `Container` signals
///
/// This trait marks types that can receive the signals provided by the top-level [`Container`] and
/// produce the required view [`OutputSignal`].
///
/// [`Container`]: ../container/struct.Container.html
/// [`OutputSignal`]: enum.OutputSignal.html
pub trait SignalHandler {
    /// Tries to handle an input signal, returning the output signals if handling was possible
    fn try_handle(&mut self, signal: container::Signal) -> Option<Vec<OutputSignal>>;
}

/// Distinct from `runtime::Signal` or a `container::Signal`, this communicates between a `View`
/// and its parent, eventually leading up to the host `Container`.
pub enum OutputSignal {
    NeedsRefresh(RefreshKind),
    SaveBottomBar,
    SetBottomBar {
        prefix: Option<char>,
        value: String,
        width: usize,
        // The column to place the cursor there. If the cursor should not be in the bottom bar,
        // then this should be emulated with the `BottomTextUpdate` signal and an implementation of
        // `View::bottom_left_text`.
        //
        // Note that this column *does* include the prefix, and starts from 0.
        //
        // If this field is `None`, the input mode will not be changed
        cursor_col: Option<usize>,
    },
    LeaveBottomBar,
    ClearBottomBar,
    Open(Direction, Box<dyn ConcreteView>),
    /// Indicates a request to replace the current view with the given one. This *must* be
    /// performed as the sender may now have an invalid state
    Replace(Box<dyn ConcreteView>),
    Close,
    /// A request to shift the cursor's focus in the given direction by the given number of
    /// `View`s.
    ShiftFocus(Direction, usize),
    NoSuchCmd,
    WaitingForMore,
}

/// How much of a refresh needs to be done?
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RefreshKind {
    // Ranked in ascending order of magnitude.
    Cursor,
    BottomText,
    Inner,
    Full,
}

/// Commands for manipulating the currently-focussed `View`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MetaCmd<T> {
    /// A request to close the current view
    TryClose(ExitKind),

    /// A request to split the current view in two, placing the new view in the given direction
    /// from the current one. The focus should shift from the current `View` to the new one
    Split(Direction),

    /// A request to open a view corresponding to the given `ViewKind` in a new `View`, splitting
    /// the current one in the given direction. The focus should shift from the current `View` to
    /// the new one
    Open(Direction, ViewKind),

    /// A request to replace the current view with the given `ViewKind`. If the current view is
    /// unable to be closed, this may alternatively open the other view in a split, where the new
    /// `View` is now focussed.
    Replace(ViewKind),

    /// A request to move the cursor's focus a number of views in the given direction
    ShiftFocus(Direction, usize),

    /// Any custom operation relevant only to that particular view
    Custom(T),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ExitKind {
    ReqSave,
    NoSave,
}

// TODO: Add warnings, etc here
#[derive(Clone, Debug)]
pub enum ExitSignal {
    Nothing,
}

impl OutputSignal {
    /// Produces an output signal corresponding to an error with the given message
    ///
    /// If `format` is true, the message will be made red. Otherwise, the formatting will be left
    /// as is. `width` should give the displayed width of the message - if not given, it will be
    /// assumed to be equal to `msg.len()`
    pub fn error(msg: &str, width: Option<usize>, format: bool) -> OutputSignal {
        let value = match format {
            true => String::from(msg).red().to_string(),
            false => msg.into(),
        };

        Self::SetBottomBar {
            prefix: None,
            value,
            width: width.unwrap_or_else(|| msg.len()),
            cursor_col: None,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Config stuff for `MetaCmd`                                                 //
////////////////////////////////////////////////////////////////////////////////

/// A builder for mode commands relating to the
#[derive(Serialize, Deserialize)]
pub struct ExtBuilder {
    insert: insert::ExtBuilder<MetaCmd<Never>>,
    normal: normal::ExtBuilder<MetaCmd<Never>>,
}

pub type ExtConfig = mode::config::ExtConfig<MetaCmd<Never>>;

lazy_static::lazy_static! {
    static ref GLOBAL: Arc<Mutex<ExtConfig>> = Arc::new(Mutex::new(Default::default()));
}

impl ConfigPart for ExtConfig {
    type Deref = MutexGuard<'static, Self>;
    type DerefMut = MutexGuard<'static, Self>;

    fn global() -> Self::Deref {
        GLOBAL.lock().unwrap()
    }
    fn global_mut() -> Self::DerefMut {
        GLOBAL.lock().unwrap()
    }

    fn update(&mut self, builder: ExtBuilder) {
        self.insert.update(builder.insert);
    }
}

impl Build for ExtConfig {
    type Builder = ExtBuilder;
}

impl Default for ExtConfig {
    fn default() -> Self {
        Self {
            parent: || Box::new(BaseConfig::global()),
            insert: Default::default(),
            normal: normal::ExtConfig {
                keys: default_normal_keybindings(),
            },
        }
    }
}

#[rustfmt::skip]
fn default_normal_keybindings() -> Trie<KeyEvent, Vec<Cmd<MetaCmd<Never>>>> {
    use Cmd::Other;
    use MetaCmd::ShiftFocus;
    use Direction::{Up, Down, Left, Right};

    let keys = vec![
        (vec![KeyEvent::ctrl('w'), KeyEvent::none('k')],
            vec![Other(ShiftFocus(Up, 1))]),
        (vec![KeyEvent::ctrl('w'), KeyEvent::none('j')],
            vec![Other(ShiftFocus(Down, 1))]),
        (vec![KeyEvent::ctrl('w'), KeyEvent::none('h')],
            vec![Other(ShiftFocus(Left, 1))]),
        (vec![KeyEvent::ctrl('w'), KeyEvent::none('l')],
            vec![Other(ShiftFocus(Right, 1))]),
    ];

    Trie::from_iter(keys.into_iter())
}

impl XFrom<ExtBuilder> for ExtConfig {
    fn xfrom(builder: ExtBuilder) -> Self {
        Self {
            parent: || Box::new(BaseConfig::global()),
            insert: builder.insert.xinto(),
            normal: builder.normal.xinto(),
        }
    }
}

fn wrap_config<T>(ext_cfg: Box<dyn ExtendsCfg<MetaCmd<Never>>>) -> Box<dyn ExtendsCfg<MetaCmd<T>>> {
    let rc: Rc<dyn ExtendsCfg<MetaCmd<Never>>> = ext_cfg.into();

    struct InsertExt {
        inner: Rc<dyn ExtendsCfg<MetaCmd<Never>>>,
    }

    struct NormalExt {
        inner: Rc<dyn ExtendsCfg<MetaCmd<Never>>>,
    }

    impl<T> insert::ExtendsCfg<MetaCmd<T>> for InsertExt {
        fn keys(&self) -> Vec<(Vec<KeyEvent>, Vec<Cmd<MetaCmd<T>>>)> {
            self.inner
                .insert()
                .keys()
                .into_iter()
                .map(|(keys, cmds)| (keys, cmds.xinto()))
                .collect()
        }
    }

    impl<T> normal::ExtendsCfg<MetaCmd<T>> for NormalExt {
        fn keys(&self) -> Vec<(Vec<KeyEvent>, Vec<Cmd<MetaCmd<T>>>)> {
            self.inner
                .normal()
                .keys()
                .into_iter()
                .map(|(keys, cmds)| (keys, cmds.xinto()))
                .collect()
        }
    }

    dyn_extends_cfg(
        move || rc.clone(),
        |c| c.parent().map(wrap_config),
        |c| Box::new(InsertExt { inner: c }),
        |c| Box::new(NormalExt { inner: c }),
    )
}

impl<T: 'static> ExtendsCfg<MetaCmd<T>> for ExtConfig {
    fn insert<'a>(&'a self) -> Box<dyn 'a + insert::ExtendsCfg<MetaCmd<T>>> {
        Box::new(&self.insert)
    }

    fn normal<'a>(&'a self) -> Box<dyn 'a + normal::ExtendsCfg<MetaCmd<T>>> {
        Box::new(&self.normal)
    }

    fn parent(&self) -> Option<Box<dyn ExtendsCfg<MetaCmd<T>>>> {
        Some(wrap_config((self.parent)()))
    }
}

impl<T> insert::ExtendsCfg<MetaCmd<T>> for insert::ExtConfig<MetaCmd<Never>> {
    fn keys(&self) -> Vec<(Vec<KeyEvent>, Vec<Cmd<MetaCmd<T>>>)> {
        self.keys
            .iter_all_prefix(&[])
            .map(|(keys, cmds)| (Vec::from(keys), cmds.clone().xinto()))
            .collect()
    }
}

impl<T> normal::ExtendsCfg<MetaCmd<T>> for normal::ExtConfig<MetaCmd<Never>> {
    fn keys(&self) -> Vec<(Vec<KeyEvent>, Vec<Cmd<MetaCmd<T>>>)> {
        self.keys
            .iter_all_prefix(&[])
            .map(|(keys, cmds)| (Vec::from(keys), cmds.clone().xinto()))
            .collect()
    }
}

////////////////////////////////////////////////////////////////////////////////
// Boilerplate trait implementations                                          //
////////////////////////////////////////////////////////////////////////////////

impl Debug for OutputSignal {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use OutputSignal::{
            ClearBottomBar, Close, LeaveBottomBar, NeedsRefresh, NoSuchCmd, Open, Replace,
            SaveBottomBar, SetBottomBar, ShiftFocus, WaitingForMore,
        };

        match self {
            NeedsRefresh(k) => write!(f, "NeedsRefresh({:?})", k),
            SaveBottomBar => write!(f, "SaveBottomBar"),
            SetBottomBar {
                prefix,
                value,
                width,
                cursor_col,
            } => f
                .debug_struct("SetBottomBar")
                .field("prefix", prefix)
                .field("value", value)
                .field("width", width)
                .field("cursor_col", cursor_col)
                .finish(),
            LeaveBottomBar => write!(f, "LeaveBottomBar"),
            ClearBottomBar => write!(f, "ClearBottomBar"),
            Open(d, _) => write!(f, "Open({:?}, ..)", d),
            Replace(_) => write!(f, "Replace(_)"),
            Close => write!(f, "Close"),
            ShiftFocus(d, n) => write!(f, "ShiftFocus({:?}, {:?})", d, n),
            NoSuchCmd => write!(f, "NoSuchCmd"),
            WaitingForMore => write!(f, "WaitingForMore"),
        }
    }
}

impl<T> XFrom<MetaCmd<Never>> for MetaCmd<T> {
    fn xfrom(meta: MetaCmd<Never>) -> Self {
        use MetaCmd::{Custom, Open, Replace, ShiftFocus, Split, TryClose};

        match meta {
            TryClose(kind) => TryClose(kind),
            Split(dir) => Split(dir),
            Open(dir, kind) => Open(dir, kind),
            Replace(kind) => Replace(kind),
            ShiftFocus(dir, n) => ShiftFocus(dir, n),
            Custom(never) => Custom(never.xinto()),
        }
    }
}
