//! Internal [`View`] functioning
//!
// TODO-DOC: Stuff about what a `View` is.
//!
//! This module only provides the facilities for interaction *between* [`View`]s; the entrypoint
//! for handling the tree of `View`s is taken care of by the [`container`](crate::container) module.

use crate::any::{Any, BoxedAny};
use crate::config::{Attribute, GetAttrAny};
use crate::container::{Input, Painter, Refresh};
use crate::event::KeyEvent;
use crate::macros::{async_method, config, impl_GetAttrAny, init};
use crate::modes::{ModeKind, ModeOutput, ModeSet, TryFromWithModes};
use crate::utils::Never;
use crate::{TermPos, TermSize, Textual};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::ops::Deref;

mod file;
mod splash;

pub use file::FileView;
pub use splash::SplashView;

init!();

config! {
    pub struct Config (ConfigBuilder) {
        keys: ModeSet<Command<Never>> = default_keybindings(),
    }
}

fn default_keybindings() -> ModeSet<Command<Never>> {
    /*
    register_DynClone!(Command<Never, String>);

    let yaml_str = include_str!("default_keybindings.yml");

    serde_yaml::from_str(yaml_str)
        .unwrap_or_else(|e| panic!("failed to deserialize built-in `View` keybindings: {}", e))
    */

    todo!()
}

// @def view::Command v0
#[derive(Debug, Clone, Serialize, Deserialize)]
enum Command<T, M = ModeKind> {
    // TODO-FEATURE: add other general commands here
    ChangeMode(M),
    Focus(Focus),
    NoSuchKeybinding(Vec<KeyEvent>),
    Other(T),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum Focus {
    Direction(Direction),
}

impl<T: 'static + Any + Send + Sync> ModeOutput for Command<T>
where
    T: 'static + Any + Send + Sync + Clone,
{
    type WithModesSet = Self;

    fn as_switch_mode(&self) -> Option<ModeKind> {
        match self {
            Command::ChangeMode(k) => Some(*k),
            _ => None,
        }
    }

    fn switches_provider(&self) -> bool {
        match self {
            Command::ChangeMode(_) | Command::Focus(_) => true,
            Command::Other(_) | Command::NoSuchKeybinding(_) => false,
        }
    }

    fn make_failed(keys: Vec<KeyEvent>) -> Self {
        Command::NoSuchKeybinding(keys)
    }
}

impl<T> TryFromWithModes for Command<T> {
    type Input = Command<T, String>;

    fn try_from_with_modes(
        input: Self::Input,
        modes: &HashMap<String, ModeKind>,
    ) -> Result<Command<T>, String> {
        use Command::*;

        let this = match input {
            ChangeMode(m) => ChangeMode(ModeKind::try_from_with_modes(m, modes)?),
            NoSuchKeybinding(ks) => NoSuchKeybinding(ks),
            Focus(f) => Focus(f),
            Other(t) => Other(t),
        };

        Ok(this)
    }
}

/// The raison d'être of this module
///
/// For more information, refer to the [module-level documentation](self)
pub trait View: Send + Sync + GetAttrAny {
    #[async_method]
    async fn handle(
        &mut self,
        input: Input,
        bottom_bar: &mut dyn Textual,
    ) -> (OutputSignal, Option<Input>);

    #[async_method]
    async fn refresh<'a>(&'a mut self, painter: Painter<'a>);

    #[async_method]
    async fn cursor_pos(&self) -> Option<TermPos>;

    // #[async_method]
    // async fn can_exit(&self, kind: ExitKind) -> bool {
    //     true
    // }

    // #[async_method]
    // async fn exit(this: Box<dyn View>, kind: ExitKind) -> io::Result<()> {
    //     Ok(())
    // }
}

impl<D: Send + Sync + Deref<Target = dyn View>> GetAttrAny for D {
    #[async_method]
    async fn get_attr_any(&self, attr: Attribute) -> Option<BoxedAny> {
        (Deref::deref(self) as &dyn View).get_attr_any(attr).await
    }
}

type Constructor = Box<dyn FnOnce(TermSize, &Refresh) -> Box<dyn View>>;

// @def enum-Direction v0
pub type Direction = crate::utils::Directional<()>;

/// The result of a [`View`]'s handling of input
pub enum OutputSignal {
    Open(Direction, Constructor),
    ReplaceThis(Constructor),
    ShiftFocus(Direction, usize),
    WaitForMore,
}

// pub enum ExitKind {}

pub fn path_view(path: String, size: TermSize, refresh: Refresh) -> Box<dyn View> {
    todo!()
}
