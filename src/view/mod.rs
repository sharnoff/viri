//! Internal [`View`] functioning
//!
// TODO-DOC: Stuff about what a `View` is.
//!
//! This module only provides the facilities for interaction *between* [`View`]s; the entrypoint
//! for handling the tree of `View`s is taken care of by the [`container`](crate::container) module.

use crate::macros::{config, init};
use crate::TermSize;

init!();

config! {
    pub struct Config (ConfigBuilder) {
        // #[builder(Vec<KeyBinding> => KeyBinding::to_hashes, KeyBinding::from_hashes)]
        // key_bindings: () = (),
    }
}

pub enum ModeKind {}

#[derive(Debug, Copy, Clone, Default, serde::Serialize, serde::Deserialize)]
struct KeyBinding;

impl KeyBinding {
    fn to_hashes(keys: Vec<KeyBinding>) -> () {
        todo!()
    }

    fn from_hashes(hashes: &()) -> Vec<KeyBinding> {
        todo!()
    }
}

pub trait View {}

pub enum OutputSignal {}

pub struct SplashView;

impl View for SplashView {}

pub fn splash_view(size: TermSize) -> SplashView {
    todo!()
}

pub fn path_view(size: TermSize) -> Box<dyn View> {
    todo!()
}
