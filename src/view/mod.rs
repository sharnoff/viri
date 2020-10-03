//! Internal [`View`] functioning
//!
// TODO: Stuff about what a `View` is.
//!
//! This module only provides the facilities for interaction *between* [`View`]s; the entrypoint
//! for handling the tree of `View`s is taken care of by the [`container`](crate::container) module.

use crate::macros::{config, init};

init!();

config! {
    pub struct Config (ConfigBuilder) {
        #[builder(Vec<KeyBinding> => KeyBinding::to_hashes, KeyBinding::from_hashes)]
        key_bindings: () = (),
    }
}

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
