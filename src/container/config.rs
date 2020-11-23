//! Configuration for the [`Container`](super::Container)

use crate::event::KeyEvent;
use crate::macros::config;
use std::collections::HashSet;

config! {
    /// The configuration for the view container
    pub struct Config (ConfigBuilder) {
        /// The set of keys that are allowed to hide error messages whenever they come up
        #[builder(Vec<KeyEvent> => make_nonempty_hashset, serialize_hashset)]
        pub hide_error_message: HashSet<KeyEvent>,
        #[flatten]
        pub use super::bottom_bar::Config as bottom_bar,
    }
}

const DEFAULT_HIDE_ERR_MSG_KEY: KeyEvent = KeyEvent {
    code: crate::event::KeyCode::Enter,
    mods: None,
};

fn make_nonempty_hashset(vec: Vec<KeyEvent>) -> HashSet<KeyEvent> {
    if vec.is_empty() {
        let mut set = HashSet::new();
        set.insert(DEFAULT_HIDE_ERR_MSG_KEY);
        return set;
    }

    vec.into_iter().collect()
}

fn serialize_hashset(set: &HashSet<KeyEvent>) -> Vec<KeyEvent> {
    set.into_iter().cloned().collect()
}
