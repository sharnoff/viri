//! Wrapper module around [`KeyModifiers`]

use crate::utils::XFrom;
use crossterm::event;
use serde::{Deserialize, Serialize};

/// A set of modifiers attached to a single [`KeyEvent`](super::KeyEvent)
///
/// This is different from crossterm's [`KeyModifiers`](crossterm::event::KeyModifiers) because it
/// gives distinct variants for all of the modifiers that can be read from the terminal.
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum KeyModifiers {
    Shift,
    Alt,
    Ctrl,
    #[serde(rename = "Shift|Alt")]
    #[serde(alias = "Alt|Shift")]
    ShiftAlt,
    #[serde(rename = "Ctrl|Alt")]
    #[serde(alias = "Alt|Ctrl")]
    AltCtrl,
}

impl XFrom<event::KeyModifiers> for Option<KeyModifiers> {
    fn xfrom(mods: event::KeyModifiers) -> Self {
        use crossterm::event::KeyModifiers as Mods;

        let has_shift = mods.contains(Mods::SHIFT);
        let has_ctrl = mods.contains(Mods::CONTROL);
        let has_alt = mods.contains(Mods::ALT);

        use KeyModifiers::*;

        match (has_shift, has_alt, has_ctrl) {
            (false, false, false) => None,
            (true, false, false) => Some(Shift),
            (false, true, false) => Some(Alt),
            (false, false, true) => Some(Ctrl),
            (true, true, false) => Some(ShiftAlt),
            (false, true, true) => Some(AltCtrl),
            _ => panic!("unexpected key modifier combination"),
        }
    }
}
