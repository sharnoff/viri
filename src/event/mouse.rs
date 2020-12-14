//! Wrapper module around [`MouseEvent`] and [`MouseButton`]

use crate::{XFrom, XInto};
use crossterm::event;
use serde::{Deserialize, Serialize};

/// A re-export of crossterm's `MouseButton`
pub use crossterm::event::MouseButton;

/// The position of the mouse within the terminal
///
/// This is primarily used within [`MouseEvent`] to give the
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct MousePos {
    pub x: u16,
    pub y: u16,
}

/// A mouse event
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum MouseEvent {
    Down(MouseButton, MousePos, Option<MouseModifiers>),
    Up(MouseButton, MousePos, Option<MouseModifiers>),
    Drag(MouseButton, MousePos, Option<MouseModifiers>),
    ScrollDown(MousePos, Option<MouseModifiers>),
    ScrollUp(MousePos, Option<MouseModifiers>),
}

/// The set of modifiers attached to a [`MouseEvent`]
///
/// This is distinct from [`KeyModifiers`](super::KeyModifiers) in that mouse events can have
/// `alt+ctrl` reported, while key presses cannot.
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum MouseModifiers {
    Alt,
    Ctrl,
    #[serde(alias = "Alt|Ctrl")]
    #[serde(alias = "Ctrl|Alt")]
    AltCtrl,
}

impl From<event::MouseEvent> for MouseEvent {
    fn from(ev: event::MouseEvent) -> Self {
        use event::MouseEvent::{Down, Drag, ScrollDown, ScrollUp, Up};

        match ev {
            Down(b, x, y, mods) => Self::Down(b, MousePos { x, y }, mods.xinto()),
            Up(b, x, y, mods) => Self::Up(b, MousePos { x, y }, mods.xinto()),
            Drag(b, x, y, mods) => Self::Drag(b, MousePos { x, y }, mods.xinto()),
            ScrollDown(x, y, mods) => Self::ScrollDown(MousePos { x, y }, mods.xinto()),
            ScrollUp(x, y, mods) => Self::ScrollUp(MousePos { x, y }, mods.xinto()),
        }
    }
}

// We need to implement XFrom in order to get conversion to Option
impl XFrom<event::KeyModifiers> for Option<MouseModifiers> {
    fn xfrom(mods: event::KeyModifiers) -> Self {
        use crossterm::event::KeyModifiers as Mods;

        let has_ctrl = mods.contains(Mods::CONTROL);
        let has_alt = mods.contains(Mods::ALT);

        use MouseModifiers::*;

        match (has_alt, has_ctrl) {
            (false, false) => None,
            (true, false) => Some(Alt),
            (false, true) => Some(Ctrl),
            (true, true) => Some(AltCtrl),
        }
    }
}
