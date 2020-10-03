//! Wrapper module around [`MouseEvent`] and [`MouseButton`]

use super::KeyModifiers;
use crate::utils::{XFrom, XInto};
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
    Down(MouseButton, MousePos, Option<KeyModifiers>),
    Up(MouseButton, MousePos, Option<KeyModifiers>),
    Drag(MouseButton, MousePos, Option<KeyModifiers>),
    ScrollDown(MousePos, Option<KeyModifiers>),
    ScrollUp(MousePos, Option<KeyModifiers>),
}

impl XFrom<event::MouseEvent> for MouseEvent {
    fn xfrom(ev: event::MouseEvent) -> Self {
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
