//! Wrapper module around [`MouseEvent`] and [`MouseButton`]

use super::KeyModifiers;
use crate::XInto;
use crossterm::event;

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
    Moved(MousePos, Option<KeyModifiers>),
    ScrollDown(MousePos, Option<KeyModifiers>),
    ScrollUp(MousePos, Option<KeyModifiers>),
}

impl From<event::MouseEvent> for MouseEvent {
    fn from(ev: event::MouseEvent) -> Self {
        use event::MouseEventKind::{Down, Drag, Moved, ScrollDown, ScrollUp, Up};

        let pos = MousePos {
            x: ev.column,
            y: ev.row,
        };
        let mods = ev.modifiers.xinto();

        match ev.kind {
            Down(b) => Self::Down(b, pos, mods),
            Up(b) => Self::Up(b, pos, mods),
            Drag(b) => Self::Drag(b, pos, mods),
            Moved => Self::Moved(pos, mods),
            ScrollDown => Self::ScrollDown(pos, mods),
            ScrollUp => Self::ScrollUp(pos, mods),
        }
    }
}
