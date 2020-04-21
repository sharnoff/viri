//! Re-definitions of items from `crossterm::event`
//!
//! There's a few reasons for this. [`KeyEvent`] is re-defined here because we want to use a
//! different [`KeyModifiers`] - one that deserializes more nicely. [`KeyEvent`] is also defined
//! here in order to have an implementation of `Ord`, which is not provided in crossterm (which is
//! reasonable).
//!
//! [`MouseEvent`] is also redefined here in order to use the updated [`KeyModifiers`].
//!
//! [`KeyEvent`]: struct.KeyEvent.html
//! [`KeyModifiers`]: struct.KeyModifiers.html
//! [`MouseEvent`]: enum.MouseEvent.html

use crossterm::event;
use serde::{Deserialize, Serialize};

pub use crossterm::event::MouseButton;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct KeyEvent {
    pub code: KeyCode,
    pub mods: KeyModifiers,
}

impl From<event::KeyEvent> for KeyEvent {
    fn from(ev: event::KeyEvent) -> Self {
        Self {
            code: ev.code.into(),
            mods: ev.modifiers.into(),
        }
    }
}

impl KeyEvent {
    pub fn none(c: char) -> KeyEvent {
        KeyEvent {
            code: KeyCode::Char(c),
            mods: KeyModifiers::NONE,
        }
    }

    pub fn ctrl(c: char) -> KeyEvent {
        KeyEvent {
            code: KeyCode::Char(c),
            mods: KeyModifiers::CTRL,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum KeyCode {
    Backspace,
    Enter,
    Left,
    Right,
    Up,
    Down,
    Home,
    End,
    PageUp,
    PageDown,
    Tab,
    BackTab,
    Delete,
    Insert,
    F(u8),
    Char(char),
    Null,
    Esc,
}

impl From<event::KeyCode> for KeyCode {
    fn from(code: event::KeyCode) -> KeyCode {
        use KeyCode::*;
        match code {
            event::KeyCode::Backspace => Backspace,
            event::KeyCode::Enter => Enter,
            event::KeyCode::Left => Left,
            event::KeyCode::Right => Right,
            event::KeyCode::Up => Up,
            event::KeyCode::Down => Down,
            event::KeyCode::Home => Home,
            event::KeyCode::End => End,
            event::KeyCode::PageUp => PageUp,
            event::KeyCode::PageDown => PageDown,
            event::KeyCode::Tab => Tab,
            event::KeyCode::BackTab => BackTab,
            event::KeyCode::Delete => Delete,
            event::KeyCode::Insert => Insert,
            event::KeyCode::F(n) => F(n),
            event::KeyCode::Char(c) => Char(c),
            event::KeyCode::Null => Null,
            event::KeyCode::Esc => Esc,
        }
    }
}

#[derive(
    Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Default, Hash, Serialize, Deserialize,
)]
pub struct KeyModifiers {
    pub shift: bool,
    pub ctrl: bool,
    pub alt: bool,
}

impl KeyModifiers {
    pub const NONE: KeyModifiers = KeyModifiers {
        shift: false,
        ctrl: false,
        alt: false,
    };
    pub const SHIFT: KeyModifiers = KeyModifiers {
        shift: true,
        ..Self::NONE
    };
    pub const CTRL: KeyModifiers = KeyModifiers {
        ctrl: true,
        ..Self::NONE
    };
    pub const ALT: KeyModifiers = KeyModifiers {
        alt: true,
        ..Self::NONE
    };
}

impl From<event::KeyModifiers> for KeyModifiers {
    fn from(mods: event::KeyModifiers) -> Self {
        use event::KeyModifiers as Mods;

        Self {
            shift: mods.contains(Mods::SHIFT),
            ctrl: mods.contains(Mods::CONTROL),
            alt: mods.contains(Mods::ALT),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub enum MouseEvent {
    Down(MouseButton, u16, u16, KeyModifiers),
    Up(MouseButton, u16, u16, KeyModifiers),
    Drag(MouseButton, u16, u16, KeyModifiers),
    ScrollDown(u16, u16, KeyModifiers),
    ScrollUp(u16, u16, KeyModifiers),
}

impl From<event::MouseEvent> for MouseEvent {
    fn from(ev: event::MouseEvent) -> Self {
        use event::MouseEvent::{Down, Drag, ScrollDown, ScrollUp, Up};

        match ev {
            Down(b, x, y, mods) => Self::Down(b, x, y, mods.into()),
            Up(b, x, y, mods) => Self::Up(b, x, y, mods.into()),
            Drag(b, x, y, mods) => Self::Drag(b, x, y, mods.into()),
            ScrollDown(x, y, mods) => Self::ScrollDown(x, y, mods.into()),
            ScrollUp(x, y, mods) => Self::ScrollUp(x, y, mods.into()),
        }
    }
}
