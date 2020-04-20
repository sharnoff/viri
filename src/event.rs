use crossterm::event;
use serde::{Deserialize, Serialize};

pub use crossterm::event::{KeyCode, MouseButton};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct KeyEvent {
    pub code: KeyCode,
    pub mods: KeyModifiers,
}

impl From<event::KeyEvent> for KeyEvent {
    fn from(ev: event::KeyEvent) -> Self {
        Self {
            code: ev.code,
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

#[derive(Copy, Clone, Debug, Eq, PartialEq, Default, Hash, Serialize, Deserialize)]
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
