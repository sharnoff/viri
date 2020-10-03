//! Wrapper module around [`KeyEvent`] and [`KeyCode`]

use super::KeyModifiers;
use crate::utils::{XFrom, XInto};
use crossterm::event;
use serde::{Deserialize, Serialize};

/// A single key input received
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct KeyEvent {
    pub code: KeyCode,
    pub mods: Option<KeyModifiers>,
}

impl XFrom<event::KeyEvent> for KeyEvent {
    fn xfrom(mut ev: event::KeyEvent) -> Self {
        use event::KeyModifiers as Mods;

        match &mut ev.code {
            event::KeyCode::Char(ref mut c) if c.is_ascii_uppercase() => {
                c.make_ascii_lowercase();
                ev.modifiers |= Mods::SHIFT;
            }
            _ => (),
        }

        Self {
            code: ev.code.xinto(),
            mods: ev.modifiers.xinto(),
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

impl XFrom<event::KeyCode> for KeyCode {
    fn xfrom(code: event::KeyCode) -> KeyCode {
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

/*
impl KeyEvent {
    pub fn none(c: char) -> KeyEvent {
        KeyEvent {
            code: KeyCode::Char(c),
            mods: KeyModifiers::NONE,
        }
    }

    pub fn shift(c: char) -> KeyEvent {
        KeyEvent {
            code: KeyCode::Char(c),
            mods: KeyModifiers::SHIFT,
        }
    }

    pub fn ctrl(c: char) -> KeyEvent {
        KeyEvent {
            code: KeyCode::Char(c),
            mods: KeyModifiers::CTRL,
        }
    }
}
*/
