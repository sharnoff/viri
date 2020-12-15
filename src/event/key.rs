//! Wrapper module around [`KeyEvent`] and [`KeyCode`]

use crate::{XFrom, XInto};
use crossterm::event;
use serde::{Deserialize, Serialize};

/// A single key input received
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct KeyEvent {
    pub code: KeyCode,
    pub mods: Option<KeyModifiers>,
}

impl From<event::KeyEvent> for KeyEvent {
    fn from(ev: event::KeyEvent) -> Self {
        Self {
            code: ev.code.into(),
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

/// A set of modifiers attached to a single [`KeyEvent`]
///
/// This is quite different from crossterm's [`KeyModifiers`](crossterm::event::KeyModifiers)
/// because (1) it disregards shift and (2) it explicitly lists possible combinations of the
/// remaining modifiers (none of them may occur here).
///
/// It's worth noting `alt+ctrl` is not possible for key inputs, but *is* possible on mouse inputs
/// - those are represented by [`MouseModifiers`](super::MouseModifiers).
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum KeyModifiers {
    Alt,
    Ctrl,
}

// We need to implement XFrom in order to get conversion to Option
impl XFrom<event::KeyModifiers> for Option<KeyModifiers> {
    fn xfrom(mods: event::KeyModifiers) -> Self {
        use crossterm::event::KeyModifiers as Mods;

        let has_ctrl = mods.contains(Mods::CONTROL);
        let has_alt = mods.contains(Mods::ALT);

        use KeyModifiers::*;

        match (has_alt, has_ctrl) {
            (false, false) => None,
            (true, false) => Some(Alt),
            (false, true) => Some(Ctrl),
            (true, true) => panic!("unexpected key input combination; please file a bug report indicating that this error occured"),
        }
    }
}
