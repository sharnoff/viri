//! A helper module for managing switching between modes in a `FileView`

use crate::event::KeyEvent;
use crate::mode::{insert::InsertMode, normal::NormalMode};
use crate::mode::{Cmd, CursorStyle, Mode};
use crate::text::ContentProvider;
use crate::views::{buffer::ViewBuffer, OutputSignal};

const INSERT_NAME: Option<(&'static str, usize)> = Some(("-- INSERT --", 12));
const NORMAL_NAME: Option<(&'static str, usize)> = /* Some(("-- NORMAL --", 12)) */ None;

#[derive(Debug)]
pub enum Modes {
    Normal(NormalMode),
    Insert(InsertMode),
}

impl Modes {
    pub fn cursor_style(&self) -> CursorStyle {
        match self {
            Self::Normal(m) => m.cursor_style(),
            Self::Insert(m) => m.cursor_style(),
        }
    }

    pub fn expecting_input(&self) -> bool {
        match self {
            Self::Normal(m) => m.expecting_input(),
            Self::Insert(m) => m.expecting_input(),
        }
    }

    pub fn try_name_with_width(&self) -> Option<(&'static str, usize)> {
        match self {
            Self::Normal(_) => NORMAL_NAME,
            Self::Insert(_) => INSERT_NAME,
        }
    }

    pub fn handle<P: ContentProvider>(
        &mut self,
        buf: &mut ViewBuffer<P>,
        key: KeyEvent,
    ) -> OutputSignal {
        todo!()
    }
}

impl Default for Modes {
    fn default() -> Self {
        Self::Normal(NormalMode::new())
    }
}
