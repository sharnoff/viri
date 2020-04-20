//! A module for defining some of the more common modes (insert/normal)
//!
//! This mainly serves to provide access to the types used

use serde::{Deserialize, Serialize};

use super::{Cmd, CursorStyle};
use crate::event::KeyEvent;

pub mod insert;
pub mod normal;

// TODO: what more needs to be here?
pub trait Mode<E> {
    fn try_handle(&mut self, key: KeyEvent) -> ModeResult<E>;

    fn cursor_style(&self) -> CursorStyle;
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModeResult<E> {
    NeedsMore,
    NoCommand,
    Cmd(Cmd<E>),
}
