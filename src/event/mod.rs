//! Re-definitions of items from `crossterm::event`
//!
//! For handling of the event stream, please refer to the [`signal`] submodule.
//!
//! There's a few reasons for this. [`KeyEvent`] is re-defined here because we want to use a
//! different [`KeyModifiers`] - one that deserializes more nicely. [`KeyEvent`] is also defined
//! here in order to have an implementation of `Ord`, which is not provided in crossterm (which is
//! reasonable).
//!
//! [`MouseEvent`] is also redefined here in order to use the updated [`KeyModifiers`].
//!
//! [`signal`]: crate::container::signal

mod key;
mod mouse;

pub use key::{KeyCode, KeyEvent, KeyModifiers};
pub use mouse::{MouseButton, MouseEvent};
