//! Wrapper module for [`BottomBar`] and related types

use crate::config::GetAttr;
use crate::macros::config;
use crate::TermSize;

mod component;
mod condition;
mod layout;
mod time;

use component::Component;
use condition::Condition;
use layout::Layout;
use time::TimeFormat;

config! {
    pub struct Config (ConfigBuilder) {
        layout: Layout = Layout::default(),
    }
}

pub struct BottomBar;

/// The evaluation context required for rendering the [`BottomBar`]
///
/// An object implementing this trait is required to be passed through in order to evaluate the
/// individual [`Component`]s - this is typically handled by a mix of the bottom bar and a
/// reference to the currently-focused [`View`](crate::view::View). Users should not need to
/// implement this trait.
pub trait Context: GetAttr {
    /// Retrieves the current input in the bottom bar, if it's focused
    fn current_input(&self) -> Option<&str>;

    /// Return the last error message that we encountered
    ///
    /// If there has not yet been an error message, this should return an empty string.
    fn get_error_message(&self) -> &str;

    /// Return whether there is an error message to display
    ///
    /// If there is, `get_error_message` should return a non-empty string.
    fn has_error_message(&self) -> bool;
}

impl BottomBar {
    /// Constructs a new `BottomBar` for use in a [`Container`]
    ///
    /// The look fo the bottom bar is given by the local, parsed [`Config`].
    ///
    /// [`Container`]: super::Container
    pub fn new() -> Self {
        todo!()
    }

    /// Returns the size of the terminal left over after accounting for the lines taken up by the
    /// bottom bar
    ///
    /// If there isn't enough room for anything other than the bottom bar, this function returns
    /// `None`.
    pub fn inner_size(&self, size: TermSize) -> Option<TermSize> {
        todo!()
    }
}
