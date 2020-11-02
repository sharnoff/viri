//! Wrapper module for [`BottomBar`] and related types

use crate::config::{Configurable, GetAttr};
use crate::container::Painter;
use crate::macros::config;
use crate::TermSize;
use std::sync::Arc;
use tokio::sync::Mutex;

mod component;
mod layout;
mod time;

use component::Component;
use layout::Layout;
use time::TimeFormat;

config! {
    pub struct Config (ConfigBuilder) {
        bottom_bar_layout: Layout = Layout::default(),
    }
}

#[derive(Debug)]
pub struct BottomBar {
    /// The last error message that that was provided to the bottom bar, if it exists
    error_message: Option<String>,

    /// Any input from the user, alongside the position of the cursor
    user_input: Option<()>, // FIXME: when crate::text is added back in, this field should use that

    /// The currently-displayed contents of the bottom bar
    currently_displayed: Mutex<Option<(String, TermSize)>>,
}

/// The evaluation context required for rendering the [`BottomBar`]
///
/// An object implementing this trait is required to be passed through in order to evaluate the
/// individual [`Component`]s - this is typically handled by a mix of the bottom bar and a
/// reference to the currently-focused [`View`](crate::view::View). Users should not need to
/// implement this trait.
pub trait Context: GetAttr {
    /// Retrieves the current input in the bottom bar, if it's focused
    ///
    /// If the bottom bar is focused but there is no input, this should return `""`.
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
        BottomBar {
            error_message: None,
            user_input: None,
            currently_displayed: Mutex::new(None),
        }
    }

    /// Returns the number of lines at the bottom of the terminal taken up by the bottom bar
    pub fn height(&self, size: TermSize) -> u16 {
        // Currently, we put everything onto a single line, so this just returns 1
        1
    }

    /// Draws the bottom bar to the top row of the painter
    pub async fn draw(&self, ctx: Arc<impl Context>, mut painter: Painter<'_>) {
        painter.clear_all();
        let layout = Config::get_global().bottom_bar_layout.load_full();
        layout.draw(ctx, painter).await;
    }
}
