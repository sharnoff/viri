//! Wrapper module for [`BottomBar`] and related types

use crate::any::BoxedAny;
use crate::config::{Attribute, Configurable, GetAttr, GetAttrAny};
use crate::container::Painter;
use crate::macros::{async_method, config};
use crate::text::Cursor;
use crate::{TermPos, TermSize, Text, Textual};
use std::sync::Arc;

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
    pub error_message: Option<String>,

    /// Any input from the user, alongside the position of the cursor within that text
    pub user_input: Option<String>, // FIXME: when crate::text is added back in, this field should use that
}

impl Text for BottomBar {}

impl Textual for BottomBar {
    fn cursor(&self) -> &Cursor {
        todo!()
    }

    fn cursor_mut(&mut self) -> &mut Cursor {
        todo!()
    }
}

/// The evaluation context required for rendering the [`BottomBar`]
///
/// An object implementing this trait is required to be passed through in order to evaluate the
/// individual [`Component`]s - this is typically handled by a mix of the bottom bar and a
/// reference to the currently-focused [`View`](crate::view::View). Users should not need to
/// implement this trait.
pub trait Context: 'static + Send + Sync + GetAttr {
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
        }
    }

    /// Returns the number of lines at the bottom of the terminal taken up by the bottom bar
    pub fn height(&self, size: TermSize) -> u16 {
        // Currently, we put everything onto a single line, so this just returns 1
        1
    }

    /// Returns the position of the cursor within the bottom bar - or where it would be with user
    /// input, if there isn't any.
    pub fn cursor_pos(&self) -> TermPos {
        todo!()
    }

    /// Draws the bottom bar to the top row of the painter
    pub async fn draw<Ctx: Context>(ctx: Ctx, mut painter: Painter<'_>) -> Ctx {
        painter.clear_all();
        let layout = Config::get_global().bottom_bar_layout.load_full();
        let arc = Arc::new(ctx);
        layout.draw(arc.clone(), painter).await;
        Arc::try_unwrap(arc).unwrap_or_else(|arc| {
            let strong_counts = Arc::strong_count(&arc);
            log::error!(
                "`Arc<Ctx>` in `BottomBar::draw` failed to unwrap; had {} strong counts",
                strong_counts
            );
            panic!(
                "failed to unwrap `Arc<Ctx>` with {} strong counts",
                strong_counts
            );
        })
    }
}

pub struct BBCtx<T: Send + Sync + GetAttrAny> {
    pub(super) bottom_bar: BottomBar,
    pub(super) attr_provider: T,
}

impl<T: Send + Sync + GetAttrAny> GetAttrAny for BBCtx<T> {
    #[async_method]
    async fn get_attr_any(&self, attr: Attribute) -> Option<BoxedAny> {
        self.attr_provider.get_attr_any(attr).await
    }
}

impl<T: 'static + Send + Sync + GetAttrAny> Context for BBCtx<T> {
    fn current_input(&self) -> Option<&str> {
        self.bottom_bar.user_input.as_ref().map(String::as_str)
    }

    fn get_error_message(&self) -> &str {
        self.bottom_bar
            .error_message
            .as_ref()
            .map(String::as_str)
            .unwrap_or("")
    }

    fn has_error_message(&self) -> bool {
        self.bottom_bar.error_message.is_some()
    }
}
