//! Wrapper module for the bottom bar context

use super::bottom_bar::Context;
use crate::any::BoxedAny;
use crate::config::attr::{Attribute, GetAttrAny};
use crate::macros::async_method;
use crate::view::View;

pub(super) struct BBCtx<'a> {
    pub(super) view: Option<&'a dyn View>,
    pub(super) input: Option<&'a str>,
    pub(super) last_err: Option<&'a str>,
}

impl<'a> Context for BBCtx<'a> {
    fn current_input(&self) -> Option<&str> {
        self.input
    }

    fn get_error_message(&self) -> &str {
        self.last_err.unwrap_or("")
    }

    fn has_error_message(&self) -> bool {
        self.last_err.is_some()
    }
}

impl<'a> GetAttrAny for BBCtx<'a> {
    #[async_method]
    async fn get_attr_any(&self, attr: Attribute) -> Option<BoxedAny> {
        match self.view {
            Some(v) => v.get_attr_any(attr).await,
            None => None,
        }
    }
}
