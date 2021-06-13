//! Internal [`View`] functioning
//!
// TODO-DOC: Stuff about what a `View` is.
//!
//! This module only provides the facilities for interaction *between* [`View`]s; the entrypoint
//! for handling the tree of `View`s is taken care of by the [`container`](crate::container) module.

use crate::any::BoxedAny;
use crate::config::{Attribute, GetAttrAny};
use crate::container::{BottomBar, Input, Painter, Refresh};
use crate::macros::{async_method, impl_GetAttrAny, init};
use crate::{TermPos, TermSize};
use serde::{Deserialize, Serialize};
use std::ops::Deref;

mod file;
mod splash;

pub use file::FileView;
pub use splash::SplashView;

init!();

#[derive(Debug, Clone, Serialize, Deserialize)]
enum Focus {
    Direction(Direction),
}

/// The raison d'être of this module
///
/// For more information, refer to the [module-level documentation](self)
pub trait View: Send + Sync + GetAttrAny {
    #[async_method]
    async fn handle(
        &mut self,
        input: Input,
        bottom_bar: &mut BottomBar,
    ) -> (OutputSignal, Option<Input>);

    #[async_method]
    async fn refresh<'a>(&'a mut self, painter: Painter<'a>);

    #[async_method]
    async fn cursor_pos(&self) -> Option<TermPos>;

    // #[async_method]
    // async fn can_exit(&self, kind: ExitKind) -> bool {
    //     true
    // }

    // #[async_method]
    // async fn exit(this: Box<dyn View>, kind: ExitKind) -> io::Result<()> {
    //     Ok(())
    // }
}

impl<D: Send + Sync + Deref<Target = dyn View>> GetAttrAny for D {
    #[async_method]
    async fn get_attr_any(&self, attr: Attribute) -> Option<BoxedAny> {
        (Deref::deref(self) as &dyn View).get_attr_any(attr).await
    }
}

type Constructor = Box<dyn FnOnce(TermSize, &Refresh) -> Box<dyn View>>;

// @def enum-Direction v0
pub type Direction = crate::utils::Directional<()>;

/// The result of a [`View`]'s handling of input
pub enum OutputSignal {
    Open(Direction, Constructor),
    ReplaceThis(Constructor),
    ShiftFocus(Direction, usize),
    WaitForMore,
}

// pub enum ExitKind {}

pub fn path_view(path: String, size: TermSize, refresh: Refresh) -> Box<dyn View> {
    todo!()
}
