//! Wrapper module for the [`FileView`]

use super::{OutputSignal, View};
use crate::container::{BottomBar, Input, Painter, Refresh};
use crate::fs::Path;
use crate::macros::{async_method, id, impl_GetAttrAny};
// use crate::text::Cursor;
use crate::{TermPos, TermSize};
use std::sync::atomic::{AtomicUsize, Ordering};

/// An editable buffer for a single "file" - independent of host location
pub struct FileView {
    text: (),
    // cursor: Cursor,
    locator: Locator,
    size: TermSize,
    refresh: Refresh,
}

id! {
    /// A unique identifier for 'blank' files - scratch buffers not tied to any concrete file
    struct BlankId;
}

impl BlankId {
    /// Creates a new, unique `BlankId`
    fn new() -> BlankId {
        static LAST: AtomicUsize = AtomicUsize::new(0);

        BlankId(LAST.fetch_add(1, Ordering::SeqCst))
    }
}

/// The place that an individual file is located - either through the filesystem or as a scratch
/// file
enum Locator {
    Blank(BlankId),
    Local(Path),
}

impl FileView {
    pub fn new_blank(size: TermSize, refresh: Refresh) -> FileView {
        FileView {
            text: (),
            // cursor: Cursor::new_single(),
            locator: Locator::Blank(BlankId::new()),
            size,
            refresh,
        }
    }
}

impl_GetAttrAny!(FileView);

impl View for FileView {
    #[async_method]
    async fn handle(
        &mut self,
        input: Input,
        bottom_bar: &mut BottomBar,
    ) -> (OutputSignal, Option<Input>) {
        todo!()
    }

    #[async_method]
    async fn refresh<'a>(&'a mut self, painter: Painter<'a>) {
        todo!()
    }

    #[async_method]
    async fn cursor_pos(&self) -> Option<TermPos> {
        todo!()
    }
}
