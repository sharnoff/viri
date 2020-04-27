//! Definitions for the `FileExecutor` type

use super::handle::Handle;
use super::FileMeta;
use crate::mode::handler::{Cmd, Executor};
use crate::mode::{self, CursorStyle};
use crate::text::ContentProvider;
use crate::views::buffer::ViewBuffer;
use crate::views::{ExitKind, MetaCmd, OutputSignal};

/// The internal `Executor` that allows handling of mode switching within the main `View`
pub(super) struct FileExecutor {
    pub(super) buffer: ViewBuffer<Handle>,
}

impl Executor<MetaCmd<FileMeta>> for FileExecutor {
    type Output = Option<Vec<OutputSignal>>;

    fn execute(
        &mut self,
        cmd: Cmd<MetaCmd<FileMeta>>,
        style: CursorStyle,
    ) -> Option<Vec<OutputSignal>> {
        use Cmd::{
            Cursor, Delete, EndEditBlock, Insert, Other, Redo, Scroll, StartEditBlock, Undo,
        };
        use ExitKind::ReqSave;
        use FileMeta::Save;
        use MetaCmd::{Custom, TryClose};
        use OutputSignal::{Close, NeedsRefresh};

        // Getting a few definitions out of the way
        //
        // The first few are the actual error messages themselves
        const UNSAVED: &'static str = "No write since last change (use ! to override)";
        const AT_OLDEST_CHANGE: &'static str = "Already at oldest change";
        const AT_NEWEST_CHANGE: &'static str = "Already at newest change";

        self.buffer.set_cursor_style(style);

        let refresh = match cmd {
            Other(o) => {
                return match o {
                    TryClose(ReqSave) if self.unsaved() => {
                        Some(vec![OutputSignal::error(UNSAVED, None, true)])
                    }
                    TryClose(_) => Some(vec![Close]),
                    Custom(Save) => match self.try_save() {
                        Ok(()) => Some(Vec::new()),
                        Err(err_str) => Some(vec![OutputSignal::error(&err_str, None, true)]),
                    },
                }
            }
            Cursor(m, n) => self.buffer.move_cursor(m, n),
            Scroll(d, n) => self.buffer.scroll(d, n),
            Insert(s) => self.buffer.insert(s.as_ref()),
            Undo(n) => {
                let (diffs, at_oldest) = match self.buffer.provider_mut().undo(n) {
                    Ok(diffs) => diffs,
                    // TODO: There should be better error handling here
                    Err(e) => panic!("{}", e),
                };

                let refresh = self.buffer.refresh_diffs(&diffs).map(NeedsRefresh);

                return if at_oldest && diffs.is_empty() {
                    // We don't need to include 'refresh' because there weren't any diffs
                    Some(vec![OutputSignal::error(AT_OLDEST_CHANGE, None, false)])
                } else if let Some(refresh_signal) = refresh {
                    Some(vec![refresh_signal])
                } else {
                    Some(Vec::new())
                };
            }
            Redo(n) => {
                let (diffs, at_newest) = match self.buffer.provider_mut().redo(n) {
                    Ok(diffs) => diffs,
                    // TODO: There should be better error handling here
                    Err(e) => panic!("{}", e),
                };

                let refresh = self.buffer.refresh_diffs(&diffs).map(NeedsRefresh);

                return if at_newest && diffs.is_empty() {
                    Some(vec![OutputSignal::error(AT_NEWEST_CHANGE, None, false)])
                } else if let Some(refresh_signal) = refresh {
                    Some(vec![refresh_signal])
                } else {
                    Some(Vec::new())
                };
            }
            StartEditBlock => {
                self.buffer.provider_mut().start_edit_block();
                None
            }
            EndEditBlock => {
                self.buffer.provider_mut().end_edit_block();
                None
            }
            Delete(kind) => self.buffer.delete(kind),
        };

        match refresh {
            Some(kind) => Some(vec![NeedsRefresh(kind)]),
            None => Some(Vec::new()),
        }
    }

    fn error(err: mode::Error) -> Option<Vec<OutputSignal>> {
        use mode::Error::{Failure, IllegalMode, NeedsMore, NoSuchCommand};
        use OutputSignal::{NoSuchCmd, WaitingForMore};

        match err {
            NeedsMore => Some(vec![WaitingForMore]),
            NoSuchCommand => Some(vec![NoSuchCmd]),
            Failure { msg } => Some(vec![OutputSignal::error(&msg, None, true)]),
            IllegalMode(_) => None,
        }
    }

    fn pre(&mut self) {
        // We'll lock the file so that all of the changes happen atomically
        // TODO: We'll also need to `refresh` here.
        self.buffer.provider_mut().lock()
    }

    fn post(&mut self) {
        // Unlock the file
        self.buffer.provider_mut().unlock()
    }
}

impl FileExecutor {
    /// Attempts to write the contents of the file to the filesystem, regardless of whether there
    /// have been changes made.
    ///
    /// Any errors are converted to ASCII strings (so they can be used knowing they have a fixed
    /// width)
    fn try_save(&mut self) -> Result<(), String> {
        self.buffer
            .provider_mut()
            .write()
            .map_err(|e| e.to_string())
    }

    /// Temporarily acquires a lock on the content, returning whether any changes made have not
    /// been written to the file system
    fn unsaved(&self) -> bool {
        self.buffer.provider().unsaved()
    }
}
