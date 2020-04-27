//! Definitions for the `FileExecutor` type

use super::handle::Handle;
use super::FileMeta;
use crate::mode::handler::{Cmd, Executor};
use crate::mode::{self, CursorStyle};
use crate::text::ContentProvider;
use crate::views::buffer::ViewBuffer;
use crate::views::{ExitKind, MetaCmd, OutputSignal};
use crossterm::style::Colorize;

/// The internal `Executor` that allows handling of mode switching within the main `View`
pub(super) struct FileExecutor {
    pub(super) buffer: ViewBuffer<Handle>,
}

impl Executor<MetaCmd<FileMeta>> for FileExecutor {
    type Output = Option<OutputSignal>;

    fn execute(&mut self, cmd: Cmd<MetaCmd<FileMeta>>, style: CursorStyle) -> Option<OutputSignal> {
        use Cmd::{
            Cursor, Delete, EndEditBlock, Insert, Other, Redo, Scroll, StartEditBlock, Undo,
        };
        use ExitKind::ReqSave;
        use FileMeta::Save;
        use MetaCmd::{Custom, TryClose};

        const UNSAVED_ERR_MSG: &'static str = "No write since last change (use ! to override)";

        self.buffer.set_cursor_style(style);

        let refresh = match cmd {
            Other(o) => {
                return match o {
                    TryClose(ReqSave) if self.unsaved() => Some(OutputSignal::SetBottomBar {
                        prefix: None,
                        value: UNSAVED_ERR_MSG.red().to_string(),
                        width: UNSAVED_ERR_MSG.len(),
                        cursor_col: None,
                    }),
                    TryClose(_) => Some(OutputSignal::Close),
                    Custom(Save) => match self.try_save() {
                        Ok(()) => Some(OutputSignal::Nothing),
                        Err(err_str) => {
                            let width = err_str.len();

                            Some(OutputSignal::SetBottomBar {
                                prefix: None,
                                value: err_str.red().to_string(),
                                width,
                                cursor_col: None,
                            })
                        }
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

                let refresh = self
                    .buffer
                    .refresh_diffs(&diffs)
                    .map(OutputSignal::NeedsRefresh)
                    .unwrap_or(OutputSignal::Nothing);

                if at_oldest && diffs.is_empty() {
                    const AT_OLDEST_CHANGE: &'static str = "Already at oldest change";
                    return Some(OutputSignal::Chain(vec![
                        OutputSignal::SetBottomBar {
                            prefix: None,
                            value: AT_OLDEST_CHANGE.into(),
                            width: AT_OLDEST_CHANGE.len(),
                            cursor_col: None,
                        },
                        // This isn't really needed, but it's included for the sake of completeness
                        refresh,
                    ]));
                } else {
                    return Some(refresh);
                }
            }
            Redo(n) => {
                let (diffs, at_newest) = match self.buffer.provider_mut().redo(n) {
                    Ok(diffs) => diffs,
                    // TODO: There should be better error handling here
                    Err(e) => panic!("{}", e),
                };

                let refresh = self
                    .buffer
                    .refresh_diffs(&diffs)
                    .map(OutputSignal::NeedsRefresh)
                    .unwrap_or(OutputSignal::Nothing);

                if at_newest && diffs.is_empty() {
                    const AT_NEWEST_CHANGE: &'static str = "Already at newest change";
                    return Some(OutputSignal::Chain(vec![
                        OutputSignal::SetBottomBar {
                            prefix: None,
                            value: AT_NEWEST_CHANGE.into(),
                            width: AT_NEWEST_CHANGE.len(),
                            cursor_col: None,
                        },
                        // This isn't really needed, but it's included for the sake of completeness
                        refresh,
                    ]));
                } else {
                    return Some(refresh);
                }
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

        Some(
            refresh
                .map(OutputSignal::NeedsRefresh)
                .unwrap_or(OutputSignal::Nothing),
        )
    }

    fn error(err: mode::Error) -> Option<OutputSignal> {
        use mode::Error::{Failure, IllegalMode, NeedsMore, NoSuchCommand};

        match err {
            NeedsMore => Some(OutputSignal::WaitingForMore),
            NoSuchCommand => Some(OutputSignal::NoSuchCmd),
            Failure { msg } => {
                let width = msg.len();
                Some(OutputSignal::SetBottomBar {
                    prefix: None,
                    value: msg.red().to_string(),
                    width,
                    cursor_col: None,
                })
            }
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
