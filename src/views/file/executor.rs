//! Definitions for the `FileExecutor` type

use super::handle::{Handle, Locator};
use super::{FileMeta, Params};
use crate::fs;
use crate::mode::handler::{Cmd, Executor};
use crate::mode::{self, CursorStyle, Direction};
use crate::text::ContentProvider;
use crate::views::{buffer::ViewBuffer, filetree::View as FileTreeView};
use crate::views::{ExitKind, MetaCmd, OutputSignal, ViewConstructorFn, ViewKind};

/// The internal `Executor` that allows handling of mode switching within the main `View`
pub(super) struct FileExecutor {
    pub(super) buffer: ViewBuffer<Handle>,
    pub(super) params: Params,
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
        use MetaCmd::{Custom, Split, TryClose};
        use OutputSignal::{Close, NeedsRefresh, Open, Replace, ShiftFocus};

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
                    TryClose(ReqSave)
                        if self.unsaved() && !self.buffer.provider().open_elsewhere() =>
                    {
                        Some(vec![OutputSignal::error(UNSAVED, true)])
                    }
                    TryClose(_) => Some(vec![Close]),
                    Split(d) => Some(vec![Open(d, self.clone_into_builder())]),
                    MetaCmd::Open(d, view_kind) => {
                        Some(vec![Open(d, self.make_constructor(view_kind))])
                    }
                    MetaCmd::ShiftFocus(d, n) => Some(vec![ShiftFocus(d, n)]),
                    MetaCmd::Replace(view_kind) => {
                        // If we're asked to replace but there's unsaved changes we can't ignore,
                        // we don't want to get rid of it - we'll split upwards or leftwards by the
                        // direction that's largest
                        let dims = self.buffer.size();
                        let new_view = self.make_constructor(view_kind);

                        if self.unsaved() && !self.buffer.provider().open_elsewhere() {
                            let dir = match dims.width > dims.height {
                                true => Direction::Left,
                                false => Direction::Up,
                            };

                            Some(vec![Open(dir, new_view)])
                        } else {
                            // Otherwise, we just replace directly
                            Some(vec![Replace(new_view)])
                        }
                    }
                    Custom(Save) => match self.try_save() {
                        Ok(()) => Some(Vec::new()),
                        Err(err_str) => Some(vec![OutputSignal::error(&err_str, true)]),
                    },
                };
            }
            Cursor(m, n) => self.buffer.move_cursor(m, n),
            Scroll {
                kind,
                amount,
                lock_cursor,
            } => self.buffer.scroll(kind, amount, lock_cursor),
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
                    Some(vec![OutputSignal::error(AT_OLDEST_CHANGE, false)])
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
                    Some(vec![OutputSignal::error(AT_NEWEST_CHANGE, false)])
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
            Failure { msg } => Some(vec![OutputSignal::error(&msg, true)]),
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

    fn clone_into_builder(&mut self) -> ViewConstructorFn {
        let file = self.buffer.provider_mut().clone();

        let view = Box::new(super::View {
            handler: super::ModeHandler::new(
                FileExecutor {
                    buffer: self.buffer.clone_from_provider(file),
                    params: self.params.clone(),
                },
                super::NormalMode::default(),
                super::ModeSet::all(),
            ),
        });

        Box::new(move |_| view)
    }

    fn make_constructor(&self, kind: ViewKind) -> ViewConstructorFn {
        match kind {
            ViewKind::File => match self.buffer.provider().locator() {
                Locator::Path(p) => super::View::constructor(p.clone()),
                Locator::Local(_) => super::View::empty_constructor(),
            },
            ViewKind::FileTree => match self.buffer.provider().locator() {
                Locator::Local(_) => FileTreeView::constructor(fs::getcwd()),
                Locator::Path(p) => FileTreeView::constructor(p.parent().unwrap()),
            },
        }
    }
}
