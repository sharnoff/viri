//! The `View` giving a file explorer in order to open other files

use super::{buffer::ViewBuffer, file::View as FileView};
use super::{
    ConcreteView, MetaCmd, OutputSignal, RefreshKind, SignalHandler, ViewConstructorFn, ViewKind,
};
use crate::config::{DerefChain, DerefMutChain};
use crate::container;
use crate::container::Signal;
use crate::event::KeyCode;
use crate::fs::{self, Path};
use crate::mode::handler::{Cmd, Executor};
use crate::mode::normal::Mode as NormalMode;
use crate::mode::{self, CursorStyle, Handler as ModeHandler, ModeKind, ModeSet};
use crate::runtime::Painter;
use crate::text::{self, ContentProvider, Lines, ReprKind};
use crate::utils::Never;
use std::sync::Arc;

pub struct View {
    handler: ModeHandler<FileTreeExecutor, MetaCmd<Never>, MetaCmd<Never>>,
}

struct FileTreeExecutor {
    buffer: ViewBuffer<Provider>,
}

struct Provider {
    dirs: Vec<(String, Path)>,
    links: Vec<(String, Path)>,
    files: Vec<(String, Path)>,
    invalids: Vec<(String, Path)>,
    base_path: Path,
    content: Lines,
}

impl super::View for View {
    fn refresh(&mut self, painter: &Painter) {
        self.handler.executor_mut().buffer.refresh(painter)
    }

    fn refresh_cursor(&self, painter: &Painter) {
        self.handler.executor().buffer.refresh_cursor(painter);
    }

    fn focus(&mut self) -> Option<RefreshKind> {
        self.handler.executor_mut().buffer.focus()
    }
}

impl View {
    pub fn constructor(path: Path) -> ViewConstructorFn {
        let mut dirs = Vec::new();
        let mut links = Vec::new();
        let mut files = Vec::new();
        let mut invalids = Vec::new();

        dirs.push(("..".into(), path.parent().unwrap_or_else(|| path.clone())));

        if let Ok(iter) = fs::read_dir(&path) {
            for entry in iter {
                let entry = match entry {
                    Ok(e) => e,
                    // FIXME: better error handing
                    Err(_) => continue,
                };

                let name = entry.file_name().to_string_lossy().into();
                let path = entry.path();

                match entry.file_type() {
                    Err(_) => invalids.push((name, path)),
                    Ok(t) if t.is_dir() => dirs.push((name, path)),
                    Ok(t) if t.is_symlink() => links.push((name, path)),
                    // Otherwise, it's a file
                    Ok(_) => files.push((name, path)),
                }
            }
        } else {
            // TODO-ERROR: better handling on failure here - maybe changing the name displayed at
            // the top or bottom of the view oto indicate that the list of entries could not be
            // successfully read
        }

        fn strs(entries: &mut [(String, Path)], trailing: Option<&str>) -> String {
            entries.sort_by(|(sx, _), (sy, _)| sx.cmp(sy));

            let mut s = String::new();
            for (name, _) in entries {
                s.push_str(name);
                if let Some(t) = trailing {
                    s.push_str(t);
                }
                s.push('\n');
            }

            s
        }

        let content_string = format!(
            concat!(
                "===================================================\n",
                "File tree viewer\n",
                "  └─{}\n", // <- Current path
                "===================================================\n",
                "../\n", // <- The parent directory, which is done separately
                "{}",    // <- the rest of the directories
                "{}",    // <- all symlinks
                "{}",    // <- all of the files
                "{}",    // <- all/any invalid directory entries
            ),
            path.to_string_lossy(),
            strs(&mut dirs[1..], Some("/")),
            strs(&mut links, Some("@")),
            strs(&mut files, None),
            strs(&mut invalids, None),
        );

        // The tabstop doesn't actually matter here because we (most likely) won't have any tabs.
        const TABSTOP: usize = 4;
        let content = Lines::from_arc(
            Arc::new(content_string.into()),
            TABSTOP,
            ReprKind::Utf8,
            None,
        );

        Box::new(move |size| {
            let mut buffer = ViewBuffer::new(
                size,
                Provider {
                    dirs,
                    links,
                    files,
                    invalids,
                    base_path: path,
                    content,
                },
            );

            // We start by moving the cursor down because we can then start the cursor on the first
            // 'clickable' line
            buffer.move_cursor(crate::mode::Movement::Down, 5);

            Box::new(View {
                handler: ModeHandler::new(
                    FileTreeExecutor { buffer },
                    NormalMode::default(),
                    ModeSet::none().allow(ModeKind::Normal),
                ),
            })
        })
    }
}

impl ConcreteView for View {}

impl SignalHandler for View {
    fn try_handle(&mut self, signal: Signal) -> Option<Vec<OutputSignal>> {
        use OutputSignal::{ClearBottomBar, LeaveBottomBar, Replace, SetBottomBar};

        if let Signal::BottomBarKey {
            prefix: Some(':'),
            value,
            key,
            ..
        } = signal
        {
            match key.code {
                KeyCode::Esc => Some(vec![LeaveBottomBar]),
                KeyCode::Backspace if value.is_empty() => {
                    Some(vec![LeaveBottomBar, ClearBottomBar])
                }
                KeyCode::Backspace => {
                    let len = value.len() - 1;
                    let new_cmd = String::from(&value[..len]);

                    Some(vec![SetBottomBar {
                        prefix: Some(':'),
                        value: new_cmd,
                        width: len,
                        // We add one because the cursor column includes the prefix character
                        cursor_col: Some(len + 1),
                    }])
                }

                // We'll only allow ASCII characters
                KeyCode::Char(c) if c.is_ascii() => {
                    let mut new_cmd = String::with_capacity(value.len() + 1);
                    new_cmd.push_str(value);
                    new_cmd.push(c);

                    let len = new_cmd.len();

                    let sig = SetBottomBar {
                        prefix: Some(':'),
                        value: new_cmd,
                        width: len,
                        // We add one because the cursor column includes the prefix character
                        cursor_col: Some(len + 1),
                    };

                    Some(vec![sig])
                }

                // We'll attempt to use this command
                KeyCode::Enter => {
                    container::cmd::try_exec_cmd(value).map(|c| self.handle_container_res(c))
                }

                // Todo: traverse history
                KeyCode::Up | KeyCode::Down => todo!(),

                _ => None,
            }
        } else if let Signal::NormalKey(k) = signal {
            if !self.handler.expecting_input() {
                if k.code == KeyCode::Char(':') {
                    return Some(vec![SetBottomBar {
                        prefix: Some(':'),
                        value: String::new(),
                        width: 0,
                        cursor_col: Some(1), // We set it to 1 because it starts from zero including the prefix
                    }]);
                } else if k.code == KeyCode::Enter {
                    log::trace!("enter!");

                    let mut row = self.handler.executor().buffer.current_row();
                    // We check 4 because that's the number of starter rows used
                    let executor = self.handler.executor();
                    let provider = executor.buffer.provider();
                    if row >= 4 {
                        row -= 4;
                        // Receiving 'enter' means that the user has selected a certain line - we'll
                        // use this to open that file
                        let constructor = loop {
                            if row < provider.dirs.len() {
                                break View::constructor(provider.dirs[row].1.clone());
                            }
                            row -= provider.dirs.len();

                            if row < provider.links.len() {
                                break FileView::constructor(provider.links[row].1.clone());
                            }
                            row -= provider.links.len();

                            if row < provider.files.len() {
                                break FileView::constructor(provider.files[row].1.clone());
                            }
                            row -= provider.files.len();

                            // TODO: Maybe we shouldn't allow editing of invalid files? This is a
                            // somewhat strange use-case.
                            break FileView::constructor(provider.invalids[row].1.clone());
                        };

                        return Some(vec![Replace(constructor)]);
                    }
                }
            }

            let mut outs: Vec<Option<Vec<OutputSignal>>> = self.handler.handle(k);

            if outs.is_empty() {
                Some(Vec::new())
            } else {
                if outs.last().unwrap().is_none() {
                    // FIXME: This is temporary and should be replaced with proper error handling.
                    let last = OutputSignal::error("Failed to execute one or more commands", true);

                    // Get rid of the last element
                    outs.pop();
                    // Replace it with an error
                    outs.push(Some(vec![last]));
                }

                Some(
                    outs.into_iter()
                        // It's okay to unwrap here because of the guarantees provided by
                        // `Handler::handle`: If the error type is returned, it will be the last
                        // element, and the `if` above will be triggered
                        .map(Option::unwrap)
                        .flatten()
                        .collect(),
                )
            }
        } else {
            None
        }
    }
}

impl Executor<MetaCmd<Never>> for FileTreeExecutor {
    type Output = Option<Vec<OutputSignal>>;

    fn execute(
        &mut self,
        cmd: Cmd<MetaCmd<Never>>,
        _style: CursorStyle,
    ) -> Option<Vec<OutputSignal>> {
        use Cmd::{
            Cursor, Delete, EndEditBlock, Insert, Other, Redo, Scroll, StartEditBlock, Undo,
        };
        use MetaCmd::{Custom, Split, TryClose};
        use OutputSignal::{Close, NeedsRefresh, Open, ShiftFocus};

        let refresh = match cmd {
            Cursor(m, n) => self.buffer.move_cursor(m, n),
            Scroll {
                kind,
                amount,
                lock_cursor,
            } => self.buffer.scroll(kind, amount, lock_cursor),
            Delete(_) | Insert(_) => {
                return Some(vec![OutputSignal::error(
                    "Cannot make changes to file tree viewer",
                    true,
                )])
            }
            Undo(_) | Redo(_) => None,
            StartEditBlock { .. } | EndEditBlock { .. } => None,
            Other(TryClose(_)) => return Some(vec![Close]),
            Other(Split(d)) => {
                return Some(vec![Open(
                    d,
                    View::constructor(self.buffer.provider().base_path.clone()),
                )]);
            }
            Other(MetaCmd::Open(d, view_kind)) => match view_kind {
                ViewKind::File => {
                    return Some(vec![OutputSignal::error(
                        "Configuration error: Attempted to open file view from filetree",
                        true,
                    )])
                }
                ViewKind::FileTree => {
                    return Some(vec![Open(
                        d,
                        View::constructor(self.buffer.provider().base_path.clone()),
                    )])
                }
            },
            Other(MetaCmd::ShiftFocus(d, n)) => return Some(vec![ShiftFocus(d, n)]),
            Other(MetaCmd::Replace(view_kind)) => {
                log::warn!(
                    "FileTreeExecutor received Replace command with '{:?}'",
                    view_kind
                );

                match view_kind {
                    ViewKind::File => {
                        return Some(vec![OutputSignal::error(
                            "Configuration error: Attempted to replace filetree with file view",
                            true,
                        )])
                    }
                    // We don't really need to replace here, and we will have already logged what
                    // we needed.
                    ViewKind::FileTree => return Some(Vec::new()),
                };
            }
            Other(Custom(_)) => unreachable!(),
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
}

impl ContentProvider for Provider {
    type Deref<'a> = DerefChain<&'a Provider, Lines>;
    type DerefMut<'a> = DerefMutChain<&'a mut Provider, Lines>;

    fn lock(&mut self) {
        /* We don't need to do anything because it's single-threaded */
    }

    fn unlock(&mut self) {
        /* We don't need to do anything because it's single-threaded */
    }

    fn content<'a>(&'a self) -> Self::Deref<'a> {
        DerefChain {
            host: self,
            get: |p| &p.content,
        }
    }

    fn content_mut<'a>(&'a mut self) -> Self::DerefMut<'a> {
        DerefMutChain {
            host: self,
            get: |p| &p.content,
            get_mut: |p| &mut p.content,
        }
    }

    fn refresh(&mut self) -> Vec<text::Diff> {
        // TODO: We might want to re-generate the list if we find that the directory entries are
        // different. That's a more difficult feature though, so we'll leave that to a later
        // update.
        Vec::new()
    }
}

impl View {
    fn handle_container_res(
        &mut self,
        res: Result<Option<container::cmd::Cmd>, String>,
    ) -> Vec<OutputSignal> {
        use container::cmd::Cmd::{ForceQuit, Quit, SetLocal};
        use OutputSignal::{Close, LeaveBottomBar, SaveBottomBar};

        match res {
            Err(msg) => return vec![LeaveBottomBar, OutputSignal::error(&msg, true)],
            Ok(None) => return vec![SaveBottomBar, LeaveBottomBar],
            Ok(Some(cmd)) => match cmd {
                Quit { .. } | ForceQuit { .. } => vec![LeaveBottomBar, Close],
                SetLocal { .. } => vec![
                    LeaveBottomBar,
                    OutputSignal::error("No local parameters to set", true),
                ],
            },
        }
    }
}
