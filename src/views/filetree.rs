//! The `View` giving a file explorer in order to open other files

use super::buffer::ViewBuffer;
use super::{
    ConcreteView, ConstructedView, MetaCmd, OutputSignal, RefreshKind, SignalHandler, ViewKind,
};
use crate::config::{DerefChain, DerefMutChain};
use crate::container;
use crate::container::Signal;
use crate::event::KeyCode;
use crate::mode::handler::{Cmd, Executor};
use crate::mode::normal::Mode as NormalMode;
use crate::mode::{self, CursorStyle, Handler as ModeHandler, ModeKind, ModeSet};
use crate::runtime::{Painter, TermSize};
use crate::text::{self, ContentProvider, Lines, ReprKind};
use crate::utils::Never;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

pub struct View {
    handler: ModeHandler<FileTreeExecutor, MetaCmd<Never>, MetaCmd<Never>>,
}

struct FileTreeExecutor {
    buffer: ViewBuffer<Provider>,
}

struct Provider {
    dirs: Vec<PathBuf>,
    links: Vec<PathBuf>,
    files: Vec<PathBuf>,
    invalids: Vec<PathBuf>,
    base_path: PathBuf,
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

impl ConstructedView for View {
    fn init<S: AsRef<str>>(size: TermSize, args: &[S]) -> Self {
        if args.len() > 1 {
            log::warn!("filetree::View received args with len > 1, ignoring entries.");
            log::warn!(
                "Ignored: {:?}",
                args[1..].iter().map(AsRef::as_ref).collect::<Vec<_>>()
            );
        }

        let path = match args {
            // We're expecting a single argument - the path of the directory to open
            [path, ..] => path.as_ref().into(),
            // If we weren't given a path, we'll just use the current working directory
            [] => match std::env::current_dir() {
                Ok(d) => d,
                // FIXME: Better error handling here
                Err(e) => panic!("Failed to get current working directory: {}", e),
            },
        };

        let path = path.canonicalize().unwrap_or_else(move |_| path);

        let mut dirs = Vec::new();
        let mut links = Vec::new();
        let mut files = Vec::new();
        let mut invalids = Vec::new();

        dirs.push(path.parent().unwrap_or(&path).into());

        if let Ok(iter) = fs::read_dir(&path) {
            for entry in iter {
                let entry = match entry {
                    Ok(e) => e,
                    // FIXME: better error handing
                    Err(_) => continue,
                };

                let path = entry.path();
                match entry.file_type() {
                    Err(_) => invalids.push(path),
                    Ok(t) if t.is_dir() => dirs.push(path),
                    Ok(t) if t.is_symlink() => links.push(path),
                    // Otherwise, it's a file
                    Ok(_) => files.push(path),
                }
            }
        } else {
            // FIXME: Better error handling here
        }

        fn strs(paths: &mut [PathBuf], trailing: Option<&str>) -> String {
            paths.sort();

            let mut s = String::new();
            for p in paths {
                s.push_str(
                    &(p.components().rev().next().unwrap().as_ref() as &Path).to_string_lossy(),
                );
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
                "{}",   // <- the rest of the directories
                "{}",   // <- all symlinks
                "{}",   // <- all of the files
                "{}",   // <- all/any invalid directory entries
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

        Self {
            handler: ModeHandler::new(
                FileTreeExecutor {
                    buffer: ViewBuffer::new(
                        size,
                        Provider {
                            dirs,
                            links,
                            files,
                            invalids,
                            base_path: path,
                            content,
                        },
                    ),
                },
                NormalMode::default(),
                ModeSet::none().allow(ModeKind::Normal),
            ),
        }
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
                        let (abs_path, view_kind) = {
                            if row < provider.dirs.len() {
                                (&provider.dirs[row], ViewKind::FileTree)
                            } else {
                                row -= provider.dirs.len();

                                if row < provider.links.len() {
                                    (&provider.links[row], ViewKind::File)
                                } else {
                                    row -= provider.links.len();
                                    if row < provider.files.len() {
                                        (&provider.files[row], ViewKind::File)
                                    } else {
                                        row -= provider.files.len();
                                        (&provider.invalids[row], ViewKind::File)
                                    }
                                }
                            }
                        };

                        let path_slice = [abs_path.to_string_lossy()];

                        return Some(vec![Replace(
                            view_kind.to_view(self.handler.executor().buffer.size(), &path_slice),
                        )]);
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
        use OutputSignal::{Close, NeedsRefresh, Open, Replace, ShiftFocus};

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
                // FIXME: This is strictly incorrect
                let new_view = ViewKind::FileTree.to_view((10, 10).into(), &[] as &[&str]);
                return Some(vec![Open(d, new_view)]);
            }
            Other(MetaCmd::Open(d, view_kind)) => {
                return Some(vec![Open(
                    d,
                    view_kind.to_view((10, 10).into(), &[] as &[&str]),
                )])
            }
            Other(MetaCmd::ShiftFocus(d, n)) => return Some(vec![ShiftFocus(d, n)]),
            Other(MetaCmd::Replace(view_kind)) => {
                return Some(vec![Replace(
                    view_kind.to_view((10, 10).into(), &[] as &[&str]),
                )])
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
