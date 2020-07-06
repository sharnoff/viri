use super::buffer::ViewBuffer;
use super::{
    ConcreteView, MetaCmd, OutputSignal, RefreshKind, SignalHandler, ViewConstructorFn, ViewKind,
};
use crate::config::{Build, ConfigPart};
use crate::container::{self, Signal};
use crate::event::{KeyCode, KeyEvent, KeyModifiers};
use crate::mode::{
    handler::{self as mode_handler, Executor, Handler as ModeHandler},
    normal::Mode as NormalMode,
    Direction, ModeSet,
};
use crate::runtime::Painter;
use crate::trie::Trie;
use crate::utils::{Never, XFrom};
use crossterm::style::Colorize;
use serde::{Deserialize, Serialize};
use std::fmt::Display;
use std::path::Path;
use std::str::FromStr;
use std::sync::{Arc, Mutex, MutexGuard};

#[macro_use]
mod macros;

mod edits;
mod executor;
mod handle;
mod syntax;

use executor::FileExecutor;
use handle::{gen_local_id, Handle};

/// The primary file viewer
pub struct View {
    handler: ModeHandler<FileExecutor, MetaCmd<FileMeta>, MetaCmd<Never>>,
}

pub fn init() {
    register_params();
    syntax::init();
}

fn try_parse<T: FromStr>(s: &str) -> Result<(), String>
where
    <T as FromStr>::Err: Display,
{
    match T::from_str(s) {
        Ok(_) => Ok(()),
        // FIXME: This should have a custom error message
        Err(e) => Err(e.to_string()),
    }
}

params! {
    /// The runtime parameters available for the file viewer
    #[derive(Debug, Clone, Default)]
    struct Params {
        show_line_numbers: bool = true,
        color_line_numbers: bool = true,
        align_line_no_left: bool = false,
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FileMeta {
    Save,
}

// A few convenience methods. More complex behavior is defined later
impl View {
    fn buffer(&self) -> &ViewBuffer<Handle> {
        &self.handler.executor().buffer
    }

    fn buffer_mut(&mut self) -> &mut ViewBuffer<Handle> {
        &mut self.handler.executor_mut().buffer
    }
}

impl super::View for View {
    fn refresh(&mut self, painter: &Painter) {
        let (width_fn, prefix_fn) = self.prefix_fn_ptrs();
        self.buffer_mut().set_prefix(width_fn, prefix_fn);

        self.buffer_mut().refresh(painter)
    }

    fn refresh_cursor(&self, painter: &Painter) {
        self.buffer().refresh_cursor(painter);
    }

    fn focus(&mut self) -> Option<RefreshKind> {
        self.buffer_mut().focus()
    }

    fn bottom_left_text(&mut self) -> Option<(String, usize)> {
        let handle = self.buffer().provider();
        let mut path_name = handle.locator().to_string();
        if handle.unsaved() {
            path_name += " [+]";
        }

        let width = path_name.len();
        Some((path_name, width))
    }

    fn bottom_right_text(&mut self) -> Option<(String, usize)> {
        // Calculate the text for the bottom right. We'll directly borrow from what Vim does: the
        // final three characters give the position in the file - either XX%, All, Top, or Bot.
        // Left of those are RRR,CC (row, column), which are allowed to expand to as wide as
        // necessary.

        let buf = self.buffer();

        let loc_str: String = {
            let row = buf.current_row();
            let height = buf.size().height;
            let top_row = row - buf.cursor_pos().row as usize;

            if top_row == 0 && height as usize >= buf.num_lines() {
                "All".into()
            } else if top_row == 0 {
                "Top".into()
            } else if top_row + height as usize >= buf.num_lines() {
                "Bot".into()
            } else {
                // Actually get the percentage. This is a complex expression that exists only
                // because we want to make a smooth transition from 0% at the top to 99% at the
                // bottom. This isn't possible if we keep a single reference point
                let lines_to_top = top_row;
                let lines_to_bot = buf.num_lines() - (top_row + height as usize);
                // ^ This subtraction is okay because if it wasn't we would have caught it with the
                // previous clause for "Bot"

                // We'll measure the percentage of the way through by the ratio between the two
                // values above.
                let percent = 100 * lines_to_top / (lines_to_top + lines_to_bot);
                //                                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^
                //                                  We could write this in terms of the buffer
                //                                  size, but this is simple enough and gets the
                //                                  point across
                format!("{: >2}%", percent)
            }
        };

        let s = format!(
            "{},{: <3}   {}",
            // We add one so that the values start at one, not zero
            buf.current_row() + 1,
            buf.current_col() + 1,
            loc_str
        );

        // Because we're only using ASCII, the length of the string is exactly equal to the width.
        let width = s.len();
        Some((s, width))
    }

    fn prefer_bottom_left(&self) -> bool {
        false
    }
}

impl View {
    pub fn constructor(path: &Path) -> ViewConstructorFn {
        let file = match Handle::open(path) {
            Ok(f) => f,
            Err(e) => {
                // If we encountered an error, log the error and provide an empty file
                // TODO: This error should get to the user as well
                log::error!("Failed to open file {:?}: {}", path, e);
                return Self::empty_constructor();
            }
        };

        Box::new(move |size| {
            let this = View {
                handler: ModeHandler::new(
                    FileExecutor {
                        buffer: ViewBuffer::new(size, file),
                        params: Params::default(),
                    },
                    NormalMode::default(),
                    ModeSet::all(),
                ),
            };

            Box::new(this)
        })
    }

    pub fn empty_constructor() -> ViewConstructorFn {
        Box::new(|size| {
            Box::new(View {
                handler: ModeHandler::new(
                    FileExecutor {
                        buffer: ViewBuffer::new(size, Handle::blank(gen_local_id(), None)),
                        params: Params::default(),
                    },
                    NormalMode::default(),
                    ModeSet::all(),
                ),
            })
        })
    }
}

fn line_num_width(buf: &ViewBuffer<Handle>) -> u16 {
    // There's an amount of padding we'll put on either side of the line numbers. Currently, this
    // value is 1, so we have a padding factor of 2 to account for both sides.
    const PADDING_FACTOR: u16 = 2;

    let width = (buf.num_lines() + 1).to_string().len() as u16;

    match width.checked_add(PADDING_FACTOR) {
        Some(w) => w,
        None => 0,
    }
}

fn line_num_prefix(
    buf: &ViewBuffer<Handle>,
    line: usize,
    align_left: bool,
    colored: bool,
) -> String {
    // Sometimes `width` might return zero - if, for instance, the value is outside the maximum
    // range of a `u16`. This won't happen in practice, but we'll catch it here anyways.
    //
    // This function should also never be called if that is the case, but we'll still be defensive
    // because it doesn't have much cost.
    let width = line_num_width(buf) as usize;
    if width == 0 {
        return String::new();
    }

    let line_no_str = match align_left {
        true => format!(" {:<width$} ", line + 1, width = width - 2),
        false => format!(" {:>width$} ", line + 1, width = width - 2),
    };

    match colored {
        true => line_no_str.yellow().to_string(),
        false => line_no_str,
    }
}

impl ConcreteView for View {}

impl SignalHandler for View {
    #[rustfmt::skip]
    fn try_handle(&mut self, signal: Signal) -> Option<Vec<OutputSignal>> {
        use OutputSignal::{NeedsRefresh, SetBottomBar};
        use RefreshKind::{BottomText, Cursor};

        // A simple function that takes any refreshes for just the cursor and raises them to
        // refresh the BottomText. This is because we want to display the location in the file in
        // the bottom right.
        fn raise_to_bottom_bar(sig: OutputSignal) -> OutputSignal {
            match sig {
                NeedsRefresh(Cursor) => NeedsRefresh(BottomText),
                _ => sig,
            }
        }

        if let Signal::NormalKey(k) = signal {
            if !self.handler.expecting_input() {
                // We'll take our opportuntity to see if we can change to some other mode
                //
                // Currently, the only other type we'll allow is "command" mode, where text is
                // entered via the bottom bar with a colon.
                if k.code == KeyCode::Char(':') {
                    return Some(vec![SetBottomBar {
                        prefix: Some(':'),
                        value: String::new(),
                        width: 0,
                        cursor_col: Some(1), // We set it to 1 because it starts from zero including the prefix
                    }]);
                }
            }

            // Otherwise, we'll just return the signal we got previously
            let mut outs: Vec<Option<Vec<OutputSignal>>> = self.handler.handle(k);

            if outs.is_empty() { Some(Vec::new()) }
            else {
                if outs.last().unwrap().is_none() {
                    // FIXME: This is temporary and should be replaced with proper error handling.
                    let last = OutputSignal::error("Failed to execute one or more commands", true);

                    // Get rid of the last element
                    outs.pop();
                    // Replace it with an error
                    outs.push(Some(vec![last]));
                }

                Some(outs.into_iter()
                    // It's okay to unwrap here because of the guarantees provided by
                    // `Handler::handle`: If the error type is returned, it will be the last
                    // element, and the `if` above will be triggered
                    .map(Option::unwrap)
                    .flatten()
                    .map(raise_to_bottom_bar)
                    .collect())
            }

        } else if let Signal::BottomBarKey { prefix: Some(':'), value, key, ..  } = signal {
            //    A few things to note here: ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
            // We're currently ignoring two fields: `cursor_col` and `previous_inputs`. These are
            // ignored for the time being because we aren't *yet* supporting changing between going
            // in/out of insert/normal mode when typing in the bottom bar. What we're doing for now
            // is always assuming that the cursor will be in the correct position.
            //
            // We're also only allowing ASCII characters, because we can then guarantee that the
            // width is correct
            self.handle_colon_key(value, key)
        } else {
            None
        }
    }
}

impl View {
    fn execute_group(&mut self, cmds: &[ColonCmd]) -> Vec<OutputSignal> {
        cmds.iter()
            .map(|cmd| {
                let style = self.handler.cursor_style();
                self.handler
                    .executor_mut()
                    .execute(cmd.clone(), style)
                    .unwrap()
                //   ^^^^^^ TODO: We shouldn't be unwrapping here
            })
            .flatten()
            .collect()
    }

    fn handle_colon_key(&mut self, cmd: &str, key: KeyEvent) -> Option<Vec<OutputSignal>> {
        use OutputSignal::{
            ClearBottomBar, LeaveBottomBar, NoSuchCmd, SaveBottomBar, SetBottomBar,
        };

        if !(key.mods == KeyModifiers::NONE || key.mods == KeyModifiers::SHIFT) {
            return None;
        }

        match key.code {
            // If the user presses escape, we'll currently just return to whatever we were in
            // before
            //
            // We won't clear the bottom bar - that can stay there until something else sets it
            KeyCode::Esc => Some(vec![LeaveBottomBar]),

            // Likewise, deleting the colon should exit the bottom bar
            //
            // This is a feature taken directly from Vim
            KeyCode::Backspace if cmd.is_empty() => Some(vec![LeaveBottomBar, ClearBottomBar]),

            KeyCode::Backspace => {
                let len = cmd.len() - 1;
                let new_cmd = String::from(&cmd[..len]);

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
                let mut new_cmd = String::with_capacity(cmd.len() + 1);
                new_cmd.push_str(cmd);
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
                // The first thing that we check is whether this command is already defined as a
                // top-level command by the container.
                //
                // If it isn't, we'll check it as one of our commands.
                if let Some(res) = container::cmd::try_exec_cmd(cmd) {
                    return Some(self.handle_container_res(res));
                }

                let cfg = Config::global();
                let chars: Vec<_> = cmd.chars().collect();

                // First, we check to see if there's a direct match
                if let Some(cmds) = cfg.keys.get(&chars) {
                    let mut signals = self.execute_group(cmds);
                    signals.extend(vec![SaveBottomBar, LeaveBottomBar]);
                    return Some(signals);
                }

                let node = cfg.keys.find(&chars);
                let no_such_command = Some(vec![LeaveBottomBar, NoSuchCmd]);

                match node {
                    None => no_such_command,
                    Some(n) if n.size() == 0 => no_such_command,
                    Some(n) => match n.try_extract() {
                        Some(cmds) => {
                            let mut signals = self.execute_group(cmds);
                            signals.extend(vec![SaveBottomBar, LeaveBottomBar]);
                            return Some(signals);
                        }

                        // This is an ambiguous case, so maybe we flash the bottom bar?
                        None => {
                            const AMBIGUOUS_COMMAND_ERR_MSG: &'static str =
                                "Ambiguous command usage";

                            Some(vec![
                                LeaveBottomBar,
                                SetBottomBar {
                                    prefix: None,
                                    value: AMBIGUOUS_COMMAND_ERR_MSG.red().to_string(),
                                    width: AMBIGUOUS_COMMAND_ERR_MSG.len(),
                                    cursor_col: None,
                                },
                            ])
                        }
                    },
                }
            }

            // Todo: traverse history
            KeyCode::Up | KeyCode::Down => todo!(),

            _ => None,
        }
    }

    fn handle_container_res(
        &mut self,
        res: Result<Option<container::cmd::Cmd>, String>,
    ) -> Vec<OutputSignal> {
        use super::ExitKind::{NoSave, ReqSave};
        use super::MetaCmd::TryClose;
        use container::cmd::Cmd::{ForceQuit, Quit, SetLocal};
        use mode_handler::Cmd::Other;
        use OutputSignal::{LeaveBottomBar, NeedsRefresh, SaveBottomBar};

        let cmd = match res {
            Err(msg) => return vec![LeaveBottomBar, OutputSignal::error(&msg, true)],
            Ok(None) => return vec![SaveBottomBar, LeaveBottomBar],
            Ok(Some(cmd)) => cmd,
        };

        let style = self.handler.cursor_style();

        let mut sigs = match cmd {
            Quit { .. } => self
                .handler
                .executor_mut()
                .execute(Other(TryClose(ReqSave)), style)
                .unwrap(),
            ForceQuit { .. } => self
                .handler
                .executor_mut()
                .execute(Other(TryClose(NoSave)), style)
                .unwrap(),
            SetLocal { args } => match self.try_set_local(args) {
                Ok(()) => {
                    self.buffer_mut().require_refresh();
                    vec![NeedsRefresh(RefreshKind::Full)]
                }
                Err(msg) => return vec![LeaveBottomBar, OutputSignal::error(&msg, true)],
            },
        };

        sigs.push(SaveBottomBar);
        sigs.push(LeaveBottomBar);
        sigs
    }

    fn prefix_fn_ptrs(
        &self,
    ) -> (
        fn(&ViewBuffer<Handle>) -> u16,
        fn(&ViewBuffer<Handle>, usize) -> String,
    ) {
        if !get_param!(self, show_line_numbers) {
            return (|_| 0, |_, _| "".into());
        }

        let colored = get_param!(self, color_line_numbers);
        let align_left = get_param!(self, align_line_no_left);

        let prefix: fn(&ViewBuffer<Handle>, usize) -> String = match (align_left, colored) {
            (true, true) => |buf, line| line_num_prefix(buf, line, true, true),
            (true, false) => |buf, line| line_num_prefix(buf, line, true, false),
            (false, true) => |buf, line| line_num_prefix(buf, line, false, true),
            (false, false) => |buf, line| line_num_prefix(buf, line, false, false),
        };

        (line_num_width, prefix)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Colon commands stuff w/ config                                             //
////////////////////////////////////////////////////////////////////////////////

type ColonCmd = mode_handler::Cmd<super::MetaCmd<FileMeta>>;

#[derive(Debug, Serialize, Deserialize)]
pub struct Builder {
    keys: Option<Vec<(String, Vec<ColonCmd>)>>,
}

static_config! {
    static GLOBAL;
    @Builder = Builder;
    pub struct Config {
        pub keys: Trie<char, Vec<ColonCmd>> = default_keybindings(),
    }

    impl ConfigPart {
        fn update(this: &mut Self, builder: Builder) {
            if let Some(ks) = builder.keys {
                ks.into_iter().for_each(|(key, cmds)| drop(this.keys.insert(key.chars().collect(), cmds)));
            }
        }
    }
}

impl XFrom<Builder> for Config {
    fn xfrom(builder: Builder) -> Self {
        Self {
            keys: builder
                .keys
                .map(|ks| {
                    Trie::from_iter(
                        ks.into_iter()
                            .map(|(key, cmds)| (key.chars().collect(), cmds)),
                    )
                })
                .unwrap_or_else(default_keybindings),
        }
    }
}

#[rustfmt::skip]
fn default_keybindings() -> Trie<char, Vec<ColonCmd>> {
    use mode_handler::Cmd::Other;
    use super::MetaCmd::{TryClose, Custom, Split, Replace, Open};
    use super::ExitKind::ReqSave;
    use Direction::{Down, Left, Up};
    use FileMeta::Save;

    let keys = vec![
        ("w", vec![Other(Custom(Save))]),
        ("wq", vec![Other(Custom(Save)), Other(TryClose(ReqSave))]),

        // Splits
        ("sp", vec![Other(Split(Down))]),
        ("vs", vec![Other(Split(Left))]),

        // Opening the file tree
        ("Ex", vec![Other(Replace(ViewKind::FileTree))]),
        ("Ve", vec![Other(Open(Left, ViewKind::FileTree))]),
        ("Se", vec![Other(Open(Up, ViewKind::FileTree))]),
    ];

    Trie::from_iter(keys.into_iter().map(|(key,cmd)| (key.chars().collect(), cmd)))
}
