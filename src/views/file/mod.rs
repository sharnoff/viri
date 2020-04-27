use crossterm::style::Colorize;

use super::buffer::ViewBuffer;
use super::{
    ConcreteView, ConstructedView, MetaCmd, OutputSignal, RefreshKind, SignalHandler, ViewKind,
};
use crate::config::prelude::*;
use crate::container::Signal;
use crate::event::{KeyCode, KeyEvent, KeyModifiers};
use crate::mode::handler::{self as mode_handler, Executor, Handler as ModeHandler};
use crate::mode::{normal::Mode as NormalMode, ModeSet};
use crate::prelude::*;
use crate::runtime::{Painter, TermSize};
use crate::trie::Trie;
use crate::utils::Seq;

mod edits;
mod executor;
mod handle;

use executor::FileExecutor;
use handle::{gen_local_id, Handle};

/// The primary file viewer
pub struct View {
    handler: ModeHandler<FileExecutor, MetaCmd<FileMeta>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum FileMeta {
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
        self.buffer_mut().refresh(painter)
    }

    fn refresh_cursor(&self, painter: &Painter) {
        self.buffer().refresh_cursor(painter);
    }

    fn bottom_left_text(&mut self) -> Option<(String, usize)> {
        let text = self.handler.try_name_with_width();

        text.map(|(s, w)| (String::from(s), w))
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
            // let top_row = row - (height - self.buffer.cursor_pos().row - 1) as usize;

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
            buf.current_row(),
            buf.current_col(),
            loc_str
        );

        // Because we're only using ASCII, the length of the string is exactly equal to the width.
        let width = s.len();
        Some((s, width))
    }

    fn prefer_bottom_left(&self) -> bool {
        false
    }

    fn resize(&mut self, size: TermSize) -> OutputSignal {
        self.buffer_mut().resize(size)
    }
}

impl ConstructedView for View {
    // Meaning of args:
    // If the first argument is not given, a blank file will be used. Otherwise, we'll try to
    // open the file with name args[0]
    fn init<S: AsRef<str>>(size: TermSize, args: &[S]) -> Self {
        if args.is_empty() {
            return Self {
                handler: ModeHandler::new(
                    FileExecutor {
                        buffer: ViewBuffer::new(size, Handle::blank(gen_local_id())),
                    },
                    NormalMode::default(),
                    ModeSet::all(),
                ),
            };
        }

        if args.len() > 1 {
            log::warn!("FileView received args with len > 1, ignoring entries.");
            log::warn!(
                "Ignored: {:?}",
                args[1..].iter().map(AsRef::as_ref).collect::<Vec<_>>()
            );
        }

        let path = args[0].as_ref();

        // TODO: In the future, this will
        let file = match Handle::open(path) {
            Ok(f) => f,
            Err(e) => {
                // (Temporary solution)
                // If we encountered an error, log the error and provide an empty file
                log::error!("Failed to open file {}: {}", path, e);
                return Self {
                    handler: ModeHandler::new(
                        FileExecutor {
                            buffer: ViewBuffer::new(size, Handle::blank(gen_local_id())),
                        },
                        NormalMode::default(),
                        ModeSet::all(),
                    ),
                };
            }
        };

        Self {
            handler: ModeHandler::new(
                FileExecutor {
                    buffer: ViewBuffer::new(size, file),
                },
                NormalMode::default(),
                ModeSet::all(),
            ),
        }
    }
}

impl ConcreteView for View {
    fn kind(&self) -> ViewKind {
        ViewKind::File
    }
}

impl SignalHandler for View {
    #[rustfmt::skip]
    fn try_handle(&mut self, signal: Signal) -> OutputSignal {
        // A simple function that takes any refreshes for just the cursor and raises them to
        // refresh the BottomText. This is because we want to display the location in the file in
        // the bottom right.
        fn raise_to_bottom_bar(sig: OutputSignal) -> OutputSignal {
            use OutputSignal::{Chain, NeedsRefresh};
            use RefreshKind::{BottomText, Cursor};

            match sig {
                NeedsRefresh(Cursor) => NeedsRefresh(BottomText),
                Chain(v) => Chain(v.into_iter().map(raise_to_bottom_bar).collect()),
                s => s,
            }
        }

        if let Signal::NormalKey(k) = signal {
            if !self.handler.expecting_input() {
                // We'll take our opportuntity to see if we can change to some other mode
                //
                // Currently, the only other type we'll allow is "command" mode, where text is
                // entered via the bottom bar with a colon.
                if k.code == KeyCode::Char(':') && k.mods == KeyModifiers::NONE {
                    return OutputSignal::SetBottomBar {
                        prefix: Some(':'),
                        value: String::new(),
                        width: 0,
                        cursor_col: Some(1), // We set it to 1 because it starts from zero including the prefix
                    };
                }
            }

            // Otherwise, we'll just return the signal we got previously
            let mut outs: Vec<Option<OutputSignal>> = self.handler.handle(k);
            log::trace!("{}:{}: outs = {:?}", file!(), line!(), outs);

            if outs.is_empty() { OutputSignal::Nothing }
            else if outs.last().unwrap().is_none() {
                // TODO: This is temporary and should be replaced with proper error handling.
                let last = OutputSignal::SetBottomBar {
                    prefix: None,
                    value: "Failed to execute command. Please rewrite this section".red().to_string(),
                    width: 54,
                    cursor_col: None,
                };

                outs.pop();
                outs.push(Some(last));
                raise_to_bottom_bar(OutputSignal::Chain(outs.into_iter().map(Option::unwrap).collect()))
            } else {
                raise_to_bottom_bar(OutputSignal::Chain(outs.into_iter().map(Option::unwrap).collect()))
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
            OutputSignal::Nothing
        }
    }
}

impl View {
    fn execute_group(&mut self, cmds: &Seq<ColonCmd>) -> OutputSignal {
        let mut chain = Vec::new();

        for cmd in cmds.iter() {
            let style = self.handler.cursor_style();
            chain.push(
                self.handler
                    .executor_mut()
                    .execute(cmd.clone(), style)
                    .unwrap(),
                // ^^^^^^ TODO: We shouldn't be unwrapping here
            )
        }

        OutputSignal::Chain(chain)
    }

    fn handle_colon_key(&mut self, cmd: &str, key: KeyEvent) -> OutputSignal {
        if key.mods != KeyModifiers::NONE {
            return OutputSignal::Nothing;
        }

        match key.code {
            // If the user presses escape, we'll currently just return to whatever we were in
            // before
            //
            // We won't clear the bottom bar - that can stay there until something else sets it
            KeyCode::Esc => OutputSignal::LeaveBottomBar,

            // Likewise, deleting the colon should exit the bottom bar
            //
            // This is a feature taken directly from Vim
            KeyCode::Backspace if cmd.is_empty() => OutputSignal::Chain(vec![
                OutputSignal::LeaveBottomBar,
                OutputSignal::ClearBottomBar,
            ]),

            KeyCode::Backspace => {
                let len = cmd.len() - 1;
                let new_cmd = String::from(&cmd[..len]);

                OutputSignal::SetBottomBar {
                    prefix: Some(':'),
                    value: new_cmd,
                    width: len,
                    // We add one because the cursor column includes the prefix character
                    cursor_col: Some(len + 1),
                }
            }

            // We'll only allow ASCII characters
            KeyCode::Char(c) if c.is_ascii() => {
                let mut new_cmd = String::with_capacity(cmd.len() + 1);
                new_cmd.push_str(cmd);
                new_cmd.push(c);

                let len = new_cmd.len();

                let sig = OutputSignal::SetBottomBar {
                    prefix: Some(':'),
                    value: new_cmd,
                    width: len,
                    // We add one because the cursor column includes the prefix character
                    cursor_col: Some(len + 1),
                };

                sig
            }

            // We'll attempt to use this command
            KeyCode::Enter => {
                let cfg = Config::global();
                let chars: Vec<_> = cmd.chars().collect();

                // First, we check to see if there's a direct match
                if let Some(cmds) = cfg.keys.get(&chars) {
                    self.execute_group(cmds)
                } else {
                    let node = cfg.keys.find(&chars);
                    let no_such_command = OutputSignal::Chain(vec![
                        OutputSignal::LeaveBottomBar,
                        OutputSignal::NoSuchCmd,
                    ]);

                    match node {
                        None => no_such_command,
                        Some(n) if n.size() == 0 => no_such_command,
                        Some(n) => match n.try_extract() {
                            Some(cmds) => self.execute_group(cmds),

                            // This is an ambiguous case, so maybe we flash the bottom bar?
                            None => {
                                const AMBIGUOUS_COMMAND_ERR_MSG: &'static str =
                                    "Ambiguous command usage";

                                OutputSignal::Chain(vec![
                                    OutputSignal::LeaveBottomBar,
                                    OutputSignal::SetBottomBar {
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
            }

            // Todo: traverse history
            KeyCode::Up | KeyCode::Down => todo!(),

            _ => OutputSignal::Nothing,
        }
    }

    fn try_save(&mut self) -> Result<(), String> {
        self.buffer_mut()
            .provider_mut()
            .write()
            .map_err(|e| e.to_string())
    }

    fn unsaved(&self) -> bool {
        let unsaved = self.buffer().provider().unsaved();
        unsaved
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Colon commands stuff w/ config                                                                 //
////////////////////////////////////////////////////////////////////////////////////////////////////

type ColonCmd = mode_handler::Cmd<super::MetaCmd<FileMeta>>;

#[derive(Debug, Serialize, Deserialize)]
struct Builder {
    keys: Option<Vec<(String, Seq<ColonCmd>)>>,
}

static_config! {
    static GLOBAL;
    @Builder = Builder;
    struct Config {
        pub keys: Trie<char, Seq<ColonCmd>> = default_keybindings(),
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
fn default_keybindings() -> Trie<char, Seq<ColonCmd>> {
    use mode_handler::Cmd::Other;
    use super::MetaCmd::{TryClose, Custom};
    use super::ExitKind::{ReqSave, NoSave};
    use FileMeta::Save;

    let keys = vec![
        ("q", One(Other(TryClose(ReqSave)))),
        ("q!", One(Other(TryClose(NoSave)))),
        ("w", One(Other(Custom(Save)))),
        ("wq", Many(vec![Other(Custom(Save)), Other(TryClose(ReqSave))])),
    ];

    Trie::from_iter(keys.into_iter().map(|(key,cmd)| (key.chars().collect(), cmd)))
}