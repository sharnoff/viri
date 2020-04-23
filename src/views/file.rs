mod handle;

use crate::config::prelude::*;
use crate::container::Signal;
use crate::event::{KeyCode, KeyEvent, KeyModifiers};
use crate::runtime::{Painter, TermSize};
use crate::trie::Trie;

use super::buffer::ViewBuffer;
use super::modes::{
    insert::{InsertCmd, InsertMode},
    normal::{NormalCmd, NormalMode},
    Mode, ModeResult,
};
use super::{
    Cmd, ConcreteView, ConstructedView, CursorStyle, ExitKind, OutputSignal, RefreshKind,
    SignalHandler, View, ViewKind,
};

use handle::{gen_local_id, Handle};

const INSERT_NAME: Option<(&'static str, usize)> = Some(("-- INSERT --", 12));
const NORMAL_NAME: Option<(&'static str, usize)> = /* Some(("-- NORMAL --", 12)) */ None;

#[derive(Debug)]
pub struct FileView {
    buffer: ViewBuffer<Handle>,
    mode: ModeSwitch,
}

#[derive(Debug)]
enum ModeSwitch {
    Normal(NormalMode),
    Insert(InsertMode),
}

impl ModeSwitch {
    fn cursor_style(&self) -> CursorStyle {
        match self {
            Self::Normal(m) => m.cursor_style(),
            Self::Insert(m) => m.cursor_style(),
        }
    }

    fn currently_waiting(&self) -> bool {
        match self {
            Self::Normal(m) => m.currently_waiting(),
            Self::Insert(m) => m.currently_waiting(),
        }
    }
}

impl Default for ModeSwitch {
    fn default() -> Self {
        Self::Normal(NormalMode::new())
    }
}

impl View for FileView {
    fn refresh(&mut self, painter: &Painter) {
        self.buffer.refresh(painter);
    }

    fn refresh_cursor(&self, painter: &Painter) {
        self.buffer.refresh_cursor(painter);
    }

    fn bottom_left_text(&mut self) -> Option<(String, usize)> {
        let text = match self.mode {
            ModeSwitch::Normal(_) => NORMAL_NAME,
            ModeSwitch::Insert(_) => INSERT_NAME,
        };

        text.map(|(s, w)| (String::from(s), w))
    }

    fn bottom_right_text(&mut self) -> Option<(String, usize)> {
        // Calculate the text for the bottom right. We'll directly borrow from what Vim does: the
        // final three characters give the position in the file - either XX%, All, Top, or Bot.
        // Left of those are RRR,CC (row, column), which are allowed to expand to as wide as
        // necessary.

        let loc_str: String = {
            let row = self.buffer.current_row();
            let height = self.buffer.size().height;
            let top_row = row - self.buffer.cursor_pos().row as usize;
            // let top_row = row - (height - self.buffer.cursor_pos().row - 1) as usize;

            if top_row == 0 && height as usize >= self.buffer.num_lines() {
                "All".into()
            } else if top_row == 0 {
                "Top".into()
            } else if top_row + height as usize >= self.buffer.num_lines() {
                "Bot".into()
            } else {
                // Actually get the percentage. This is a complex expression that exists only
                // because we want to make a smooth transition from 0% at the top to 99% at the
                // bottom. This isn't possible if we keep a single reference point
                let lines_to_top = top_row;
                let lines_to_bot = self.buffer.num_lines() - (top_row + height as usize);
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
            self.buffer.current_row(),
            self.buffer.current_col(),
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
        self.buffer.resize(size)
    }
}

impl ConstructedView for FileView {
    // Meaning of args:
    // If the first argument is not given, a blank file will be used. Otherwise, we'll try to
    // open the file with name args[0]
    fn init<S: AsRef<str>>(size: TermSize, args: &[S]) -> Self {
        if args.is_empty() {
            return Self {
                buffer: ViewBuffer::new(size, Handle::blank(gen_local_id())),
                mode: ModeSwitch::default(),
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
                    buffer: ViewBuffer::new(size, Handle::blank(gen_local_id())),
                    mode: ModeSwitch::default(),
                };
            }
        };

        Self {
            buffer: ViewBuffer::new(size, file),
            mode: ModeSwitch::default(),
        }
    }
}

impl ConcreteView for FileView {
    fn kind(&self) -> ViewKind {
        ViewKind::File
    }
}

impl SignalHandler for FileView {
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
            if !self.mode.currently_waiting() {
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

            let (new_mode, sig) = match &mut self.mode {
                ModeSwitch::Normal(m) => Self::handle_normal(&mut self.buffer, m, k),
                ModeSwitch::Insert(m) => Self::handle_insert(&mut self.buffer, m, k),
            };

            log::trace!("new mode: {:?}, sig: {:?}", new_mode, sig);

            if let Some(m) = new_mode {
                self.mode = m;
            }

            // Otherwise, we'll just return the signal we got previously
            raise_to_bottom_bar(sig)
        } else if let Signal::BottomBarKey {
            prefix: Some(':'),
            value,
            key,
            ..
        } = signal
        {
            //    A few things to note here: ^^^^^^^^^^^^^^^^^^^^^^^^^^^
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

impl FileView {
    fn handle_normal(
        buf: &mut ViewBuffer<Handle>,
        mode: &mut NormalMode,
        key: KeyEvent,
    ) -> (Option<ModeSwitch>, OutputSignal) {
        use ModeResult::{NeedsMore, NoCommand};
        use OutputSignal::{NoSuchCmd, WaitingForMore};

        let res = mode.try_handle(key);
        log::trace!("handled normal: {:?}", res);
        match res {
            NeedsMore => (None, WaitingForMore),
            NoCommand => (None, NoSuchCmd),
            ModeResult::Cmd(c) => {
                let mut new_mode: Option<ModeSwitch> = None;

                let refresh: Option<RefreshKind> = buf.execute_cmd(&c, &mut |buf, cmd| {
                    log::trace!("handle_normal_cmd: {:?}", cmd);
                    Self::handle_normal_cmd(buf, cmd, &mut new_mode)
                });

                // TODO: When we actually start handling files, this will need to be done better.
                let sig = match c {
                    Cmd::TryClose(_) => OutputSignal::Close,
                    _ => refresh
                        .map(OutputSignal::NeedsRefresh)
                        .unwrap_or(OutputSignal::Nothing),
                };

                (new_mode, sig)
            }
        }
    }

    fn handle_normal_cmd(
        buf: &mut ViewBuffer<Handle>,
        cmd: &NormalCmd,
        new_mode: &mut Option<ModeSwitch>,
    ) -> Option<RefreshKind> {
        use super::HorizontalMove::{UntilFst, UntilSnd};
        use super::Movement::{Down, Left, Right, Up};

        match cmd {
            NormalCmd::ExitMode => None,
            NormalCmd::ChangeMode(s) => match s.as_ref() {
                "insert" => {
                    *new_mode = Some(ModeSwitch::Insert(InsertMode::new()));
                    buf.set_allow_after(new_mode.as_ref().unwrap().cursor_style().allow_after);
                    None
                }
                _ => {
                    log::warn!(
                        "{}: Tried to switch to mode {}, which is not known",
                        "views::file::FileView::handle_normal_cmd",
                        s
                    );
                    None
                }
            },
            &NormalCmd::Delete(movement, amount) => match movement {
                Right(UntilFst(pred), cross) => {
                    buf.delete_movement(Right(UntilSnd(pred), cross), amount, true)
                }
                Left(_, _) | Right(_, _) => buf.delete_movement(movement, amount, true),
                Up | Down => {
                    // the '?' implies that if we don't move, we won't delete anything
                    let (new_row, _) = buf.simulate_movement(movement, amount, true)?;
                    let old_row = buf.current_row();

                    if new_row > old_row {
                        buf.delete_lines(old_row..=new_row)
                    } else {
                        buf.delete_lines(new_row..=old_row)
                    }
                }
            },
        }
    }

    fn handle_insert(
        buf: &mut ViewBuffer<Handle>,
        mode: &mut InsertMode,
        key: KeyEvent,
    ) -> (Option<ModeSwitch>, OutputSignal) {
        use ModeResult::{NeedsMore, NoCommand};
        use OutputSignal::{NoSuchCmd, WaitingForMore};

        match mode.try_handle(key) {
            NeedsMore => (None, WaitingForMore),
            NoCommand => (None, NoSuchCmd),
            ModeResult::Cmd(c) => {
                let mut new_mode = None;

                let refresh: Option<RefreshKind> = buf.execute_cmd(&c, &mut |buf, cmd| {
                    Self::handle_insert_cmd(buf, cmd, &mut new_mode)
                });
                // TODO: When we actually start handling files, this will need to be done better.
                let sig = match c {
                    Cmd::TryClose(_) => OutputSignal::Close,
                    _ => refresh
                        .map(OutputSignal::NeedsRefresh)
                        .unwrap_or(OutputSignal::Nothing),
                };

                (new_mode, sig)
            }
        }
    }

    fn handle_insert_cmd(
        buf: &mut ViewBuffer<Handle>,
        cmd: &InsertCmd,
        new_mode: &mut Option<ModeSwitch>,
    ) -> Option<RefreshKind> {
        match cmd {
            InsertCmd::ExitMode => {
                *new_mode = Some(ModeSwitch::Normal(NormalMode::new()));
                buf.set_allow_after(new_mode.as_ref().unwrap().cursor_style().allow_after);
                None
            }
            InsertCmd::InsertChar(c) => {
                let mut b = [0_u8; 4];
                buf.insert(c.encode_utf8(&mut b))
            }
            InsertCmd::Delete(movement) => buf.delete_movement(*movement, 1, true),
        }
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

                log::trace!("views::file - {:?}", sig);
                sig
            }

            // We'll attempt to use this command
            KeyCode::Enter => {
                let cfg = Config::global();
                let chars: Vec<_> = cmd.chars().collect();

                log::trace!("chars: {:?}", chars);
                log::trace!("trie: {:?}", cfg.keys);

                // First, we check to see if there's a direct match
                if let Some(cmd) = cfg.keys.get(&chars) {
                    self.handle_colon_cmd(cmd)
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
                            Some(cmd) => self.handle_colon_cmd(cmd),

                            // This is an ambiguous case, so maybe we flash the bottom bar?
                            None => {
                                log::trace!("faulty todo - node: {:?}", n);
                                todo!()
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

    fn handle_colon_cmd(&mut self, cmd: &Cmd<ColonCmd>) -> OutputSignal {
        use crossterm::style::Colorize;
        use Cmd::{Cursor, Extra, Scroll, TryClose};
        use ExitKind::{NoSave, ReqSave};
        use OutputSignal::{Chain, Close, LeaveBottomBar, SaveBottomBar, SetBottomBar};

        match cmd {
            TryClose(ReqSave) => {
                if self.unsaved() {
                    const UNSAVED_ERR_MSG: &'static str =
                        "No write since last change (use ! to override)";

                    let set_err_msg = SetBottomBar {
                        prefix: None,
                        value: UNSAVED_ERR_MSG.red().to_string(),
                        width: UNSAVED_ERR_MSG.len(),
                        cursor_col: None,
                    };

                    Chain(vec![LeaveBottomBar, set_err_msg])
                } else {
                    Chain(vec![SaveBottomBar, Close])
                }
            }

            TryClose(NoSave) => Chain(vec![SaveBottomBar, Close]),

            // These should probably issue some kind of warning that they aren't allowed (yet?)
            // ^ But we're probably allowing cursor movement soon, just not scrolling.
            Cursor(_, _) | Scroll(_, _) => todo!(),

            Extra(ColonCmd::Save) => match self.try_save() {
                Err(err_str) => {
                    let width = err_str.len();
                    Chain(vec![
                        LeaveBottomBar,
                        SetBottomBar {
                            prefix: None,
                            value: err_str.red().to_string(),
                            width,
                            cursor_col: None,
                        },
                    ])
                }
                Ok(_) => Chain(vec![SaveBottomBar, LeaveBottomBar]),
            },

            // TODO: There should be a better way of doing this
            Cmd::Chain(v) => Chain(v.iter().map(|c| self.handle_colon_cmd(c)).collect()),
        }
    }

    fn try_save(&mut self) -> Result<(), String> {
        self.buffer
            .provider_mut()
            .write()
            .map_err(|e| e.to_string())
    }

    fn unsaved(&self) -> bool {
        log::trace!("checking unsaved");
        let unsaved = self.buffer.provider().unsaved();
        log::trace!("unsaved: {}", unsaved);
        unsaved
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Colon commands stuff w/ config                                                                 //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[non_exhaustive]
#[derive(Debug, Clone, Serialize, Deserialize)]
enum ColonCmd {
    /// A request to save the current file
    Save,
}

#[derive(Debug, Serialize, Deserialize)]
struct Builder {
    keys: Option<Vec<(String, Cmd<ColonCmd>)>>,
}

static_config! {
    static GLOBAL;
    @Builder = Builder;
    struct Config {
        pub keys: Trie<char, Cmd<ColonCmd>> = default_keybindings(),
    }

    impl ConfigPart {
        fn update(this: &mut Self, builder: Builder) {
            if let Some(ks) = builder.keys {
                ks.into_iter().for_each(|(key, cmd)| drop(this.keys.insert(key.chars().collect(), cmd)));
            }
        }
    }
}

impl From<Builder> for Config {
    fn from(builder: Builder) -> Self {
        Self {
            keys: builder
                .keys
                .map(|ks| {
                    Trie::from_iter(
                        ks.into_iter()
                            .map(|(key, cmd)| (key.chars().collect(), cmd)),
                    )
                })
                .unwrap_or_else(default_keybindings),
        }
    }
}

#[rustfmt::skip]
fn default_keybindings() -> Trie<char, Cmd<ColonCmd>> {
    // use crate::event::{KeyCode::Esc, KeyModifiers as Mods};
    use Cmd::{TryClose, Chain, Extra};
    use ExitKind::{ReqSave, NoSave};
    use ColonCmd::Save;

    let keys = vec![
        ("q", TryClose(ReqSave)),
        ("q!", TryClose(NoSave)),
        ("w", Extra(Save)),
        ("wq", Chain(vec![Extra(Save), TryClose(ReqSave)])),
    ];

    Trie::from_iter(keys.into_iter().map(|(key,cmd)| (key.chars().collect(), cmd)))
}
