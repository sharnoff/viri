use std::collections::HashMap;
use std::convert::TryInto;
use std::io::{self, Write};

use crossterm::{cursor, style, QueueableCommand};

use crate::event::{KeyEvent, MouseEvent};
use crate::runtime::{self as rt, Painter, TermSize};
use crate::utils;
use crate::views::{self, ConcreteView, RefreshKind, ViewKind};

/// The primary interface between the runtime and the tree of `View`s
///
/// This type takes runtime signals as input and feeds them to the tree of [`View`]s, before taking
/// the resulting view signal and returning a runtime signal, if any was generating. This is done
/// through the [`handle_rt_event`] method.
///
/// [`View`]: ../views/trait.View.html
/// [`handle_rt_event`]: #method.handle_rt_event
pub struct Container {
    /// The displayed view. We box it so that any type of view may be used.
    inner: Box<dyn ConcreteView>,

    /// The current size of the editor
    ///
    /// This is updated any `resize` operation
    size: TermSize,

    /// The current input mode
    ///
    /// This is described in more detail in the [section about the type].
    ///
    /// [section about the type]: enum.InputMode.html
    input_mode: InputMode,

    /// The set of previously used inputs on the bottom bar
    ///
    /// The keys in the hashmap are the starting characters at the bottom bar. The inputs are
    /// stored in the order they were used, so that the last element was the most recent ending
    /// value.
    previous_bottom_bars: HashMap<Option<char>, Vec<String>>,
}

/// The current input method - either directly to views or through the bottom bar
///
/// This doesn't strictly map to the total set of available modes; it only records the field that
/// input is being provided to.
#[derive(Debug, Clone)]
pub enum InputMode {
    /// The "default" way of using the editor
    ///
    /// This corresponds to keybindings that are being fed directly to the views - typically
    /// "normal", "insert", or "visual" mode.
    Normal,

    /// Entering text with a certain starting character at the *bottom left*
    ///
    /// This corresponds to a certain subset of input methods in vi/vim: typically searching (with
    /// '/') or entering commands (with ':'). The prefix field gives the starting character of the
    /// bottom bar, if present.  If this is not a character with a display width of one column,
    /// this *can* affect displayed values on the same line.
    ///
    /// ## Example value
    ///
    /// For a bottom bar that looks like the following:
    /// ```text
    /// :%s/foo/bar/g
    /// ```
    /// the prefix is the character `:`, and the value is the string `"%s/foo/bar/g"`.
    ///
    /// Note that this input mode is distinct from displaying to the bottom bar; the latter will be
    /// ignored (with warnings emitted) while this is true.
    // ^ TODO: Update documentation. This was originally written for a version that did not have
    // optional prefixes/cursor columns
    BottomBar {
        prefix: Option<char>,
        value: String,
        width: usize,
        cursor_col: Option<usize>,
    },
}

/// The input signals sent to `View`s
///
/// The primary purpose of the [`Container`] is to handle the conversion of runtime [`Signal`]s into
/// these signals for providing to [`View`]s
///
/// [`Container`]: struct.Container.html
/// [`Signal`]: ../runtime/enum.Signal.html
/// [`View`]: ../views/trait.View.html
#[derive(Debug, Copy, Clone)]
pub enum Signal<'a> {
    /// Represents a key input given while the input mode is `Normal`
    NormalKey(KeyEvent),
    BottomBarKey {
        prefix: Option<char>,
        value: &'a str,
        key: KeyEvent,
        cursor_col: usize,
        previous_inputs: &'a [String],
    },
    Mouse(MouseEvent),
}

/// Picks which view to initialize the container with
///
/// The current implementation always defaults to the file viewer - this can be changed fairly
/// easily, however.
fn pick_init_view(args: &[&str]) -> ViewKind {
    #![allow(unused_variables)]
    ViewKind::File
}

////////////////////////////////////////////////////////////////////////////////
// Utility functions                                                          //
////////////////////////////////////////////////////////////////////////////////

impl Container {
    fn bottom_offset(&self) -> usize {
        match &self.input_mode {
            &InputMode::BottomBar {
                width, cursor_col, ..
            } => {
                let max_width = cursor_col.unwrap_or(0).max(width + 1);
                (max_width - 1) / self.size.width as usize + 1
            }
            InputMode::Normal => 1,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Core facilities                                                            //
// ---------------                                                            //
// This excludes one function, `handle_view_output_exits`. That function      //
// relies on many others, so they are all grouped into a separate impl block. //
////////////////////////////////////////////////////////////////////////////////

impl Container {
    /// Refreshes the cursor location, whether that is the bottom bar or in the inner `View`
    fn update_cursor(&mut self) {
        match self.input_mode {
            InputMode::BottomBar {
                cursor_col: Some(col),
                ..
            } => {
                let start_height = self.size.height - self.bottom_offset() as u16;
                let cursor_height = start_height + (col / self.size.width as usize) as u16;
                let cursor_col = (col % self.size.width as usize) as u16;

                io::stdout()
                    .queue(cursor::MoveTo(cursor_col, cursor_height))
                    .unwrap()
                    .flush()
                    .unwrap();
            }
            _ => {
                let mut painter = Painter::global(self.size);
                if let Ok(offset) = self.bottom_offset().try_into() {
                    if let Some(mut p) = painter.trim_bot(offset) {
                        self.inner.refresh_cursor(&mut p);
                    }
                }
            }
        }
    }

    /// Writes the contents of the bottom bar to the screen
    fn write_bottom_bar(&mut self) {
        match &self.input_mode {
            InputMode::Normal => {
                // get the bottom bar from the view
                let bot_str = self.inner.construct_bottom_text(self.size.width);

                // And now print it
                //
                // * We move to the last row because it will *always* be exactly just the last row
                // that gets printed.
                let mut stdout = io::stdout();
                stdout
                    .queue(cursor::MoveTo(0, self.size.height - 1))
                    .unwrap();
                stdout.queue(style::Print(bot_str)).unwrap();
                stdout.flush().unwrap();
            }
            InputMode::BottomBar {
                prefix,
                value,
                width,
                ..
            } => {
                let offset = self.bottom_offset();
                // handle the bottom bar stuff
                let remaining_width = offset * (self.size.width as usize) - width;

                let post_str = utils::blank_str(remaining_width as u16);

                let start_height = self.size.height - (offset as u16);
                // ^ FIXME: Currently this will panic if the offset is greater than the height.
                // This needs fixing, along with the other places that make a similar assumption.
                // To find those, search by `bottom_offset()`.

                let mut bot_str = String::with_capacity(1 + value.len() + post_str.len());
                if let &Some(p) = prefix {
                    bot_str.push(p);
                }
                bot_str.push_str(&value);
                bot_str.push_str(post_str);

                io::stdout()
                    .queue(cursor::MoveTo(0, start_height))
                    .unwrap()
                    .queue(style::Print(bot_str))
                    .unwrap()
                    .flush()
                    .unwrap();
            }
        }
    }

    /// The primary interface to the runtime
    ///
    /// This handles a runtime user event, and returns a runtime signal - if one was generated.
    pub fn handle_rt_event(&mut self, event: rt::Event) -> Option<rt::Signal> {
        use rt::Event::{Resize, User};
        use rt::UserEvent::{Key, Mouse};
        use InputMode::BottomBar;

        let signals: Option<Vec<_>> = match event {
            User(event) => {
                // We need this complex control flow here because separating it into multiple
                // functions would cause a borrow-checker conflict.
                //
                // If only we had partial borrows... :(
                let signal = match event {
                    Key(key) => match &self.input_mode {
                        BottomBar {
                            prefix,
                            value,
                            cursor_col: Some(cursor_col),
                            ..
                        } => Signal::BottomBarKey {
                            prefix: *prefix,
                            value: &value,
                            key,
                            cursor_col: *cursor_col,
                            previous_inputs: self
                                .previous_bottom_bars
                                .get(prefix)
                                .map(Vec::as_ref)
                                .unwrap_or(&[]),
                        },
                        _ => Signal::NormalKey(key),
                    },
                    Mouse(m) => Signal::Mouse(m),
                };

                log::debug!("{}:{}: giving inner signal: {:?}", file!(), line!(), signal);

                self.inner.try_handle(signal)
            }
            Resize(size) => {
                self.size = size;
                // We'll resize the inner `View` by giving an update through a resized painter
                self.handle_refresh(RefreshKind::Full);
                Some(Vec::new())
            }
        };

        log::debug!(
            "{}:{}: received `OutputSignal`s: {:?}",
            file!(),
            line!(),
            signals
        );

        if signals?
            .into_iter()
            .any(|sig| self.handle_view_output_exits(sig))
        {
            return Some(rt::Signal::Exit);
        }

        None
    }

    /// Initializes the container with the default `View`, provided with the given arguments
    pub fn init(size: TermSize, args: &[&str]) -> Self {
        // Current version:
        //  - Always use the text viewer
        //  - Only support (at most) one argument, the filepath to open

        let input_mode = InputMode::Normal;
        // Bottom offset is always 1 for normal mode
        let bottom_offset = 1_u16;

        let inner_size = TermSize {
            height: size.height - bottom_offset,
            width: size.width,
        };

        let mut inner = pick_init_view(args).to_view(inner_size, args);
        inner.refresh(&mut Painter::global(inner_size));

        let mut this = Self {
            inner,
            size,
            input_mode,
            previous_bottom_bars: HashMap::new(),
        };

        this.write_bottom_bar();
        this.update_cursor();

        this
    }
}

////////////////////////////////////////////////////////////////////////////////
// Handling `View` output signals                                             //
// ------------------------------                                             //
// This impl block primarily defines `handle_view_output_exits`, which        //
// handles a single `OutputSignal` from the inner `View`.                     //
//                                                                            //
// There are many different variants to account for, so (for the most part)   //
// they are split into separate functions. These functions exist purely as    //
// helper functions; they are not intended to be called from outside this     //
// impl block.                                                                //
////////////////////////////////////////////////////////////////////////////////

impl Container {
    /// Handles the result of passing a signal to the outermost view
    ///
    /// Returns true iff the the resulting signal successfully requested an exit
    fn handle_view_output_exits(&mut self, signal: views::OutputSignal) -> bool {
        use views::OutputSignal::{
            ClearBottomBar, Close, LeaveBottomBar, NeedsRefresh, NoSuchCmd, Nothing, SaveBottomBar,
            SetBottomBar, WaitingForMore,
        };

        match signal {
            Nothing => (),
            NeedsRefresh(kind) => self.handle_refresh(kind),
            SaveBottomBar => self.save_bottom_bar(),

            SetBottomBar {
                prefix,
                value,
                width,
                cursor_col,
            } => return self.set_bottom_bar(prefix, value, width, cursor_col),

            LeaveBottomBar => self.leave_bottom_bar(),

            ClearBottomBar => self.clear_bottom_bar(),

            // TODO: Ring the bell when we don't have a command?
            NoSuchCmd => {}

            // TODO - In a later version we'll need to keep track of this
            WaitingForMore => {}

            // If the outer-most view closes, we exit.
            Close => return true,
        }

        false
    }

    fn handle_refresh(&mut self, kind: RefreshKind) {
        use InputMode::BottomBar;
        use RefreshKind::{BottomText, Cursor, Full, Inner};

        let mut global_painter = Painter::global(self.size);
        let mut local = match self.bottom_offset().try_into() {
            Ok(offset) => global_painter.trim_bot(offset),
            Err(_) => None,
        };

        match kind {
            Cursor => match self.input_mode {
                BottomBar { cursor_col, .. } if cursor_col.is_some() => {
                    log::warn!(
                        "{}:{}: cannot refresh cursor; current input mode is bottom bar",
                        file!(),
                        line!(),
                    );
                }
                _ => self.update_cursor(),
            },
            BottomText => {
                self.write_bottom_bar();
                self.update_cursor();
            }
            Full | Inner if local.is_some() => {
                self.inner.refresh(local.as_mut().unwrap());
                self.write_bottom_bar();
                self.update_cursor();
            }
            // Tried to refresh but there isn't anything there to display
            _ => log::warn!(
                "{}:{}: cannot refresh inner `View`; current PTY is too small",
                file!(),
                line!(),
            ),
        }
    }

    fn save_bottom_bar(&mut self) {
        use InputMode::BottomBar;

        if let BottomBar { prefix, value, .. } = &self.input_mode {
            let mut new_list = self
                .previous_bottom_bars
                .remove(prefix)
                .unwrap_or(Vec::new());
            new_list.push(value.clone());
            self.previous_bottom_bars.insert(*prefix, new_list);
        } else {
            log::warn!(
                "{}:{} - Attempted to save bottom bar when nothing is there",
                file!(),
                line!()
            );
        }
    }

    /// The boolean return here has the same meaning as for `handle_view_output_exits`
    fn set_bottom_bar(
        &mut self,
        prefix: Option<char>,
        value: String,
        width: usize,
        cursor_col: Option<usize>,
    ) -> bool {
        // Something to note here:
        // If the total width is greater than the width of the screen, we'll need to split
        // it into multiple lines. If this changes the `num_rows` field of `BottomBar`,
        // we'll need to resize the contents.

        // Now we're set to replace the contents.
        let max_width = cursor_col.unwrap_or(0).max(width + 1);
        let num_rows = (max_width - 1) / (self.size.width as usize) + 1;
        // ^ Integer division rounding up
        let previous_bottom_offset = self.bottom_offset();

        self.input_mode = InputMode::BottomBar {
            prefix,
            value,
            width: max_width,
            cursor_col,
        };

        // Actually write the bottom row(s)
        self.write_bottom_bar();

        // if num_rows changed, resize
        if num_rows != (previous_bottom_offset as usize) && (self.size.height as usize) > num_rows {
            // We resized, so we'll refresh the inner `View`
            self.handle_refresh(RefreshKind::Full);
        }

        self.update_cursor();
        false
    }

    fn leave_bottom_bar(&mut self) {
        match &mut self.input_mode {
            InputMode::Normal
            | InputMode::BottomBar {
                cursor_col: None, ..
            } => log::warn!(
                "{}:{}: received `LeaveBottomBar` signal while already in `Normal` input mode",
                file!(),
                line!(),
            ),
            InputMode::BottomBar { cursor_col, .. } => {
                *cursor_col = None;
                self.update_cursor();
            }
        }
    }

    fn clear_bottom_bar(&mut self) {
        match self.input_mode {
            InputMode::Normal => log::warn!(
                "{}:{}: received `ClearBottomBar` signal when bottom bar is already clear",
                file!(),
                line!()
            ),
            InputMode::BottomBar {
                cursor_col: Some(_),
                ..
            } => log::warn!(
                "{}:{}: cannot clear bottom bar; it is currently in use",
                file!(),
                line!()
            ),
            _ => {
                self.input_mode = InputMode::Normal;
                self.write_bottom_bar();
                self.update_cursor();
            }
        }
    }
}
