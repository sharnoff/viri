use crate::event::{KeyEvent, MouseEvent};
use crate::mode::Direction;
use crate::runtime::{self as rt, Painter, TermSize};
use crate::utils::{self, OpaqueOption};
use crate::views::split::{Horiz, Vert};
use crate::views::{self, ConcreteView, RefreshKind, ViewKind};
use crossterm::{cursor, style, QueueableCommand};
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::convert::TryInto;
use std::fmt::{self, Debug, Formatter};
use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, Ordering::SeqCst};
use std::sync::Mutex;

/// The primary interface between the runtime and the tree of `View`s
///
/// This type takes runtime signals as input and feeds them to the tree of [`View`]s, before taking
/// the resulting view signal and returning a runtime signal, if any was generating. This is done
/// through the [`handle_rt_event`] method.
///
/// [`View`]: ../views/trait.View.html
/// [`handle_rt_event`]: #method.handle_rt_event
pub struct Container {
    /// The displayed view. We box it so that any type of view may be used. This value will only
    /// ever temporarily be `None` - it can be assumed to be `Some(_)` everywhere outside the
    /// places it is obviously not.
    inner: Option<Box<dyn ConcreteView>>,

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

    fn inner(&self) -> &Box<dyn ConcreteView> {
        self.inner.as_ref().unwrap()
    }

    fn inner_mut(&mut self) -> &mut Box<dyn ConcreteView> {
        self.inner.as_mut().unwrap()
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
                let painter = Painter::global(self.size);
                if let Ok(offset) = self.bottom_offset().try_into() {
                    if let Some(mut p) = painter.trim_bot(offset) {
                        self.inner().refresh_cursor(&mut p);
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
                let width = self.size.width;
                let bot_str = self.inner_mut().construct_bottom_text(width);

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

                self.inner.as_mut().unwrap().try_handle(signal)
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

        // If there's been a change in runtime parameters that wasn't handled by
        // `handle_view_output_exits`, we'll do that now.
        if CHANGED_RUNTIME_VALS.swap(false, SeqCst) {
            self.handle_refresh(RefreshKind::Full);
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
            inner: Some(inner),
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
            ClearBottomBar, Close, LeaveBottomBar, NeedsRefresh, NoSuchCmd, Open, Replace,
            SaveBottomBar, SetBottomBar, ShiftFocus, WaitingForMore,
        };

        match signal {
            ShiftFocus(_, _) => (),
            NeedsRefresh(mut kind) => {
                if CHANGED_RUNTIME_VALS.swap(false, SeqCst) {
                    kind = RefreshKind::Full;
                }
                self.handle_refresh(kind)
            }
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

            Replace(new_view) => {
                self.inner = Some(new_view);
                self.handle_refresh(RefreshKind::Full);
            }

            Open(direction, new_view) => self.open_new(direction, new_view),

            // If the outer-most view closes, we exit.
            Close => return true,
        }

        false
    }

    fn handle_refresh(&mut self, kind: RefreshKind) {
        use InputMode::BottomBar;
        use RefreshKind::{BottomText, Cursor, Full, Inner};

        let global_painter = Painter::global(self.size);
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
                self.inner_mut().refresh(local.as_mut().unwrap());
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

    fn open_new(&mut self, direction: Direction, new_inner: Box<dyn ConcreteView>) {
        use Direction::{Down, Left, Right, Up};

        let old_inner = self.inner.take().unwrap();

        let inner = match direction {
            Up => Box::new(Horiz::construct(vec![new_inner, old_inner])) as Box<dyn ConcreteView>,
            Down => Box::new(Horiz::construct(vec![old_inner, new_inner])),
            Left => Box::new(Vert::construct(vec![new_inner, old_inner])),
            Right => Box::new(Vert::construct(vec![old_inner, new_inner])),
        };

        self.inner = Some(inner);
        self.handle_refresh(RefreshKind::Full);
    }
}

////////////////////////////////////////////////////////////////////////////////
// Runtime parameters                                                         //
// ------------------                                                         //
// This section gives all of the types, statics, and functions for handling   //
// the runtime parameters given by the container. These are all detailed      //
// individually with the documentation on each item.                          //
////////////////////////////////////////////////////////////////////////////////

lazy_static! {
    /// The runtime parameters provided by the `set` colon command
    ///
    /// This is exposed internally through the [`set_runtime_value`] function, and simply provides
    /// a map of string keys (e.g. `color_line_numbers`) to values (e.g. `yes` or `yellow`).
    ///
    /// All runtime parameters *must* have an entry here. For more information, see
    /// [`RTParamInfo`].
    ///
    /// [`set_runtime_value`]: fn.set_runtime_value.html
    /// [`RTParamInfo`]: struct.RTParamInfo.html
    static ref RUNTIME_PARAMS: Mutex<HashMap<&'static str, RTParamInfo>> = Mutex::new(HashMap::new());
}

/// A marker to track whether any runtime values have been updated
///
/// This is used by the container instance to force redrawing of all views whenever there's been a
/// change in any runtime parameters.
static CHANGED_RUNTIME_VALS: AtomicBool = AtomicBool::new(false);

/// Information for any particular runtime parameter
///
/// Every parameter in use will have a corresponding entry to indicate that it *is* indeed in use.
/// Note that this does not include the actual name of the parameter; this is given by the key in
/// the containing map.
#[derive(Clone, Default)]
struct RTParamInfo {
    /// The value of the runtime parameter, if it has been set
    value: Option<String>,

    /// A validator function for determining whether the assigned value is valid.
    ///
    /// This value need not be present, in which case this instance might only serve to indicate
    /// that the parameter exists.
    is_valid: Option<fn(&str) -> Result<(), String>>,
}

/// Sets a runtime parameter, returning an error if it is unknown or invalid
///
/// Retrieving these values can be done via the [`get_runtime_param`] function.
///
/// Runtime parameters are global to the entire application, and so a successful assignment here
/// will cause a full refresh of all views.
///
/// Errors may be returned under two cases: (1) if the key is unknown - i.e. if it has not been
/// marked as used by [`register_rt_param`] - or (2) if the value is invalid, as given by a
/// validator function provided by [`set_rt_param_validator`].
///
/// [`get_rt_param`]: fn.get_rt_param.html
/// [`register_rt_param`]: fn.requires_rt_param.html
/// [`set_rt_param_validator`]: fn.set_rt_param_validator.html
pub fn set_runtime_param(param: &str, val: String) -> Result<(), String> {
    let mut guard = RUNTIME_PARAMS.lock().unwrap();

    let mut entry = match guard.get_mut(param) {
        None => return Err(format!("Unknown runtime parameter '{}'", param)),
        Some(e) => e,
    };

    // If there's a validator, we'll check that the value is okay
    if let Some(validator) = entry.is_valid.as_ref() {
        validator(&val)?;
    }

    entry.value = Some(val);
    CHANGED_RUNTIME_VALS.store(false, SeqCst);
    Ok(())
}

/// Gets the value of the given runtime parameter, returning `None` if it has not been set
///
/// This requires that the parameter already be registered by [`register_rt_param`]; this function
/// will panic if this is not the case. Additionally, if a validator function has been set by
/// [`set_rt_param_validator`], any returned value will be guaranteed to satisfy the validator.
///
/// [`register_rt_param`]: fn.register_rt_param.html
/// [`set_rt_param_validator`]: fn.set_rt_param_validator.html
pub fn get_runtime_param(param: &str) -> Option<String> {
    let guard = RUNTIME_PARAMS.lock().unwrap();

    match guard.get(param) {
        None => {
            // Because this error is likely to happen at runtime, we intentionally don't drop the
            // guard, because we'd rather poison it and cause whole-program shutdown.
            panic!(concat!(
                "fatal internal error: attempted to get value of unregistered runtime param\n",
                "help: use `container::register_rt_param` to make this parameter known",
            ));
        }
        Some(entry) => entry.value.clone(),
    }
}

/// Registers the runtime parameter as used in some form
///
/// This *must* be called for each parameter that may be used during runtime; if it is not,
/// attempting to retrieve the value will panic.
///
/// This function (unlike [`set_rt_param_validator`]) may be called multiple times for the same
/// parameter name.
pub fn register_rt_param(param: &'static str) {
    let mut guard = RUNTIME_PARAMS.lock().unwrap();

    if !guard.contains_key(param) {
        guard.insert(param, RTParamInfo::default());
    }
}

/// Sets the validation function for a runtime parameter
///
/// This may be used to prevent bad values being given for certain parameters, for example ensuring
/// that tabstops must be a positive integer. The given function should return an error message to
/// give to the user.
///
/// ## Semantics
///
/// The validator for the same parameter must not be set multiple times; if this is attempted, this
/// function will panic. Additionally, [`register_rt_param`] must be called for the parameter
/// before this function.
///
/// If a validator is added to a parameter after its value is set to something marked as invalid,
/// then a warning will be emitted and the original value returned. This is given by the first
/// value in the error variant of the return. The second element in the tuple gives the resulting
/// error message from the validator.
pub fn set_rt_param_validator(
    param: &str,
    is_valid: fn(&str) -> Result<(), String>,
) -> Result<(), (String, String)> {
    let mut guard = RUNTIME_PARAMS.lock().unwrap();

    match guard.get_mut(param) {
        None => panic!(concat!(
            "fatal internal error: attempted to set validator of unregistered runtime param\n",
            "help: use `container::register_rt_param` to make this parameter known",
        )),
        Some(entry) if entry.is_valid.is_some() => panic!(
            "fatal internal error: attempted to twice set validator of runtime param '{}'",
            param
        ),
        Some(mut entry) => {
            entry.is_valid = Some(is_valid);
            match entry.value.as_ref().map(|v| (v, is_valid(&v))) {
                None | Some((_, Ok(_))) => Ok(()),
                Some((v, Err(msg))) => {
                    let res = Err((v.clone(), msg));
                    entry.value = None;
                    res
                }
            }
        }
    }
}

impl Debug for RTParamInfo {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        fmt.debug_struct("RTParamInfo")
            .field("value", &self.value)
            .field("is_valid", &OpaqueOption::from(&self.is_valid))
            .finish()
    }
}
