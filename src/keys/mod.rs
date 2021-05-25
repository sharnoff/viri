//! High-level interface for keybindings and everything they control

use crate::event::KeyEvent;
use smallvec::SmallVec;
use std::marker::PhantomData;
use std::sync::Arc;

mod combinators;
mod modifier_set;
mod sources;

#[cfg(test)]
mod tests;

pub use combinators::*;
pub use modifier_set::ModifierSet;
pub use sources::*;

/// The keybindings for a collection of modes
pub struct ModeSet<Cmd> {
    modes: Vec<ModeBindings<Cmd>>,
    key_buf: Vec<KeyEvent>,
    current_mode: ModeId,
    // If, the last time `ModeSet::output` was called, we *did* have an output, but we could have
    // taken more, this stores that output for later
    last_output: Option<Cmd>,
    // True if the last value from `ModeSet::output` was a conflict with `could_take_more = true`
    last_was_conflict: bool,
}

/// The keybindings for a particular mode
pub struct ModeBindings<Cmd> {
    parser: Arc<dyn KeyParser<Output = Cmd>>,
}

/// A parser taking key events as input and possibly produces an `Output`
#[doc(notable_trait)] // @def "KeyParser notable_trait" v0
pub trait KeyParser {
    /// The type of a successful parse
    type Output;

    /// Attempts to parse the value, drawing from the [`KeyStream`] as needed
    fn parse(&self, keys: &mut KeyStream) -> ParseResult<Self::Output>;
}

/// The result of parsing a value, used by the [`KeyParser`] trait
#[derive(Copy, Clone, Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum ParseResult<T> {
    /// A successful value was made -- `could_take_more` indicates whether more input *could*
    /// provide another output instead
    Success { val: T, could_take_more: bool },

    /// Two or more parses were successful -- `could_take_more` indicates whether more input
    /// *could* provide another output instead
    Conflict { could_take_more: bool },

    /// There were no possible successful parses, and more input wouldn't change this
    Fail,

    /// There wasn't enough input to construct a successful parse
    NeedsMore,
}

impl<T> ParseResult<T> {
    /// Maps a successful result by the given function
    #[rustfmt::skip]
    pub fn map<S>(self, func: impl FnOnce(T) -> S) -> ParseResult<S> {
        use ParseResult::*;

        match self {
            Success { val, could_take_more } => {
                Success { val: func(val), could_take_more }
            },
            Conflict { could_take_more } => Conflict { could_take_more },
            Fail => Fail,
            NeedsMore => NeedsMore,
        }
    }

    /// Unwraps the `ParseResult` into the success value, panicking if it is not successful
    #[track_caller]
    #[rustfmt::skip]
    pub fn unwrap(self) -> T {
        let panic_msg = match self {
            ParseResult::Success { val, .. } => return val,
            ParseResult::Conflict { could_take_more } => {
                format!(
                    "Conflict {{ could_take_more: {:?} }}",
                    could_take_more
                )
            }
            ParseResult::Fail => "Fail".to_owned(),
            ParseResult::NeedsMore => "NeedsMore".to_owned(),
        };

        panic!("called `ParseResult::unwrap` on {}", panic_msg)
    }

    /// Returns true if the result is the `Success` variant
    pub fn is_success(&self) -> bool {
        matches!(self, ParseResult::Success { .. })
    }
}

/// A unique identifier for particular modes
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModeId(pub usize);

/// Marker trait for commands that could switch the current mode
pub trait ModeCommand {
    /// If this particular command is an instruction to switch the modes, return the ID of the mode
    /// to switch to
    fn as_switch(&self) -> Option<ModeId>;
}

/// The output type from parsing keybindings with [`ModeSet::output`]
pub enum Output<T> {
    Success(ModeId, T),
    NoMatchingBinding,
    ConflictingBindings,
}

impl<Cmd: ModeCommand> ModeSet<Cmd> {
    /// Creates a new `ModeSet` with the given bindings for each mode
    pub fn new(starting_mode: ModeId, modes: Vec<ModeBindings<Cmd>>) -> Self {
        ModeSet {
            modes,
            key_buf: Vec::new(),
            current_mode: starting_mode,
            last_output: None,
            last_was_conflict: false,
        }
    }

    /// Extracts the output from a particular set of keybindings
    ///
    /// The returned vector will be empty if and only if
    #[rustfmt::skip]
    pub fn output(&mut self, new_keys: &[KeyEvent]) -> SmallVec<[Output<Cmd>; 1]> {
        self.last_output = None;
        self.last_was_conflict = false;

        self.key_buf.extend_from_slice(new_keys);

        let mut outs = SmallVec::new();

        loop {
            let mode = &self.modes[self.current_mode.0];
            let mut stream = KeyStream::new(&self.key_buf);

            let parse_result = mode.parser.parse(&mut stream);
            let stream_pos = stream.pos;

            match parse_result {
                ParseResult::Success { val, could_take_more } => {
                    // Check that if we could take more, this parse used up all of the keys
                    assert!(!could_take_more || stream_pos == self.key_buf.len());

                    if !could_take_more {
                        let mode = self.current_mode;
                        self.drop_first(stream_pos);
                        self.maybe_switch_mode(&val);
                        outs.push(Output::Success(mode, val));
                    } else {
                        self.last_output = Some(val);
                        break;
                    }
                }
                ParseResult::Conflict { could_take_more } => {
                    assert!(!could_take_more || stream_pos == self.key_buf.len());

                    if !could_take_more {
                        outs.push(Output::ConflictingBindings);
                        self.drop_first(stream_pos);
                    } else {
                        self.last_was_conflict = true;
                    }
                },
                ParseResult::Fail => {
                    outs.push(Output::NoMatchingBinding);
                    self.drop_first(stream_pos);
                }
                // We stop the loop when there's clearly nothing more that can be done
                ParseResult::NeedsMore => break,
            }
        }

        outs
    }

    /// If the last item in the last call to `output` was `Output::ConflictingBindings`, this
    /// method attempts to resolve that conflict, if possible
    pub fn resolve_conflict(&mut self) -> Option<Cmd> {
        if let Some(out) = self.last_output.take() {
            // We drop the entire length of the key buffer, because a conflict only gets stored if
            // it was *exactly* the length of the key buffer.
            self.drop_first(self.key_buf.len());
            self.maybe_switch_mode(&out);
            Some(out)
        } else if self.last_was_conflict {
            self.drop_first(self.key_buf.len());
            self.last_was_conflict = false;
            None
        } else {
            None
        }
    }

    /// Drops the first `len` key events from the internal buffer
    fn drop_first(&mut self, len: usize) {
        self.key_buf.drain(..len);
    }

    /// Checks if we need to switch modes, depending upon what the command dictates
    fn maybe_switch_mode(&mut self, out: &Cmd) {
        if let Some(new_mode) = out.as_switch() {
            self.current_mode = new_mode;
        }
    }
}

impl<Cmd> ModeBindings<Cmd> {
    /// Creates a new `ModeBindings` from the parser
    pub fn new(parser: impl 'static + KeyParser<Output = Cmd>) -> ModeBindings<Cmd> {
        ModeBindings {
            parser: Arc::new(parser),
        }
    }
}

/// A stream of keys to parse
///
/// Primary usage of this type is
///
/// Cloning is cheap -- we could have provided an implementation of `Copy`, but mutable methods on
/// `Copy` types tend to run into trouble. Alternatively, the [`fork`](Self::fork) method is provided with the
/// same behavior.
#[derive(Clone)]
pub struct KeyStream<'a> {
    keys: &'a [KeyEvent],
    /// The current position in the sequence
    pos: usize,
}

impl<'a> KeyStream<'a> {
    /// Creates a new `KeyStream` from the slice of keys
    pub fn new(keys: &'a [KeyEvent]) -> Self {
        KeyStream { keys, pos: 0 }
    }

    /// Gets the next key from the stream, bumping the position up by one
    pub fn next(&mut self) -> Option<KeyEvent> {
        let key = self.keys.get(self.pos).cloned();
        if key.is_some() {
            self.pos += 1;
        }

        key
    }

    /// Gets the next key from the stream without bumping the positoin
    pub fn peek(&self) -> Option<KeyEvent> {
        self.keys.get(self.pos).cloned()
    }

    /// Returns the current state of the `KeyStream`, which can be restored with
    /// [`KeyStream::restore`]
    ///
    /// This is typically used for speculative parsing, as an alternative to some kind of forking.
    /// The state is invariant over the lifetime of the stream to avoid accidentally mismatching
    /// them.
    ///
    /// Please note that when using the state for speculative parsing, you *should* always return
    /// the stream to a state corresponding to what was actually used -- this may mean storing both
    /// the state before and after parsing. Failure to properly est the state may result in
    /// unexpected behavior.
    pub fn state(&self) -> KeyStreamState<'a> {
        KeyStreamState {
            pos: self.pos,
            mark_invariant: PhantomData,
        }
    }

    /// Restores the `KeyStream` to the previous state, given by [`KeyStream::state`]
    pub fn restore(&mut self, state: KeyStreamState<'a>) {
        assert!(state.pos <= self.keys.len());
        self.pos = state.pos;
    }
}

/// The state of a `KeyStream`, invariant over the stream's lifetime
///
/// This is produced by the [`KeyStream::state`] method and can be used by [`KeyStream::restore`]
/// to return the stream to its state at the time this value was produced.
///
/// The lifetime of the state exists only to tie it to the originating stream. As such, it is
/// invariant over that lifetime.
///
/// ## Ordering
///
/// States are considered "greater" than another if the key stream in that state had consumed more
/// input. This can be useful in determining the shortest or longest match among a set -- notably
/// in the implementation of [`KeyParser`] for [`Any`].
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(test, derive(Debug))]
pub struct KeyStreamState<'a> {
    pos: usize,
    // &mut T is invariant over T, so this becomes invariant over 'a. The outer &'a mut _ doesn't
    // "expand" the variance.
    mark_invariant: PhantomData<&'a mut &'a ()>,
}
