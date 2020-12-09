//! The event loop for the view container

use crate::event::{KeyEvent, MouseEvent};
use crate::TermSize;
use crate::XInto;
use smallvec::{smallvec, SmallVec};
use std::error;
use std::fmt::{self, Display, Formatter};
use tokio::stream::{Stream, StreamExt};

/// A single singal provided to the container
pub enum Signal {
    Input(Input),
    /// A resize signal, giving the new size of the terminal
    Resize(TermSize),
}

/// A user input, through the keyboard or the mouse
///
/// When multiple keys are provided in very quick succession (e.g. when pasting from the clipboard),
/// they are collected into a list in the `Keys` enum. This uses a [`SmallVec`] so that the common
/// case (of just a single key) is handled without too much extra allocation.
#[derive(Debug)]
pub enum Input {
    Keys(SmallVec<[KeyEvent; 1]>),
    Mouse(MouseEvent),
}

#[derive(Debug)]
pub enum Error {}

/// Creates the event stream for use by [`Container::run_event_loop`]
///
/// This function is intended only for use in providing a value for [`Container::run_event_loop`]
/// at program startup, and - if called again before the first one is dropped, this will panic.
/// If this was allowed, the streams would fight for receiving each signal, meaning that each
/// version would get some subset of all of the signals.
///
/// [`Container::run_event_loop`]: super::Container::run_event_loop
pub fn make_event_stream() -> Result<impl Stream<Item = Signal>, Error> {
    // use signal_hook::iterator::Signals;

    // Create the two streams we want to merge
    //
    // NOTE: Delayed until later - `signal_hook` uses an outdated version of streams. A fix
    // appears to be in progress. See:
    //   * https://github.com/vorner/signal-hook/issues/39
    //   * https://github.com/vorner/signal-hook/pull/47
    // let unix_signals = Signals::new(&[])
    //     .map_err(Error::UnixSignalSetup)?
    //     .into_async();

    let crossterm_events = crossterm::event::EventStream::new();

    use crossterm::event::Event::{Key, Mouse, Resize};

    // TODO-ALG: We should have a different method of mapping here, so that we actually produce
    // multiple keys when they come in quick succession.
    //
    // That's moderately complicated though (considering that we're working on streams), so we're
    // leaving that for later.
    Ok(crossterm_events.filter_map(|res| {
        res.ok().map(|event| match event {
            Key(k_ev) => Signal::Input(Input::Keys(smallvec![k_ev.xinto()])),
            Mouse(m_ev) => Signal::Input(Input::Mouse(m_ev.xinto())),
            Resize(cols, rows) => Signal::Resize(TermSize::new(cols, rows)),
        })
    }))
}

impl Display for Error {
    fn fmt(&self, _f: &mut Formatter) -> fmt::Result {
        match *self {
            // Error::UnixSignalSetup(io_err) => f.write_fmt(format_args!(
            //     "could not listen for unix signals: {}",
            //     io_err
            // )),
        }
    }
}

impl error::Error for Error {}
