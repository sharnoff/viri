/// The types and functions associated with the running of the editor
///
/// These are largely concerned with the events loop and the internal handlers (e.g. the panic
/// handler).
use std::io::{self, stderr};
use std::panic::{catch_unwind, resume_unwind, UnwindSafe};
use std::process;

use serde::{Deserialize, Serialize};

use crate::event::{KeyEvent, MouseEvent};

mod painter;
pub mod panic;

pub use painter::Painter;
pub use panic::add_exit_msg;

use panic::PanicWriter;

#[derive(Clone, Debug)]
pub enum Signal {
    Exit,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum UserEvent {
    Key(KeyEvent),
    Mouse(MouseEvent),
}

#[derive(Clone, Debug)]
pub enum Event {
    User(UserEvent),
    Resize(TermSize),
    // SigKill,
    //
    // TODO: Add signal handling for various OS signals.
    // -- use `signal_hook::iterator::Signals::new()`
}

#[derive(Copy, Clone, Debug)]
pub struct EventsLoop;

impl Iterator for EventsLoop {
    type Item = Event;

    fn next(&mut self) -> Option<Event> {
        use crossterm::event::Event as CTEvent;

        let event = match crossterm::event::read().unwrap() {
            CTEvent::Key(k) => Event::User(UserEvent::Key(k.into())),
            CTEvent::Mouse(m) => Event::User(UserEvent::Mouse(m.into())),
            CTEvent::Resize(width, height) => Event::Resize((width, height).into()),
        };

        Some(event)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct TermSize {
    pub width: u16,
    pub height: u16,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct TermCoord {
    pub row: u16,
    pub col: u16,
}

impl From<(u16, u16)> for TermSize {
    fn from(tuple: (u16, u16)) -> Self {
        Self {
            width: tuple.0,
            height: tuple.1,
        }
    }
}

impl From<(u16, u16)> for TermCoord {
    fn from(tuple: (u16, u16)) -> Self {
        Self {
            row: tuple.0,
            col: tuple.1,
        }
    }
}

impl std::ops::Add for TermCoord {
    type Output = Self;

    fn add(mut self, other: TermCoord) -> TermCoord {
        self.row += other.row;
        self.col += other.col;
        self
    }
}

/// Immediately ends the program, cleans up the terminal, and prints whatever exit messages have
/// been provided to the panic writer.
///
/// This may be useful in cases like `ViewContainer` initialization - which doesn't have a provided
/// method for handling failure, but may nonetheless encounter some form of irrecoverable error.
/// This will not handle anything else (like syncing files, for example), so use with caution.
///
/// To add a message to the exit, use `add_exit_msg` before calling this function.
pub fn hard_exit(code: i32) -> ! {
    cleanup(stderr());
    process::exit(code)
}

fn enter_alternate_screen() -> crossterm::Result<()> {
    use crossterm::terminal::EnterAlternateScreen;
    use crossterm::ExecutableCommand;
    io::stdout().execute(EnterAlternateScreen)?;

    Ok(())
}

fn leave_alternate_screen() -> crossterm::Result<()> {
    use crossterm::terminal::LeaveAlternateScreen;
    use crossterm::ExecutableCommand;
    io::stdout().execute(LeaveAlternateScreen)?;

    Ok(())
}

pub fn run<F: UnwindSafe + FnMut()>(mut func: F) {
    panic::set_hook();

    let res = catch_unwind(move || {
        use crossterm::terminal;

        log::trace!("Enabling raw mode");
        terminal::enable_raw_mode().unwrap_or_else(|e| panic!("Failed to enable raw mode: {}", e));
        log::trace!("Entering alternate screen");
        enter_alternate_screen()
            .unwrap_or_else(|e| panic!("Failed to enter alternate screen: {}", e));

        func()
    });

    cleanup(stderr());

    if let Err(e) = res {
        resume_unwind(e);
    }
}

/// Returns the size of the terminal. This really should only be called at
/// program initialization, as all further resizes will be events that can then
/// be handled.
pub fn get_size() -> crossterm::Result<TermSize> {
    crossterm::terminal::size().map(TermSize::from)
}

fn cleanup<W: io::Write>(writer: W) {
    use crossterm::terminal;
    drop(leave_alternate_screen());
    drop(terminal::disable_raw_mode());
    PanicWriter::write_all(writer);
}
