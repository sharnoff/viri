//! Utilities for interacting with the terminal

use crate::TermSize;
use std::io;
use std::sync::atomic::{AtomicU8, Ordering};

// The status of the terminal - changed only by `try_prepare_terminal` and `try_cleanup_terminal`.
// Because we can't have atomic enums, we represent the different states as values here:
//   0: Unprepared - in the default state
//   1: Partially prepared - either raw mode is enabled or in the alternate screen
//   2: Fully prepared - raw mode enabled + in alternate screen
static TERM_STATUS: AtomicU8 = AtomicU8::new(0);

fn ct_to_io(err: crossterm::ErrorKind) -> io::Error {
    use crossterm::ErrorKind::IoError;
    use io::ErrorKind::Other;

    match err {
        IoError(e) => e,
        e @ _ => io::Error::new(Other, Box::new(e)),
    }
}

/// Prepares the terminal for standard use in the editor
///
/// This function does a couple things: (1) Enable [raw mode], and (2) switch to the alternate
/// screen.
///
/// Once called, this function cannot be called again until after the terminal state has been
/// cleaned by [`cleanup_terminal`]. Both of these functions are only intended to be used by
/// `main`, for initial preparation and cleanup when the program ends.
pub fn prepare_terminal() -> io::Result<()> {
    use crossterm::terminal::EnterAlternateScreen;
    use crossterm::{ErrorKind, ExecutableCommand};

    if TERM_STATUS.swap(1, Ordering::SeqCst) != 0 {
        panic!("tried to prepare terminal twice");
    }

    // We have a couple things to do here:
    //   (1) Enable raw mode, and
    //   (2) Enter the alternate screen

    crossterm::terminal::enable_raw_mode().map_err(ct_to_io)?;

    match io::stdout().execute(EnterAlternateScreen) {
        Ok(_) => {
            TERM_STATUS.store(2, Ordering::SeqCst);
            Ok(())
        }
        Err(ErrorKind::IoError(e)) => {
            // We already successfully enabled raw mode, so if entering the alternate screen fails,
            // we should try to undo that. We'll ignore any errors because we already have one.
            let _ = crossterm::terminal::disable_raw_mode();
            Err(e)
        }
        Err(_) => unreachable!(),
    }
}

/// Cleans up the terminal from the state made by [`prepare_terminal`]
///
/// This function can only be called after [`prepare_terminal`], and will panic if this is not the
/// case.
pub fn cleanup_terminal() -> io::Result<()> {
    use crossterm::terminal::LeaveAlternateScreen;
    use crossterm::ExecutableCommand;

    // We have a couple things to do here:
    //  (1) leave the alternate screen, and
    //  (2) disable raw mode

    io::stdout()
        .execute(LeaveAlternateScreen)
        .map_err(ct_to_io)?;
    crossterm::terminal::disable_raw_mode().map_err(ct_to_io)
}

pub fn get_size() -> io::Result<TermSize> {
    crossterm::terminal::size()
        .map(TermSize::from_pair)
        .map_err(ct_to_io)
}
