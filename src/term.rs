//! Utilities for interacting with the terminal

use crate::TermSize;
use crossterm::Command;
use std::sync::atomic::{AtomicU8, Ordering};
use tokio::io;

/// A wrapper around a string with to store crossterm [`Command`]s before executing them
///
/// This type provides a low-level queued interface with the terminal. Unless you're writing as
/// part of the containing module, it's probably not what you're looking for.
///
/// The standard way of using this type is with "construct-queue-execute":
/// ```ignore
/// let mut buf = CommandBuffer::new();
/// let cmd = /* Crossterm command */;
///
/// // Maybe we're executing the same command twice
/// buf.queue(cmd);
/// buf.queue(cmd);
///
/// // Take ownership, consuming the buffer:
/// buf.execute().await?;
/// ```
struct CommandBuffer {
    buf: Vec<u8>,
}

impl CommandBuffer {
    /// Initializes an empty buffer
    fn new() -> Self {
        CommandBuffer { buf: Vec::new() }
    }

    /// Queues a `crossterm` [`Command`] for later output to the terminal
    ///
    /// Queued commands can be executed by writing to stdout with the [`execute`](Self::execute)
    /// method.
    fn queue(&mut self, command: impl Command) {
        use crossterm::QueueableCommand;

        self.buf
            .queue(command)
            .expect("failed to queue terminal command");
    }

    /// Writes all of the buffer's commands to `stdout`
    async fn execute(&self) -> io::Result<()> {
        use tokio::io::AsyncWriteExt;

        let mut stdout = io::stdout();
        stdout.write_all(&self.buf).await
    }
}

// The status of the terminal - changed only by `try_prepare_terminal` and `try_cleanup_terminal`.
// Because we can't have atomic enums, we represent the different states as values here:
//   0: Unprepared - in the default state
//   1: Partially prepared - either raw mode is enabled or in the alternate screen
//   2: Fully prepared - raw mode enabled + in alternate screen
static TERM_STATUS: AtomicU8 = AtomicU8::new(0);

/// Prepares the terminal for standard use in the editor
///
/// This function does a couple things: (1) Enable [raw mode], and (2) switch to the alternate
/// screen.
///
/// Once called, this function cannot be called again until after the terminal state has been
/// cleaned by [`cleanup_terminal`]. Both of these functions are only intended to be used by
/// `main`, for initial preparation and cleanup when the program ends.
pub async fn prepare_terminal() -> io::Result<()> {
    use crossterm::terminal::EnterAlternateScreen;

    if TERM_STATUS.swap(1, Ordering::SeqCst) != 0 {
        panic!("tried to prepare terminal twice");
    }

    // We have a couple things to do here:
    //   (1) Enable raw mode, and
    //   (2) Enter the alternate screen

    crossterm::terminal::enable_raw_mode()?;

    let mut buf = CommandBuffer::new();
    buf.queue(EnterAlternateScreen);
    let res = buf.execute().await;

    if res.is_err() {
        // We already successfully enable raw mode, so if entering the alternate screen fails, we
        // should try to undo that. We'll ignore any errors.
        let _ = crossterm::terminal::disable_raw_mode();
    } else {
        TERM_STATUS.store(2, Ordering::SeqCst);
    }

    res
}

/// Cleans up the terminal from the state made by [`prepare_terminal`]
///
/// This function can only be called after [`prepare_terminal`], and will panic if this is not the
/// case.
pub async fn cleanup_terminal() -> io::Result<()> {
    use crossterm::terminal::LeaveAlternateScreen;

    // We have a couple things to do here:
    //  (1) leave the alternate screen, and
    //  (2) disable raw mode

    let mut buf = CommandBuffer::new();
    buf.queue(LeaveAlternateScreen);
    buf.execute().await?;

    crossterm::terminal::disable_raw_mode()
}

pub fn get_size() -> io::Result<TermSize> {
    crossterm::terminal::size().map(TermSize::from_pair)
}
