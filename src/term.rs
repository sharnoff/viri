//! Utilities for interacting with the terminal

use crossterm::Command;
use std::io as stdio;
use tokio::io;

/// A wrapper around a string with to store crossterm [`Command`]s before executing them
#[must_use = "Commands queued to a buffer do nothing without flushing"]
struct Buffer {
    buf: Vec<u8>,
}

impl Buffer {
    /// Initializes an empty buffer
    fn new() -> Self {
        Buffer { buf: Vec::new() }
    }

    /// Queues a `crossterm` [`Command`] for later
    fn queue(&mut self, command: impl Command) {
        use crossterm::QueueableCommand;

        self.buf
            .queue(command)
            .expect("failed to queue terminal command");
    }

    /// Consumes the buffer, writing all of the commands to `stdout`
    async fn flush_stdout(self) -> io::Result<()> {
        use tokio::io::AsyncWriteExt;

        let mut stdout = io::stdout();
        stdout.write_all(&self.buf).await
    }
}

pub async fn try_prepare_terminal() -> io::Result<()> {
    use crossterm::terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen};
    use crossterm::ErrorKind;

    // We have a couple things to do here:
    //   (1) Enable raw mode, and
    //   (2) Enter the alternate screen

    enable_raw_mode()
        .map_err(|e| match e {
            ErrorKind::IoError(e) => e,
            _ => panic!("unexpected error kind from enabling raw mode: {}", e),
        })
        .map_err(stdio_err_to_tokio)?;

    let mut buf = Buffer::new();
    buf.queue(EnterAlternateScreen);
    let res = buf.flush_stdout().await;

    if res.is_err() {
        // We already successfully enable raw mode, so if entering the alternate screen fails, we
        // should try to undo that. We'll ignore any errors.
        let _ = disable_raw_mode();
    }

    res
}

pub async fn try_cleanup_terminal() -> io::Result<()> {
    use crossterm::terminal::{disable_raw_mode, LeaveAlternateScreen};
    use crossterm::ErrorKind;

    // We have a couple things to do here:
    //  (1) leave the alternate screen, and
    //  (2) disable raw mode

    let mut buf = Buffer::new();
    buf.queue(LeaveAlternateScreen);
    buf.flush_stdout().await?;

    disable_raw_mode()
        .map_err(|e| match e {
            ErrorKind::IoError(e) => e,
            _ => panic!("unexpected error kind from disabling raw mode: {}", e),
        })
        .map_err(stdio_err_to_tokio)
}

fn stdio_err_to_tokio(err: stdio::Error) -> io::Error {
    // If the error was a standard OS error, we'll simply return it
    if let Some(err_code) = err.raw_os_error() {
        return io::Error::from_raw_os_error(err_code);
    }

    // Otherwise, we re-create the error:
    if err.get_ref().is_none() {
        panic!("IO error has unexpected value: {}", err);
    }

    let kind = err.kind();
    let inner = err.into_inner().unwrap();
    io::Error::new(kind, inner)
}
