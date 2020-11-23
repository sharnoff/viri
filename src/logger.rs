//! Core definitions for logging
//!
//! This file sets up the logger that we use in the rest of the crate, along with the tools that
//! keep it in order.
//!
//! This module doesn't provide much that can be used during the runtime of the program, instead
//! merely setting it up to work with the standard logging macros.

use crate::macros::{init, require_initialized};
use arc_swap::{ArcSwapAny, ArcSwapOption};
use lazy_static::lazy_static;
use log::{Metadata, Record};
use std::sync::Arc;
use tokio::fs::File;
use tokio::io::{AsyncWriteExt, Error as IoError};
use tokio::stream::{Stream, StreamExt};
use tokio::sync::{mpsc, watch, Mutex};
use tokio::task::yield_now;

// The default log level
const DEFAULT_LEVEL: log::LevelFilter = log::LevelFilter::Info;

lazy_static! {
    // The file that we write our logs to
    static ref LOG_FILE: ArcSwapOption<Mutex<File>> = ArcSwapAny::empty();

    // A channel that we send all log lines through in order to make logging non-blocking
    //
    // The init function ensures that this gets initialized
    static ref LOG_SENDER: ArcSwapOption<mpsc::UnboundedSender<String>> = ArcSwapAny::empty();

    // A stored receiver for listening to logging-related IO errors.
    //
    // Because `watch` channels require an initial value, we have an `Option< Error >` instead of
    // just the bare error itself.
    static ref IO_ERROR: ArcSwapOption<watch::Receiver<Option<Arc<IoError>>>> = ArcSwapAny::empty();
}

// Initialize the logging utilities
//
// The primary things we do here are (1) setting up the logger (from the `log` crate), and
// (2) starting a background async task to allow logging to be done from synchronous code
//
// This second task also forwards any errors to a separate watch channel, `IO_ERROR`. Receivers are
// given by the `io_errors` function.
init! {
    static LOGGER: DummyLogger = DummyLogger;

    // We require the runtime to be initialized, because we rely on async io to do logging, which
    // can be considered available once this module has been initialized.
    require_initialized!(crate::runtime);
    log::set_logger(&LOGGER).expect("failed to set the global logger");
    log::set_max_level(DEFAULT_LEVEL);

    // The channel for transmitting log messages
    let (tx, mut rx) = mpsc::unbounded_channel();
    LOG_SENDER.swap(Some(Arc::new(tx)));

    // And the channel(s) for transmitting io errors resulting from writing the messages
    let (io_tx, io_rx) = watch::channel(None);
    IO_ERROR.swap(Some(Arc::new(io_rx)));

    // Start a background task to write logs to the file
    crate::runtime::spawn(async move {
        for log_msg in rx.next().await {
            // For every string we want to log, we'll write to the log file
            //
            // We need to reload the log file on each write because it might have been changed
            // between the last logging and now.
            if let Some(file) = LOG_FILE.load_full() {
                let mut file = file.lock().await;
                if let Err(e) = file.write(log_msg.as_ref()).await {
                    // If there was an error, we'll send a message to anyone who cares that there
                    // was an error from trying to log a message

                    io_tx.send(Some(Arc::new(e)))
                        .expect("failed to report logging IO failure from writing");
                } else {
                    // If we didn't run into an error from writing, we'll try to flush
                    if let Err(e) = file.flush().await {
                        // Same error handling as from earlier
                        io_tx.send(Some(Arc::new(e)))
                            .expect("failed to report logging IO failure from flushing");
                    }
                }
            }
        }
    });
}

/// Sets the application-wide logger to the given file handle, returning the
/// old one, if it was present.
pub async fn set_file(file: File) -> Option<File> {
    let mut previous: Arc<Mutex<File>> = LOG_FILE.swap(Some(Arc::new(Mutex::new(file))))?;

    // Spin lock :(
    loop {
        match Arc::try_unwrap(previous) {
            Ok(mutex) => return Some(mutex.into_inner()),
            Err(arc) => previous = arc,
        }

        yield_now().await;
    }
}

/// Sets the application-wide logging level, returning the previous one
///
/// This is generally only intended to be run at startup, but nothing will stop you from doing this
/// at runtime.
pub fn set_level(level: impl AsRef<log::LevelFilter>) -> log::LevelFilter {
    let previous = log::max_level();
    log::set_max_level(*level.as_ref());
    previous
}

/// Utility function for grabbing the log level from a string.
///
/// The string should always be one of:
///  * `"Trace"`
///  * `"Debug"`
///  * `"Info"`
///  * `"Warn"`
///  * `"Error"`
///  * `"Off"`
/// The only place this function is called is in `main()`, where the argument
/// has already been validated by clap.
pub fn level_filter_from_str(s: &str) -> log::LevelFilter {
    match s {
        "Trace" => log::LevelFilter::Trace,
        "Debug" => log::LevelFilter::Debug,
        "Info" => log::LevelFilter::Info,
        "Warn" => log::LevelFilter::Warn,
        "Error" => log::LevelFilter::Error,
        "Off" => log::LevelFilter::Off,
        _ => panic!("Unexpected log level string"),
    }
}

/// Returns a listener for any IO errors that occur from logging
///
/// This function is primarily provided for diagnostics information when things go south, so that
/// the user might at least have *some* indication of what is going wrong. As such, it is *not*
/// guaranteed to return every error that's encountered - it is only guaranteed to get *at least*
/// one error, if such an error occurs.
pub fn io_errors() -> impl Stream<Item = Arc<IoError>> {
    require_initialized!(crate::runtime);

    let mut errors_receiver = watch::Receiver::clone(
        &IO_ERROR
            .load()
            .as_ref()
            .expect("logger has not been initialized"),
    );

    let (tx, rx) = mpsc::channel(0);
    crate::runtime::spawn(async move {
        while let Ok(()) = errors_receiver.changed().await {
            let cloned: Option<Arc<IoError>> = (*errors_receiver.borrow()).clone();
            if let Some(e) = cloned {
                // After passing the value along, if they're no longer using this channel, we can
                // be done here.
                if tx.send(e).await.is_err() {
                    return;
                }
            }
        }
    });

    rx
}

/// The public-facing logger.
///
/// This only actually serves to implement the required interface, connecting the logging macros to
/// an internal, asynchronous file writer.
struct DummyLogger;

impl log::Log for DummyLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= log::max_level()
    }

    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

        let write_str = format!("{}\n", record.args());
        LOG_SENDER
            .load()
            .as_ref()
            .expect("logging has not yet been initialized")
            .send(write_str)
            .expect("failed to connect to logging task");
    }

    // We don't do anything on requests to flush, because that's handled for us in the file-writing
    // routine
    fn flush(&self) {}
}
