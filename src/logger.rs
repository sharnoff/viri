/// Where the logger lives
///
/// This file sets up the logger that we use in the rest of the crate, along
/// with the tools that keep it in order
use std::fs::File;
use std::io::Write;
use std::mem;
use std::sync::{Arc, Mutex};

use crate::prelude::*;
use lazy_static::lazy_static;
use log::{Metadata, Record};

lazy_static! {
    /// The global logger
    ///
    /// This lock is provided both to sync writes to whatever log file we're using,
    /// AND to allow access to changing the logger at runtime.
    static ref LOG: Arc<Mutex<Option<File>>> = Arc::new(Mutex::new(None));
}

const DEFAULT_LEVEL: log::LevelFilter = log::LevelFilter::Info;

/// Initializes the logging utilities, particularly setting the global logger
/// to be the one given here.
///
/// This should only ever be called once. It will panic if that condition is
/// not met.
pub fn init() {
    log::set_logger(&LOGGER).unwrap();
    log::set_max_level(DEFAULT_LEVEL);
}

/// Sets the application-wide logger to the given file handle, returning the
/// old one, if it was present.
pub fn set_file(file: File) -> Option<File> {
    let mut guard = LOG.lock().unwrap();
    mem::replace(&mut guard, Some(file))
}

/// Sets the application-wide logging level, returning the previous one
pub fn set_level(level: log::LevelFilter) -> log::LevelFilter {
    let previous = log::max_level();
    log::set_max_level(level);
    previous
}

/// Returns whether there there is currently a logger in use
pub fn logging() -> bool {
    LOG.lock().unwrap().is_some()
}

/// Returns the curent level of the logger
pub fn level() -> log::LevelFilter {
    log::max_level()
}

/// Utility function for grabbing the log level from a string.
///
/// The string should always be one of:
///   "Trace", "Debug", "Info", "Warn", "Error", "Off"
/// The only place this function is called is in `main()`, where the argument
/// has already been validated by Clap.
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

/// The public-facing logger. This is an empty struct that uses the internal
/// functions of the rest of the logging utilities to perform the logging.
pub struct Logger;

/// A dummy type that allows a static reference to a global logger.
pub static LOGGER: Logger = Logger;

impl log::Log for Logger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= log::max_level()
    }

    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

        let mut guard = LOG.lock().unwrap();

        // We only log if we actually have a file to log to
        if let Some(log_file) = guard.as_mut() {
            // TODO: Also print the time here
            if writeln!(log_file, "{}", record.args()).is_err() {
                // FIXME: Need to figure out what to do here.
                //
                // Option 1:
                // This triggers some form of "soft panic", i.e. the program
                // should display a message to the user and give some
                // functionality to fix it;
                //
                // Option 2:
                // We set the log file to `None` and notify the user, along with
                // letting them know how to set the log file from within the
                todo!()
            }
        }
    }

    fn flush(&self) {
        if let Some(file) = LOG.lock().unwrap().as_mut() {
            if file.flush().is_err() {
                // Similar case as with encoutering an error in the `log` method:
                // We need to figure out what to do here.
                todo!()
            }
        }
    }
}
