//! Defines panic-handling utilities and sets the panic handler for the program
//!
//! The panic handler that's used throughout the runtime is defined here. It allows us to have
//! *real* panics during the course of the program - in case something goes terribly wrong - but
//! ALSO allows us to properly clean up if that happens, so that the user's terminal remains intact
//! *and* the panic messages are properly displayed.
//!
//! Many of the types and methods in this module are made public so that they can be easily
//! examined in the documentation - *NOT* so that they can be used elsewhere. This information will
//! hopefully provide insight into the inner workings of the editor.

use std::collections::HashMap;
use std::io::Write;
use std::panic::{self, PanicInfo};
use std::sync::{Mutex, MutexGuard};
use std::thread::{self, ThreadId};

// use crate::prelude::*;
use backtrace::Backtrace;
use lazy_static::lazy_static;

lazy_static! {
    static ref PANIC_WRITER: PanicWriter = PanicWriter::new();
}

/// A type to store the output of panicked threads for displaying later
///
/// There is a single static instance of this type to use for writing all of the panic messages to,
/// in case multiple threads panic. Any exit messages from [`add_exit_msg`] are also stored here.
///
/// [`add_exit_msg`]: fn.add_exit_msg.html
pub struct PanicWriter {
    threads: Mutex<HashMap<ThreadId, Vec<u8>>>,
    exit_msgs: Mutex<Vec<(ThreadId, String)>>,
}

impl PanicWriter {
    /// Initializes the panic writer as empty - i.e. no threads have panicked yet
    pub fn new() -> Self {
        Self {
            threads: Mutex::new(HashMap::new()),
            exit_msgs: Mutex::new(Vec::new()),
        }
    }

    /// Prints the contents of the global panic writer to a writer
    ///
    /// This function is usually called to clean up the program. As such, it is not allowed to
    /// panic. If any errors are encountered in the process of writing, they are ignored.
    pub fn write_all<W: Write>(mut writer: W) {
        let mut threads = force_lock(&PANIC_WRITER.threads);
        let mut exit_msgs = force_lock(&PANIC_WRITER.exit_msgs);

        let space_between = !(threads.is_empty() || exit_msgs.is_empty());

        threads
            .drain()
            .map(
                |(thread_id, panic_str)| match std::str::from_utf8(&panic_str) {
                    Ok(s) => writeln!(writer, "{}", s),
                    Err(_) => writeln!(
                        writer,
                        "<ThreadId {:?}: Invalid utf8: \n{:?}>",
                        thread_id, &panic_str
                    ),
                },
            )
            // We can't worry about handling the results, because there isn't another place we
            // could print to - we're already writing to the place where we'd print it them.
            .for_each(drop);

        // Purely for aesthetics: Only create a gap between things if the exit messages are
        if space_between {
            // A similar story here: we can't do anything with the result
            let _ = writeln!(writer);
        }

        if !exit_msgs.is_empty() {
            let _ = writeln!(writer, "Exit messages:");
            exit_msgs
                .drain(..)
                .map(|(thread_id, m)| writeln!(writer, "<ThreadId {:?}>: {}", thread_id, m))
                .for_each(drop);
        }
    }
}

/// Adds a message to be displayed after the program exits through a panic or hard exit
pub fn add_exit_msg<S: Into<String>>(msg: S) {
    force_lock(&PANIC_WRITER.exit_msgs).push((thread::current().id(), msg.into()));
}

/// Locks a mutex, ignoring whether it has been poisoned
fn force_lock<T>(data: &Mutex<T>) -> MutexGuard<T> {
    match data.lock() {
        Ok(g) => g,
        Err(e) => e.into_inner(),
    }
}

pub fn set_hook() {
    panic::set_hook(Box::new(panic_hook));
}

fn panic_hook(info: &PanicInfo<'_>) {
    // The majority of this function is very heavily based on the standard library's `default_hook`
    // function. The biggest difference is that we're redirecting the output writing to the
    // `PanicWriter` instead of stderr.
    //
    // A small difference is that we'll always print a backtrace, because panics *should never
    // happen* in normal execution

    let current_thread = thread::current();

    // If this thread has already panicked, we'll ignore it - double panics shouldn't happen.
    // TODO: Investigate this. Should we explicitly cater for double panics?
    let mut panic_writer = force_lock(&PANIC_WRITER.threads);
    if panic_writer.get(&current_thread.id()).is_some() {
        return;
    }

    // A comment taken from the standard library default hook:
    // "The current implementation always returns `Some`"
    // -- Rust version 1.40.0
    let location = info.location().unwrap();

    let msg = match info.payload().downcast_ref::<&'static str>() {
        Some(s) => *s,
        None => match info.payload().downcast_ref::<String>() {
            Some(s) => &s[..],
            None => "Box<Any>",
        },
    };

    let name = current_thread.name().unwrap_or("<unnamed>");

    let mut panic_msg: Vec<u8> = Vec::new();

    // write our panic message. We can discard the error because it'll never fail
    let _ = writeln!(
        panic_msg,
        "Thread '{}' panicked at '{}', {}",
        name, msg, location
    );
    let _ = write!(panic_msg, "{:?}", Backtrace::new());

    panic_writer.insert(current_thread.id(), panic_msg);

    return;
}
