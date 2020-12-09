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
//
// One additional thing to note here is that we *intentionally* don't make anything here
// asynchronous. If we did, it would open up the door to the asynchronous executor atttempting to
// call itself during a panic, which might blow up in unexpected ways.
//
// The only usage of tokio here is for tasks that want to be notified whenever panics happen.

use crate::macros::init;
use backtrace::Backtrace;
use lazy_static::lazy_static;
use std::io::{stderr, Write};
use std::panic::{self, PanicInfo};
use std::sync::{Mutex, MutexGuard};
use std::thread::{self, ThreadId};
use tokio::sync::watch::{channel, Receiver, Sender};
use tokio::sync::Notify;

lazy_static! {
    static ref PANIC_WRITER: PanicWriter = PanicWriter::new();

    /// (*Internal*) Notifiers for whether a panic has occured
    ///
    /// The boolean value here is only given as true if there was indeed a panic. This is exposed
    /// through the `panic_listener` function, which just gives a notifier.
    static ref PANIC_NOTIFIERS: (Sender<bool>, Receiver<bool>) = channel(false);

    /// (*Internal*) A single notifier for whether a panic has occured
    ///
    /// This is exposed through the `panic_listener` function, which simply returns a reference to
    /// it.
    static ref PANIC_NOTIFIER: Notify = Notify::new();
}

init! {
    lazy_static::initialize(&PANIC_WRITER);
    lazy_static::initialize(&PANIC_NOTIFIER);
    panic::set_hook(Box::new(panic_hook));
}

/// Writes all of of the stored panic messages to STDERR, alongside their backtraces
pub fn finalize() {
    // `take_hook` unregisters our custom panic hook, and replaces it with the default one
    let _ = panic::take_hook();
    // and then - only once we've transferred the panics away - we write the contents
    PanicWriter::write_all(stderr());
}

/// Returns a notifier that is triggered whenever a panic has occured
///
/// This is one part of the system that can be used for elegant handling in the case of an
/// unexpected early shutdown. Please note that this will be triggered on *any* panic - even for
/// internal systems that may expect some form of panics to occur, and so does not always indicate
/// that a shutdown will occur as a result of the panic.
///
/// This might be used in conjunction with [`runtime::shutdown_notifier`] to get more accurate
/// diagnostics about the current state of the program.
///
/// [`runtime::shutdown_notifier`]: crate::runtime::shutdown_notifier.
pub fn panic_notifier() -> &'static Notify {
    &PANIC_NOTIFIER
}

/// A type to store the output of panicked threads for displaying later
///
/// There is a single static instance of this type to use for writing all of the panic messages to,
/// in case multiple threads panic.
pub struct PanicWriter {
    messages: Mutex<Vec<(ThreadId, Vec<u8>)>>,
}

impl PanicWriter {
    /// Initializes the panic writer as empty - i.e. no threads have panicked yet
    pub fn new() -> Self {
        PanicWriter {
            messages: Mutex::new(Vec::new()),
        }
    }

    /// Prints the contents of the global panic writer to a writer
    ///
    /// This function is usually called to clean up the program. As such, it is not allowed to
    /// panic. If any errors are encountered in the process of writing, they are ignored.
    fn write_all<W: Write>(mut writer: W) {
        // TODO-ERROR: Should be re-enabled once logging is no longer async
        // @req "log is async" v0
        // log::debug!("{}: writing panic information", file!());

        force_lock(&PANIC_WRITER.messages)
            .drain(..)
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

        // Same as above. @req "log is async" v0
        // log::debug!("{}: done writing panic information", file!());
    }
}

/// Utility function to lock a mutex, ignoring whether it has been poisoned
fn force_lock<T>(data: &Mutex<T>) -> MutexGuard<T> {
    match data.lock() {
        Ok(g) => g,
        Err(e) => e.into_inner(),
    }
}

fn panic_hook(info: &PanicInfo<'_>) {
    // The majority of this function is very heavily based on the standard library's `default_hook`
    // function. The biggest difference is that we're redirecting the output writing to the
    // `PanicWriter` instead of stderr.
    //
    // A small difference is that we'll always print a backtrace, because panics *should never
    // happen* in normal execution
    //
    // One additional thing to note here is that we don't care about panics that occur twice in the
    // same thread - we're generally expecting tokio to handle panics in a way that means it's
    // entirely possible for two different *tasks* to panic on the same *worker thread*.

    let msg = match info.payload().downcast_ref::<&'static str>() {
        Some(s) => *s,
        None => match info.payload().downcast_ref::<String>() {
            Some(s) => s.as_str(),
            None => "Box<Any>",
        },
    };

    let thread = thread::current();
    let name = thread.name().unwrap_or("<unnamed>");

    let mut panic_msg: Vec<u8> = Vec::new();

    // write our panic message. We can discard the error because it'll never fail, and we can't
    // exactly panic if it does
    let _ = match info.location() {
        Some(location) => writeln!(
            panic_msg,
            "Thread '{}' panicked at '{}', {}",
            name, msg, location
        ),
        None => writeln!(panic_msg, "Thread '{}' panicked at {}", name, msg),
    };
    let _ = write!(panic_msg, "{:?}", Backtrace::new());
    let mut panic_writer = force_lock(&PANIC_WRITER.messages);
    panic_writer.push((thread.id(), panic_msg));
    drop(panic_writer);

    // After we've fully handled this panic, we notify any tasks that are currently waiting that it
    // happened
    //
    // This can (thankfully) be called from outside async code, even though it interacts with it
    PANIC_NOTIFIER.notify_waiters();

    return;
}
