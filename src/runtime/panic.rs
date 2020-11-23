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

use crate::macros::init;
use crate::runtime;
use backtrace::Backtrace;
use lazy_static::lazy_static;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::io::{stderr, Write};
use std::panic::{self, PanicInfo};
use std::sync::{Arc, Mutex, MutexGuard};
use std::thread::{self, ThreadId};
use tokio::sync::watch::{channel, Receiver, Sender};
use tokio::sync::Notify;

lazy_static! {
    static ref PANIC_WRITER: PanicWriter = PanicWriter::new();

    /// Notifiers for whether a panic has occured
    ///
    /// The boolean value here is only given as true if there was indeed a panic. This is exposed
    /// through the `panic_listener` function, which just gives a notifier.
    static ref PANIC_NOTIFIERS: (Sender<bool>, Receiver<bool>) = channel(false);
}

init! {
    lazy_static::initialize(&PANIC_WRITER);
    lazy_static::initialize(&PANIC_NOTIFIERS);
    panic::set_hook(Box::new(panic_hook));
}

/// Writes all of of the stored panic messages to STDERR, alongside their backtraces
pub fn finalize() {
    PanicWriter::write_all(stderr());
}

/// Returns a notifier that is triggered whenever a panic has occured
///
/// This is intended to be used for elegant shutdown in the case of an unexpected early shutdown.
pub fn panic_listener() -> Arc<Notify> {
    let notify = Arc::new(Notify::new());
    let cloned = notify.clone();
    let mut rx = PANIC_NOTIFIERS.1.clone();

    runtime::spawn(async move {
        while let Ok(()) = rx.changed().await {
            if *rx.borrow() {
                notify.notify_one();
            }
        }

        panic!("panic receiver unexpectedly closed");
    });

    cloned
}

/// A type to store the output of panicked threads for displaying later
///
/// There is a single static instance of this type to use for writing all of the panic messages to,
/// in case multiple threads panic.
pub struct PanicWriter {
    threads: Mutex<HashMap<ThreadId, Vec<u8>>>,
}

impl PanicWriter {
    /// Initializes the panic writer as empty - i.e. no threads have panicked yet
    pub fn new() -> Self {
        Self {
            threads: Mutex::new(HashMap::new()),
        }
    }

    /// Prints the contents of the global panic writer to a writer
    ///
    /// This function is usually called to clean up the program. As such, it is not allowed to
    /// panic. If any errors are encountered in the process of writing, they are ignored.
    fn write_all<W: Write>(mut writer: W) {
        force_lock(&PANIC_WRITER.threads)
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
    }
}

/// Locks a mutex, ignoring whether it has been poisoned
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

    let current_thread = thread::current();

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

    // One thing to note here is that we don't care about panics that occur twice in the same
    // thread - we're generally expecting tokio to
    let mut panic_writer = force_lock(&PANIC_WRITER.threads);
    match panic_writer.entry(current_thread.id()) {
        Entry::Vacant(e) => drop(e.insert(panic_msg)),
        Entry::Occupied(mut e) => e.get_mut().extend(panic_msg),
    }
    drop(panic_writer);

    // We aren't using this result because:
    //  (1) It'll never fail, and
    //  (2) Even if it did, there's nothing we can do about it
    let _: Result<_, _> = PANIC_NOTIFIERS.0.send(true);

    return;
}
