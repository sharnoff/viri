use std::collections::HashMap;
use std::io::{self, Write};
use std::panic::{self, PanicInfo};
use std::sync::{Mutex, MutexGuard};
use std::thread::{self, ThreadId};

use backtrace::Backtrace;
use lazy_static::lazy_static;

lazy_static! {
    static ref PANIC_WRITER: PanicWriter = PanicWriter::new();
}

struct PanicWriter {
    inner: Mutex<HashMap<ThreadId, Vec<u8>>>,
}

impl PanicWriter {
    fn new() -> Self {
        PanicWriter {
            inner: Mutex::new(HashMap::new()),
        }
    }

    fn print_all<W: io::Write>(&self, mut writer: W) {
        hard_lock(&self.inner)
            .drain()
            .map(|(t_id, v)| match String::from_utf8(v) {
                Ok(s) => writeln!(writer, "{}", s),
                Err(_) => writeln!(writer, "<ThreadId {:?}: Invalid utf8>", t_id),
            })
            .for_each(drop);
    }
}

pub fn cleanup_print<W: io::Write>(writer: W) {
    PANIC_WRITER.print_all(writer);
}

pub fn set_hook() {
    panic::set_hook(Box::new(hook));
}

fn hook(info: &PanicInfo<'_>) {
    // The majority of this function is very heavily based on the standard
    // library's `default_hook` function. The only difference is that we're
    // redirecting the output writing to

    // One key difference is that we'll always print a backtrace.

    let current_thread = thread::current();

    // If this thread has already panicked, we'll ignore it.
    let mut panic_writer = hard_lock(&PANIC_WRITER.inner);
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

    let mut writer: Vec<u8> = Vec::new();

    // write our panic message.
    let _ = writeln!(
        writer,
        "Thread '{}' panicked at '{}', {}",
        name, msg, location
    );
    let _ = write!(writer, "{:?}", Backtrace::new());

    panic_writer.insert(current_thread.id(), writer);

    return;
}

fn hard_lock<T>(data: &Mutex<T>) -> MutexGuard<T> {
    match data.lock() {
        Ok(g) => g,
        Err(e) => e.into_inner(),
    }
}
