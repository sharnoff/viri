use crate::macros::{config, init};
use crate::term;
use crate::view::{OutputSignal, View};
use crate::TermSize;
use clap::{Arg, ArgMatches};
use tokio::io;
use tokio::stream::Stream;

pub mod bottom_bar;
pub mod signal;

use bottom_bar::BottomBar;
pub use signal::make_event_stream;
use signal::Signal;

// Currently, we don't have any initialization that needs to be done here, but this is kept as a
// placeholder in case we *do* have more at some point.
init!();

config! {
    /// The configuration for the view container
    ///
    /// This is mostly just a wrapper type around [`bottom_bar::Config`].
    pub struct Config (ConfigBuilder) {
        pub use bottom_bar::Config as bottom_bar,
    }
}

/// The primary interface between the event loop and the tree of `View`s
///
/// This type takes [`Signal`]s as input and feeds them to the tree of [`View`]s, before taking the
/// resulting [view signal](OutputSignal) and returning a runtime singal, if any was generated.
pub struct Container {
    // The last recorded size of the terminal
    size: TermSize,
    // The inner `View` being displayed
    inner: InnerState,
    bottom_bar: BottomBar,
}

enum InnerState {
    Concrete(Box<dyn View>),
    WaitingForNonZeroSize(Box<dyn FnOnce(TermSize) -> Box<dyn View>>),
}

/// Adds the `clap` arguments to base app configuration
///
/// Essentially, because this module is the primary user of a large set of arguments, we want to
/// define them where they're actually used. So this function takes the clap [`App`](clap::App)
/// with some of the system-wide configuration and adds some more specific pieces.
#[rustfmt::skip]
pub fn add_args(app: clap::App) -> clap::App {
    app.arg(Arg::new("FILE")
            .about("Sets the file to open")
            .long_about(concat!(
                "Sets the file or directory to open.\n",
                "If no file is given, a blank file will be used instead.",
                // " When multiple files are",
                // " given, they will be opened in a predetermined, split, consistent layout with all",
                // " files visible.",
            ))
            .index(1)
        )
        /*
        .arg(Arg::new("vertical")
            .long("vert")
            .about("Indicates to open multiple files by splitting vertically")
            .long_about(concat!(
                "Indicates to open multiple files by splitting vertically.\n",
                "This setting only has an effect when opening multiple files at the same time.",
                " I'd only recommend using this in settings where the number of files is known",
                " beforehand, because it *will* give all of the files as a one-deep vertical",
                " split.",
            ))
            .conflicts_with("horizontal")
        )
        .arg(Arg::new("horizontal")
            .long("horiz")
            .about("Indicates to open multiple files by splitting horizontally")
            .long_about(concat!(
                "Indicates to open multiple files by splitting horizontally.\n",
                "This setting only has an effect when opening multiple files at the same time.",
                " I'd only recommend using this in settings where the number of files is known",
                " beforehand, because it *will* give all of the files as a one-deep horizontal",
                " split.",
            ))
            .conflicts_with("vertical")
        )
        */
}

impl Container {
    /// Constructs a new view container with the given program arguments
    ///
    /// This is only really intended to be called once, during program initialization. If there
    /// were any errors, they will be returned as a pre-formatted string with no added trailing
    /// newline.
    pub fn new(args: &ArgMatches) -> Result<Container, String> {
        let size = term::get_size().map_err(|e| format!("failed to get terminal size: {}", e))?;

        let bottom_bar = BottomBar::new();

        let initial_view = match args.value_of("FILE") {
            None => todo!(),
            _ => todo!(),
        };

        Ok(Container {
            size,
            inner: initial_view,
            bottom_bar,
        })
    }

    /// Runs the container with the given event stream
    ///
    /// This function is primarily used within `main` to hand off control of general program
    /// execution. The function terminates only once the event stream is closed and there is
    /// nothing more to handle.
    pub async fn run_event_loop(self, event_stream: impl Stream<Item = io::Result<Signal>>) {
        todo!()
    }
}
