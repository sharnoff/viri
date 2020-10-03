use crate::macros::init;
use crate::view::{OutputSignal, View};
use clap::{Arg, ArgMatches};

// Currently, we don't have any initialization that needs to be done here, but this is kept as a
// placeholder in case we *do* have more at some point.
init!();

/// Adds the `clap` arguments to base app configuration
///
/// Essentially, because this module is the primary user of a large set of arguments, we want to
/// define them where they're actually used. So this function takes the clap [`App`](clap::App)
/// with some of the system-wide configuration and adds some more specific pieces.
#[rustfmt::skip]
pub fn add_args(app: clap::App) -> clap::App {
    app.arg(Arg::new("FILES")
            .about("Sets the file(s) to open")
            .long_about(concat!(
                "Sets the file(s) to open.\n",
                "If no files are given, a blank file will be used instead. When multiple files are",
                " given, they will be opened in a predetermined, split, consistent layout with all",
                " files visible.",
            ))
            .index(1)
        )
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
}

/// The primary interface between the event loop and the tree of `View`s
///
/// This type takes [`Signal`]s as input and feeds them to the tree of [`View`]s, before taking the
/// resulting [view signal](OutputSignal) and returning a runtime singal, if any was generated.
pub struct Container {}

pub enum Signal {}

impl Container {
    pub fn new(args: &ArgMatches) -> Result<Container, ()> {
        todo!()
    }
}
