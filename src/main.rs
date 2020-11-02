//! A rusty editor

// "todo" categories:
//  * TODO-ERROR: Places where error handling should be improved
//  * TODO-ALG: Places where algorithms could be improved for efficiency
//  * TODO-DOC: Places where documentation is desparately needed
//  * TODO-CORRECTNESS: Where the code might not be correct, but works for now
//  * TODO-FEATURE: Where a feature should be added

// Feature sets
#![allow(incomplete_features)]
#![feature(
    // generic_associated_types,
    const_type_name, // allows `any::type_name` in a const context
    const_type_id, // Allows `TypeId::of` in a const context
    rustc_attrs,
    const_fn,
    const_generics,
)]
// Other flags:
#![allow(clippy::needless_lifetimes)] // They aren't needless due to a bug with GATs
#![warn(clippy::style, clippy::perf)]
#![deny(
    clippy::perf,
    clippy::len_zero,
    clippy::redundant_closure,
    private_in_public,
    mutable_borrow_reservation_conflict,
    unused_must_use
)]

use clap::{Arg, ArgMatches};
use std::ops::Deref;
use std::process::exit;
use std::sync::Arc;

#[macro_use]
mod macros;

mod config;
mod container;
mod event;
mod fs;
mod logger;
mod runtime;
mod size;
mod term;
mod utils;
mod view;

use container::Container;
use macros::initialize;

pub use size::{TermPos, TermSize};
pub use utils::{Never, XFrom, XInto};

/// The default name for the configuration file within its directory
static DEFAULT_CONFIG_FILE_NAME: &str = "viri.yml";

use fs::{File, Path};

/// A helper function for initializing modules that you might have written
///
/// If you have written any, this is where they should go.
fn initalize_custom_modules() {
    initialize! {
        // your module here
        mod container;
        mod view;
        mod config;
    };
}

fn main() {
    let mut clap_app = generate_main_clap_app();
    clap_app = container::add_args(clap_app);

    let matches = clap_app.get_matches();

    // First, initialize the runtime.
    //
    // There's a whole bunch more initialization we'll do later, but that gets deferred to
    // `continue_main_with_runtime`, which makes the assumption that the runtime has been
    // initialized.
    //
    // We need to keep it separate because initializing the runtime sets a panic hook that won't
    // display until we explicitly tell it to.
    initialize! {
        mod runtime;
    }

    // We'll provide just a little bit of extra information
    // This has to be an `AtomicBool` because `&mut _` is not unwind-safe
    let res = std::panic::catch_unwind(|| continue_main_with_runtime(&matches));

    // We try to leave the alternate screen. That will only really fail due to some form of IO
    // error, which means that there isn't much we can do. Logging something that should be a user
    // error is really a last resort.
    if let Err(e) = runtime::block_on(async { term::cleanup_terminal().await }) {
        log::error!("failed to leave alternate screen: {:?}", e);
    }

    runtime::slow_shutdown();

    if let Err(e) = res {
        std::panic::resume_unwind(e);
    }
}

/// Continues the process of setting up the application, only once the runtime has been initialized
///
/// Ordinarily, this would all be part of the standard main function, but there's certain
/// distinctions
fn continue_main_with_runtime(matches: &ArgMatches) {
    // Because the panic hook has been set, it's now appropriate for us to continue.
    initialize! {
        mod logger;
        mod fs;
    }

    let cfg_file = matches
        .value_of("config")
        .map(|path| Path::from(path).join(DEFAULT_CONFIG_FILE_NAME))
        .or_else(config::find_default_directory_location);

    // The majority of the rest of this function just serves to enact the various pieces of
    // configuration information.

    let main_config = config::set_initial_from_file(cfg_file.as_ref());
    if let Some(file_name) = matches.value_of("log-file") {
        main_config.log_file.store(Arc::new(Some(file_name.into())));
    }

    if let Some(level) = matches.value_of("log-level") {
        main_config
            .log_level
            .store(Arc::new(logger::level_filter_from_str(level)));
    }

    logger::set_level(main_config.log_level.load().deref());
    if let Some(file_name) = main_config.log_file.load().as_ref() {
        runtime::block_on(async {
            let file = match File::create(Path::from(file_name)).await {
                Ok(f) => f,
                Err(e) => {
                    eprintln!(
                        "fatal error: failed to open logging file '{}': {}",
                        file_name, e
                    );
                    exit(1);
                }
            };

            logger::set_file(file).await;
        });
    }

    log::info!("config parsed, logging fully initialized");

    initalize_custom_modules();

    // After setting up all of the configuration, we'll construct the initial view (note:
    // without displaying it)
    let container = match Container::new(&matches) {
        Ok(c) => c,
        // If we failed to set up the container, we'll just return.
        Err(err_msg) => {
            eprintln!("{}", err_msg);
            return;
        }
    };

    let event_stream = match container::make_event_stream() {
        Ok(st) => st,
        Err(e) => {
            eprintln!("failed to construct event stream: {}", e);
            return;
        }
    };

    if let Err(e) = runtime::block_on(async { term::prepare_terminal().await }) {
        eprintln!("fatal error: failed to prepare terminal: {}", e);
        exit(1);
    }
    runtime::block_on(async { container.run_event_loop(event_stream).await });
}

/// Generates the inital, main arguments for the application
///
/// This is used in conjunction with [`container::add_args`] to generate the full `clap`
/// application.
#[rustfmt::skip]
fn generate_main_clap_app() -> clap::App<'static> {
    clap::App::new("viri")
        .version("0.1")
        .author("Max Sharnoff <viri@max.sharnoff.org>")
        .about("A rusty, re-imagined vi")
        .arg(Arg::new("config")
            .long("config")
            .about("Sets the config file to use")
            // @req config-file-location v0
            .long_about(concat!(
                "Sets the config file to use.\n",
                "If not given, the default behavior is as follows: We search for the existence",
                " of a directory '$XDG_CONFIG_HOME/viri', '$HOME/.config/viri', and then",
                " '$HOME/.viri'. For the first directory $dir that we find, we parse the",
                " configuration from '$dir/viri.yml'.\n"
            ))
            .takes_value(true)
        )
        .arg(Arg::new("log-file")
            .long("log-file")
            .about("Optionally enables logging to a file")
            .long_about(concat!(
                "Optionally enables logging to a file\n",
            ))
            .takes_value(true)
        )
        .arg(Arg::new("log-level")
            .long("log-level")
            .about("Sets the level of log output to provide")
            .long_about(concat!(
                "Sets the level of log output to provide.\n",
                // @req default-log-level v0
                r#"Defaults to "Warn" - i.e. excluding "Trace", "Debug", and "Info" messages."#,
                " This can also be provided by the 'log_level' field in the configuration file",
            ))
            .requires("log-file")
            .about("Sets the log level to use")
            .takes_value(true)
            .possible_values(&["Off", "Trace", "Debug", "Info", "Warn", "Error"])
        )
}

/*
use container::Container;
use runtime::Signal;

fn main() {
    log::info!("Logging initialized.");
    log::debug!("Starting the runtime.");

    runtime::run(move || {
        let size = match runtime::get_size() {
            Ok(s) => s,
            Err(e) => {
                log::error!("main: Failed to get the size of the terminal: {}", e);
                runtime::add_exit_msg(format!(
                    "main: Failed to get the size of the terminal: {}",
                    e
                ));
                runtime::hard_exit(1)
            }
        };

        let args = matches
            .values_of("ARGS")
            .map(Iterator::collect::<Vec<_>>)
            .unwrap_or_else(Vec::new);

        log::debug!(
            "viri::main - Setting up `Container` with size {:?} and args {:?}",
            size,
            args
        );

        let mut container = Container::init(size, &args);

        log::info!("viri::main - Editor initialized successfully. Starting events loop");

        for event in runtime::EventsLoop {
            let signal = container.handle_rt_event(event);
            match signal {
                Some(Signal::Exit) => {
                    log::info!("viri::main - Received exit signal from `Container`. Returning");
                    return;
                }
                None => (),
            }
        }
    })
}
*/
