#![allow(incomplete_features)]
#![feature(generic_associated_types)]
#![feature(associated_type_bounds)]
#![allow(clippy::needless_lifetimes)] // They aren't needless due to a bug with GATs
#![feature(never_type)]
#![deny(unused_must_use)]
// #![deny(unused_imports)]
// #![deny(unused_variables)]
// #![deny(dead_code)]
// #![deny(deprecated)]
#![deny(private_in_public)]
#![deny(mutable_borrow_reservation_conflict)]
#![allow(unused_parens)]
#![warn(clippy::perf)]
#![allow(clippy::style)] // Periodically disable to get other suggestions
#![allow(clippy::redundant_closure_call)] // https://github.com/rust-lang/rust-clippy/issues/3354
#![deny(clippy::len_zero)]

extern crate clap;
extern crate crossterm;
extern crate lazy_static;
extern crate log;
extern crate serde;
extern crate uuid;

#[macro_use]
mod config;
#[macro_use]
mod container;

mod event;
mod lock;
mod logger;
mod mode;
mod runtime;
mod text;
mod trie;
mod utils;
mod views;

use std::env;
use std::fs::{self, File};
use std::path::PathBuf;
use std::process;

use clap::App;
use log::LevelFilter;
use serde::{Deserialize, Serialize};

use container::Container;
use runtime::Signal;

#[derive(Debug, Clone, Serialize, Deserialize)]
struct MainConfig {
    log_file: Option<String>,
    log_level: Option<LevelFilter>,
}

fn main() {
    let clap_yaml = clap::load_yaml!("clap.yml");
    let matches = App::from(clap_yaml).get_matches();

    let (cfg_dir, force_cfg) = match matches.value_of("config") {
        Some(c) => (Some(PathBuf::from(c)), true),
        None => {
            let path = env::var("HOME")
                .ok()
                .map(|p| PathBuf::from(p).join(".config/viri"));
            (path, false)
        }
    };

    // Run some initializers. `logger` must go first because everything else might attempt to log
    // warnings or errors.
    logger::init();
    views::init();

    // try to load the config
    let main_config = cfg_dir.clone().and_then(|cfg_dir| {
        let cfg_file = cfg_dir.join("viri.yml");
        let read_result = fs::read_to_string(&cfg_file);

        match read_result {
            Err(e) => {
                if force_cfg {
                    eprintln!(
                        "Viri: Failed to open, could not read specified config file {:?}: {}",
                        &cfg_file, e
                    );
                    process::exit(1);
                } else {
                    None
                }
            }
            Ok(s) => match serde_yaml::from_str(&s) {
                Err(e) => {
                    eprintln!("Viri: Failed to parse config file {:?}: {}", &cfg_file, e);
                    process::exit(1);
                }
                Ok(cfg) => Some(cfg),
            },
        }
    });

    // Now we'll try to load view configs
    if let Some(dir) = cfg_dir.as_ref() {
        load_configs!(cfg_dir = dir, force = false, mod [views]);
    }

    // Get the log file, either from the args or a config file
    let log_file_opt = matches.value_of("log").or_else(|| {
        main_config
            .as_ref()
            .and_then(|c: &MainConfig| c.log_file.as_ref())
            .map(|s: &String| s.as_str())
    });

    if let Some(log_file) = log_file_opt {
        // Try to open the file
        let file = File::create(&log_file).unwrap_or_else(|e| {
            eprintln!("Viri: Failed to open log file {:?}: {}", log_file, e);
            process::exit(1);
        });
        logger::set_file(file);
    }

    // Get the log level, either from the args or a config file
    let log_level_opt = matches
        .value_of("log-level")
        .map(logger::level_filter_from_str)
        .or_else(|| main_config.as_ref().and_then(|c: &MainConfig| c.log_level));

    if let Some(log_level) = log_level_opt {
        logger::set_level(log_level);
    }

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
