//! Handling of configuration for the editor
//!
//! There are broadly two things stored here: The traits for implementing configurable components,
//! alongside the top-level configuration root.
//!
//! The traits are not intended to be manually implemented; the `viri_macros::config!` macro is
//! provided exactly for this purpose.

use crate::fs::{self, Path};
use crate::macros::config;
use crate::runtime;
use log::LevelFilter;
use serde::{Deserialize, Serialize};
use std::env;
use std::process::exit;
use std::sync::Arc;

// Define the main, crate-level configuation
// @def main-config v0
config! {
    static ROOT_CONFIG;

    /// The main configuration for the application
    ///
    /// Additional modules with configuration should be added here.
    pub struct MainConfig (MainConfigBuilder) {
        #[flatten]
        pub use crate::view::Config as view_config,

        // NOTE: This really shouldn't be a string but a `fs::Path`, because then the location
        // given here wouldn't change if we changed our current working directory
        #[builder(Option<String> => std::convert::identity, Clone::clone)]
        pub log_file: Option<String> = None,

        /// The inital log level to use
        ///
        /// Please note that this is not synchronized with calls to [`logger::set_level`], and so
        /// is not guaranteed to be equal at runtime.
        ///
        /// [`logger::set_level`]: crate::logger::set_level
        // @def default-log-level v0
        pub log_level: LevelFilter = LevelFilter::Warn,
    }
}

/// Configurable items that can be accessed at runtime
///
/// While implementing this trait can be done manually, it's typically generated through the
/// `config!` and `global_config!` macros, which handle much of the boilerplate here.
pub trait Configurable: Sized {
    /// A type from which the config can be constructed
    ///
    /// This is the type that's actually parsed in order to construct the configuration at runtime.
    type Builder: Default + Serialize + for<'a> Deserialize<'a> + Into<Self>;

    /// Returns a reference to the current global configuration
    ///
    /// Within macros, this is generated by the parent configuration, relying on *its*
    /// implementation of `Configurable`.
    fn get() -> Arc<Self>;

    /// Converts the configuration into a `Builder` that can be used to exactly re-construct it
    ///
    /// This function is provided as part of the feature set allowing configuration serialization,
    /// hence why `Builder` has the constraint that it must implement `Serialize`.
    fn to_builder(&self) -> Self::Builder;
}

/// A trait for pieces of configuration that are stored as part of another
///
/// The items defined here are really just a subset of what's required for [`Configurable`], so
/// that the [`config`] macro may come and finish the implementation.
pub trait ChildConfig: Sized {
    /// A copy of `Configurable::Builder` for inner configs, so that macros can generate
    /// implemenations of [`Configurable`] given only an impementation of `ChildConfig`.
    ///
    /// For more information, please refer to [`Configurable`]
    type Builder: Default + Serialize + for<'a> Deserialize<'a> + Into<Self>;

    /// An copied version of [`Configurable::to_builder`] for the same reason as for `Builder`
    fn to_builder(&self) -> Self::Builder;
}

/// Sets the initial main configuration, parsing from the default file in the configuration
/// directory, if given
///
/// This function can only be run once, at program initialization. As such, it's only called from
/// within `main`.
pub fn set_initial_from_file(cfg_file: Option<&Path>) -> Arc<MainConfig> {
    if ROOT_CONFIG.load().is_some() {
        panic!(
            "cannot set initial configuration, `main_config` module has already been initialized"
        );
    }

    let builder: MainConfigBuilder = runtime::block_on(async {
        #[rustfmt::skip]
        let cfg = (fs::read_to_string(cfg_file.as_ref()?).await)
            .map(|s| serde_yaml::from_str(&s))
            // Unwrap an IO error
            .unwrap_or_else(|e| {
                eprintln!("fatal error: failed to read config file {:?}: {}", cfg_file, e);
                exit(1);
            })
            // Unwrap a serialization error
            .unwrap_or_else(|e| {
                eprintln!("fatal error: failed to parse config file {:?}: {}", cfg_file, e);
                exit(1);
            });

        Some(cfg)
    })
    .unwrap_or_default();

    let arc: Arc<MainConfig> = Arc::new(builder.into());
    ROOT_CONFIG.store(Some(arc.clone()));

    arc
}

/// Attempts to find a directory containing configuration information, checking the standard
/// expected places (at least on Linux)
pub fn find_default_directory_location() -> Option<Path> {
    // For the default config location, we'll look at the following locations in order:
    //   * $XDG_CONFIG_HOME/viri
    //   * $HOME/.config/viri
    //   * $HOME/.viri
    // @def config-file-location v0
    if let Ok(xdg_config_dir) = env::var("XDG_CONFIG_HOME").map(Path::from) {
        // Check $XDG_CONFIG_HOME/viri
        let path = xdg_config_dir.join("viri");
        if path.exists() {
            return Some(path);
        }
    } else if let Ok(home_dir) = env::var("HOME").map(Path::from) {
        // Check $HOME/.config/viri
        let home_config_dir = home_dir.join(".config/viri");
        if home_config_dir.exists() {
            return Some(home_config_dir);
        }

        // Check $HOME/.viri
        let home_dot_viri = home_dir.join(".viri");
        if home_dot_viri.exists() {
            return Some(home_dot_viri);
        }
    }

    None
}
