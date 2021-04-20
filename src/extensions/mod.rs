//! Definitions of extensions that are internally defined
//!
//! The path to each extension is typically an upper Pascal-case version of the module name,
//! provided as the string in [`ExtensionPath::Internal`](crate::dispatch::ExtensionPath).
//!
//! In addition to these definitions, there are a couple helper traits analagous to those in
//! [`crate::init`] to assist with ensuring that all extensions are properly registered.

use std::collections::HashMap;

use crate::dispatch::{ExtensionId, Value};
use crate::init::LazyInit;
use crate::macros::{async_fn, init, register_extensions};

mod file;
mod text;

// The global registry of all internally-defined extensions. Each extension corresponds to a
// submodule (or perhaps a sub-submodule of this one)
static REGISTRY: LazyInit<HashMap<&'static str, Extension>> = LazyInit::new();

init! {
    mod text;
    mod file;
    REGISTRY.initialize_with(register_extensions![text, file]);
}

/// The data representing an internally-defined extension
///
/// This type mostly exists for the [`get_method`](Self::get_method) method, which returns the
/// registered function by the name, if it exists. Initializing an extension is done with the
/// [`load`](Self::load) method here.
pub struct Extension {
    // A callback that loads the extension, providing the values for `self.methods`
    loader: async_fn![
        fn(
            ExtensionId,
            ExtensionId,
        ) -> HashMap<&'static str, async_fn![fn(Value<'_>) -> Value<'static>]>
    ],

    // The methods provided by the extension. This value is not set until the loading function has
    // been run
    methods: LazyInit<HashMap<&'static str, async_fn![fn(Value<'_>) -> Value<'static>]>>,
}

impl Extension {
    /// Returns the function with the given name registered by this extension, if it exists
    pub fn get_method(&self, name: &str) -> Option<async_fn![fn(Value<'_>) -> Value<'static>]> {
        self.methods.get(name).cloned()
    }

    /// Loads the extension, performing any work that the extension may require as a result of it
    pub async fn load(&self, builtin: ExtensionId, this: ExtensionId) {
        self.methods
            .initialize_with((self.loader)(builtin, this).await);
    }
}

/// Returns a handle on the extension with the provided name, if it exists
///
/// If no extension with the given name exists, this function returns `None`.
pub fn extension_handle(name: &str) -> Option<&'static Extension> {
    REGISTRY.get(name)
}
