//! Miscellaneous procedural macros for use in the editor
//!
//! Each collection of macros is given within a separate sub-module, much in the same way that
//! `viri::macros` is subdivided. In order to comply with the compiler's (perhaps strange rules),
//! we then have wrapper functions in the crate root for each of those.

use proc_macro::TokenStream;

mod config;
mod init_expr;

#[proc_macro]
pub fn init(input: TokenStream) -> TokenStream {
    init_expr::init(input)
}

#[proc_macro]
pub fn initialize(input: TokenStream) -> TokenStream {
    init_expr::initialize(input)
}

#[proc_macro]
pub fn require_initialized(input: TokenStream) -> TokenStream {
    init_expr::require_initialized(input)
}

#[proc_macro]
pub fn config(input: TokenStream) -> TokenStream {
    config::config(input)
}
