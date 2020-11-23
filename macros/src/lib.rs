//! Miscellaneous procedural macros for use in the editor
//!
//! Each collection of macros is given within a separate sub-module, much in the same way that
//! `viri::macros` is subdivided. In order to comply with the compiler's (perhaps strange rules),
//! we then have wrapper functions in the crate root for each of those.

use proc_macro::TokenStream;

mod async_fns;
mod attr;
mod config;
mod id;
mod init_expr;
mod named_fn;

// A helper macro for bringing in the functions from the submodules
macro_rules! macros {
    ($mod_name:ident :: $fn_name:ident, $($tail:tt)*) => {
        #[proc_macro]
        pub fn $fn_name(input: TokenStream) -> TokenStream {
            $mod_name::$fn_name(input)
        }

        macros!($($tail)*);
    };
    ($mod_name:ident :: { $( $fn_name:ident ),* $(,)? }, $($tail:tt)*) => {
        $(macros!($mod_name::$fn_name,);)*
        macros!($($tail)*);
    };
    () => {};
}

macros! {
    init_expr::{init, initialize, require_initialized},
    config::config,
    attr::{new_attrs, provide_attrs, attr_type, impl_get_attr_any},
    async_fns::async_fn,
    id::id,
}

#[proc_macro_attribute]
pub fn named(attr: TokenStream, item: TokenStream) -> TokenStream {
    named_fn::named(attr, item)
}

#[proc_macro_attribute]
pub fn async_method(attr: TokenStream, item: TokenStream) -> TokenStream {
    async_fns::async_method(attr, item)
}
