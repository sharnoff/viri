//! Miscellaneous procedural macros for use in the editor
//!
//! Each collection of macros is given within a separate sub-module, much in the same way that
//! `viri::macros` is subdivided. In order to comply with the compiler's (perhaps strange rules),
//! we then have wrapper functions in the crate root for each of those.

#![feature(drain_filter)]

use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::ToTokens;
use syn::parse::ParseStream;
use syn::Token;

#[cfg(test)]
macro_rules! test_macro {
    (
        @name: $fn_name:ident,
        $macro_fn:ident! $(($($pre:tt)*))? {
            $($inp:tt)*
        } => {
            $($out:tt)*
        }
    ) => {
        #[test]
        fn $fn_name() {
            use proc_macro2::TokenStream;
            use syn::parse_str;

            // First convert the (right here) macro's tokens to a string
            let input_str = stringify!($($inp)*);
            let expected_str = stringify!($($out)*);

            // Then turn that string into a token stream we can work with
            let input_tokens: TokenStream = parse_str(input_str).unwrap();
            let expected_tokens: TokenStream = parse_str(expected_str).unwrap();

            // And then run the macro:
            let output_tokens: TokenStream =
                $macro_fn(
                    $({
                        let ts: TokenStream = parse_str(stringify!($($pre)*)).unwrap();
                        ts.into()
                    },)?
                    input_tokens.into(),
                )
                .into();

            let output_to_str = output_tokens.to_string();
            // We re-convert expected tokens to a string, because I'm not 100% sure that stringify!
            // will produce the same formatting.
            let expected_to_str = expected_tokens.to_string();

            if output_to_str != expected_to_str {
                panic!(
                    "output != expected\noutput = ```\n{}\n```,\nexpected = ```\n{}\n```",
                    output_to_str,
                    expected_to_str,
                )
            }
        }
    };
}

macro_rules! parse_macro_input2 {
    ($tokenstream:ident as $ty:ty) => {{
        match syn::parse2::<$ty>($tokenstream) {
            Ok(v) => v,
            Err(err) => return err.to_compile_error(),
        }
    }};
}

/// A helper trait for the `@<kwd>` syntax
trait Peek2 {
    /// Peeks at the second token in the parse stream, using it to determine whether the type can
    /// be parsed after consuming the first
    fn peek2(input: ParseStream) -> bool;
}

macro_rules! keywords {
    (mod kwd = $($kwds:ident),* $(,)?) => {
        mod kwd {
            $(
            syn::custom_keyword!($kwds);

            impl crate::Peek2 for $kwds {
                fn peek2(input: syn::parse::ParseStream) -> bool {
                    input.peek2($kwds)
                }
            }
            )*
        }
    };
}

/// Wrapper type for the `@<kwd>` syntax, parsing as `@ K`
#[derive(Parse)]
struct AtKwd<K: Peek2> {
    at_token: Token![@],
    kwd: K,
}

impl<K: Peek2> AtKwd<K> {
    /// Peeks at the first two tokens of the [`ParseStream`], returning if they start with
    /// `@ <kwd>`, where `<kwd>` is the keyword specified by `K`.
    fn peek(input: ParseStream) -> bool {
        input.peek(Token![@]) && K::peek2(input)
    }
}

impl<K: Peek2 + ToTokens> ToTokens for AtKwd<K> {
    fn to_tokens(&self, ts: &mut TokenStream2) {
        self.at_token.to_tokens(ts);
        self.kwd.to_tokens(ts);
    }
}

/// Helper macro for peeking with an [`AtKwd`]. Usage tends to look like:
///
/// ```ignore
/// #[derive(Parse)]
/// enum Foo {
///     #[peek_with(at_kwd![my_kwd], name = "`@my_kwd`")]
///     MyKwd(AtKwd<kwd::my_kwd>, BarBaz),
/// }
/// ```
#[rustfmt::skip]
macro_rules! at_kwd { ($name:ident) => { <AtKwd<kwd::$name>>::peek }; }

mod async_fns;
mod attr;
mod config;
mod dyn_serde;
mod extension;
mod flag;
mod history_core_test;
mod id;
mod init_expr;
mod named_fn;
mod type_sig;
mod typed;

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
    dyn_serde::register_dyn_clone,
    history_core_test::history_core_test,
    typed::{manual_derive_typed},
    type_sig::type_sig,
    flag::flag,
    extension::{make_extension, register_extensions, request},
}

#[proc_macro_attribute]
pub fn named(attr: TokenStream, item: TokenStream) -> TokenStream {
    named_fn::named(attr, item)
}

#[proc_macro_attribute]
pub fn async_method(attr: TokenStream, item: TokenStream) -> TokenStream {
    async_fns::async_method(attr, item)
}

#[proc_macro_derive(SerdeDynClone)]
pub fn serde_dyn_clone(item: TokenStream) -> TokenStream {
    dyn_serde::serde_dyn_clone(item)
}

#[proc_macro_derive(Typed)]
pub fn derive_typed(item: TokenStream) -> TokenStream {
    typed::manual_derive_typed(item)
}

#[proc_macro_attribute]
pub fn extension_export(attr: TokenStream, input: TokenStream) -> TokenStream {
    extension::extension_export(attr, input)
}
