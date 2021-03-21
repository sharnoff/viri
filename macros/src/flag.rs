use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use quote::quote_spanned;
use syn::{parse_macro_input, Attribute, Ident, Token, Visibility};

#[derive(Parse)]
struct Input {
    #[call(Attribute::parse_outer)]
    attrs: Vec<Attribute>,
    vis: Visibility,
    enum_kwd: Token![enum],

    // Allow an optional trailing semicolon, in case this macro is used like:
    //
    //   flag! {
    //      /// Docs! :)
    //      enum FooFlag;
    //   }
    #[postfix(Option<Token![;]>)]
    name: Ident,
}

pub fn flag(input: TokenStream) -> TokenStream {
    let Input {
        attrs, vis, name, ..
    } = parse_macro_input!(input as Input);

    quote_spanned!(
        name.span()=>

        #( #attrs )*
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        #vis enum #name {
            No,
            Yes,
        }

        impl #name {
            /// Converts the to a boolean
            ///
            /// Typical usage is within an `if` statement, e.g:
            /// ```ignore
            /// if my_flag.as_bool() {
            ///     do_flag_specific_thing();
            /// }
            /// ```
            #[allow(dead_code)]
            #vis fn as_bool(&self) -> ::std::primitive::bool {
                match self {
                    Self::Yes => true,
                    Self::No => false,
                }
            }
        }

        impl ::std::convert::From<::std::primitive::bool> for #name {
            fn from(b: ::std::primitive::bool) -> Self {
                match b {
                    true => Self::Yes,
                    false => Self::No,
                }
            }
        }
    )
    .into()
}
