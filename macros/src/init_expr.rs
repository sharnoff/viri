use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, quote_spanned};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{parse_macro_input, Block, Item, Path, Stmt};

/// A wrapper struct to parse the inside of a block expression
struct InnerBlock {
    stmts: Vec<Stmt>,
}

pub fn init(input: TokenStream) -> TokenStream {
    let fn_inner: TokenStream2 = initialize(input).into();

    let output = quote! {
        // A value to indicate the intialization status of the module:
        //   0 = Not initialized
        //   1 = In progress
        //   2 = Initialized
        #[doc(hidden)]
        pub static __INITIALIZED: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

        // A marker type that has `Initialized` implemented for it in the calling macro
        #[doc(hidden)]
        pub struct __IsInitialized;

        #[doc(hidden)]
        pub(super) fn __init() {
            let _: <__IsInitialized as crate::macros::Initialized>::This = __IsInitialized;

            {
                use std::sync::atomic::Ordering;

                let previous_value = __INITIALIZED.swap(1, Ordering::SeqCst);
                if previous_value != 0 {
                    panic!("module initialization called twice");
                }
            }

            {
                #fn_inner
            }

            __INITIALIZED.store(2, std::sync::atomic::Ordering::SeqCst);
        }
    };

    output.into()
}

pub fn initialize(input: TokenStream) -> TokenStream {
    let stmts = parse_macro_input!(input as InnerBlock)
        .stmts
        .into_iter()
        .map(|stmt| match stmt {
            Stmt::Item(Item::Mod(m)) if m.content.is_none() => {
                let span = m.span();
                let name = m.ident;
                quote_spanned! {
                    span=>
                    {
                        impl crate::macros::Initialized for #name::__IsInitialized {
                            type This = Self;
                        }

                        #name::__init();
                    }
                }
            }
            _ => quote_spanned!(stmt.span() => #stmt),
        });

    quote!(#( #stmts )*).into()
}

pub fn require_initialized(input: TokenStream) -> TokenStream {
    let path_segments = parse_macro_input!(input as Path);

    quote!({
        use std::sync::atomic::Ordering;

        let current_value = #path_segments :: __INITIALIZED.load(Ordering::SeqCst);
        let is_initialized = current_value == 2;
        assert!(is_initialized);
    })
    .into()
}

impl Parse for InnerBlock {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(InnerBlock {
            stmts: Block::parse_within(input)?,
        })
    }
}
