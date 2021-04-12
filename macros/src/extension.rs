//! Macros for creating & registering the internally-defined extensions

use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{format_ident, quote, quote_spanned};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{parse_macro_input, token, Block, Ident, ItemFn, LitStr, Path, Signature, Token, Type};

keywords! { mod kwd = aliases, exports, init, path, extensions }

/// Input to the `make_extension!` macro
#[derive(Parse)]
struct MakeInput {
    #[prefix(kwd::path)]
    #[prefix(Token![:])]
    #[postfix(Token![,])]
    path: Path,

    #[prefix(kwd::aliases)]
    #[prefix(Token![:])]
    #[bracket]
    aliases_bracket: token::Bracket,
    #[postfix(Token![,])]
    #[inside(aliases_bracket)]
    #[parse_terminated(syn::parse::Parse::parse)]
    aliases: Punctuated<LitStr, Token![,]>,

    #[prefix(kwd::exports)]
    #[prefix(Token![:])]
    #[bracket]
    exports_bracket: token::Bracket,
    #[postfix(Token![,])]
    #[inside(exports_bracket)]
    #[parse_terminated(Export::parse)]
    exports: Punctuated<Export, Token![,]>,

    #[prefix(kwd::init)]
    #[prefix(Token![:])]
    #[postfix(Option<Token![,]>)]
    init_block: Block,
}

#[derive(Parse)]
struct Export {
    ident: Ident,

    #[prefix(Option<Token![as]> as as_token)]
    #[parse_if(as_token.is_some())]
    name: Option<LitStr>,
}

pub fn make_extension(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as MakeInput);
    #[rustfmt::skip]
    let MakeInput { path, aliases, exports, init_block, ..  } = input;
    let block_span = init_block.span();
    let init = init_block.stmts;

    // An iterator over (export name => wrapper function path)
    let exports = exports.into_iter().map(|Export { ident, name }| {
        let wrapper_path = format_ident!("__{}__export_wrapper", ident);
        let export_name = name.unwrap_or_else(|| LitStr::new(&ident.to_string(), ident.span()));
        quote!( #export_name => #wrapper_path )
    });

    let num_aliases = aliases.len();
    let alias_elems = aliases.into_iter().map(|alias| {
        quote_spanned! {alias.span()=>
            (#alias, Request {
                originating_ext: this,
                kind: RequestKind::GetValue {
                    from: Name { extension_id: builtin, method: String::from("SetAlias") },
                    arg: Value::new(String::from(#alias)),
                },
            }.spawn())
        }
    });

    let loader = quote! {
        pub use __ext_loader_module::SELF_PATH as __EXT_SELF_PATH;
        pub use __ext_loader_module::load as __ext_load;

        mod __ext_loader_module {
            use crate::dispatch::{ExtensionId, Value, Request, RequestKind, Name};
            use crate::macros::{async_fn, async_method};
            use ::std::collections::HashMap;
            use ::std::vec::Vec;
            use ::std::string::String;

            pub static SELF_PATH: &'static ::std::primitive::str = ::std::stringify!(#path);

            #[async_method]
            pub async fn load(builtin: ExtensionId, this: ExtensionId) -> HashMap<&'static str, async_fn![fn(Value) -> Value]> {
                let mut alias_futures: Vec<_> = Vec::with_capacity(#num_aliases);
                #( alias_futures.push(#alias_elems); )*
                for (name, f) in alias_futures {
                    match f.await {
                        Err(e) => ::log::warn!(
                            "unable to alias internal extension {:?} as {:?}",
                            SELF_PATH,
                            name,
                        ),
                        Ok(_) => (),
                    }
                }

                ::maplit::hashmap! {
                    #( #exports, )*
                }
            }
        }
    };

    let initialization = quote_spanned! {
        block_span=>
        crate::macros::init! {
            // No actual additional initialization is performed here, but the benefit of putting it
            // like this is that it's abundantly clear to someone using this that the
            // initialization occurs *before* the extension starts loading.
            #( #init )*
        }
    };

    quote!(
        #loader
        #initialization
    )
    .into()
}

#[derive(Parse)]
struct RegisterInput {
    #[parse_terminated(Ident::parse)]
    extensions: Punctuated<Ident, Token![,]>,
}

/// Constructs the hashmap of extension names to `Extension` objects
pub fn register_extensions(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as RegisterInput);

    // Iterator over (extension name => actual extension object)
    let exts = input.extensions.into_iter().map(|ext| {
        quote_spanned! {ext.span()=>
            self::#ext::__EXT_SELF_PATH => crate::extensions::Extension {
                loader: self::#ext::__ext_load,
                methods: crate::init::LazyInit::new(),
            }
        }
    });

    quote!(::maplit::hashmap! {
        #( #exts, )*
    })
    .into()
}

pub fn extension_export(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new(
            Span::call_site(),
            "the `#[extension_export]` attribute takes no arguments",
        )
        .to_compile_error()
        .into();
    }

    let func = parse_macro_input!(item as ItemFn);
    #[rustfmt::skip]
    let ItemFn { attrs, vis, sig, block } = func;

    let wrapper_name = format_ident!("__{}_export_wrapper", sig.ident);
    let func_name = &sig.ident;

    let (arg_fields, input_types) = match get_fields(&sig) {
        Ok((a, i)) => (a, i),
        Err(e) => return e.to_compile_error().into(),
    };

    let maybe_await = match &sig.asyncness {
        Some(t) => quote_spanned!(t.span()=> .await),
        None => TokenStream2::new(),
    };

    quote!(
        // Original function
        #( #attrs )*
        #vis #sig #block

        // Wrapper
        #[crate::macros::async_method]
        #vis async fn #wrapper_name(arg: crate::dispatch::Value) -> crate::dispatch::Value<'static> {
            use crate::macros::Typed;

            #[derive(Typed)]
            struct __Input {
                #( #arg_fields: #input_types, )*
            }

            let __Input { #( #arg_fields, )* } = arg.convert();
            crate::dispatch::Value::new( #func_name(#( #arg_fields, )*) #maybe_await )
        }
    )
    .into()
}

fn get_fields(sig: &Signature) -> syn::Result<(Vec<&Ident>, Vec<&Type>)> {
    use syn::{FnArg, Pat};

    macro_rules! err {
        ($($ts:tt)*) => {{
            return Err(syn::Error::new( $($ts)* ));
        }}
    }

    // Preliminary checks on the "outer" parts of the signature
    if let Some(unsafe_token) = &sig.unsafety {
        err!(
            unsafe_token.span(),
            "unsafe functions cannot be exported as part of an extension",
        );
    } else if !sig.generics.params.is_empty() {
        err!(
            sig.generics.params.span(),
            "generic functions cannot be exported as part of an extension",
        );
    } else if let Some(w_c) = &sig.generics.where_clause {
        err!(
            w_c.span(),
            "generic functions cannot be exported as part of an extension"
        );
    } else if let Some(vars) = &sig.variadic {
        err!(
            vars.span(),
            "variadic functions cannot be exported as part of an extension"
        );
    }

    // Now, get the names of the fields
    let mut idents = Vec::new();
    let mut types = Vec::new();

    for arg in sig.inputs.iter() {
        match arg {
            FnArg::Receiver(_) => panic!("unexpected receiver arg in `ItemFn`"),
            FnArg::Typed(pt) => {
                types.push(&*pt.ty);

                match &*pt.pat {
                    Pat::Ident(x) => idents.push(&x.ident),
                    p => err!(p.span(), "complex argument patterns cannot be exported"),
                }
            }
        }
    }

    Ok((idents, types))
}